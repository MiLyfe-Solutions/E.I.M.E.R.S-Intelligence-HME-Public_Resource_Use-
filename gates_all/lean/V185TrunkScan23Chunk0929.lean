import V185TrunkScan23Chunk0928

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5498503 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 1, 5, 2]
def baseStart_5498503 : Nat := 118140960795 + 5498503 * 2 ^ 59
def prefixEnd_5498503 : Nat := 4983230072969 + 3 ^ 40 * 5498503 * 2
def baseEnd_5498503 : Nat := 2823374919188805815425351

theorem tailTrace_5498503 : CollatzResearch.WordTrace tailWord_5498503 prefixEnd_5498503 2823374919188805815425351 := by
  unfold tailWord_5498503
  simp only [CollatzResearch.WordTrace]
  refine ⟨200546879998870175394364163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133697919999246783596242775 200546879998870175394364163)
  ·
    refine ⟨300820319998305263091546245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200546879998870175394364163 300820319998305263091546245)
    ·
      refine ⟨56403809999682236829664921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300820319998305263091546245 56403809999682236829664921)
      ·
        refine ⟨42302857499761677622248691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56403809999682236829664921 42302857499761677622248691)
        ·
          refine ⟨63454286249642516433373037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42302857499761677622248691 63454286249642516433373037)
          ·
            refine ⟨23795357343615943662514889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63454286249642516433373037 23795357343615943662514889)
            ·
              refine ⟨17846518007711957746886167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23795357343615943662514889 17846518007711957746886167)
              ·
                refine ⟨26769777011567936620329251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17846518007711957746886167 26769777011567936620329251)
                ·
                  refine ⟨40154665517351904930493877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26769777011567936620329251 40154665517351904930493877)
                  ·
                    refine ⟨3764499892251741087233801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40154665517351904930493877 3764499892251741087233801)
                    ·
                      refine ⟨2823374919188805815425351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764499892251741087233801 2823374919188805815425351)
                      ·
                        rfl

theorem cell23_5498503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_5498503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498503 prefixEnd_5498503 := by exact prefixLift 5498503
  have htrace : WordTrace (prefixWord ++ tailWord_5498503) baseStart_5498503 baseEnd_5498503 := by
    simpa [prefixWord, tailWord_5498503, baseEnd_5498503] using wordTrace_append hprefix tailTrace_5498503
  have hstable : (prefixWord ++ tailWord_5498503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498503).length < 2 ^ (prefixWord ++ tailWord_5498503).sum := by decide
  have hdescent : baseEnd_5498503 < baseStart_5498503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498504 : List Nat := [2, 1, 3, 5, 1, 2, 1, 3, 1, 4]
def baseStart_5498504 : Nat := 118140960795 + 5498504 * 2 ^ 59
def prefixEnd_5498504 : Nat := 4983230072969 + 3 ^ 40 * 5498504 * 2
def baseEnd_5498504 : Nat := 941125144223153437170949

theorem tailTrace_5498504 : CollatzResearch.WordTrace tailWord_5498504 prefixEnd_5498504 941125144223153437170949 := by
  unfold tailWord_5498504
  simp only [CollatzResearch.WordTrace]
  refine ⟨100273458235933276282575283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133697944314577701710100377 100273458235933276282575283)
  ·
    refine ⟨150410187353899914423862925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100273458235933276282575283 150410187353899914423862925)
    ·
      refine ⟨56403820257712467908948597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150410187353899914423862925 56403820257712467908948597)
      ·
        refine ⟨5287858149160543866463931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56403820257712467908948597 5287858149160543866463931)
        ·
          refine ⟨7931787223740815799695897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5287858149160543866463931 7931787223740815799695897)
          ·
            refine ⟨5948840417805611849771923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7931787223740815799695897 5948840417805611849771923)
            ·
              refine ⟨8923260626708417774657885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5948840417805611849771923 8923260626708417774657885)
              ·
                refine ⟨3346222735015656665496707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8923260626708417774657885 3346222735015656665496707)
                ·
                  refine ⟨5019334102523484998245061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3346222735015656665496707 5019334102523484998245061)
                  ·
                    refine ⟨941125144223153437170949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5019334102523484998245061 941125144223153437170949)
                    ·
                      rfl

theorem cell23_5498504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_5498504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498504 prefixEnd_5498504 := by exact prefixLift 5498504
  have htrace : WordTrace (prefixWord ++ tailWord_5498504) baseStart_5498504 baseEnd_5498504 := by
    simpa [prefixWord, tailWord_5498504, baseEnd_5498504] using wordTrace_append hprefix tailTrace_5498504
  have hstable : (prefixWord ++ tailWord_5498504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498504).length < 2 ^ (prefixWord ++ tailWord_5498504).sum := by decide
  have hdescent : baseEnd_5498504 < baseStart_5498504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498520 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 2, 3, 2]
def baseStart_5498520 : Nat := 118140960795 + 5498520 * 2 ^ 59
def prefixEnd_5498520 : Nat := 4983230072969 + 3 ^ 40 * 5498520 * 2
def baseEnd_5498520 : Nat := 2823383648359932248912773

theorem tailTrace_5498520 : CollatzResearch.WordTrace tailWord_5498520 prefixEnd_5498520 2823383648359932248912773 := by
  unfold tailWord_5498520
  simp only [CollatzResearch.WordTrace]
  refine ⟨100273750019904293648866507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133698333359872391531822009 100273750019904293648866507)
  ·
    refine ⟨150410625029856440473299761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100273750019904293648866507 150410625029856440473299761)
    ·
      refine ⟨112807968772392330354974821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150410625029856440473299761 112807968772392330354974821)
      ·
        refine ⟨21151494144823561941557779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112807968772392330354974821 21151494144823561941557779)
        ·
          refine ⟨31727241217235342912336669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21151494144823561941557779 31727241217235342912336669)
          ·
            refine ⟨11897715456463253592126251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31727241217235342912336669 11897715456463253592126251)
            ·
              refine ⟨17846573184694880388189377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11897715456463253592126251 17846573184694880388189377)
              ·
                refine ⟨13384929888521160291142033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17846573184694880388189377 13384929888521160291142033)
                ·
                  refine ⟨10038697416390870218356525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13384929888521160291142033 10038697416390870218356525)
                  ·
                    refine ⟨3764511531146576331883697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10038697416390870218356525 3764511531146576331883697)
                    ·
                      refine ⟨2823383648359932248912773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764511531146576331883697 2823383648359932248912773)
                      ·
                        rfl

theorem cell23_5498520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_5498520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498520 prefixEnd_5498520 := by exact prefixLift 5498520
  have htrace : WordTrace (prefixWord ++ tailWord_5498520) baseStart_5498520 baseEnd_5498520 := by
    simpa [prefixWord, tailWord_5498520, baseEnd_5498520] using wordTrace_append hprefix tailTrace_5498520
  have hstable : (prefixWord ++ tailWord_5498520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498520).length < 2 ^ (prefixWord ++ tailWord_5498520).sum := by decide
  have hdescent : baseEnd_5498520 < baseStart_5498520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498543 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 2, 4]
def baseStart_5498543 : Nat := 118140960795 + 5498543 * 2 ^ 59
def prefixEnd_5498543 : Nat := 4983230072969 + 3 ^ 40 * 5498543 * 2
def baseEnd_5498543 : Nat := 941131819471661886308389

theorem tailTrace_5498543 : CollatzResearch.WordTrace tailWord_5498543 prefixEnd_5498543 941131819471661886308389 := by
  unfold tailWord_5498543
  simp only [CollatzResearch.WordTrace]
  refine ⟨200548338918725262225820283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133698892612483508150546855 200548338918725262225820283)
  ·
    refine ⟨300822508378087893338730425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200548338918725262225820283 300822508378087893338730425)
    ·
      refine ⟨225616881283565920004047819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300822508378087893338730425 225616881283565920004047819)
      ·
        refine ⟨338425321925348880006071729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225616881283565920004047819 338425321925348880006071729)
        ·
          refine ⟨253818991444011660004553797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338425321925348880006071729 253818991444011660004553797)
          ·
            refine ⟨47591060895752186250853837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253818991444011660004553797 47591060895752186250853837)
            ·
              refine ⟨17846647835907069844070189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47591060895752186250853837 17846647835907069844070189)
              ·
                refine ⟨6692492938465151191526321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17846647835907069844070189 6692492938465151191526321)
                ·
                  refine ⟨5019369703848863393644741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6692492938465151191526321 5019369703848863393644741)
                  ·
                    refine ⟨941131819471661886308389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5019369703848863393644741 941131819471661886308389)
                    ·
                      rfl

theorem cell23_5498543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 4].length) (baseStart_5498543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498543 prefixEnd_5498543 := by exact prefixLift 5498543
  have htrace : WordTrace (prefixWord ++ tailWord_5498543) baseStart_5498543 baseEnd_5498543 := by
    simpa [prefixWord, tailWord_5498543, baseEnd_5498543] using wordTrace_append hprefix tailTrace_5498543
  have hstable : (prefixWord ++ tailWord_5498543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498543).length < 2 ^ (prefixWord ++ tailWord_5498543).sum := by decide
  have hdescent : baseEnd_5498543 < baseStart_5498543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498546 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_5498546 : Nat := 118140960795 + 5498546 * 2 ^ 59
def prefixEnd_5498546 : Nat := 4983230072969 + 3 ^ 40 * 5498546 * 2
def baseEnd_5498546 : Nat := 2823396998856949147187653

theorem tailTrace_5498546 : CollatzResearch.WordTrace tailWord_5498546 prefixEnd_5498546 2823396998856949147187653 := by
  unfold tailWord_5498546
  simp only [CollatzResearch.WordTrace]
  refine ⟨50137112084428598434544873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133698965558476262492119661 50137112084428598434544873)
  ·
    refine ⟨37602834063321448825908655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50137112084428598434544873 37602834063321448825908655)
    ·
      refine ⟨56404251094982173238862983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37602834063321448825908655 56404251094982173238862983)
      ·
        refine ⟨84606376642473259858294475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56404251094982173238862983 84606376642473259858294475)
        ·
          refine ⟨126909564963709889787441713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84606376642473259858294475 126909564963709889787441713)
          ·
            refine ⟨95182173722782417340581285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126909564963709889787441713 95182173722782417340581285)
            ·
              refine ⟨17846657573021703251358991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95182173722782417340581285 17846657573021703251358991)
              ·
                refine ⟨26769986359532554877038487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17846657573021703251358991 26769986359532554877038487)
                ·
                  refine ⟨40154979539298832315557731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26769986359532554877038487 40154979539298832315557731)
                  ·
                    refine ⟨60232469308948248473336597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40154979539298832315557731 60232469308948248473336597)
                    ·
                      refine ⟨2823396998856949147187653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60232469308948248473336597 2823396998856949147187653)
                      ·
                        rfl

theorem cell23_5498546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_5498546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498546 prefixEnd_5498546 := by exact prefixLift 5498546
  have htrace : WordTrace (prefixWord ++ tailWord_5498546) baseStart_5498546 baseEnd_5498546 := by
    simpa [prefixWord, tailWord_5498546, baseEnd_5498546] using wordTrace_append hprefix tailTrace_5498546
  have hstable : (prefixWord ++ tailWord_5498546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498546).length < 2 ^ (prefixWord ++ tailWord_5498546).sum := by decide
  have hdescent : baseEnd_5498546 < baseStart_5498546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498556 : List Nat := [2, 2, 2, 3, 1, 2, 2, 9]
def baseStart_5498556 : Nat := 118140960795 + 5498556 * 2 ^ 59
def prefixEnd_5498556 : Nat := 4983230072969 + 3 ^ 40 * 5498556 * 2
def baseEnd_5498556 : Nat := 104570449394944226224541

theorem tailTrace_5498556 : CollatzResearch.WordTrace tailWord_5498556 prefixEnd_5498556 104570449394944226224541 := by
  unfold tailWord_5498556
  simp only [CollatzResearch.WordTrace]
  refine ⟨100274406533839082723021761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133699208711785443630695681 100274406533839082723021761)
  ·
    refine ⟨75205804900379312042266321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100274406533839082723021761 75205804900379312042266321)
    ·
      refine ⟨56404353675284484031699741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75205804900379312042266321 56404353675284484031699741)
      ·
        refine ⟨21151632628231681511887403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56404353675284484031699741 21151632628231681511887403)
        ·
          refine ⟨31727448942347522267831105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21151632628231681511887403 31727448942347522267831105)
          ·
            refine ⟨23795586706760641700873329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31727448942347522267831105 23795586706760641700873329)
            ·
              refine ⟨17846690030070481275654997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23795586706760641700873329 17846690030070481275654997)
              ·
                refine ⟨104570449394944226224541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17846690030070481275654997 104570449394944226224541)
                ·
                  rfl

theorem cell23_5498556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 9].length) (baseStart_5498556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498556 prefixEnd_5498556 := by exact prefixLift 5498556
  have htrace : WordTrace (prefixWord ++ tailWord_5498556) baseStart_5498556 baseEnd_5498556 := by
    simpa [prefixWord, tailWord_5498556, baseEnd_5498556] using wordTrace_append hprefix tailTrace_5498556
  have hstable : (prefixWord ++ tailWord_5498556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498556).length < 2 ^ (prefixWord ++ tailWord_5498556).sum := by decide
  have hdescent : baseEnd_5498556 < baseStart_5498556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498567 : List Nat := [1, 1, 4, 1, 1, 1, 4, 5, 1, 2, 2]
def baseStart_5498567 : Nat := 118140960795 + 5498567 * 2 ^ 59
def prefixEnd_5498567 : Nat := 4983230072969 + 3 ^ 40 * 5498567 * 2
def baseEnd_5498567 : Nat := 2823407781950693565025057

theorem tailTrace_5498567 : CollatzResearch.WordTrace tailWord_5498567 prefixEnd_5498567 2823407781950693565025057 := by
  unfold tailWord_5498567
  simp only [CollatzResearch.WordTrace]
  refine ⟨200549214270638314324693955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133699476180425542883129303 200549214270638314324693955)
  ·
    refine ⟨300823821405957471487040933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200549214270638314324693955 300823821405957471487040933)
    ·
      refine ⟨56404466513617025903820175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300823821405957471487040933 56404466513617025903820175)
      ·
        refine ⟨84606699770425538855730263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56404466513617025903820175 84606699770425538855730263)
        ·
          refine ⟨126910049655638308283595395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84606699770425538855730263 126910049655638308283595395)
          ·
            refine ⟨190365074483457462425393093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126910049655638308283595395 190365074483457462425393093)
            ·
              refine ⟨35693451465648274204761205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190365074483457462425393093 35693451465648274204761205)
              ·
                refine ⟨3346261074904525706696363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35693451465648274204761205 3346261074904525706696363)
                ·
                  refine ⟨5019391612356788560044545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3346261074904525706696363 5019391612356788560044545)
                  ·
                    refine ⟨3764543709267591420033409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5019391612356788560044545 3764543709267591420033409)
                    ·
                      refine ⟨2823407781950693565025057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764543709267591420033409 2823407781950693565025057)
                      ·
                        rfl

theorem cell23_5498567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_5498567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498567 prefixEnd_5498567 := by exact prefixLift 5498567
  have htrace : WordTrace (prefixWord ++ tailWord_5498567) baseStart_5498567 baseEnd_5498567 := by
    simpa [prefixWord, tailWord_5498567, baseEnd_5498567] using wordTrace_append hprefix tailTrace_5498567
  have hstable : (prefixWord ++ tailWord_5498567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498567).length < 2 ^ (prefixWord ++ tailWord_5498567).sum := by decide
  have hdescent : baseEnd_5498567 < baseStart_5498567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498570 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_5498570 : Nat := 118140960795 + 5498570 * 2 ^ 59
def prefixEnd_5498570 : Nat := 4983230072969 + 3 ^ 40 * 5498570 * 2
def baseEnd_5498570 : Nat := 2823409322392657053287543

theorem tailTrace_5498570 : CollatzResearch.WordTrace tailWord_5498570 prefixEnd_5498570 2823409322392657053287543 := by
  unfold tailWord_5498570
  simp only [CollatzResearch.WordTrace]
  refine ⟨50137330922406861459263291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133699549126418297224702109 50137330922406861459263291)
  ·
    refine ⟨75205996383610292188894937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50137330922406861459263291 75205996383610292188894937)
    ·
      refine ⟨56404497287707719141671203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75205996383610292188894937 56404497287707719141671203)
      ·
        refine ⟨84606745931561578712506805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56404497287707719141671203 84606745931561578712506805)
        ·
          refine ⟨7931882431083898004297513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84606745931561578712506805 7931882431083898004297513)
          ·
            refine ⟨5948911823312923503223135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7931882431083898004297513 5948911823312923503223135)
            ·
              refine ⟨8923367734969385254834703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5948911823312923503223135 8923367734969385254834703)
              ·
                refine ⟨13385051602454077882252055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8923367734969385254834703 13385051602454077882252055)
                ·
                  refine ⟨20077577403681116823378083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13385051602454077882252055 20077577403681116823378083)
                  ·
                    refine ⟨30116366105521675235067125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20077577403681116823378083 30116366105521675235067125)
                    ·
                      refine ⟨2823409322392657053287543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30116366105521675235067125 2823409322392657053287543)
                      ·
                        rfl

theorem cell23_5498570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_5498570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498570 prefixEnd_5498570 := by exact prefixLift 5498570
  have htrace : WordTrace (prefixWord ++ tailWord_5498570) baseStart_5498570 baseEnd_5498570 := by
    simpa [prefixWord, tailWord_5498570, baseEnd_5498570] using wordTrace_append hprefix tailTrace_5498570
  have hstable : (prefixWord ++ tailWord_5498570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498570).length < 2 ^ (prefixWord ++ tailWord_5498570).sum := by decide
  have hdescent : baseEnd_5498570 < baseStart_5498570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498573 : List Nat := [1, 6, 2, 1, 1, 12]
def baseStart_5498573 : Nat := 118140960795 + 5498573 * 2 ^ 59
def prefixEnd_5498573 : Nat := 4983230072969 + 3 ^ 40 * 5498573 * 2
def baseEnd_5498573 : Nat := 11618974744175393175103

theorem tailTrace_5498573 : CollatzResearch.WordTrace tailWord_5498573 prefixEnd_5498573 11618974744175393175103 := by
  unfold tailWord_5498573
  simp only [CollatzResearch.WordTrace]
  refine ⟨200549433108616577349412373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133699622072411051566274915 200549433108616577349412373)
  ·
    refine ⟨9400754676966402063253705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 200549433108616577349412373 9400754676966402063253705)
    ·
      refine ⟨7050566007724801547440279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9400754676966402063253705 7050566007724801547440279)
      ·
        refine ⟨10575849011587202321160419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7050566007724801547440279 10575849011587202321160419)
        ·
          refine ⟨15863773517380803481740629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10575849011587202321160419 15863773517380803481740629)
          ·
            refine ⟨11618974744175393175103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15863773517380803481740629 11618974744175393175103)
            ·
              rfl

theorem cell23_5498573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 12].length) (baseStart_5498573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498573 prefixEnd_5498573 := by exact prefixLift 5498573
  have htrace : WordTrace (prefixWord ++ tailWord_5498573) baseStart_5498573 baseEnd_5498573 := by
    simpa [prefixWord, tailWord_5498573, baseEnd_5498573] using wordTrace_append hprefix tailTrace_5498573
  have hstable : (prefixWord ++ tailWord_5498573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498573).length < 2 ^ (prefixWord ++ tailWord_5498573).sum := by decide
  have hdescent : baseEnd_5498573 < baseStart_5498573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498586 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_5498586 : Nat := 118140960795 + 5498586 * 2 ^ 59
def prefixEnd_5498586 : Nat := 4983230072969 + 3 ^ 40 * 5498586 * 2
def baseEnd_5498586 : Nat := 941139179361042996895823

theorem tailTrace_5498586 : CollatzResearch.WordTrace tailWord_5498586 prefixEnd_5498586 941139179361042996895823 := by
  unfold tailWord_5498586
  simp only [CollatzResearch.WordTrace]
  refine ⟨50137476814392370142408903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133699938171712987046423741 50137476814392370142408903)
  ·
    refine ⟨75206215221588555213613355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50137476814392370142408903 75206215221588555213613355)
    ·
      refine ⟨112809322832382832820420033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75206215221588555213613355 112809322832382832820420033)
      ·
        refine ⟨84606992124287124615315025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112809322832382832820420033 84606992124287124615315025)
        ·
          refine ⟨63455244093215343461486269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84606992124287124615315025 63455244093215343461486269)
          ·
            refine ⟨23795716534955753798057351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63455244093215343461486269 23795716534955753798057351)
            ·
              refine ⟨35693574802433630697086027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23795716534955753798057351 35693574802433630697086027)
              ·
                refine ⟨53540362203650446045629041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35693574802433630697086027 53540362203650446045629041)
                ·
                  refine ⟨40155271652737834534221781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53540362203650446045629041 40155271652737834534221781)
                  ·
                    refine ⟨941139179361042996895823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40155271652737834534221781 941139179361042996895823)
                    ·
                      rfl

theorem cell23_5498586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_5498586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498586 prefixEnd_5498586 := by exact prefixLift 5498586
  have htrace : WordTrace (prefixWord ++ tailWord_5498586) baseStart_5498586 baseEnd_5498586 := by
    simpa [prefixWord, tailWord_5498586, baseEnd_5498586] using wordTrace_append hprefix tailTrace_5498586
  have hstable : (prefixWord ++ tailWord_5498586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498586).length < 2 ^ (prefixWord ++ tailWord_5498586).sum := by decide
  have hdescent : baseEnd_5498586 < baseStart_5498586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498600 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_5498600 : Nat := 118140960795 + 5498600 * 2 ^ 59
def prefixEnd_5498600 : Nat := 4983230072969 + 3 ^ 40 * 5498600 * 2
def baseEnd_5498600 : Nat := 2823424726812291935912405

theorem tailTrace_5498600 : CollatzResearch.WordTrace tailWord_5498600 prefixEnd_5498600 2823424726812291935912405 := by
  unfold tailWord_5498600
  simp only [CollatzResearch.WordTrace]
  refine ⟨100275208939759380480322627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133700278586345840640430169 100275208939759380480322627)
  ·
    refine ⟨150412813409639070720483941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100275208939759380480322627 150412813409639070720483941)
    ·
      refine ⟨28202402514307325760090739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150412813409639070720483941 28202402514307325760090739)
      ·
        refine ⟨42303603771460988640136109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28202402514307325760090739 42303603771460988640136109)
        ·
          refine ⟨15863851414297870740051041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42303603771460988640136109 15863851414297870740051041)
          ·
            refine ⟨11897888560723403055038281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15863851414297870740051041 11897888560723403055038281)
            ·
              refine ⟨8923416420542552291278711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11897888560723403055038281 8923416420542552291278711)
              ·
                refine ⟨13385124630813828436918067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8923416420542552291278711 13385124630813828436918067)
                ·
                  refine ⟨20077686946220742655377101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13385124630813828436918067 20077686946220742655377101)
                  ·
                    refine ⟨7529132604832778495766413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20077686946220742655377101 7529132604832778495766413)
                    ·
                      refine ⟨2823424726812291935912405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7529132604832778495766413 2823424726812291935912405)
                      ·
                        rfl

theorem cell23_5498600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_5498600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498600 prefixEnd_5498600 := by exact prefixLift 5498600
  have htrace : WordTrace (prefixWord ++ tailWord_5498600) baseStart_5498600 baseEnd_5498600 := by
    simpa [prefixWord, tailWord_5498600, baseEnd_5498600] using wordTrace_append hprefix tailTrace_5498600
  have hstable : (prefixWord ++ tailWord_5498600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498600).length < 2 ^ (prefixWord ++ tailWord_5498600).sum := by decide
  have hdescent : baseEnd_5498600 < baseStart_5498600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498610 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 3, 3, 2]
def baseStart_5498610 : Nat := 118140960795 + 5498610 * 2 ^ 59
def prefixEnd_5498610 : Nat := 4983230072969 + 3 ^ 40 * 5498610 * 2
def baseEnd_5498610 : Nat := 2823429861618836896787359

theorem tailTrace_5498610 : CollatzResearch.WordTrace tailWord_5498610 prefixEnd_5498610 2823429861618836896787359 := by
  unfold tailWord_5498610
  simp only [CollatzResearch.WordTrace]
  refine ⟨50137695652370633167127321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133700521739655021779006189 50137695652370633167127321)
  ·
    refine ⟨37603271739277974875345491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50137695652370633167127321 37603271739277974875345491)
    ·
      refine ⟨56404907608916962313018237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37603271739277974875345491 56404907608916962313018237)
      ·
        refine ⟨21151840353343860867381839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56404907608916962313018237 21151840353343860867381839)
        ·
          refine ⟨31727760530015791301072759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21151840353343860867381839 31727760530015791301072759)
          ·
            refine ⟨47591640795023686951609139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31727760530015791301072759 47591640795023686951609139)
            ·
              refine ⟨71387461192535530427413709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47591640795023686951609139 71387461192535530427413709)
              ·
                refine ⟨26770297947200823910280141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71387461192535530427413709 26770297947200823910280141)
                ·
                  refine ⟨10038861730200308966355053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26770297947200823910280141 10038861730200308966355053)
                  ·
                    refine ⟨3764573148825115862383145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10038861730200308966355053 3764573148825115862383145)
                    ·
                      refine ⟨2823429861618836896787359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764573148825115862383145 2823429861618836896787359)
                      ·
                        rfl

theorem cell23_5498610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_5498610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498610 prefixEnd_5498610 := by exact prefixLift 5498610
  have htrace : WordTrace (prefixWord ++ tailWord_5498610) baseStart_5498610 baseEnd_5498610 := by
    simpa [prefixWord, tailWord_5498610, baseEnd_5498610] using wordTrace_append hprefix tailTrace_5498610
  have hstable : (prefixWord ++ tailWord_5498610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498610).length < 2 ^ (prefixWord ++ tailWord_5498610).sum := by decide
  have hdescent : baseEnd_5498610 < baseStart_5498610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498627 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 1, 3, 2]
def baseStart_5498627 : Nat := 118140960795 + 5498627 * 2 ^ 59
def prefixEnd_5498627 : Nat := 4983230072969 + 3 ^ 40 * 5498627 * 2
def baseEnd_5498627 : Nat := 2823438590789963330274781

theorem tailTrace_5498627 : CollatzResearch.WordTrace tailWord_5498627 prefixEnd_5498627 2823438590789963330274781 := by
  unfold tailWord_5498627
  simp only [CollatzResearch.WordTrace]
  refine ⟨200551402650420944571878135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133700935100280629714585423 200551402650420944571878135)
  ·
    refine ⟨300827103975631416857817203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200551402650420944571878135 300827103975631416857817203)
    ·
      refine ⟨451240655963447125286725805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300827103975631416857817203 451240655963447125286725805)
      ·
        refine ⟨169215245986292671982522177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451240655963447125286725805 169215245986292671982522177)
        ·
          refine ⟨126911434489719503986891633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169215245986292671982522177 126911434489719503986891633)
          ·
            refine ⟨95183575867289627990168725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126911434489719503986891633 95183575867289627990168725)
            ·
              refine ⟨4461730118779201312039159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95183575867289627990168725 4461730118779201312039159)
              ·
                refine ⟨6692595178168801968058739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4461730118779201312039159 6692595178168801968058739)
                ·
                  refine ⟨10038892767253202952088109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6692595178168801968058739 10038892767253202952088109)
                  ·
                    refine ⟨3764584787719951107033041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10038892767253202952088109 3764584787719951107033041)
                    ·
                      refine ⟨2823438590789963330274781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764584787719951107033041 2823438590789963330274781)
                      ·
                        rfl

theorem cell23_5498627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 3, 2].length) (baseStart_5498627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498627 prefixEnd_5498627 := by exact prefixLift 5498627
  have htrace : WordTrace (prefixWord ++ tailWord_5498627) baseStart_5498627 baseEnd_5498627 := by
    simpa [prefixWord, tailWord_5498627, baseEnd_5498627] using wordTrace_append hprefix tailTrace_5498627
  have hstable : (prefixWord ++ tailWord_5498627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498627).length < 2 ^ (prefixWord ++ tailWord_5498627).sum := by decide
  have hdescent : baseEnd_5498627 < baseStart_5498627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498657 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 1, 4, 2]
def baseStart_5498657 : Nat := 118140960795 + 5498657 * 2 ^ 59
def prefixEnd_5498657 : Nat := 4983230072969 + 3 ^ 40 * 5498657 * 2
def baseEnd_5498657 : Nat := 2823453995209598212899643

theorem tailTrace_5498657 : CollatzResearch.WordTrace tailWord_5498657 prefixEnd_5498657 2823453995209598212899643 := by
  unfold tailWord_5498657
  simp only [CollatzResearch.WordTrace]
  refine ⟨200552496840312259695470225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133701664560208173130313483 200552496840312259695470225)
  ·
    refine ⟨150414372630234194771602669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200552496840312259695470225 150414372630234194771602669)
    ·
      refine ⟨56405389736337823039351001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150414372630234194771602669 56405389736337823039351001)
      ·
        refine ⟨42304042302253367279513251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56405389736337823039351001 42304042302253367279513251)
        ·
          refine ⟨63456063453380050919269877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42304042302253367279513251 63456063453380050919269877)
          ·
            refine ⟨5949005948754379773681551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63456063453380050919269877 5949005948754379773681551)
            ·
              refine ⟨8923508923131569660522327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949005948754379773681551 8923508923131569660522327)
              ·
                refine ⟨13385263384697354490783491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8923508923131569660522327 13385263384697354490783491)
                ·
                  refine ⟨20077895077046031736175237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13385263384697354490783491 20077895077046031736175237)
                  ·
                    refine ⟨3764605326946130950532857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20077895077046031736175237 3764605326946130950532857)
                    ·
                      refine ⟨2823453995209598212899643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764605326946130950532857 2823453995209598212899643)
                      ·
                        rfl

theorem cell23_5498657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_5498657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498657 prefixEnd_5498657 := by exact prefixLift 5498657
  have htrace : WordTrace (prefixWord ++ tailWord_5498657) baseStart_5498657 baseEnd_5498657 := by
    simpa [prefixWord, tailWord_5498657, baseEnd_5498657] using wordTrace_append hprefix tailTrace_5498657
  have hstable : (prefixWord ++ tailWord_5498657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498657).length < 2 ^ (prefixWord ++ tailWord_5498657).sum := by decide
  have hdescent : baseEnd_5498657 < baseStart_5498657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498680 : List Nat := [2, 1, 2, 1, 3, 3, 3, 3, 5]
def baseStart_5498680 : Nat := 118140960795 + 5498680 * 2 ^ 59
def prefixEnd_5498680 : Nat := 4983230072969 + 3 ^ 40 * 5498680 * 2
def baseEnd_5498680 : Nat := 313718422807183513656893

theorem tailTrace_5498680 : CollatzResearch.WordTrace tailWord_5498680 prefixEnd_5498680 313718422807183513656893 := by
  unfold tailWord_5498680
  simp only [CollatzResearch.WordTrace]
  refine ⟨100276667859614467311778747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133702223812819289749038329 100276667859614467311778747)
  ·
    refine ⟨150415001789421700967668121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100276667859614467311778747 150415001789421700967668121)
    ·
      refine ⟨112811251342066275725751091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150415001789421700967668121 112811251342066275725751091)
      ·
        refine ⟨169216877013099413588626637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112811251342066275725751091 169216877013099413588626637)
        ·
          refine ⟨63456328879912280095734989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169216877013099413588626637 63456328879912280095734989)
          ·
            refine ⟨23796123329967105035900621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63456328879912280095734989 23796123329967105035900621)
            ·
              refine ⟨8923546248737664388462733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23796123329967105035900621 8923546248737664388462733)
              ·
                refine ⟨3346329843276624145673525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8923546248737664388462733 3346329843276624145673525)
                ·
                  refine ⟨313718422807183513656893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3346329843276624145673525 313718422807183513656893)
                  ·
                    rfl

theorem cell23_5498680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 5].length) (baseStart_5498680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498680 prefixEnd_5498680 := by exact prefixLift 5498680
  have htrace : WordTrace (prefixWord ++ tailWord_5498680) baseStart_5498680 baseEnd_5498680 := by
    simpa [prefixWord, tailWord_5498680, baseEnd_5498680] using wordTrace_append hprefix tailTrace_5498680
  have hstable : (prefixWord ++ tailWord_5498680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498680).length < 2 ^ (prefixWord ++ tailWord_5498680).sum := by decide
  have hdescent : baseEnd_5498680 < baseStart_5498680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498693 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_5498693 : Nat := 118140960795 + 5498693 * 2 ^ 59
def prefixEnd_5498693 : Nat := 4983230072969 + 3 ^ 40 * 5498693 * 2
def baseEnd_5498693 : Nat := 941157493504386690683159

theorem tailTrace_5498693 : CollatzResearch.WordTrace tailWord_5498693 prefixEnd_5498693 941157493504386690683159 := by
  unfold tailWord_5498693
  simp only [CollatzResearch.WordTrace]
  refine ⟨200553809868181837843780733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133702539912121225229187155 200553809868181837843780733)
  ·
    refine ⟨75207678700568189191417775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200553809868181837843780733 75207678700568189191417775)
    ·
      refine ⟨112811518050852283787126663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75207678700568189191417775 112811518050852283787126663)
      ·
        refine ⟨169217277076278425680689995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112811518050852283787126663 169217277076278425680689995)
        ·
          refine ⟨253825915614417638521034993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169217277076278425680689995 253825915614417638521034993)
          ·
            refine ⟨190369436710813228890776245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253825915614417638521034993 190369436710813228890776245)
            ·
              refine ⟨17847134691638740208510273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190369436710813228890776245 17847134691638740208510273)
              ·
                refine ⟨13385351018729055156382705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17847134691638740208510273 13385351018729055156382705)
                ·
                  refine ⟨10039013264046791367287029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13385351018729055156382705 10039013264046791367287029)
                  ·
                    refine ⟨941157493504386690683159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10039013264046791367287029 941157493504386690683159)
                    ·
                      rfl

theorem cell23_5498693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_5498693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498693 prefixEnd_5498693 := by exact prefixLift 5498693
  have htrace : WordTrace (prefixWord ++ tailWord_5498693) baseStart_5498693 baseEnd_5498693 := by
    simpa [prefixWord, tailWord_5498693, baseEnd_5498693] using wordTrace_append hprefix tailTrace_5498693
  have hstable : (prefixWord ++ tailWord_5498693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498693).length < 2 ^ (prefixWord ++ tailWord_5498693).sum := by decide
  have hdescent : baseEnd_5498693 < baseStart_5498693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498713 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 4]
def baseStart_5498713 : Nat := 118140960795 + 5498713 * 2 ^ 59
def prefixEnd_5498713 : Nat := 4983230072969 + 3 ^ 40 * 5498713 * 2
def baseEnd_5498713 : Nat := 2823482750126249993799385

theorem tailTrace_5498713 : CollatzResearch.WordTrace tailWord_5498713 prefixEnd_5498713 2823482750126249993799385 := by
  unfold tailWord_5498713
  simp only [CollatzResearch.WordTrace]
  refine ⟨200554539328109381259508793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133703026218739587506339195 200554539328109381259508793)
  ·
    refine ⟨150415904496082035944631595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200554539328109381259508793 150415904496082035944631595)
    ·
      refine ⟨225623856744123053916947393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150415904496082035944631595 225623856744123053916947393)
      ·
        refine ⟨169217892558092290437710545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225623856744123053916947393 169217892558092290437710545)
        ·
          refine ⟨126913419418569217828282909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169217892558092290437710545 126913419418569217828282909)
          ·
            refine ⟨47592532281963456685606091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126913419418569217828282909 47592532281963456685606091)
            ·
              refine ⟨71388798422945185028409137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47592532281963456685606091 71388798422945185028409137)
              ·
                refine ⟨53541598817208888771306853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71388798422945185028409137 53541598817208888771306853)
                ·
                  refine ⟨10039049778226666644620035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53541598817208888771306853 10039049778226666644620035)
                  ·
                    refine ⟨15058574667339999966930053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10039049778226666644620035 15058574667339999966930053)
                    ·
                      refine ⟨2823482750126249993799385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15058574667339999966930053 2823482750126249993799385)
                      ·
                        rfl

theorem cell23_5498713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_5498713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498713 prefixEnd_5498713 := by exact prefixLift 5498713
  have htrace : WordTrace (prefixWord ++ tailWord_5498713) baseStart_5498713 baseEnd_5498713 := by
    simpa [prefixWord, tailWord_5498713, baseEnd_5498713] using wordTrace_append hprefix tailTrace_5498713
  have hstable : (prefixWord ++ tailWord_5498713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498713).length < 2 ^ (prefixWord ++ tailWord_5498713).sum := by decide
  have hdescent : baseEnd_5498713 < baseStart_5498713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498757 : List Nat := [1, 3, 1, 1, 3, 2, 3, 4, 1, 4]
def baseStart_5498757 : Nat := 118140960795 + 5498757 * 2 ^ 59
def prefixEnd_5498757 : Nat := 4983230072969 + 3 ^ 40 * 5498757 * 2
def baseEnd_5498757 : Nat := 941168447758349273883061

theorem tailTrace_5498757 : CollatzResearch.WordTrace tailWord_5498757 prefixEnd_5498757 941168447758349273883061 := by
  unfold tailWord_5498757
  simp only [CollatzResearch.WordTrace]
  refine ⟨200556144139949976774110525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133704096093299984516073683 200556144139949976774110525)
  ·
    refine ⟨75208554052481241290291447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200556144139949976774110525 75208554052481241290291447)
    ·
      refine ⟨112812831078721861935437171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75208554052481241290291447 112812831078721861935437171)
      ·
        refine ⟨169219246618082792903155757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112812831078721861935437171 169219246618082792903155757)
        ·
          refine ⟨63457217481781047338683409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169219246618082792903155757 63457217481781047338683409)
          ·
            refine ⟨47592913111335785504012557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63457217481781047338683409 47592913111335785504012557)
            ·
              refine ⟨17847342416750919564004709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47592913111335785504012557 17847342416750919564004709)
              ·
                refine ⟨3346376703140797418250883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17847342416750919564004709 3346376703140797418250883)
                ·
                  refine ⟨5019565054711196127376325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3346376703140797418250883 5019565054711196127376325)
                  ·
                    refine ⟨941168447758349273883061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5019565054711196127376325 941168447758349273883061)
                    ·
                      rfl

theorem cell23_5498757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_5498757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498757 prefixEnd_5498757 := by exact prefixLift 5498757
  have htrace : WordTrace (prefixWord ++ tailWord_5498757) baseStart_5498757 baseEnd_5498757 := by
    simpa [prefixWord, tailWord_5498757, baseEnd_5498757] using wordTrace_append hprefix tailTrace_5498757
  have hstable : (prefixWord ++ tailWord_5498757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498757).length < 2 ^ (prefixWord ++ tailWord_5498757).sum := by decide
  have hdescent : baseEnd_5498757 < baseStart_5498757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498763 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 3]
def baseStart_5498763 : Nat := 118140960795 + 5498763 * 2 ^ 59
def prefixEnd_5498763 : Nat := 4983230072969 + 3 ^ 40 * 5498763 * 2
def baseEnd_5498763 : Nat := 2823508424158974798174155

theorem tailTrace_5498763 : CollatzResearch.WordTrace tailWord_5498763 prefixEnd_5498763 2823508424158974798174155 := by
  unfold tailWord_5498763
  simp only [CollatzResearch.WordTrace]
  refine ⟨200556362977928239798828943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133704241985285493199219295 200556362977928239798828943)
  ·
    refine ⟨300834544466892359698243415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200556362977928239798828943 300834544466892359698243415)
    ·
      refine ⟨451251816700338539547365123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300834544466892359698243415 451251816700338539547365123)
      ·
        refine ⟨676877725050507809321047685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451251816700338539547365123 676877725050507809321047685)
        ·
          refine ⟨126914573446970214247696441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 676877725050507809321047685 126914573446970214247696441)
          ·
            refine ⟨95185930085227660685772331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126914573446970214247696441 95185930085227660685772331)
            ·
              refine ⟨142778895127841491028658497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95185930085227660685772331 142778895127841491028658497)
              ·
                refine ⟨107084171345881118271493873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142778895127841491028658497 107084171345881118271493873)
                ·
                  refine ⟨80313128509410838703620405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107084171345881118271493873 80313128509410838703620405)
                  ·
                    refine ⟨7529355797757266128464413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80313128509410838703620405 7529355797757266128464413)
                    ·
                      refine ⟨2823508424158974798174155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7529355797757266128464413 2823508424158974798174155)
                      ·
                        rfl

theorem cell23_5498763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 3].length) (baseStart_5498763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498763 prefixEnd_5498763 := by exact prefixLift 5498763
  have htrace : WordTrace (prefixWord ++ tailWord_5498763) baseStart_5498763 baseEnd_5498763 := by
    simpa [prefixWord, tailWord_5498763, baseEnd_5498763] using wordTrace_append hprefix tailTrace_5498763
  have hstable : (prefixWord ++ tailWord_5498763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498763).length < 2 ^ (prefixWord ++ tailWord_5498763).sum := by decide
  have hdescent : baseEnd_5498763 < baseStart_5498763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498814 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_5498814 : Nat := 118140960795 + 5498814 * 2 ^ 59
def prefixEnd_5498814 : Nat := 4983230072969 + 3 ^ 40 * 5498814 * 2
def baseEnd_5498814 : Nat := 2823534611672354098636421

theorem tailTrace_5498814 : CollatzResearch.WordTrace tailWord_5498814 prefixEnd_5498814 2823534611672354098636421 := by
  unfold tailWord_5498814
  simp only [CollatzResearch.WordTrace]
  refine ⟨25069777887592934438616937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133705482067162317005956997 25069777887592934438616937)
  ·
    refine ⟨18802333415694700828962703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25069777887592934438616937 18802333415694700828962703)
    ·
      refine ⟨28203500123542051243444055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18802333415694700828962703 28203500123542051243444055)
      ·
        refine ⟨42305250185313076865166083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28203500123542051243444055 42305250185313076865166083)
        ·
          refine ⟨63457875277969615297749125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42305250185313076865166083 63457875277969615297749125)
          ·
            refine ⟨11898351614619302868327961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63457875277969615297749125 11898351614619302868327961)
            ·
              refine ⟨8923763710964477151245971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11898351614619302868327961 8923763710964477151245971)
              ·
                refine ⟨13385645566446715726868957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8923763710964477151245971 13385645566446715726868957)
                ·
                  refine ⟨5019617087417518397575859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13385645566446715726868957 5019617087417518397575859)
                  ·
                    refine ⟨7529425631126277596363789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5019617087417518397575859 7529425631126277596363789)
                    ·
                      refine ⟨2823534611672354098636421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7529425631126277596363789 2823534611672354098636421)
                      ·
                        rfl

theorem cell23_5498814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_5498814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498814 prefixEnd_5498814 := by exact prefixLift 5498814
  have htrace : WordTrace (prefixWord ++ tailWord_5498814) baseStart_5498814 baseEnd_5498814 := by
    simpa [prefixWord, tailWord_5498814, baseEnd_5498814] using wordTrace_append hprefix tailTrace_5498814
  have hstable : (prefixWord ++ tailWord_5498814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498814).length < 2 ^ (prefixWord ++ tailWord_5498814).sum := by decide
  have hdescent : baseEnd_5498814 < baseStart_5498814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498834 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_5498834 : Nat := 118140960795 + 5498834 * 2 ^ 59
def prefixEnd_5498834 : Nat := 4983230072969 + 3 ^ 40 * 5498834 * 2
def baseEnd_5498834 : Nat := 941181627095148006795443

theorem tailTrace_5498834 : CollatzResearch.WordTrace tailWord_5498834 prefixEnd_5498834 941181627095148006795443 := by
  unfold tailWord_5498834
  simp only [CollatzResearch.WordTrace]
  refine ⟨50139738140167754731165889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133705968373780679283109037 50139738140167754731165889)
  ·
    refine ⟨37604803605125816048374417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50139738140167754731165889 37604803605125816048374417)
    ·
      refine ⟨28203602703844362036280813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37604803605125816048374417 28203602703844362036280813)
      ·
        refine ⟨10576351013941635763605305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28203602703844362036280813 10576351013941635763605305)
        ·
          refine ⟨7932263260456226822703979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10576351013941635763605305 7932263260456226822703979)
          ·
            refine ⟨11898394890684340234055969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7932263260456226822703979 11898394890684340234055969)
            ·
              refine ⟨8923796168013255175541977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11898394890684340234055969 8923796168013255175541977)
              ·
                refine ⟨6692847126009941381656483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8923796168013255175541977 6692847126009941381656483)
                ·
                  refine ⟨10039270689014912072484725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6692847126009941381656483 10039270689014912072484725)
                  ·
                    refine ⟨941181627095148006795443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10039270689014912072484725 941181627095148006795443)
                    ·
                      rfl

theorem cell23_5498834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_5498834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498834 prefixEnd_5498834 := by exact prefixLift 5498834
  have htrace : WordTrace (prefixWord ++ tailWord_5498834) baseStart_5498834 baseEnd_5498834 := by
    simpa [prefixWord, tailWord_5498834, baseEnd_5498834] using wordTrace_append hprefix tailTrace_5498834
  have hstable : (prefixWord ++ tailWord_5498834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498834).length < 2 ^ (prefixWord ++ tailWord_5498834).sum := by decide
  have hdescent : baseEnd_5498834 < baseStart_5498834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498837 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_5498837 : Nat := 118140960795 + 5498837 * 2 ^ 59
def prefixEnd_5498837 : Nat := 4983230072969 + 3 ^ 40 * 5498837 * 2
def baseEnd_5498837 : Nat := 2823546421727407508648815

theorem tailTrace_5498837 : CollatzResearch.WordTrace tailWord_5498837 prefixEnd_5498837 2823546421727407508648815 := by
  unfold tailWord_5498837
  simp only [CollatzResearch.WordTrace]
  refine ⟨200559061979660150437022765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133706041319773433624681843 200559061979660150437022765)
  ·
    refine ⟨75209648242372556413883537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200559061979660150437022765 75209648242372556413883537)
    ·
      refine ⟨56407236181779417310412653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75209648242372556413883537 56407236181779417310412653)
      ·
        refine ⟨21152713568167281491404745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56407236181779417310412653 21152713568167281491404745)
        ·
          refine ⟨15864535176125461118553559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21152713568167281491404745 15864535176125461118553559)
          ·
            refine ⟨23796802764188191677830339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15864535176125461118553559 23796802764188191677830339)
            ·
              refine ⟨35695204146282287516745509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23796802764188191677830339 35695204146282287516745509)
              ·
                refine ⟨6692850777427928909389783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35695204146282287516745509 6692850777427928909389783)
                ·
                  refine ⟨10039276166141893364084675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6692850777427928909389783 10039276166141893364084675)
                  ·
                    refine ⟨15058914249212840046127013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10039276166141893364084675 15058914249212840046127013)
                    ·
                      refine ⟨2823546421727407508648815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15058914249212840046127013 2823546421727407508648815)
                      ·
                        rfl

theorem cell23_5498837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_5498837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498837 prefixEnd_5498837 := by exact prefixLift 5498837
  have htrace : WordTrace (prefixWord ++ tailWord_5498837) baseStart_5498837 baseEnd_5498837 := by
    simpa [prefixWord, tailWord_5498837, baseEnd_5498837] using wordTrace_append hprefix tailTrace_5498837
  have hstable : (prefixWord ++ tailWord_5498837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498837).length < 2 ^ (prefixWord ++ tailWord_5498837).sum := by decide
  have hdescent : baseEnd_5498837 < baseStart_5498837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498937 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 2, 6]
def baseStart_5498937 : Nat := 118140960795 + 5498937 * 2 ^ 59
def prefixEnd_5498937 : Nat := 4983230072969 + 3 ^ 40 * 5498937 * 2
def baseEnd_5498937 : Nat := 941199256597619039132785

theorem tailTrace_5498937 : CollatzResearch.WordTrace tailWord_5498937 prefixEnd_5498937 941199256597619039132785 := by
  unfold tailWord_5498937
  simp only [CollatzResearch.WordTrace]
  refine ⟨200562709279297867515663065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133708472852865245010442043 200562709279297867515663065)
  ·
    refine ⟨150422031959473400636747299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200562709279297867515663065 150422031959473400636747299)
    ·
      refine ⟨225633047939210100955120949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150422031959473400636747299 225633047939210100955120949)
      ·
        refine ⟨21153098244300946964542589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 225633047939210100955120949 21153098244300946964542589)
        ·
          refine ⟨7932411841612855111703471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21153098244300946964542589 7932411841612855111703471)
          ·
            refine ⟨11898617762419282667555207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7932411841612855111703471 11898617762419282667555207)
            ·
              refine ⟨17847926643628924001332811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11898617762419282667555207 17847926643628924001332811)
              ·
                refine ⟨26771889965443386001999217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17847926643628924001332811 26771889965443386001999217)
                ·
                  refine ⟨20078917474082539501499413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26771889965443386001999217 20078917474082539501499413)
                  ·
                    refine ⟨941199256597619039132785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20078917474082539501499413 941199256597619039132785)
                    ·
                      rfl

theorem cell23_5498937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 6].length) (baseStart_5498937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498937 prefixEnd_5498937 := by exact prefixLift 5498937
  have htrace : WordTrace (prefixWord ++ tailWord_5498937) baseStart_5498937 baseEnd_5498937 := by
    simpa [prefixWord, tailWord_5498937, baseEnd_5498937] using wordTrace_append hprefix tailTrace_5498937
  have hstable : (prefixWord ++ tailWord_5498937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498937).length < 2 ^ (prefixWord ++ tailWord_5498937).sum := by decide
  have hdescent : baseEnd_5498937 < baseStart_5498937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498944 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 1, 4, 2]
def baseStart_5498944 : Nat := 118140960795 + 5498944 * 2 ^ 59
def prefixEnd_5498944 : Nat := 4983230072969 + 3 ^ 40 * 5498944 * 2
def baseEnd_5498944 : Nat := 2823601364157438590010823

theorem tailTrace_5498944 : CollatzResearch.WordTrace tailWord_5498944 prefixEnd_5498944 2823601364157438590010823 := by
  unfold tailWord_5498944
  simp only [CollatzResearch.WordTrace]
  refine ⟨100281482295136253855583943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133708643060181671807445257 100281482295136253855583943)
  ·
    refine ⟨150422223442704380783375915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100281482295136253855583943 150422223442704380783375915)
    ·
      refine ⟨225633335164056571175063873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150422223442704380783375915 225633335164056571175063873)
      ·
        refine ⟨169225001373042428381297905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225633335164056571175063873 169225001373042428381297905)
        ·
          refine ⟨126918751029781821285973429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169225001373042428381297905 126918751029781821285973429)
          ·
            refine ⟨11898632909042045745560009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126918751029781821285973429 11898632909042045745560009)
            ·
              refine ⟨8923974681781534309170007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11898632909042045745560009 8923974681781534309170007)
              ·
                refine ⟨13385962022672301463755011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8923974681781534309170007 13385962022672301463755011)
                ·
                  refine ⟨20078943034008452195632517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13385962022672301463755011 20078943034008452195632517)
                  ·
                    refine ⟨3764801818876584786681097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20078943034008452195632517 3764801818876584786681097)
                    ·
                      refine ⟨2823601364157438590010823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764801818876584786681097 2823601364157438590010823)
                      ·
                        rfl

theorem cell23_5498944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 4, 2].length) (baseStart_5498944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498944 prefixEnd_5498944 := by exact prefixLift 5498944
  have htrace : WordTrace (prefixWord ++ tailWord_5498944) baseStart_5498944 baseEnd_5498944 := by
    simpa [prefixWord, tailWord_5498944, baseEnd_5498944] using wordTrace_append hprefix tailTrace_5498944
  have hstable : (prefixWord ++ tailWord_5498944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498944).length < 2 ^ (prefixWord ++ tailWord_5498944).sum := by decide
  have hdescent : baseEnd_5498944 < baseStart_5498944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498957 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_5498957 : Nat := 118140960795 + 5498957 * 2 ^ 59
def prefixEnd_5498957 : Nat := 4983230072969 + 3 ^ 40 * 5498957 * 2
def baseEnd_5498957 : Nat := 2823608039405947039148263

theorem tailTrace_5498957 : CollatzResearch.WordTrace tailWord_5498957 prefixEnd_5498957 2823608039405947039148263 := by
  unfold tailWord_5498957
  simp only [CollatzResearch.WordTrace]
  refine ⟨200563438739225410931391125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133708959159483607287594083 200563438739225410931391125)
  ·
    refine ⟨9401411190901191137408959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 200563438739225410931391125 9401411190901191137408959)
    ·
      refine ⟨14102116786351786706113439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9401411190901191137408959 14102116786351786706113439)
      ·
        refine ⟨21153175179527680059170159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14102116786351786706113439 21153175179527680059170159)
        ·
          refine ⟨31729762769291520088755239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21153175179527680059170159 31729762769291520088755239)
          ·
            refine ⟨47594644153937280133132859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31729762769291520088755239 47594644153937280133132859)
            ·
              refine ⟨71391966230905920199699289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47594644153937280133132859 71391966230905920199699289)
              ·
                refine ⟨53543974673179440149774467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71391966230905920199699289 53543974673179440149774467)
                ·
                  refine ⟨80315962009769160224661701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53543974673179440149774467 80315962009769160224661701)
                  ·
                    refine ⟨15059242876831717542124069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80315962009769160224661701 15059242876831717542124069)
                    ·
                      refine ⟨2823608039405947039148263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15059242876831717542124069 2823608039405947039148263)
                      ·
                        rfl

theorem cell23_5498957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_5498957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498957 prefixEnd_5498957 := by exact prefixLift 5498957
  have htrace : WordTrace (prefixWord ++ tailWord_5498957) baseStart_5498957 baseEnd_5498957 := by
    simpa [prefixWord, tailWord_5498957, baseEnd_5498957] using wordTrace_append hprefix tailTrace_5498957
  have hstable : (prefixWord ++ tailWord_5498957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498957).length < 2 ^ (prefixWord ++ tailWord_5498957).sum := by decide
  have hdescent : baseEnd_5498957 < baseStart_5498957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498967 : List Nat := [1, 1, 3, 2, 2, 1, 3, 5, 5]
def baseStart_5498967 : Nat := 118140960795 + 5498967 * 2 ^ 59
def prefixEnd_5498967 : Nat := 4983230072969 + 3 ^ 40 * 5498967 * 2
def baseEnd_5498967 : Nat := 313734797134721333335913

theorem tailTrace_5498967 : CollatzResearch.WordTrace tailWord_5498967 prefixEnd_5498967 313734797134721333335913 := by
  unfold tailWord_5498967
  simp only [CollatzResearch.WordTrace]
  refine ⟨200563803469189182639255155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133709202312792788426170103 200563803469189182639255155)
  ·
    refine ⟨300845705203783773958882733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200563803469189182639255155 300845705203783773958882733)
    ·
      refine ⟨112817139451418915234581025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300845705203783773958882733 112817139451418915234581025)
      ·
        refine ⟨84612854588564186425935769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112817139451418915234581025 84612854588564186425935769)
        ·
          refine ⟨63459640941423139819451827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84612854588564186425935769 63459640941423139819451827)
          ·
            refine ⟨95189461412134709729177741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63459640941423139819451827 95189461412134709729177741)
            ·
              refine ⟨35696048029550516148441653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95189461412134709729177741 35696048029550516148441653)
              ·
                refine ⟨3346504502770360888916405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35696048029550516148441653 3346504502770360888916405)
                ·
                  refine ⟨313734797134721333335913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3346504502770360888916405 313734797134721333335913)
                  ·
                    rfl

theorem cell23_5498967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 5].length) (baseStart_5498967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498967 prefixEnd_5498967 := by exact prefixLift 5498967
  have htrace : WordTrace (prefixWord ++ tailWord_5498967) baseStart_5498967 baseEnd_5498967 := by
    simpa [prefixWord, tailWord_5498967, baseEnd_5498967] using wordTrace_append hprefix tailTrace_5498967
  have hstable : (prefixWord ++ tailWord_5498967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498967).length < 2 ^ (prefixWord ++ tailWord_5498967).sum := by decide
  have hdescent : baseEnd_5498967 < baseStart_5498967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5498978 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5498978 : Nat := 118140960795 + 5498978 * 2 ^ 59
def prefixEnd_5498978 : Nat := 4983230072969 + 3 ^ 40 * 5498978 * 2
def baseEnd_5498978 : Nat := 2823618822499691456985667

theorem tailTrace_5498978 : CollatzResearch.WordTrace tailWord_5498978 prefixEnd_5498978 2823618822499691456985667 := by
  unfold tailWord_5498978
  simp only [CollatzResearch.WordTrace]
  refine ⟨50141051168037332879476397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133709469781432887678603725 50141051168037332879476397)
  ·
    refine ⟨18802894188013999829803649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50141051168037332879476397 18802894188013999829803649)
    ·
      refine ⟨14102170641010499872352737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18802894188013999829803649 14102170641010499872352737)
      ·
        refine ⟨10576627980757874904264553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14102170641010499872352737 10576627980757874904264553)
        ·
          refine ⟨7932470985568406178198415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10576627980757874904264553 7932470985568406178198415)
          ·
            refine ⟨11898706478352609267297623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7932470985568406178198415 11898706478352609267297623)
            ·
              refine ⟨17848059717528913900946435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11898706478352609267297623 17848059717528913900946435)
              ·
                refine ⟨26772089576293370851419653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17848059717528913900946435 26772089576293370851419653)
                ·
                  refine ⟨5019766795555007034641185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26772089576293370851419653 5019766795555007034641185)
                  ·
                    refine ⟨3764825096666255275980889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5019766795555007034641185 3764825096666255275980889)
                    ·
                      refine ⟨2823618822499691456985667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3764825096666255275980889 2823618822499691456985667)
                      ·
                        rfl

theorem cell23_5498978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5498978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5498978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5498978 prefixEnd_5498978 := by exact prefixLift 5498978
  have htrace : WordTrace (prefixWord ++ tailWord_5498978) baseStart_5498978 baseEnd_5498978 := by
    simpa [prefixWord, tailWord_5498978, baseEnd_5498978] using wordTrace_append hprefix tailTrace_5498978
  have hstable : (prefixWord ++ tailWord_5498978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5498978).length < 2 ^ (prefixWord ++ tailWord_5498978).sum := by decide
  have hdescent : baseEnd_5498978 < baseStart_5498978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5498978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499017 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 4]
def baseStart_5499017 : Nat := 118140960795 + 5499017 * 2 ^ 59
def prefixEnd_5499017 : Nat := 4983230072969 + 3 ^ 40 * 5499017 * 2
def baseEnd_5499017 : Nat := 2823638848245216804397987

theorem tailTrace_5499017 : CollatzResearch.WordTrace tailWord_5499017 prefixEnd_5499017 2823638848245216804397987 := by
  unfold tailWord_5499017
  simp only [CollatzResearch.WordTrace]
  refine ⟨200565627119008041178575305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133710418079338694119050203 200565627119008041178575305)
  ·
    refine ⟨150424220339256030883931479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200565627119008041178575305 150424220339256030883931479)
    ·
      refine ⟨225636330508884046325897219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150424220339256030883931479 225636330508884046325897219)
      ·
        refine ⟨338454495763326069488845829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225636330508884046325897219 338454495763326069488845829)
        ·
          refine ⟨63460217955623638029158593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 338454495763326069488845829 63460217955623638029158593)
          ·
            refine ⟨47595163466717728521868945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63460217955623638029158593 47595163466717728521868945)
            ·
              refine ⟨35696372600038296391401709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47595163466717728521868945 35696372600038296391401709)
              ·
                refine ⟨13386139725014361146775641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35696372600038296391401709 13386139725014361146775641)
                ·
                  refine ⟨10039604793760770860081731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13386139725014361146775641 10039604793760770860081731)
                  ·
                    refine ⟨15059407190641156290122597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10039604793760770860081731 15059407190641156290122597)
                    ·
                      refine ⟨2823638848245216804397987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15059407190641156290122597 2823638848245216804397987)
                      ·
                        rfl

theorem cell23_5499017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_5499017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499017 prefixEnd_5499017 := by exact prefixLift 5499017
  have htrace : WordTrace (prefixWord ++ tailWord_5499017) baseStart_5499017 baseEnd_5499017 := by
    simpa [prefixWord, tailWord_5499017, baseEnd_5499017] using wordTrace_append hprefix tailTrace_5499017
  have hstable : (prefixWord ++ tailWord_5499017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499017).length < 2 ^ (prefixWord ++ tailWord_5499017).sum := by decide
  have hdescent : baseEnd_5499017 < baseStart_5499017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499020 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_5499020 : Nat := 118140960795 + 5499020 * 2 ^ 59
def prefixEnd_5499020 : Nat := 4983230072969 + 3 ^ 40 * 5499020 * 2
def baseEnd_5499020 : Nat := 2823640388687180292660473

theorem tailTrace_5499020 : CollatzResearch.WordTrace tailWord_5499020 prefixEnd_5499020 2823640388687180292660473 := by
  unfold tailWord_5499020
  simp only [CollatzResearch.WordTrace]
  refine ⟨100282868268998586345467257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133710491025331448460623009 100282868268998586345467257)
  ·
    refine ⟨75212151201748939759100443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100282868268998586345467257 75212151201748939759100443)
    ·
      refine ⟨112818226802623409638650665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75212151201748939759100443 112818226802623409638650665)
      ·
        refine ⟨84613670101967557228987999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112818226802623409638650665 84613670101967557228987999)
        ·
          refine ⟨126920505152951335843481999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84613670101967557228987999 126920505152951335843481999)
          ·
            refine ⟨190380757729427003765222999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126920505152951335843481999 190380757729427003765222999)
            ·
              refine ⟨285571136594140505647834499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190380757729427003765222999 285571136594140505647834499)
              ·
                refine ⟨428356704891210758471751749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285571136594140505647834499 428356704891210758471751749)
                ·
                  refine ⟨80316882167102017213453453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 428356704891210758471751749 80316882167102017213453453)
                  ·
                    refine ⟨30118830812663256455045045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80316882167102017213453453 30118830812663256455045045)
                    ·
                      refine ⟨2823640388687180292660473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30118830812663256455045045 2823640388687180292660473)
                      ·
                        rfl

theorem cell23_5499020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_5499020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499020 prefixEnd_5499020 := by exact prefixLift 5499020
  have htrace : WordTrace (prefixWord ++ tailWord_5499020) baseStart_5499020 baseEnd_5499020 := by
    simpa [prefixWord, tailWord_5499020, baseEnd_5499020] using wordTrace_append hprefix tailTrace_5499020
  have hstable : (prefixWord ++ tailWord_5499020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499020).length < 2 ^ (prefixWord ++ tailWord_5499020).sum := by decide
  have hdescent : baseEnd_5499020 < baseStart_5499020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499134 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_5499134 : Nat := 118140960795 + 5499134 * 2 ^ 59
def prefixEnd_5499134 : Nat := 4983230072969 + 3 ^ 40 * 5499134 * 2
def baseEnd_5499134 : Nat := 941232975160597615544983

theorem tailTrace_5499134 : CollatzResearch.WordTrace tailWord_5499134 prefixEnd_5499134 941232975160597615544983 := by
  unfold tailWord_5499134
  simp only [CollatzResearch.WordTrace]
  refine ⟨25071236807448021270073057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133713262973056113440389637 25071236807448021270073057)
  ·
    refine ⟨18803427605586015952554793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25071236807448021270073057 18803427605586015952554793)
    ·
      refine ⟨14102570704189511964416095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18803427605586015952554793 14102570704189511964416095)
      ·
        refine ⟨21153856056284267946624143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14102570704189511964416095 21153856056284267946624143)
        ·
          refine ⟨31730784084426401919936215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21153856056284267946624143 31730784084426401919936215)
          ·
            refine ⟨47596176126639602879904323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31730784084426401919936215 47596176126639602879904323)
            ·
              refine ⟨71394264189959404319856485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47596176126639602879904323 71394264189959404319856485)
              ·
                refine ⟨13386424535617388309973091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71394264189959404319856485 13386424535617388309973091)
                ·
                  refine ⟨20079636803426082464959637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13386424535617388309973091 20079636803426082464959637)
                  ·
                    refine ⟨941232975160597615544983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20079636803426082464959637 941232975160597615544983)
                    ·
                      rfl

theorem cell23_5499134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_5499134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499134 prefixEnd_5499134 := by exact prefixLift 5499134
  have htrace : WordTrace (prefixWord ++ tailWord_5499134) baseStart_5499134 baseEnd_5499134 := by
    simpa [prefixWord, tailWord_5499134, baseEnd_5499134] using wordTrace_append hprefix tailTrace_5499134
  have hstable : (prefixWord ++ tailWord_5499134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499134).length < 2 ^ (prefixWord ++ tailWord_5499134).sum := by decide
  have hdescent : baseEnd_5499134 < baseStart_5499134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499138 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_5499138 : Nat := 118140960795 + 5499138 * 2 ^ 59
def prefixEnd_5499138 : Nat := 4983230072969 + 3 ^ 40 * 5499138 * 2
def baseEnd_5499138 : Nat := 941233659801470276994977

theorem tailTrace_5499138 : CollatzResearch.WordTrace tailWord_5499138 prefixEnd_5499138 941233659801470276994977 := by
  unfold tailWord_5499138
  simp only [CollatzResearch.WordTrace]
  refine ⟨50142510087892419710932517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133713360234379785895820045 50142510087892419710932517)
  ·
    refine ⟨9401720641479828695799847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50142510087892419710932517 9401720641479828695799847)
    ·
      refine ⟨14102580962219743043699771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9401720641479828695799847 14102580962219743043699771)
      ·
        refine ⟨21153871443329614565549657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14102580962219743043699771 21153871443329614565549657)
        ·
          refine ⟨15865403582497210924162243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21153871443329614565549657 15865403582497210924162243)
          ·
            refine ⟨23798105373745816386243365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15865403582497210924162243 23798105373745816386243365)
            ·
              refine ⟨4462144757577340572420631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23798105373745816386243365 4462144757577340572420631)
              ·
                refine ⟨6693217136366010858630947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462144757577340572420631 6693217136366010858630947)
                ·
                  refine ⟨10039825704549016287946421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6693217136366010858630947 10039825704549016287946421)
                  ·
                    refine ⟨941233659801470276994977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10039825704549016287946421 941233659801470276994977)
                    ·
                      rfl

theorem cell23_5499138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_5499138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499138 prefixEnd_5499138 := by exact prefixLift 5499138
  have htrace : WordTrace (prefixWord ++ tailWord_5499138) baseStart_5499138 baseEnd_5499138 := by
    simpa [prefixWord, tailWord_5499138, baseEnd_5499138] using wordTrace_append hprefix tailTrace_5499138
  have hstable : (prefixWord ++ tailWord_5499138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499138).length < 2 ^ (prefixWord ++ tailWord_5499138).sum := by decide
  have hdescent : baseEnd_5499138 < baseStart_5499138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499168 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 2, 4]
def baseStart_5499168 : Nat := 118140960795 + 5499168 * 2 ^ 59
def prefixEnd_5499168 : Nat := 4983230072969 + 3 ^ 40 * 5499168 * 2
def baseEnd_5499168 : Nat := 941238794608015237869931

theorem tailTrace_5499168 : CollatzResearch.WordTrace tailWord_5499168 prefixEnd_5499168 941238794608015237869931 := by
  unfold tailWord_5499168
  simp only [CollatzResearch.WordTrace]
  refine ⟨100285567270730496983661079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133714089694307329311548105 100285567270730496983661079)
  ·
    refine ⟨150428350906095745475491619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100285567270730496983661079 150428350906095745475491619)
    ·
      refine ⟨225642526359143618213237429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150428350906095745475491619 225642526359143618213237429)
      ·
        refine ⟨21153986846169714207491009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 225642526359143618213237429 21153986846169714207491009)
        ·
          refine ⟨15865490134627285655618257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21153986846169714207491009 15865490134627285655618257)
          ·
            refine ⟨11899117600970464241713693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15865490134627285655618257 11899117600970464241713693)
            ·
              refine ⟨4462169100363924090642635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11899117600970464241713693 4462169100363924090642635)
              ·
                refine ⟨6693253650545886135963953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462169100363924090642635 6693253650545886135963953)
                ·
                  refine ⟨5019940237909414601972965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6693253650545886135963953 5019940237909414601972965)
                  ·
                    refine ⟨941238794608015237869931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5019940237909414601972965 941238794608015237869931)
                    ·
                      rfl

theorem cell23_5499168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 2, 4].length) (baseStart_5499168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499168 prefixEnd_5499168 := by exact prefixLift 5499168
  have htrace : WordTrace (prefixWord ++ tailWord_5499168) baseStart_5499168 baseEnd_5499168 := by
    simpa [prefixWord, tailWord_5499168, baseEnd_5499168] using wordTrace_append hprefix tailTrace_5499168
  have hstable : (prefixWord ++ tailWord_5499168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499168).length < 2 ^ (prefixWord ++ tailWord_5499168).sum := by decide
  have hdescent : baseEnd_5499168 < baseStart_5499168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499181 : List Nat := [1, 5, 3, 1, 2, 1, 1, 9]
def baseStart_5499181 : Nat := 118140960795 + 5499181 * 2 ^ 59
def prefixEnd_5499181 : Nat := 4983230072969 + 3 ^ 40 * 5499181 * 2
def baseEnd_5499181 : Nat := 104582335521205709731379

theorem tailTrace_5499181 : CollatzResearch.WordTrace tailWord_5499181 prefixEnd_5499181 104582335521205709731379 := by
  unfold tailWord_5499181
  simp only [CollatzResearch.WordTrace]
  refine ⟨200571608690413897187545397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133714405793609264791696931 200571608690413897187545397)
  ·
    refine ⟨18803588314726302861332381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200571608690413897187545397 18803588314726302861332381)
    ·
      refine ⟨7051345618022363572999643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18803588314726302861332381 7051345618022363572999643)
      ·
        refine ⟨10577018427033545359499465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7051345618022363572999643 10577018427033545359499465)
        ·
          refine ⟨7932763820275159019624599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10577018427033545359499465 7932763820275159019624599)
          ·
            refine ⟨11899145730412738529436899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7932763820275159019624599 11899145730412738529436899)
            ·
              refine ⟨17848718595619107794155349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11899145730412738529436899 17848718595619107794155349)
              ·
                refine ⟨104582335521205709731379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17848718595619107794155349 104582335521205709731379)
                ·
                  rfl

theorem cell23_5499181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 9].length) (baseStart_5499181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499181 prefixEnd_5499181 := by exact prefixLift 5499181
  have htrace : WordTrace (prefixWord ++ tailWord_5499181) baseStart_5499181 baseEnd_5499181 := by
    simpa [prefixWord, tailWord_5499181, baseEnd_5499181] using wordTrace_append hprefix tailTrace_5499181
  have hstable : (prefixWord ++ tailWord_5499181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499181).length < 2 ^ (prefixWord ++ tailWord_5499181).sum := by decide
  have hdescent : baseEnd_5499181 < baseStart_5499181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499187 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 5]
def baseStart_5499187 : Nat := 118140960795 + 5499187 * 2 ^ 59
def prefixEnd_5499187 : Nat := 4983230072969 + 3 ^ 40 * 5499187 * 2
def baseEnd_5499187 : Nat := 2823726139956481139272205

theorem tailTrace_5499187 : CollatzResearch.WordTrace tailWord_5499187 prefixEnd_5499187 2823726139956481139272205 := by
  unfold tailWord_5499187
  simp only [CollatzResearch.WordTrace]
  refine ⟨200571827528392160212263815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133714551685594773474842543 200571827528392160212263815)
  ·
    refine ⟨300857741292588240318395723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200571827528392160212263815 300857741292588240318395723)
    ·
      refine ⟨451286611938882360477593585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300857741292588240318395723 451286611938882360477593585)
      ·
        refine ⟨338464958954161770358195189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451286611938882360477593585 338464958954161770358195189)
        ·
          refine ⟨31731089901952665971080799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 338464958954161770358195189 31731089901952665971080799)
          ·
            refine ⟨47596634852928998956621199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31731089901952665971080799 47596634852928998956621199)
            ·
              refine ⟨71394952279393498434931799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47596634852928998956621199 71394952279393498434931799)
              ·
                refine ⟨107092428419090247652397699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71394952279393498434931799 107092428419090247652397699)
                ·
                  refine ⟨160638642628635371478596549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107092428419090247652397699 160638642628635371478596549)
                  ·
                    refine ⟨30119745492869132152236853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 160638642628635371478596549 30119745492869132152236853)
                    ·
                      refine ⟨2823726139956481139272205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30119745492869132152236853 2823726139956481139272205)
                      ·
                        rfl

theorem cell23_5499187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_5499187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499187 prefixEnd_5499187 := by exact prefixLift 5499187
  have htrace : WordTrace (prefixWord ++ tailWord_5499187) baseStart_5499187 baseEnd_5499187 := by
    simpa [prefixWord, tailWord_5499187, baseEnd_5499187] using wordTrace_append hprefix tailTrace_5499187
  have hstable : (prefixWord ++ tailWord_5499187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499187).length < 2 ^ (prefixWord ++ tailWord_5499187).sum := by decide
  have hdescent : baseEnd_5499187 < baseStart_5499187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499247 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_5499247 : Nat := 118140960795 + 5499247 * 2 ^ 59
def prefixEnd_5499247 : Nat := 4983230072969 + 3 ^ 40 * 5499247 * 2
def baseEnd_5499247 : Nat := 2823756948795750904521929

theorem tailTrace_5499247 : CollatzResearch.WordTrace tailWord_5499247 prefixEnd_5499247 2823756948795750904521929 := by
  unfold tailWord_5499247
  simp only [CollatzResearch.WordTrace]
  refine ⟨200574015908174790459447995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133716010605449860306298663 200574015908174790459447995)
  ·
    refine ⟨300861023862262185689171993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200574015908174790459447995 300861023862262185689171993)
    ·
      refine ⟨225645767896696639266878995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300861023862262185689171993 225645767896696639266878995)
      ·
        refine ⟨338468651845044958900318493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225645767896696639266878995 338468651845044958900318493)
        ·
          refine ⟨126925744441891859587619435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338468651845044958900318493 126925744441891859587619435)
          ·
            refine ⟨190388616662837789381429153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126925744441891859587619435 190388616662837789381429153)
            ·
              refine ⟨142791462497128342036071865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190388616662837789381429153 142791462497128342036071865)
              ·
                refine ⟨107093596872846256527053899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142791462497128342036071865 107093596872846256527053899)
                ·
                  refine ⟨160640395309269384790580849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107093596872846256527053899 160640395309269384790580849)
                  ·
                    refine ⟨120480296481952038592935637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160640395309269384790580849 120480296481952038592935637)
                    ·
                      refine ⟨2823756948795750904521929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120480296481952038592935637 2823756948795750904521929)
                      ·
                        rfl

theorem cell23_5499247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_5499247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499247 prefixEnd_5499247 := by exact prefixLift 5499247
  have htrace : WordTrace (prefixWord ++ tailWord_5499247) baseStart_5499247 baseEnd_5499247 := by
    simpa [prefixWord, tailWord_5499247, baseEnd_5499247] using wordTrace_append hprefix tailTrace_5499247
  have hstable : (prefixWord ++ tailWord_5499247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499247).length < 2 ^ (prefixWord ++ tailWord_5499247).sum := by decide
  have hdescent : baseEnd_5499247 < baseStart_5499247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499265 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_5499265 : Nat := 118140960795 + 5499265 * 2 ^ 59
def prefixEnd_5499265 : Nat := 4983230072969 + 3 ^ 40 * 5499265 * 2
def baseEnd_5499265 : Nat := 2823766191447531834096847

theorem tailTrace_5499265 : CollatzResearch.WordTrace tailWord_5499265 prefixEnd_5499265 2823766191447531834096847 := by
  unfold tailWord_5499265
  simp only [CollatzResearch.WordTrace]
  refine ⟨200574672422109579533603249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133716448281406386355735499 200574672422109579533603249)
  ·
    refine ⟨150431004316582184650202437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200574672422109579533603249 150431004316582184650202437)
    ·
      refine ⟨28205813309359159621912957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150431004316582184650202437 28205813309359159621912957)
      ·
        refine ⟨10577179991009684858217359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28205813309359159621912957 10577179991009684858217359)
        ·
          refine ⟨15865769986514527287326039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10577179991009684858217359 15865769986514527287326039)
          ·
            refine ⟨23798654979771790930989059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15865769986514527287326039 23798654979771790930989059)
            ·
              refine ⟨35697982469657686396483589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23798654979771790930989059 35697982469657686396483589)
              ·
                refine ⟨6693371713060816199340673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35697982469657686396483589 6693371713060816199340673)
                ·
                  refine ⟨5020028784795612149505505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6693371713060816199340673 5020028784795612149505505)
                  ·
                    refine ⟨3765021588596709112129129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5020028784795612149505505 3765021588596709112129129)
                    ·
                      refine ⟨2823766191447531834096847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765021588596709112129129 2823766191447531834096847)
                      ·
                        rfl

theorem cell23_5499265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_5499265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499265 prefixEnd_5499265 := by exact prefixLift 5499265
  have htrace : WordTrace (prefixWord ++ tailWord_5499265) baseStart_5499265 baseEnd_5499265 := by
    simpa [prefixWord, tailWord_5499265, baseEnd_5499265] using wordTrace_append hprefix tailTrace_5499265
  have hstable : (prefixWord ++ tailWord_5499265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499265).length < 2 ^ (prefixWord ++ tailWord_5499265).sum := by decide
  have hdescent : baseEnd_5499265 < baseStart_5499265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499271 : List Nat := [1, 1, 4, 2, 2, 1, 3, 4, 5]
def baseStart_5499271 : Nat := 118140960795 + 5499271 * 2 ^ 59
def prefixEnd_5499271 : Nat := 4983230072969 + 3 ^ 40 * 5499271 * 2
def baseEnd_5499271 : Nat := 313752141370162090069091

theorem tailTrace_5499271 : CollatzResearch.WordTrace tailWord_5499271 prefixEnd_5499271 313752141370162090069091 := by
  unfold tailWord_5499271
  simp only [CollatzResearch.WordTrace]
  refine ⟨200574891260087842558321667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133716594173391895038881111 200574891260087842558321667)
  ·
    refine ⟨300862336890131763837482501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200574891260087842558321667 300862336890131763837482501)
    ·
      refine ⟨56411688166899705719527969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300862336890131763837482501 56411688166899705719527969)
      ·
        refine ⟨42308766125174779289645977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56411688166899705719527969 42308766125174779289645977)
        ·
          refine ⟨31731574593881084467234483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42308766125174779289645977 31731574593881084467234483)
          ·
            refine ⟨47597361890821626700851725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31731574593881084467234483 47597361890821626700851725)
            ·
              refine ⟨17849010709058110012819397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47597361890821626700851725 17849010709058110012819397)
              ·
                refine ⟨3346689507948395627403637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17849010709058110012819397 3346689507948395627403637)
                ·
                  refine ⟨313752141370162090069091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3346689507948395627403637 313752141370162090069091)
                  ·
                    rfl

theorem cell23_5499271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 5].length) (baseStart_5499271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499271 prefixEnd_5499271 := by exact prefixLift 5499271
  have htrace : WordTrace (prefixWord ++ tailWord_5499271) baseStart_5499271 baseEnd_5499271 := by
    simpa [prefixWord, tailWord_5499271, baseEnd_5499271] using wordTrace_append hprefix tailTrace_5499271
  have hstable : (prefixWord ++ tailWord_5499271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499271).length < 2 ^ (prefixWord ++ tailWord_5499271).sum := by decide
  have hdescent : baseEnd_5499271 < baseStart_5499271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499316 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_5499316 : Nat := 118140960795 + 5499316 * 2 ^ 59
def prefixEnd_5499316 : Nat := 4983230072969 + 3 ^ 40 * 5499316 * 2
def baseEnd_5499316 : Nat := 2823792378960911134559113

theorem tailTrace_5499316 : CollatzResearch.WordTrace tailWord_5499316 prefixEnd_5499316 2823792378960911134559113 := by
  unfold tailWord_5499316
  simp only [CollatzResearch.WordTrace]
  refine ⟨100288266272462407621854901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133717688363283210162473201 100288266272462407621854901)
  ·
    refine ⟨9402024963043350714548897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100288266272462407621854901 9402024963043350714548897)
    ·
      refine ⟨7051518722282513035911673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9402024963043350714548897 7051518722282513035911673)
      ·
        refine ⟨5288639041711884776933755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7051518722282513035911673 5288639041711884776933755)
        ·
          refine ⟨7932958562567827165400633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5288639041711884776933755 7932958562567827165400633)
          ·
            refine ⟨5949718921925870374050475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7932958562567827165400633 5949718921925870374050475)
            ·
              refine ⟨8924578382888805561075713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949718921925870374050475 8924578382888805561075713)
              ·
                refine ⟨6693433787166604170806785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8924578382888805561075713 6693433787166604170806785)
                ·
                  refine ⟨5020075340374953128105089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6693433787166604170806785 5020075340374953128105089)
                  ·
                    refine ⟨3765056505281214846078817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5020075340374953128105089 3765056505281214846078817)
                    ·
                      refine ⟨2823792378960911134559113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765056505281214846078817 2823792378960911134559113)
                      ·
                        rfl

theorem cell23_5499316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_5499316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499316 prefixEnd_5499316 := by exact prefixLift 5499316
  have htrace : WordTrace (prefixWord ++ tailWord_5499316) baseStart_5499316 baseEnd_5499316 := by
    simpa [prefixWord, tailWord_5499316, baseEnd_5499316] using wordTrace_append hprefix tailTrace_5499316
  have hstable : (prefixWord ++ tailWord_5499316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499316).length < 2 ^ (prefixWord ++ tailWord_5499316).sum := by decide
  have hdescent : baseEnd_5499316 < baseStart_5499316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499348 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_5499348 : Nat := 118140960795 + 5499348 * 2 ^ 59
def prefixEnd_5499348 : Nat := 4983230072969 + 3 ^ 40 * 5499348 * 2
def baseEnd_5499348 : Nat := 941269603447285003119655

theorem tailTrace_5499348 : CollatzResearch.WordTrace tailWord_5499348 prefixEnd_5499348 941269603447285003119655 := by
  unfold tailWord_5499348
  simp only [CollatzResearch.WordTrace]
  refine ⟨100288849840404442354437349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133718466453872589805916465 100288849840404442354437349)
  ·
    refine ⟨18804159345075832941457003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100288849840404442354437349 18804159345075832941457003)
    ·
      refine ⟨28206239017613749412185505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18804159345075832941457003 28206239017613749412185505)
      ·
        refine ⟨21154679263210312059139129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28206239017613749412185505 21154679263210312059139129)
        ·
          refine ⟨15866009447407734044354347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21154679263210312059139129 15866009447407734044354347)
          ·
            refine ⟨23799014171111601066531521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15866009447407734044354347 23799014171111601066531521)
            ·
              refine ⟨17849260628333700799898641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23799014171111601066531521 17849260628333700799898641)
              ·
                refine ⟨13386945471250275599923981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17849260628333700799898641 13386945471250275599923981)
                ·
                  refine ⟨5020104551718853349971493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13386945471250275599923981 5020104551718853349971493)
                  ·
                    refine ⟨941269603447285003119655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5020104551718853349971493 941269603447285003119655)
                    ·
                      rfl

theorem cell23_5499348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_5499348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499348 prefixEnd_5499348 := by exact prefixLift 5499348
  have htrace : WordTrace (prefixWord ++ tailWord_5499348) baseStart_5499348 baseEnd_5499348 := by
    simpa [prefixWord, tailWord_5499348, baseEnd_5499348] using wordTrace_append hprefix tailTrace_5499348
  have hstable : (prefixWord ++ tailWord_5499348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499348).length < 2 ^ (prefixWord ++ tailWord_5499348).sum := by decide
  have hdescent : baseEnd_5499348 < baseStart_5499348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499382 : List Nat := [5, 1, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_5499382 : Nat := 118140960795 + 5499382 * 2 ^ 59
def prefixEnd_5499382 : Nat := 4983230072969 + 3 ^ 40 * 5499382 * 2
def baseEnd_5499382 : Nat := 941275422894702625444603

theorem tailTrace_5499382 : CollatzResearch.WordTrace tailWord_5499382 prefixEnd_5499382 941275422894702625444603 := by
  unfold tailWord_5499382
  simp only [CollatzResearch.WordTrace]
  refine ⟨12536183735167856782225775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133719293175123805677074933 12536183735167856782225775)
  ·
    refine ⟨18804275602751785173338663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12536183735167856782225775 18804275602751785173338663)
    ·
      refine ⟨28206413404127677760007995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18804275602751785173338663 28206413404127677760007995)
      ·
        refine ⟨42309620106191516640011993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28206413404127677760007995 42309620106191516640011993)
        ·
          refine ⟨31732215079643637480008995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42309620106191516640011993 31732215079643637480008995)
          ·
            refine ⟨47598322619465456220013493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31732215079643637480008995 47598322619465456220013493)
            ·
              refine ⟨4462342745574886520626265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47598322619465456220013493 4462342745574886520626265)
              ·
                refine ⟨3346757059181164890469699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4462342745574886520626265 3346757059181164890469699)
                ·
                  refine ⟨5020135588771747335704549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3346757059181164890469699 5020135588771747335704549)
                  ·
                    refine ⟨941275422894702625444603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5020135588771747335704549 941275422894702625444603)
                    ·
                      rfl

theorem cell23_5499382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_5499382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499382 prefixEnd_5499382 := by exact prefixLift 5499382
  have htrace : WordTrace (prefixWord ++ tailWord_5499382) baseStart_5499382 baseEnd_5499382 := by
    simpa [prefixWord, tailWord_5499382, baseEnd_5499382] using wordTrace_append hprefix tailTrace_5499382
  have hstable : (prefixWord ++ tailWord_5499382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499382).length < 2 ^ (prefixWord ++ tailWord_5499382).sum := by decide
  have hdescent : baseEnd_5499382 < baseStart_5499382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499411 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 4]
def baseStart_5499411 : Nat := 118140960795 + 5499411 * 2 ^ 59
def prefixEnd_5499411 : Nat := 4983230072969 + 3 ^ 40 * 5499411 * 2
def baseEnd_5499411 : Nat := 2823841159623088262871175

theorem tailTrace_5499411 : CollatzResearch.WordTrace tailWord_5499411 prefixEnd_5499411 2823841159623088262871175 := by
  unfold tailWord_5499411
  simp only [CollatzResearch.WordTrace]
  refine ⟨200579997479580646468418087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133719998319720430978945391 200579997479580646468418087)
  ·
    refine ⟨300869996219370969702627131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200579997479580646468418087 300869996219370969702627131)
    ·
      refine ⟨451304994329056454553940697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300869996219370969702627131 451304994329056454553940697)
      ·
        refine ⟨338478745746792340915455523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451304994329056454553940697 338478745746792340915455523)
        ·
          refine ⟨507718118620188511373183285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338478745746792340915455523 507718118620188511373183285)
          ·
            refine ⟨47598573620642672941235933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 507718118620188511373183285 47598573620642672941235933)
            ·
              refine ⟨17849465107741002352963475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47598573620642672941235933 17849465107741002352963475)
              ·
                refine ⟨26774197661611503529445213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17849465107741002352963475 26774197661611503529445213)
                ·
                  refine ⟨10040324123104313823541955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26774197661611503529445213 10040324123104313823541955)
                  ·
                    refine ⟨15060486184656470735312933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10040324123104313823541955 15060486184656470735312933)
                    ·
                      refine ⟨2823841159623088262871175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15060486184656470735312933 2823841159623088262871175)
                      ·
                        rfl

theorem cell23_5499411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_5499411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499411 prefixEnd_5499411 := by exact prefixLift 5499411
  have htrace : WordTrace (prefixWord ++ tailWord_5499411) baseStart_5499411 baseEnd_5499411 := by
    simpa [prefixWord, tailWord_5499411, baseEnd_5499411] using wordTrace_append hprefix tailTrace_5499411
  have hstable : (prefixWord ++ tailWord_5499411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499411).length < 2 ^ (prefixWord ++ tailWord_5499411).sum := by decide
  have hdescent : baseEnd_5499411 < baseStart_5499411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499421 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_5499421 : Nat := 118140960795 + 5499421 * 2 ^ 59
def prefixEnd_5499421 : Nat := 4983230072969 + 3 ^ 40 * 5499421 * 2
def baseEnd_5499421 : Nat := 941282098143211074582043

theorem tailTrace_5499421 : CollatzResearch.WordTrace tailWord_5499421 prefixEnd_5499421 941282098143211074582043 := by
  unfold tailWord_5499421
  simp only [CollatzResearch.WordTrace]
  refine ⟨200580362209544418176282117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133720241473029612117521411 200580362209544418176282117)
  ·
    refine ⟨37608817914289578408052897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200580362209544418176282117 37608817914289578408052897)
    ·
      refine ⟨28206613435717183806039673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37608817914289578408052897 28206613435717183806039673)
      ·
        refine ⟨21154960076787887854529755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28206613435717183806039673 21154960076787887854529755)
        ·
          refine ⟨31732440115181831781794633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21154960076787887854529755 31732440115181831781794633)
          ·
            refine ⟨23799330086386373836345975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31732440115181831781794633 23799330086386373836345975)
            ·
              refine ⟨35698995129579560754518963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23799330086386373836345975 35698995129579560754518963)
              ·
                refine ⟨53548492694369341131778445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35698995129579560754518963 53548492694369341131778445)
                ·
                  refine ⟨20080684760388502924416917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53548492694369341131778445 20080684760388502924416917)
                  ·
                    refine ⟨941282098143211074582043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20080684760388502924416917 941282098143211074582043)
                    ·
                      rfl

theorem cell23_5499421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_5499421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499421 prefixEnd_5499421 := by exact prefixLift 5499421
  have htrace : WordTrace (prefixWord ++ tailWord_5499421) baseStart_5499421 baseEnd_5499421 := by
    simpa [prefixWord, tailWord_5499421, baseEnd_5499421] using wordTrace_append hprefix tailTrace_5499421
  have hstable : (prefixWord ++ tailWord_5499421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499421).length < 2 ^ (prefixWord ++ tailWord_5499421).sum := by decide
  have hdescent : baseEnd_5499421 < baseStart_5499421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499445 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_5499445 : Nat := 118140960795 + 5499445 * 2 ^ 59
def prefixEnd_5499445 : Nat := 4983230072969 + 3 ^ 40 * 5499445 * 2
def baseEnd_5499445 : Nat := 2823858617965341129846019

theorem tailTrace_5499445 : CollatzResearch.WordTrace tailWord_5499445 prefixEnd_5499445 2823858617965341129846019 := by
  unfold tailWord_5499445
  simp only [CollatzResearch.WordTrace]
  refine ⟨200581237561457470275155789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133720825040971646850103859 200581237561457470275155789)
  ·
    refine ⟨75217964085546551353183421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200581237561457470275155789 75217964085546551353183421)
    ·
      refine ⟨28206736532079956757443783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75217964085546551353183421 28206736532079956757443783)
      ·
        refine ⟨42310104798119935136165675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28206736532079956757443783 42310104798119935136165675)
        ·
          refine ⟨63465157197179902704248513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42310104798119935136165675 63465157197179902704248513)
          ·
            refine ⟨47598867897884927028186385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63465157197179902704248513 47598867897884927028186385)
            ·
              refine ⟨35699150923413695271139789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47598867897884927028186385 35699150923413695271139789)
              ·
                refine ⟨13387181596280135726677421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35699150923413695271139789 13387181596280135726677421)
                ·
                  refine ⟨5020193098605050897504033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13387181596280135726677421 5020193098605050897504033)
                  ·
                    refine ⟨3765144823953788173128025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5020193098605050897504033 3765144823953788173128025)
                    ·
                      refine ⟨2823858617965341129846019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765144823953788173128025 2823858617965341129846019)
                      ·
                        rfl

theorem cell23_5499445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_5499445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499445 prefixEnd_5499445 := by exact prefixLift 5499445
  have htrace : WordTrace (prefixWord ++ tailWord_5499445) baseStart_5499445 baseEnd_5499445 := by
    simpa [prefixWord, tailWord_5499445, baseEnd_5499445] using wordTrace_append hprefix tailTrace_5499445
  have hstable : (prefixWord ++ tailWord_5499445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499445).length < 2 ^ (prefixWord ++ tailWord_5499445).sum := by decide
  have hdescent : baseEnd_5499445 < baseStart_5499445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499511 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 2, 6]
def baseStart_5499511 : Nat := 118140960795 + 5499511 * 2 ^ 59
def prefixEnd_5499511 : Nat := 4983230072969 + 3 ^ 40 * 5499511 * 2
def baseEnd_5499511 : Nat := 941297502562845957206905

theorem tailTrace_5499511 : CollatzResearch.WordTrace tailWord_5499511 prefixEnd_5499511 941297502562845957206905 := by
  unfold tailWord_5499511
  simp only [CollatzResearch.WordTrace]
  refine ⟨200583644779218363547058387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133722429852812242364705591 200583644779218363547058387)
  ·
    refine ⟨300875467168827545320587581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200583644779218363547058387 300875467168827545320587581)
    ·
      refine ⟨112828300188310329495220343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300875467168827545320587581 112828300188310329495220343)
      ·
        refine ⟨169242450282465494242830515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112828300188310329495220343 169242450282465494242830515)
        ·
          refine ⟨253863675423698241364245773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169242450282465494242830515 253863675423698241364245773)
          ·
            refine ⟨95198878283886840511592165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253863675423698241364245773 95198878283886840511592165)
            ·
              refine ⟨17849789678228782595923531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95198878283886840511592165 17849789678228782595923531)
              ·
                refine ⟨26774684517343173893885297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17849789678228782595923531 26774684517343173893885297)
                ·
                  refine ⟨20081013388007380420413973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26774684517343173893885297 20081013388007380420413973)
                  ·
                    refine ⟨941297502562845957206905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20081013388007380420413973 941297502562845957206905)
                    ·
                      rfl

theorem cell23_5499511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_5499511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499511 prefixEnd_5499511 := by exact prefixLift 5499511
  have htrace : WordTrace (prefixWord ++ tailWord_5499511) baseStart_5499511 baseEnd_5499511 := by
    simpa [prefixWord, tailWord_5499511, baseEnd_5499511] using wordTrace_append hprefix tailTrace_5499511
  have hstable : (prefixWord ++ tailWord_5499511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499511).length < 2 ^ (prefixWord ++ tailWord_5499511).sum := by decide
  have hdescent : baseEnd_5499511 < baseStart_5499511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499531 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 4]
def baseStart_5499531 : Nat := 118140960795 + 5499531 * 2 ^ 59
def prefixEnd_5499531 : Nat := 4983230072969 + 3 ^ 40 * 5499531 * 2
def baseEnd_5499531 : Nat := 2823902777301627793370623

theorem tailTrace_5499531 : CollatzResearch.WordTrace tailWord_5499531 prefixEnd_5499531 2823902777301627793370623 := by
  unfold tailWord_5499531
  simp only [CollatzResearch.WordTrace]
  refine ⟨200584374239145906962786447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133722916159430604641857631 200584374239145906962786447)
  ·
    refine ⟨300876561358718860444179671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200584374239145906962786447 300876561358718860444179671)
    ·
      refine ⟨451314842038078290666269507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300876561358718860444179671 451314842038078290666269507)
      ·
        refine ⟨676972263057117435999404261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451314842038078290666269507 676972263057117435999404261)
        ·
          refine ⟨126932299323209519249888299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 676972263057117435999404261 126932299323209519249888299)
          ·
            refine ⟨190398448984814278874832449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126932299323209519249888299 190398448984814278874832449)
            ·
              refine ⟨142798836738610709156124337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190398448984814278874832449 142798836738610709156124337)
              ·
                refine ⟨107099127553958031867093253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142798836738610709156124337 107099127553958031867093253)
                ·
                  refine ⟨20081086416367130975079985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107099127553958031867093253 20081086416367130975079985)
                  ·
                    refine ⟨15060814812275348231309989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20081086416367130975079985 15060814812275348231309989)
                    ·
                      refine ⟨2823902777301627793370623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15060814812275348231309989 2823902777301627793370623)
                      ·
                        rfl

theorem cell23_5499531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 4].length) (baseStart_5499531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499531 prefixEnd_5499531 := by exact prefixLift 5499531
  have htrace : WordTrace (prefixWord ++ tailWord_5499531) baseStart_5499531 baseEnd_5499531 := by
    simpa [prefixWord, tailWord_5499531, baseEnd_5499531] using wordTrace_append hprefix tailTrace_5499531
  have hstable : (prefixWord ++ tailWord_5499531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499531).length < 2 ^ (prefixWord ++ tailWord_5499531).sum := by decide
  have hdescent : baseEnd_5499531 < baseStart_5499531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499538 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_5499538 : Nat := 118140960795 + 5499538 * 2 ^ 59
def prefixEnd_5499538 : Nat := 4983230072969 + 3 ^ 40 * 5499538 * 2
def baseEnd_5499538 : Nat := 2823906371666209265983091

theorem tailTrace_5499538 : CollatzResearch.WordTrace tailWord_5499538 prefixEnd_5499538 2823906371666209265983091 := by
  unfold tailWord_5499538
  simp only [CollatzResearch.WordTrace]
  refine ⟨50146157387530136789572817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133723086366747031438860845 50146157387530136789572817)
  ·
    refine ⟨37609618040647602592179613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50146157387530136789572817 37609618040647602592179613)
    ·
      refine ⟨14103606765242850972067355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37609618040647602592179613 14103606765242850972067355)
      ·
        refine ⟨21155410147864276458101033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14103606765242850972067355 21155410147864276458101033)
        ·
          refine ⟨15866557610898207343575775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21155410147864276458101033 15866557610898207343575775)
          ·
            refine ⟨23799836416347311015363663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15866557610898207343575775 23799836416347311015363663)
            ·
              refine ⟨35699754624520966523045495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23799836416347311015363663 35699754624520966523045495)
              ·
                refine ⟨53549631936781449784568243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35699754624520966523045495 53549631936781449784568243)
                ·
                  refine ⟨80324447905172174676852365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53549631936781449784568243 80324447905172174676852365)
                  ·
                    refine ⟨30121667964439565503819637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80324447905172174676852365 30121667964439565503819637)
                    ·
                      refine ⟨2823906371666209265983091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30121667964439565503819637 2823906371666209265983091)
                      ·
                        rfl

theorem cell23_5499538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_5499538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499538 prefixEnd_5499538 := by exact prefixLift 5499538
  have htrace : WordTrace (prefixWord ++ tailWord_5499538) baseStart_5499538 baseEnd_5499538 := by
    simpa [prefixWord, tailWord_5499538, baseEnd_5499538] using wordTrace_append hprefix tailTrace_5499538
  have hstable : (prefixWord ++ tailWord_5499538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499538).length < 2 ^ (prefixWord ++ tailWord_5499538).sum := by decide
  have hdescent : baseEnd_5499538 < baseStart_5499538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499598 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_5499598 : Nat := 118140960795 + 5499598 * 2 ^ 59
def prefixEnd_5499598 : Nat := 4983230072969 + 3 ^ 40 * 5499598 * 2
def baseEnd_5499598 : Nat := 2823937180505479031232815

theorem tailTrace_5499598 : CollatzResearch.WordTrace tailWord_5499598 prefixEnd_5499598 2823937180505479031232815 := by
  unfold tailWord_5499598
  simp only [CollatzResearch.WordTrace]
  refine ⟨25073352241237897175684431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133724545286602118270316965 25073352241237897175684431)
  ·
    refine ⟨37610028361856845763526647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25073352241237897175684431 37610028361856845763526647)
    ·
      refine ⟨56415042542785268645289971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37610028361856845763526647 56415042542785268645289971)
      ·
        refine ⟨84622563814177902967934957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56415042542785268645289971 84622563814177902967934957)
        ·
          refine ⟨31733461430316713612975609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84622563814177902967934957 31733461430316713612975609)
          ·
            refine ⟨23800096072737535209731707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31733461430316713612975609 23800096072737535209731707)
            ·
              refine ⟨35700144109106302814597561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23800096072737535209731707 35700144109106302814597561)
              ·
                refine ⟨26775108081829727110948171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35700144109106302814597561 26775108081829727110948171)
                ·
                  refine ⟨40162662122744590666422257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26775108081829727110948171 40162662122744590666422257)
                  ·
                    refine ⟨30121996592058442999816693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40162662122744590666422257 30121996592058442999816693)
                    ·
                      refine ⟨2823937180505479031232815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30121996592058442999816693 2823937180505479031232815)
                      ·
                        rfl

theorem cell23_5499598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_5499598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499598 prefixEnd_5499598 := by exact prefixLift 5499598
  have htrace : WordTrace (prefixWord ++ tailWord_5499598) baseStart_5499598 baseEnd_5499598 := by
    simpa [prefixWord, tailWord_5499598, baseEnd_5499598] using wordTrace_append hprefix tailTrace_5499598
  have hstable : (prefixWord ++ tailWord_5499598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499598).length < 2 ^ (prefixWord ++ tailWord_5499598).sum := by decide
  have hdescent : baseEnd_5499598 < baseStart_5499598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499612 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5499612 : Nat := 118140960795 + 5499612 * 2 ^ 59
def prefixEnd_5499612 : Nat := 4983230072969 + 3 ^ 40 * 5499612 * 2
def baseEnd_5499612 : Nat := 2823944369234641976457751

theorem tailTrace_5499612 : CollatzResearch.WordTrace tailWord_5499612 prefixEnd_5499612 2823944369234641976457751 := by
  unfold tailWord_5499612
  simp only [CollatzResearch.WordTrace]
  refine ⟨100293664275926228898242545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133724885701234971864323393 100293664275926228898242545)
  ·
    refine ⟨75220248206944671673681909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100293664275926228898242545 75220248206944671673681909)
    ·
      refine ⟨7051898269401062969407679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75220248206944671673681909 7051898269401062969407679)
      ·
        refine ⟨10577847404101594454111519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7051898269401062969407679 10577847404101594454111519)
        ·
          refine ⟨15866771106152391681167279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10577847404101594454111519 15866771106152391681167279)
          ·
            refine ⟨23800156659228587521750919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15866771106152391681167279 23800156659228587521750919)
            ·
              refine ⟨35700234988842881282626379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23800156659228587521750919 35700234988842881282626379)
              ·
                refine ⟨53550352483264321923939569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35700234988842881282626379 53550352483264321923939569)
                ·
                  refine ⟨40162764362448241442954677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53550352483264321923939569 40162764362448241442954677)
                  ·
                    refine ⟨3765259158979522635277001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40162764362448241442954677 3765259158979522635277001)
                    ·
                      refine ⟨2823944369234641976457751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765259158979522635277001 2823944369234641976457751)
                      ·
                        rfl

theorem cell23_5499612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5499612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499612 prefixEnd_5499612 := by exact prefixLift 5499612
  have htrace : WordTrace (prefixWord ++ tailWord_5499612) baseStart_5499612 baseEnd_5499612 := by
    simpa [prefixWord, tailWord_5499612, baseEnd_5499612] using wordTrace_append hprefix tailTrace_5499612
  have hstable : (prefixWord ++ tailWord_5499612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499612).length < 2 ^ (prefixWord ++ tailWord_5499612).sum := by decide
  have hdescent : baseEnd_5499612 < baseStart_5499612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499628 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 3]
def baseStart_5499628 : Nat := 118140960795 + 5499628 * 2 ^ 59
def prefixEnd_5499628 : Nat := 4983230072969 + 3 ^ 40 * 5499628 * 2
def baseEnd_5499628 : Nat := 2823952584925113913857677

theorem tailTrace_5499628 : CollatzResearch.WordTrace tailWord_5499628 prefixEnd_5499628 2823952584925113913857677 := by
  unfold tailWord_5499628
  simp only [CollatzResearch.WordTrace]
  refine ⟨100293956059897246264533769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133725274746529661686045025 100293956059897246264533769)
  ·
    refine ⟨75220467044922934698400327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100293956059897246264533769 75220467044922934698400327)
    ·
      refine ⟨112830700567384402047600491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75220467044922934698400327 112830700567384402047600491)
      ·
        refine ⟨169246050851076603071400737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112830700567384402047600491 169246050851076603071400737)
        ·
          refine ⟨126934538138307452303550553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169246050851076603071400737 126934538138307452303550553)
          ·
            refine ⟨95200903603730589227662915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126934538138307452303550553 95200903603730589227662915)
            ·
              refine ⟨142801355405595883841494373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95200903603730589227662915 142801355405595883841494373)
              ·
                refine ⟨26775254138549228220280195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142801355405595883841494373 26775254138549228220280195)
                ·
                  refine ⟨40162881207823842330420293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26775254138549228220280195 40162881207823842330420293)
                  ·
                    refine ⟨7530540226466970436953805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40162881207823842330420293 7530540226466970436953805)
                    ·
                      refine ⟨2823952584925113913857677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7530540226466970436953805 2823952584925113913857677)
                      ·
                        rfl

theorem cell23_5499628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_5499628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499628 prefixEnd_5499628 := by exact prefixLift 5499628
  have htrace : WordTrace (prefixWord ++ tailWord_5499628) baseStart_5499628 baseEnd_5499628 := by
    simpa [prefixWord, tailWord_5499628, baseEnd_5499628] using wordTrace_append hprefix tailTrace_5499628
  have hstable : (prefixWord ++ tailWord_5499628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499628).length < 2 ^ (prefixWord ++ tailWord_5499628).sum := by decide
  have hdescent : baseEnd_5499628 < baseStart_5499628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499682 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 6]
def baseStart_5499682 : Nat := 118140960795 + 5499682 * 2 ^ 59
def prefixEnd_5499682 : Nat := 4983230072969 + 3 ^ 40 * 5499682 * 2
def baseEnd_5499682 : Nat := 313775590320050744731381

theorem tailTrace_5499682 : CollatzResearch.WordTrace tailWord_5499682 prefixEnd_5499682 313775590320050744731381 := by
  unfold tailWord_5499682
  simp only [CollatzResearch.WordTrace]
  refine ⟨50147470415399714937883325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133726587774399239834355533 50147470415399714937883325)
  ·
    refine ⟨18805301405774893101706247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50147470415399714937883325 18805301405774893101706247)
    ·
      refine ⟨28207952108662339652559371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18805301405774893101706247 28207952108662339652559371)
      ·
        refine ⟨42311928162993509478839057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28207952108662339652559371 42311928162993509478839057)
        ·
          refine ⟨31733946122245132109129293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42311928162993509478839057 31733946122245132109129293)
          ·
            refine ⟨11900229795841924540923485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31733946122245132109129293 11900229795841924540923485)
            ·
              refine ⟨4462586173440721702846307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11900229795841924540923485 4462586173440721702846307)
              ·
                refine ⟨6693879260161082554269461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462586173440721702846307 6693879260161082554269461)
                ·
                  refine ⟨313775590320050744731381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6693879260161082554269461 313775590320050744731381)
                  ·
                    rfl

theorem cell23_5499682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_5499682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499682 prefixEnd_5499682 := by exact prefixLift 5499682
  have htrace : WordTrace (prefixWord ++ tailWord_5499682) baseStart_5499682 baseEnd_5499682 := by
    simpa [prefixWord, tailWord_5499682, baseEnd_5499682] using wordTrace_append hprefix tailTrace_5499682
  have hstable : (prefixWord ++ tailWord_5499682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499682).length < 2 ^ (prefixWord ++ tailWord_5499682).sum := by decide
  have hdescent : baseEnd_5499682 < baseStart_5499682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499685 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 3, 5, 2]
def baseStart_5499685 : Nat := 118140960795 + 5499685 * 2 ^ 59
def prefixEnd_5499685 : Nat := 4983230072969 + 3 ^ 40 * 5499685 * 2
def baseEnd_5499685 : Nat := 2823981853322420190844915

theorem tailTrace_5499685 : CollatzResearch.WordTrace tailWord_5499685 prefixEnd_5499685 2823981853322420190844915 := by
  unfold tailWord_5499685
  simp only [CollatzResearch.WordTrace]
  refine ⟨200589991080587991263892509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133726660720391994175928339 200589991080587991263892509)
  ·
    refine ⟨75221246655220496723959691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200589991080587991263892509 75221246655220496723959691)
    ·
      refine ⟨112831869982830745085939537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75221246655220496723959691 112831869982830745085939537)
      ·
        refine ⟨84623902487123058814454653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112831869982830745085939537 84623902487123058814454653)
        ·
          refine ⟨31733963432671147055420495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84623902487123058814454653 31733963432671147055420495)
          ·
            refine ⟨47600945149006720583130743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31733963432671147055420495 47600945149006720583130743)
            ·
              refine ⟨71401417723510080874696115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47600945149006720583130743 71401417723510080874696115)
              ·
                refine ⟨107102126585265121312044173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71401417723510080874696115 107102126585265121312044173)
                ·
                  refine ⟨40163297469474420492016565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107102126585265121312044173 40163297469474420492016565)
                  ·
                    refine ⟨3765309137763226921126553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40163297469474420492016565 3765309137763226921126553)
                    ·
                      refine ⟨2823981853322420190844915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765309137763226921126553 2823981853322420190844915)
                      ·
                        rfl

theorem cell23_5499685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_5499685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499685 prefixEnd_5499685 := by exact prefixLift 5499685
  have htrace : WordTrace (prefixWord ++ tailWord_5499685) baseStart_5499685 baseEnd_5499685 := by
    simpa [prefixWord, tailWord_5499685, baseEnd_5499685] using wordTrace_append hprefix tailTrace_5499685
  have hstable : (prefixWord ++ tailWord_5499685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499685).length < 2 ^ (prefixWord ++ tailWord_5499685).sum := by decide
  have hdescent : baseEnd_5499685 < baseStart_5499685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499708 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_5499708 : Nat := 118140960795 + 5499708 * 2 ^ 59
def prefixEnd_5499708 : Nat := 4983230072969 + 3 ^ 40 * 5499708 * 2
def baseEnd_5499708 : Nat := 941331221125824533619103

theorem tailTrace_5499708 : CollatzResearch.WordTrace tailWord_5499708 prefixEnd_5499708 941331221125824533619103 := by
  unfold tailWord_5499708
  simp only [CollatzResearch.WordTrace]
  refine ⟨100295414979752333095989889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133727219973003110794653185 100295414979752333095989889)
  ·
    refine ⟨75221561234814249821992417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100295414979752333095989889 75221561234814249821992417)
    ·
      refine ⟨56416170926110687366494313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75221561234814249821992417 56416170926110687366494313)
      ·
        refine ⟨42312128194583015524870735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56416170926110687366494313 42312128194583015524870735)
        ·
          refine ⟨63468192291874523287306103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42312128194583015524870735 63468192291874523287306103)
          ·
            refine ⟨95202288437811784930959155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63468192291874523287306103 95202288437811784930959155)
            ·
              refine ⟨142803432656717677396438733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95202288437811784930959155 142803432656717677396438733)
              ·
                refine ⟨53551287246269129023664525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142803432656717677396438733 53551287246269129023664525)
                ·
                  refine ⟨20081732717350923383874197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53551287246269129023664525 20081732717350923383874197)
                  ·
                    refine ⟨941331221125824533619103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20081732717350923383874197 941331221125824533619103)
                    ·
                      rfl

theorem cell23_5499708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_5499708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499708 prefixEnd_5499708 := by exact prefixLift 5499708
  have htrace : WordTrace (prefixWord ++ tailWord_5499708) baseStart_5499708 baseEnd_5499708 := by
    simpa [prefixWord, tailWord_5499708, baseEnd_5499708] using wordTrace_append hprefix tailTrace_5499708
  have hstable : (prefixWord ++ tailWord_5499708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499708).length < 2 ^ (prefixWord ++ tailWord_5499708).sum := by decide
  have hdescent : baseEnd_5499708 < baseStart_5499708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499715 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 4]
def baseStart_5499715 : Nat := 118140960795 + 5499715 * 2 ^ 59
def prefixEnd_5499715 : Nat := 4983230072969 + 3 ^ 40 * 5499715 * 2
def baseEnd_5499715 : Nat := 2823997257742055073469777

theorem tailTrace_5499715 : CollatzResearch.WordTrace tailWord_5499715 prefixEnd_5499715 2823997257742055073469777 := by
  unfold tailWord_5499715
  simp only [CollatzResearch.WordTrace]
  refine ⟨200591085270479306387484599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133727390180319537591656399 200591085270479306387484599)
  ·
    refine ⟨300886627905718959581226899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200591085270479306387484599 300886627905718959581226899)
    ·
      refine ⟨451329941858578439371840349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300886627905718959581226899 451329941858578439371840349)
      ·
        refine ⟨169248728196966914764440131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451329941858578439371840349 169248728196966914764440131)
        ·
          refine ⟨253873092295450372146660197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169248728196966914764440131 253873092295450372146660197)
          ·
            refine ⟨47601204805396944777498787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253873092295450372146660197 47601204805396944777498787)
            ·
              refine ⟨71401807208095417166248181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47601204805396944777498787 71401807208095417166248181)
              ·
                refine ⟨6693919425758945359335767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71401807208095417166248181 6693919425758945359335767)
                ·
                  refine ⟨10040879138638418039003651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6693919425758945359335767 10040879138638418039003651)
                  ·
                    refine ⟨15061318707957627058505477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10040879138638418039003651 15061318707957627058505477)
                    ·
                      refine ⟨2823997257742055073469777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15061318707957627058505477 2823997257742055073469777)
                      ·
                        rfl

theorem cell23_5499715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_5499715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499715 prefixEnd_5499715 := by exact prefixLift 5499715
  have htrace : WordTrace (prefixWord ++ tailWord_5499715) baseStart_5499715 baseEnd_5499715 := by
    simpa [prefixWord, tailWord_5499715, baseEnd_5499715] using wordTrace_append hprefix tailTrace_5499715
  have hstable : (prefixWord ++ tailWord_5499715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499715).length < 2 ^ (prefixWord ++ tailWord_5499715).sum := by decide
  have hdescent : baseEnd_5499715 < baseStart_5499715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499728 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 6]
def baseStart_5499728 : Nat := 118140960795 + 5499728 * 2 ^ 59
def prefixEnd_5499728 : Nat := 4983230072969 + 3 ^ 40 * 5499728 * 2
def baseEnd_5499728 : Nat := 2824003932990563522607217

theorem tailTrace_5499728 : CollatzResearch.WordTrace tailWord_5499728 prefixEnd_5499728 2824003932990563522607217 := by
  unfold tailWord_5499728
  simp only [CollatzResearch.WordTrace]
  refine ⟨100295779709716104803853919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133727706279621473071805225 100295779709716104803853919)
  ·
    refine ⟨150443669564574157205780879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100295779709716104803853919 150443669564574157205780879)
    ·
      refine ⟨225665504346861235808671319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150443669564574157205780879 225665504346861235808671319)
      ·
        refine ⟨338498256520291853713006979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225665504346861235808671319 338498256520291853713006979)
        ·
          refine ⟨507747384780437780569510469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338498256520291853713006979 507747384780437780569510469)
          ·
            refine ⟨95202634646332083856783213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 507747384780437780569510469 95202634646332083856783213)
            ·
              refine ⟨35700987992374531446293705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95202634646332083856783213 35700987992374531446293705)
              ·
                refine ⟨26775740994280898584720279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35700987992374531446293705 26775740994280898584720279)
                ·
                  refine ⟨40163611491421347877080419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26775740994280898584720279 40163611491421347877080419)
                  ·
                    refine ⟨60245417237132021815620629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40163611491421347877080419 60245417237132021815620629)
                    ·
                      refine ⟨2824003932990563522607217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60245417237132021815620629 2824003932990563522607217)
                      ·
                        rfl

theorem cell23_5499728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_5499728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499728 prefixEnd_5499728 := by exact prefixLift 5499728
  have htrace : WordTrace (prefixWord ++ tailWord_5499728) baseStart_5499728 baseEnd_5499728 := by
    simpa [prefixWord, tailWord_5499728, baseEnd_5499728] using wordTrace_append hprefix tailTrace_5499728
  have hstable : (prefixWord ++ tailWord_5499728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499728).length < 2 ^ (prefixWord ++ tailWord_5499728).sum := by decide
  have hdescent : baseEnd_5499728 < baseStart_5499728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499735 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_5499735 : Nat := 118140960795 + 5499735 * 2 ^ 59
def prefixEnd_5499735 : Nat := 4983230072969 + 3 ^ 40 * 5499735 * 2
def baseEnd_5499735 : Nat := 2824007527355144995219685

theorem tailTrace_5499735 : CollatzResearch.WordTrace tailWord_5499735 prefixEnd_5499735 2824007527355144995219685 := by
  unfold tailWord_5499735
  simp only [CollatzResearch.WordTrace]
  refine ⟨200591814730406849803212659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133727876486937899868808439 200591814730406849803212659)
  ·
    refine ⟨300887722095610274704818989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200591814730406849803212659 300887722095610274704818989)
    ·
      refine ⟨112832895785853853014307121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300887722095610274704818989 112832895785853853014307121)
      ·
        refine ⟨84624671839390389760730341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112832895785853853014307121 84624671839390389760730341)
        ·
          refine ⟨15867125969885698080136939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84624671839390389760730341 15867125969885698080136939)
          ·
            refine ⟨23800688954828547120205409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15867125969885698080136939 23800688954828547120205409)
            ·
              refine ⟨17850516716121410340154057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23800688954828547120205409 17850516716121410340154057)
              ·
                refine ⟨13387887537091057755115543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17850516716121410340154057 13387887537091057755115543)
                ·
                  refine ⟨20081831305636586632673315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13387887537091057755115543 20081831305636586632673315)
                  ·
                    refine ⟨30122746958454879949009973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20081831305636586632673315 30122746958454879949009973)
                    ·
                      refine ⟨2824007527355144995219685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30122746958454879949009973 2824007527355144995219685)
                      ·
                        rfl

theorem cell23_5499735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_5499735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499735 prefixEnd_5499735 := by exact prefixLift 5499735
  have htrace : WordTrace (prefixWord ++ tailWord_5499735) baseStart_5499735 baseEnd_5499735 := by
    simpa [prefixWord, tailWord_5499735, baseEnd_5499735] using wordTrace_append hprefix tailTrace_5499735
  have hstable : (prefixWord ++ tailWord_5499735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499735).length < 2 ^ (prefixWord ++ tailWord_5499735).sum := by decide
  have hdescent : baseEnd_5499735 < baseStart_5499735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499738 : List Nat := [3, 1, 1, 2, 1, 4, 1, 10]
def baseStart_5499738 : Nat := 118140960795 + 5499738 * 2 ^ 59
def prefixEnd_5499738 : Nat := 4983230072969 + 3 ^ 40 * 5499738 * 2
def baseEnd_5499738 : Nat := 104592928436929943832673

theorem tailTrace_5499738 : CollatzResearch.WordTrace tailWord_5499738 prefixEnd_5499738 104592928436929943832673 := by
  unfold tailWord_5499738
  simp only [CollatzResearch.WordTrace]
  refine ⟨50147981037348995328892967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133727949432930654210381245 50147981037348995328892967)
  ·
    refine ⟨75221971556023492993339451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50147981037348995328892967 75221971556023492993339451)
    ·
      refine ⟨112832957334035239490009177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75221971556023492993339451 112832957334035239490009177)
      ·
        refine ⟨84624718000526429617506883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112832957334035239490009177 84624718000526429617506883)
        ·
          refine ⟨126937077000789644426260325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84624718000526429617506883 126937077000789644426260325)
          ·
            refine ⟨23800701937648058329923811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126937077000789644426260325 23800701937648058329923811)
            ·
              refine ⟨35701052906472087494885717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23800701937648058329923811 35701052906472087494885717)
              ·
                refine ⟨104592928436929943832673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35701052906472087494885717 104592928436929943832673)
                ·
                  rfl

theorem cell23_5499738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 10].length) (baseStart_5499738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499738 prefixEnd_5499738 := by exact prefixLift 5499738
  have htrace : WordTrace (prefixWord ++ tailWord_5499738) baseStart_5499738 baseEnd_5499738 := by
    simpa [prefixWord, tailWord_5499738, baseEnd_5499738] using wordTrace_append hprefix tailTrace_5499738
  have hstable : (prefixWord ++ tailWord_5499738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499738).length < 2 ^ (prefixWord ++ tailWord_5499738).sum := by decide
  have hdescent : baseEnd_5499738 < baseStart_5499738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499746 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_5499746 : Nat := 118140960795 + 5499746 * 2 ^ 59
def prefixEnd_5499746 : Nat := 4983230072969 + 3 ^ 40 * 5499746 * 2
def baseEnd_5499746 : Nat := 941337725214114817394045

theorem tailTrace_5499746 : CollatzResearch.WordTrace tailWord_5499746 prefixEnd_5499746 941337725214114817394045 := by
  unfold tailWord_5499746
  simp only [CollatzResearch.WordTrace]
  refine ⟨50148053983341749670465773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133728143955577999121242061 50148053983341749670465773)
  ·
    refine ⟨18805520243753156126424665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50148053983341749670465773 18805520243753156126424665)
    ·
      refine ⟨14104140182814867094818499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18805520243753156126424665 14104140182814867094818499)
      ·
        refine ⟨21156210274222300642227749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14104140182814867094818499 21156210274222300642227749)
        ·
          refine ⟨3966789426416681370417703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21156210274222300642227749 3966789426416681370417703)
          ·
            refine ⟨5950184139625022055626555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3966789426416681370417703 5950184139625022055626555)
            ·
              refine ⟨8925276209437533083439833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5950184139625022055626555 8925276209437533083439833)
              ·
                refine ⟨6693957157078149812579875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8925276209437533083439833 6693957157078149812579875)
                ·
                  refine ⟨10040935735617224718869813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6693957157078149812579875 10040935735617224718869813)
                  ·
                    refine ⟨941337725214114817394045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10040935735617224718869813 941337725214114817394045)
                    ·
                      rfl

theorem cell23_5499746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_5499746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499746 prefixEnd_5499746 := by exact prefixLift 5499746
  have htrace : WordTrace (prefixWord ++ tailWord_5499746) baseStart_5499746 baseEnd_5499746 := by
    simpa [prefixWord, tailWord_5499746, baseEnd_5499746] using wordTrace_append hprefix tailTrace_5499746
  have hstable : (prefixWord ++ tailWord_5499746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499746).length < 2 ^ (prefixWord ++ tailWord_5499746).sum := by decide
  have hdescent : baseEnd_5499746 < baseStart_5499746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499752 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_5499752 : Nat := 118140960795 + 5499752 * 2 ^ 59
def prefixEnd_5499752 : Nat := 4983230072969 + 3 ^ 40 * 5499752 * 2
def baseEnd_5499752 : Nat := 2824016256526271428707107

theorem tailTrace_5499752 : CollatzResearch.WordTrace tailWord_5499752 prefixEnd_5499752 2824016256526271428707107 := by
  unfold tailWord_5499752
  simp only [CollatzResearch.WordTrace]
  refine ⟨100296217385672630853290755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133728289847563507804387673 100296217385672630853290755)
  ·
    refine ⟨150444326078508946279936133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100296217385672630853290755 150444326078508946279936133)
    ·
      refine ⟨28208311139720427427488025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150444326078508946279936133 28208311139720427427488025)
      ·
        refine ⟨21156233354790320570616019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28208311139720427427488025 21156233354790320570616019)
        ·
          refine ⟨31734350032185480855924029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21156233354790320570616019 31734350032185480855924029)
          ·
            refine ⟨11900381262069555320971511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31734350032185480855924029 11900381262069555320971511)
            ·
              refine ⟨17850571893104332981457267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11900381262069555320971511 17850571893104332981457267)
              ·
                refine ⟨26775857839656499472185901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17850571893104332981457267 26775857839656499472185901)
                ·
                  refine ⟨10040946689871187302069713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26775857839656499472185901 10040946689871187302069713)
                  ·
                    refine ⟨7530710017403390476552285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10040946689871187302069713 7530710017403390476552285)
                    ·
                      refine ⟨2824016256526271428707107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7530710017403390476552285 2824016256526271428707107)
                      ·
                        rfl

theorem cell23_5499752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_5499752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499752 prefixEnd_5499752 := by exact prefixLift 5499752
  have htrace : WordTrace (prefixWord ++ tailWord_5499752) baseStart_5499752 baseEnd_5499752 := by
    simpa [prefixWord, tailWord_5499752, baseEnd_5499752] using wordTrace_append hprefix tailTrace_5499752
  have hstable : (prefixWord ++ tailWord_5499752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499752).length < 2 ^ (prefixWord ++ tailWord_5499752).sum := by decide
  have hdescent : baseEnd_5499752 < baseStart_5499752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499766 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_5499766 : Nat := 118140960795 + 5499766 * 2 ^ 59
def prefixEnd_5499766 : Nat := 4983230072969 + 3 ^ 40 * 5499766 * 2
def baseEnd_5499766 : Nat := 2824023445255434373932043

theorem tailTrace_5499766 : CollatzResearch.WordTrace tailWord_5499766 prefixEnd_5499766 2824023445255434373932043 := by
  unfold tailWord_5499766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12537059087080908881099447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133728630262196361398394101 12537059087080908881099447)
  ·
    refine ⟨18805588630621363321649171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12537059087080908881099447 18805588630621363321649171)
    ·
      refine ⟨28208382945932044982473757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18805588630621363321649171 28208382945932044982473757)
      ·
        refine ⟨10578143604724516868427659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28208382945932044982473757 10578143604724516868427659)
        ·
          refine ⟨15867215407086775302641489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10578143604724516868427659 15867215407086775302641489)
          ·
            refine ⟨11900411555315081476981117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15867215407086775302641489 11900411555315081476981117)
            ·
              refine ⟨4462654333243155553867919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11900411555315081476981117 4462654333243155553867919)
              ·
                refine ⟨6693981499864733330801879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462654333243155553867919 6693981499864733330801879)
                ·
                  refine ⟨10040972249797099996202819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6693981499864733330801879 10040972249797099996202819)
                  ·
                    refine ⟨15061458374695649994304229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10040972249797099996202819 15061458374695649994304229)
                    ·
                      refine ⟨2824023445255434373932043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15061458374695649994304229 2824023445255434373932043)
                      ·
                        rfl

theorem cell23_5499766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_5499766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499766 prefixEnd_5499766 := by exact prefixLift 5499766
  have htrace : WordTrace (prefixWord ++ tailWord_5499766) baseStart_5499766 baseEnd_5499766 := by
    simpa [prefixWord, tailWord_5499766, baseEnd_5499766] using wordTrace_append hprefix tailTrace_5499766
  have hstable : (prefixWord ++ tailWord_5499766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499766).length < 2 ^ (prefixWord ++ tailWord_5499766).sum := by decide
  have hdescent : baseEnd_5499766 < baseStart_5499766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499769 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 1, 2, 3]
def baseStart_5499769 : Nat := 118140960795 + 5499769 * 2 ^ 59
def prefixEnd_5499769 : Nat := 4983230072969 + 3 ^ 40 * 5499769 * 2
def baseEnd_5499769 : Nat := 2824024985697397862194529

theorem tailTrace_5499769 : CollatzResearch.WordTrace tailWord_5499769 prefixEnd_5499769 2824024985697397862194529 := by
  unfold tailWord_5499769
  simp only [CollatzResearch.WordTrace]
  refine ⟨200593054812283673609950361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133728703208189115739966907 200593054812283673609950361)
  ·
    refine ⟨150444791109212755207462771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200593054812283673609950361 150444791109212755207462771)
    ·
      refine ⟨225667186663819132811194157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150444791109212755207462771 225667186663819132811194157)
      ·
        refine ⟨84625194998932174804197809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225667186663819132811194157 84625194998932174804197809)
        ·
          refine ⟨63468896249199131103148357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84625194998932174804197809 63468896249199131103148357)
          ·
            refine ⟨11900418046724837081840317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63468896249199131103148357 11900418046724837081840317)
            ·
              refine ⟨4462656767521813905690119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11900418046724837081840317 4462656767521813905690119)
              ·
                refine ⟨6693985151282720858535179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462656767521813905690119 6693985151282720858535179)
                ·
                  refine ⟨10040977726924081287802769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6693985151282720858535179 10040977726924081287802769)
                  ·
                    refine ⟨7530733295193060965852077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10040977726924081287802769 7530733295193060965852077)
                    ·
                      refine ⟨2824024985697397862194529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7530733295193060965852077 2824024985697397862194529)
                      ·
                        rfl

theorem cell23_5499769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_5499769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499769 prefixEnd_5499769 := by exact prefixLift 5499769
  have htrace : WordTrace (prefixWord ++ tailWord_5499769) baseStart_5499769 baseEnd_5499769 := by
    simpa [prefixWord, tailWord_5499769, baseEnd_5499769] using wordTrace_append hprefix tailTrace_5499769
  have hstable : (prefixWord ++ tailWord_5499769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499769).length < 2 ^ (prefixWord ++ tailWord_5499769).sum := by decide
  have hdescent : baseEnd_5499769 < baseStart_5499769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499783 : List Nat := [1, 1, 4, 2, 3, 1, 4, 2, 1, 2, 2]
def baseStart_5499783 : Nat := 118140960795 + 5499783 * 2 ^ 59
def prefixEnd_5499783 : Nat := 4983230072969 + 3 ^ 40 * 5499783 * 2
def baseEnd_5499783 : Nat := 2824032174426560807419465

theorem tailTrace_5499783 : CollatzResearch.WordTrace tailWord_5499783 prefixEnd_5499783 2824032174426560807419465 := by
  unfold tailWord_5499783
  simp only [CollatzResearch.WordTrace]
  refine ⟨200593565434232954000960003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133729043622821969333973335 200593565434232954000960003)
  ·
    refine ⟨300890348151349431001440005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200593565434232954000960003 300890348151349431001440005)
    ·
      refine ⟨56416940278378018312770001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300890348151349431001440005 56416940278378018312770001)
      ·
        refine ⟨42312705208783513734577501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56416940278378018312770001 42312705208783513734577501)
        ·
          refine ⟨15867264453293817650466563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42312705208783513734577501 15867264453293817650466563)
          ·
            refine ⟨23800896679940726475699845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15867264453293817650466563 23800896679940726475699845)
            ·
              refine ⟨4462668127488886214193721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23800896679940726475699845 4462668127488886214193721)
              ·
                refine ⟨3347001095616664660645291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4462668127488886214193721 3347001095616664660645291)
                ·
                  refine ⟨5020501643424996990967937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347001095616664660645291 5020501643424996990967937)
                  ·
                    refine ⟨3765376232568747743225953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5020501643424996990967937 3765376232568747743225953)
                    ·
                      refine ⟨2824032174426560807419465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765376232568747743225953 2824032174426560807419465)
                      ·
                        rfl

theorem cell23_5499783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_5499783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499783 prefixEnd_5499783 := by exact prefixLift 5499783
  have htrace : WordTrace (prefixWord ++ tailWord_5499783) baseStart_5499783 baseEnd_5499783 := by
    simpa [prefixWord, tailWord_5499783, baseEnd_5499783] using wordTrace_append hprefix tailTrace_5499783
  have hstable : (prefixWord ++ tailWord_5499783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499783).length < 2 ^ (prefixWord ++ tailWord_5499783).sum := by decide
  have hdescent : baseEnd_5499783 < baseStart_5499783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499805 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_5499805 : Nat := 118140960795 + 5499805 * 2 ^ 59
def prefixEnd_5499805 : Nat := 4983230072969 + 3 ^ 40 * 5499805 * 2
def baseEnd_5499805 : Nat := 2824043471000959721344363

theorem tailTrace_5499805 : CollatzResearch.WordTrace tailWord_5499805 prefixEnd_5499805 2824043471000959721344363 := by
  unfold tailWord_5499805
  simp only [CollatzResearch.WordTrace]
  refine ⟨200594367840153251758260869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133729578560102167838840579 200594367840153251758260869)
  ·
    refine ⟨37611443970028734704673913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200594367840153251758260869 37611443970028734704673913)
    ·
      refine ⟨28208582977521551028505435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37611443970028734704673913 28208582977521551028505435)
      ·
        refine ⟨42312874466282326542758153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28208582977521551028505435 42312874466282326542758153)
        ·
          refine ⟨31734655849711744907068615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42312874466282326542758153 31734655849711744907068615)
          ·
            refine ⟨47601983774567617360602923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31734655849711744907068615 47601983774567617360602923)
            ·
              refine ⟨71402975661851426040904385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47601983774567617360602923 71402975661851426040904385)
              ·
                refine ⟨53552231746388569530678289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71402975661851426040904385 53552231746388569530678289)
                ·
                  refine ⟨40164173809791427148008717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53552231746388569530678289 40164173809791427148008717)
                  ·
                    refine ⟨15061565178671785180503269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40164173809791427148008717 15061565178671785180503269)
                    ·
                      refine ⟨2824043471000959721344363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15061565178671785180503269 2824043471000959721344363)
                      ·
                        rfl

theorem cell23_5499805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_5499805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499805 prefixEnd_5499805 := by exact prefixLift 5499805
  have htrace : WordTrace (prefixWord ++ tailWord_5499805) baseStart_5499805 baseEnd_5499805 := by
    simpa [prefixWord, tailWord_5499805, baseEnd_5499805] using wordTrace_append hprefix tailTrace_5499805
  have hstable : (prefixWord ++ tailWord_5499805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499805).length < 2 ^ (prefixWord ++ tailWord_5499805).sum := by decide
  have hdescent : baseEnd_5499805 < baseStart_5499805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499809 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5499809 : Nat := 118140960795 + 5499809 * 2 ^ 59
def prefixEnd_5499809 : Nat := 4983230072969 + 3 ^ 40 * 5499809 * 2
def baseEnd_5499809 : Nat := 2824045524923577705694345

theorem tailTrace_5499809 : CollatzResearch.WordTrace tailWord_5499809 prefixEnd_5499809 2824045524923577705694345 := by
  unfold tailWord_5499809
  simp only [CollatzResearch.WordTrace]
  refine ⟨200594513732138760441406481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133729675821425840294270987 200594513732138760441406481)
  ·
    refine ⟨150445885299104070331054861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200594513732138760441406481 150445885299104070331054861)
    ·
      refine ⟨56417206987164026374145573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150445885299104070331054861 56417206987164026374145573)
      ·
        refine ⟨10578226310093254945152295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56417206987164026374145573 10578226310093254945152295)
        ·
          refine ⟨15867339465139882417728443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10578226310093254945152295 15867339465139882417728443)
          ·
            refine ⟨23801009197709823626592665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15867339465139882417728443 23801009197709823626592665)
            ·
              refine ⟨17850756898282367719944499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23801009197709823626592665 17850756898282367719944499)
              ·
                refine ⟨26776135347423551579916749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17850756898282367719944499 26776135347423551579916749)
                ·
                  refine ⟨10041050755283831842468781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26776135347423551579916749 10041050755283831842468781)
                  ·
                    refine ⟨3765394033231436940925793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10041050755283831842468781 3765394033231436940925793)
                    ·
                      refine ⟨2824045524923577705694345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765394033231436940925793 2824045524923577705694345)
                      ·
                        rfl

theorem cell23_5499809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5499809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499809 prefixEnd_5499809 := by exact prefixLift 5499809
  have htrace : WordTrace (prefixWord ++ tailWord_5499809) baseStart_5499809 baseEnd_5499809 := by
    simpa [prefixWord, tailWord_5499809, baseEnd_5499809] using wordTrace_append hprefix tailTrace_5499809
  have hstable : (prefixWord ++ tailWord_5499809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499809).length < 2 ^ (prefixWord ++ tailWord_5499809).sum := by decide
  have hdescent : baseEnd_5499809 < baseStart_5499809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499839 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 2, 2, 2]
def baseStart_5499839 : Nat := 118140960795 + 5499839 * 2 ^ 59
def prefixEnd_5499839 : Nat := 4983230072969 + 3 ^ 40 * 5499839 * 2
def baseEnd_5499839 : Nat := 2824060929343212588319207

theorem tailTrace_5499839 : CollatzResearch.WordTrace tailWord_5499839 prefixEnd_5499839 2824060929343212588319207 := by
  unfold tailWord_5499839
  simp only [CollatzResearch.WordTrace]
  refine ⟨200595607922030075564998571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133730405281353383709999047 200595607922030075564998571)
  ·
    refine ⟨300893411883045113347497857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200595607922030075564998571 300893411883045113347497857)
    ·
      refine ⟨225670058912283835010623393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300893411883045113347497857 225670058912283835010623393)
      ·
        refine ⟨169252544184212876257967545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225670058912283835010623393 169252544184212876257967545)
        ·
          refine ⟨126939408138159657193475659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169252544184212876257967545 126939408138159657193475659)
          ·
            refine ⟨190409112207239485790213489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126939408138159657193475659 190409112207239485790213489)
            ·
              refine ⟨142806834155429614342660117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190409112207239485790213489 142806834155429614342660117)
              ·
                refine ⟨6694070351035763172312193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142806834155429614342660117 6694070351035763172312193)
                ·
                  refine ⟨5020552763276822379234145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6694070351035763172312193 5020552763276822379234145)
                  ·
                    refine ⟨3765414572457616784425609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5020552763276822379234145 3765414572457616784425609)
                    ·
                      refine ⟨2824060929343212588319207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765414572457616784425609 2824060929343212588319207)
                      ·
                        rfl

theorem cell23_5499839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 2, 2].length) (baseStart_5499839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499839 prefixEnd_5499839 := by exact prefixLift 5499839
  have htrace : WordTrace (prefixWord ++ tailWord_5499839) baseStart_5499839 baseEnd_5499839 := by
    simpa [prefixWord, tailWord_5499839, baseEnd_5499839] using wordTrace_append hprefix tailTrace_5499839
  have hstable : (prefixWord ++ tailWord_5499839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499839).length < 2 ^ (prefixWord ++ tailWord_5499839).sum := by decide
  have hdescent : baseEnd_5499839 < baseStart_5499839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499875 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 1, 7]
def baseStart_5499875 : Nat := 118140960795 + 5499875 * 2 ^ 59
def prefixEnd_5499875 : Nat := 4983230072969 + 3 ^ 40 * 5499875 * 2
def baseEnd_5499875 : Nat := 941359804882258149156347

theorem tailTrace_5499875 : CollatzResearch.WordTrace tailWord_5499875 prefixEnd_5499875 941359804882258149156347 := by
  unfold tailWord_5499875
  simp only [CollatzResearch.WordTrace]
  refine ⟨200596920949899653713309079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133731280633266435808872719 200596920949899653713309079)
  ·
    refine ⟨300895381424849480569963619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200596920949899653713309079 300895381424849480569963619)
    ·
      refine ⟨451343072137274220854945429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300895381424849480569963619 451343072137274220854945429)
      ·
        refine ⟨21156706506434729102575567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 451343072137274220854945429 21156706506434729102575567)
        ·
          refine ⟨31735059759652093653863351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21156706506434729102575567 31735059759652093653863351)
          ·
            refine ⟨47602589639478140480795027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31735059759652093653863351 47602589639478140480795027)
            ·
              refine ⟨71403884459217210721192541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47602589639478140480795027 71403884459217210721192541)
              ·
                refine ⟨26776456672206454020447203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71403884459217210721192541 26776456672206454020447203)
                ·
                  refine ⟨40164685008309681030670805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26776456672206454020447203 40164685008309681030670805)
                  ·
                    refine ⟨941359804882258149156347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40164685008309681030670805 941359804882258149156347)
                    ·
                      rfl

theorem cell23_5499875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 7].length) (baseStart_5499875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499875 prefixEnd_5499875 := by exact prefixLift 5499875
  have htrace : WordTrace (prefixWord ++ tailWord_5499875) baseStart_5499875 baseEnd_5499875 := by
    simpa [prefixWord, tailWord_5499875, baseEnd_5499875] using wordTrace_append hprefix tailTrace_5499875
  have hstable : (prefixWord ++ tailWord_5499875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499875).length < 2 ^ (prefixWord ++ tailWord_5499875).sum := by decide
  have hdescent : baseEnd_5499875 < baseStart_5499875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499879 : List Nat := [1, 1, 5, 2, 2, 1, 3, 3, 5]
def baseStart_5499879 : Nat := 118140960795 + 5499879 * 2 ^ 59
def prefixEnd_5499879 : Nat := 4983230072969 + 3 ^ 40 * 5499879 * 2
def baseEnd_5499879 : Nat := 313786829841043603535447

theorem tailTrace_5499879 : CollatzResearch.WordTrace tailWord_5499879 prefixEnd_5499879 313786829841043603535447 := by
  unfold tailWord_5499879
  simp only [CollatzResearch.WordTrace]
  refine ⟨200597066841885162396454691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133731377894590108264303127 200597066841885162396454691)
  ·
    refine ⟨300895600262827743594682037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200597066841885162396454691 300895600262827743594682037)
    ·
      refine ⟨28208962524640100962001441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 300895600262827743594682037 28208962524640100962001441)
      ·
        refine ⟨21156721893480075721501081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28208962524640100962001441 21156721893480075721501081)
        ·
          refine ⟨15867541420110056791125811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21156721893480075721501081 15867541420110056791125811)
          ·
            refine ⟨23801312130165085186688717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15867541420110056791125811 23801312130165085186688717)
            ·
              refine ⟨8925492048811906945008269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23801312130165085186688717 8925492048811906945008269)
              ·
                refine ⟨3347059518304465104378101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8925492048811906945008269 3347059518304465104378101)
                ·
                  refine ⟨313786829841043603535447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3347059518304465104378101 313786829841043603535447)
                  ·
                    rfl

theorem cell23_5499879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 5].length) (baseStart_5499879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499879 prefixEnd_5499879 := by exact prefixLift 5499879
  have htrace : WordTrace (prefixWord ++ tailWord_5499879) baseStart_5499879 baseEnd_5499879 := by
    simpa [prefixWord, tailWord_5499879, baseEnd_5499879] using wordTrace_append hprefix tailTrace_5499879
  have hstable : (prefixWord ++ tailWord_5499879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499879).length < 2 ^ (prefixWord ++ tailWord_5499879).sum := by decide
  have hdescent : baseEnd_5499879 < baseStart_5499879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499952 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 6]
def baseStart_5499952 : Nat := 118140960795 + 5499952 * 2 ^ 59
def prefixEnd_5499952 : Nat := 4983230072969 + 3 ^ 40 * 5499952 * 2
def baseEnd_5499952 : Nat := 313790994739685627356243

theorem tailTrace_5499952 : CollatzResearch.WordTrace tailWord_5499952 prefixEnd_5499952 313790994739685627356243 := by
  unfold tailWord_5499952
  simp only [CollatzResearch.WordTrace]
  refine ⟨100299864685310347931931055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133733152913747130575908073 100299864685310347931931055)
  ·
    refine ⟨150449797027965521897896583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100299864685310347931931055 150449797027965521897896583)
    ·
      refine ⟨225674695541948282846844875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150449797027965521897896583 225674695541948282846844875)
      ·
        refine ⟨338512043312922424270267313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225674695541948282846844875 338512043312922424270267313)
        ·
          refine ⟨253884032484691818202700485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338512043312922424270267313 253884032484691818202700485)
          ·
            refine ⟨47603256090879715913006341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253884032484691818202700485 47603256090879715913006341)
            ·
              refine ⟨8925610517039946733688689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47603256090879715913006341 8925610517039946733688689)
              ·
                refine ⟨6694207887779960050266517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8925610517039946733688689 6694207887779960050266517)
                ·
                  refine ⟨313790994739685627356243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6694207887779960050266517 313790994739685627356243)
                  ·
                    rfl

theorem cell23_5499952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 6].length) (baseStart_5499952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499952 prefixEnd_5499952 := by exact prefixLift 5499952
  have htrace : WordTrace (prefixWord ++ tailWord_5499952) baseStart_5499952 baseEnd_5499952 := by
    simpa [prefixWord, tailWord_5499952, baseEnd_5499952] using wordTrace_append hprefix tailTrace_5499952
  have hstable : (prefixWord ++ tailWord_5499952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499952).length < 2 ^ (prefixWord ++ tailWord_5499952).sum := by decide
  have hdescent : baseEnd_5499952 < baseStart_5499952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499955 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 6]
def baseStart_5499955 : Nat := 118140960795 + 5499955 * 2 ^ 59
def prefixEnd_5499955 : Nat := 4983230072969 + 3 ^ 40 * 5499955 * 2
def baseEnd_5499955 : Nat := 2824120493099134134468673

theorem tailTrace_5499955 : CollatzResearch.WordTrace tailWord_5499955 prefixEnd_5499955 2824120493099134134468673 := by
  unfold tailWord_5499955
  simp only [CollatzResearch.WordTrace]
  refine ⟨200599838789609827376221319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133733225859739884917480879 200599838789609827376221319)
  ·
    refine ⟨300899758184414741064331979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200599838789609827376221319 300899758184414741064331979)
    ·
      refine ⟨451349637276622111596497969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300899758184414741064331979 451349637276622111596497969)
      ·
        refine ⟨338512227957466583697373477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451349637276622111596497969 338512227957466583697373477)
        ·
          refine ⟨63471042742024984443257527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 338512227957466583697373477 63471042742024984443257527)
          ·
            refine ⟨95206564113037476664886291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63471042742024984443257527 95206564113037476664886291)
            ·
              refine ⟨142809846169556214997329437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95206564113037476664886291 142809846169556214997329437)
              ·
                refine ⟨53553692313583580623998539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142809846169556214997329437 53553692313583580623998539)
                ·
                  refine ⟨80330538470375370935997809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53553692313583580623998539 80330538470375370935997809)
                  ·
                    refine ⟨60247903852781528201998357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80330538470375370935997809 60247903852781528201998357)
                    ·
                      refine ⟨2824120493099134134468673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60247903852781528201998357 2824120493099134134468673)
                      ·
                        rfl

theorem cell23_5499955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_5499955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499955 prefixEnd_5499955 := by exact prefixLift 5499955
  have htrace : WordTrace (prefixWord ++ tailWord_5499955) baseStart_5499955 baseEnd_5499955 := by
    simpa [prefixWord, tailWord_5499955, baseEnd_5499955] using wordTrace_append hprefix tailTrace_5499955
  have hstable : (prefixWord ++ tailWord_5499955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499955).length < 2 ^ (prefixWord ++ tailWord_5499955).sum := by decide
  have hdescent : baseEnd_5499955 < baseStart_5499955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499982 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_5499982 : Nat := 118140960795 + 5499982 * 2 ^ 59
def prefixEnd_5499982 : Nat := 4983230072969 + 3 ^ 40 * 5499982 * 2
def baseEnd_5499982 : Nat := 941378119025601842943683

theorem tailTrace_5499982 : CollatzResearch.WordTrace tailWord_5499982 prefixEnd_5499982 941378119025601842943683 := by
  unfold tailWord_5499982
  simp only [CollatzResearch.WordTrace]
  refine ⟨25075102945064001373431775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133733882373674673991636133 25075102945064001373431775)
  ·
    refine ⟨37612654417596002060147663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25075102945064001373431775 37612654417596002060147663)
    ·
      refine ⟨56418981626394003090221495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37612654417596002060147663 56418981626394003090221495)
      ·
        refine ⟨84628472439591004635332243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56418981626394003090221495 84628472439591004635332243)
        ·
          refine ⟨126942708659386506952998365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84628472439591004635332243 126942708659386506952998365)
          ·
            refine ⟨47603515747269940107374387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126942708659386506952998365 47603515747269940107374387)
            ·
              refine ⟨71405273620904910161061581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47603515747269940107374387 71405273620904910161061581)
              ·
                refine ⟨26776977607839341310398093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71405273620904910161061581 26776977607839341310398093)
                ·
                  refine ⟨10041366602939752991399285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26776977607839341310398093 10041366602939752991399285)
                  ·
                    refine ⟨941378119025601842943683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10041366602939752991399285 941378119025601842943683)
                    ·
                      rfl

theorem cell23_5499982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_5499982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499982 prefixEnd_5499982 := by exact prefixLift 5499982
  have htrace : WordTrace (prefixWord ++ tailWord_5499982) baseStart_5499982 baseEnd_5499982 := by
    simpa [prefixWord, tailWord_5499982, baseEnd_5499982] using wordTrace_append hprefix tailTrace_5499982
  have hstable : (prefixWord ++ tailWord_5499982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499982).length < 2 ^ (prefixWord ++ tailWord_5499982).sum := by decide
  have hdescent : baseEnd_5499982 < baseStart_5499982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5499989 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 1, 5, 2]
def baseStart_5499989 : Nat := 118140960795 + 5499989 * 2 ^ 59
def prefixEnd_5499989 : Nat := 4983230072969 + 3 ^ 40 * 5499989 * 2
def baseEnd_5499989 : Nat := 2824137951441387001443517

theorem tailTrace_5499989 : CollatzResearch.WordTrace tailWord_5499989 prefixEnd_5499989 2824137951441387001443517 := by
  unfold tailWord_5499989
  simp only [CollatzResearch.WordTrace]
  refine ⟨200601078871486651182959021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133734052580991100788639347 200601078871486651182959021)
  ·
    refine ⟨75225404576807494193609633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200601078871486651182959021 75225404576807494193609633)
    ·
      refine ⟨56419053432605620645207225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75225404576807494193609633 56419053432605620645207225)
      ·
        refine ⟨42314290074454215483905419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56419053432605620645207225 42314290074454215483905419)
        ·
          refine ⟨63471435111681323225858129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42314290074454215483905419 63471435111681323225858129)
          ·
            refine ⟨47603576333760992419393597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63471435111681323225858129 47603576333760992419393597)
            ·
              refine ⟨17851341125160372157272599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47603576333760992419393597 17851341125160372157272599)
              ·
                refine ⟨26777011687740558235908899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17851341125160372157272599 26777011687740558235908899)
                ·
                  refine ⟨40165517531610837353863349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26777011687740558235908899 40165517531610837353863349)
                  ·
                    refine ⟨3765517268588516001924689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40165517531610837353863349 3765517268588516001924689)
                    ·
                      refine ⟨2824137951441387001443517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765517268588516001924689 2824137951441387001443517)
                      ·
                        rfl

theorem cell23_5499989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_5499989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5499989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5499989 prefixEnd_5499989 := by exact prefixLift 5499989
  have htrace : WordTrace (prefixWord ++ tailWord_5499989) baseStart_5499989 baseEnd_5499989 := by
    simpa [prefixWord, tailWord_5499989, baseEnd_5499989] using wordTrace_append hprefix tailTrace_5499989
  have hstable : (prefixWord ++ tailWord_5499989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5499989).length < 2 ^ (prefixWord ++ tailWord_5499989).sum := by decide
  have hdescent : baseEnd_5499989 < baseStart_5499989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5499989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500013 : List Nat := [1, 5, 1, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_5500013 : Nat := 118140960795 + 5500013 * 2 ^ 59
def prefixEnd_5500013 : Nat := 4983230072969 + 3 ^ 40 * 5500013 * 2
def baseEnd_5500013 : Nat := 2824150274977094907543407

theorem tailTrace_5500013 : CollatzResearch.WordTrace tailWord_5500013 prefixEnd_5500013 2824150274977094907543407 := by
  unfold tailWord_5500013
  simp only [CollatzResearch.WordTrace]
  refine ⟨200601954223399703281832693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133734636148933135521221795 200601954223399703281832693)
  ·
    refine ⟨18806433208443722182671815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200601954223399703281832693 18806433208443722182671815)
    ·
      refine ⟨28209649812665583274007723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18806433208443722182671815 28209649812665583274007723)
      ·
        refine ⟨42314474718998374911011585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28209649812665583274007723 42314474718998374911011585)
        ·
          refine ⟨31735856039248781183258689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42314474718998374911011585 31735856039248781183258689)
          ·
            refine ⟨23801892029436585887444017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31735856039248781183258689 23801892029436585887444017)
            ·
              refine ⟨17851419022077439415583013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23801892029436585887444017 17851419022077439415583013)
              ·
                refine ⟨3347141066639519890421815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17851419022077439415583013 3347141066639519890421815)
                ·
                  refine ⟨5020711599959279835632723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347141066639519890421815 5020711599959279835632723)
                  ·
                    refine ⟨7531067399938919753449085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5020711599959279835632723 7531067399938919753449085)
                    ·
                      refine ⟨2824150274977094907543407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7531067399938919753449085 2824150274977094907543407)
                      ·
                        rfl

theorem cell23_5500013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_5500013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500013 prefixEnd_5500013 := by exact prefixLift 5500013
  have htrace : WordTrace (prefixWord ++ tailWord_5500013) baseStart_5500013 baseEnd_5500013 := by
    simpa [prefixWord, tailWord_5500013, baseEnd_5500013] using wordTrace_append hprefix tailTrace_5500013
  have hstable : (prefixWord ++ tailWord_5500013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500013).length < 2 ^ (prefixWord ++ tailWord_5500013).sum := by decide
  have hdescent : baseEnd_5500013 < baseStart_5500013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500036 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_5500036 : Nat := 118140960795 + 5500036 * 2 ^ 59
def prefixEnd_5500036 : Nat := 4983230072969 + 3 ^ 40 * 5500036 * 2
def baseEnd_5500036 : Nat := 2824162085032148317555801

theorem tailTrace_5500036 : CollatzResearch.WordTrace tailWord_5500036 prefixEnd_5500036 2824162085032148317555801 := by
  unfold tailWord_5500036
  simp only [CollatzResearch.WordTrace]
  refine ⟨100301396551158189104959981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133735195401544252139946641 100301396551158189104959981)
  ·
    refine ⟨37613023706684320914359993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100301396551158189104959981 37613023706684320914359993)
    ·
      refine ⟨28209767780013240685769995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37613023706684320914359993 28209767780013240685769995)
      ·
        refine ⟨42314651670019861028654993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28209767780013240685769995 42314651670019861028654993)
        ·
          refine ⟨31735988752514895771491245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42314651670019861028654993 31735988752514895771491245)
          ·
            refine ⟨11900995782193085914309217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31735988752514895771491245 11900995782193085914309217)
            ·
              refine ⟨8925746836644814435731913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11900995782193085914309217 8925746836644814435731913)
              ·
                refine ⟨6694310127483610826798935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8925746836644814435731913 6694310127483610826798935)
                ·
                  refine ⟨10041465191225416240198403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6694310127483610826798935 10041465191225416240198403)
                  ·
                    refine ⟨15062197786838124360297605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10041465191225416240198403 15062197786838124360297605)
                    ·
                      refine ⟨2824162085032148317555801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15062197786838124360297605 2824162085032148317555801)
                      ·
                        rfl

theorem cell23_5500036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_5500036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500036 prefixEnd_5500036 := by exact prefixLift 5500036
  have htrace : WordTrace (prefixWord ++ tailWord_5500036) baseStart_5500036 baseEnd_5500036 := by
    simpa [prefixWord, tailWord_5500036, baseEnd_5500036] using wordTrace_append hprefix tailTrace_5500036
  have hstable : (prefixWord ++ tailWord_5500036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500036).length < 2 ^ (prefixWord ++ tailWord_5500036).sum := by decide
  have hdescent : baseEnd_5500036 < baseStart_5500036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500042 : List Nat := [3, 1, 2, 3, 1, 1, 3, 9]
def baseStart_5500042 : Nat := 118140960795 + 5500042 * 2 ^ 59
def prefixEnd_5500042 : Nat := 4983230072969 + 3 ^ 40 * 5500042 * 2
def baseEnd_5500042 : Nat := 104598709848743529410399

theorem tailTrace_5500042 : CollatzResearch.WordTrace tailWord_5500042 prefixEnd_5500042 104598709848743529410399 := by
  unfold tailWord_5500042
  simp only [CollatzResearch.WordTrace]
  refine ⟨50150752985073660308659595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133735341293529760823092253 50150752985073660308659595)
  ·
    refine ⟨75226129477610490462989393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50150752985073660308659595 75226129477610490462989393)
    ·
      refine ⟨56419597108207867847242045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75226129477610490462989393 56419597108207867847242045)
      ·
        refine ⟨21157348915577950442715767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56419597108207867847242045 21157348915577950442715767)
        ·
          refine ⟨31736023373366925664073651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21157348915577950442715767 31736023373366925664073651)
          ·
            refine ⟨47604035060050388496110477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31736023373366925664073651 47604035060050388496110477)
            ·
              refine ⟨17851513147518895686041429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47604035060050388496110477 17851513147518895686041429)
              ·
                refine ⟨104598709848743529410399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17851513147518895686041429 104598709848743529410399)
                ·
                  rfl

theorem cell23_5500042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 9].length) (baseStart_5500042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500042 prefixEnd_5500042 := by exact prefixLift 5500042
  have htrace : WordTrace (prefixWord ++ tailWord_5500042) baseStart_5500042 baseEnd_5500042 := by
    simpa [prefixWord, tailWord_5500042, baseEnd_5500042] using wordTrace_append hprefix tailTrace_5500042
  have hstable : (prefixWord ++ tailWord_5500042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500042).length < 2 ^ (prefixWord ++ tailWord_5500042).sum := by decide
  have hdescent : baseEnd_5500042 < baseStart_5500042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500053 : List Nat := [1, 3, 2, 1, 1, 1, 2, 7, 1, 2, 2]
def baseStart_5500053 : Nat := 118140960795 + 5500053 * 2 ^ 59
def prefixEnd_5500053 : Nat := 4983230072969 + 3 ^ 40 * 5500053 * 2
def baseEnd_5500053 : Nat := 2824170814203274751043223

theorem tailTrace_5500053 : CollatzResearch.WordTrace tailWord_5500053 prefixEnd_5500053 2824170814203274751043223 := by
  unfold tailWord_5500053
  simp only [CollatzResearch.WordTrace]
  refine ⟨200603413143254790113288813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133735608762169860075525875 200603413143254790113288813)
  ·
    refine ⟨75226279928720546292483305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200603413143254790113288813 75226279928720546292483305)
    ·
      refine ⟨56419709946540409719362479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75226279928720546292483305 56419709946540409719362479)
      ·
        refine ⟨84629564919810614579043719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56419709946540409719362479 84629564919810614579043719)
        ·
          refine ⟨126944347379715921868565579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84629564919810614579043719 126944347379715921868565579)
          ·
            refine ⟨190416521069573882802848369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126944347379715921868565579 190416521069573882802848369)
            ·
              refine ⟨142812390802180412102136277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190416521069573882802848369 142812390802180412102136277)
              ·
                refine ⟨3347165409426103408643819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 142812390802180412102136277 3347165409426103408643819)
                ·
                  refine ⟨5020748114139155112965729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347165409426103408643819 5020748114139155112965729)
                  ·
                    refine ⟨3765561085604366334724297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5020748114139155112965729 3765561085604366334724297)
                    ·
                      refine ⟨2824170814203274751043223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765561085604366334724297 2824170814203274751043223)
                      ·
                        rfl

theorem cell23_5500053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_5500053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500053 prefixEnd_5500053 := by exact prefixLift 5500053
  have htrace : WordTrace (prefixWord ++ tailWord_5500053) baseStart_5500053 baseEnd_5500053 := by
    simpa [prefixWord, tailWord_5500053, baseEnd_5500053] using wordTrace_append hprefix tailTrace_5500053
  have hstable : (prefixWord ++ tailWord_5500053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500053).length < 2 ^ (prefixWord ++ tailWord_5500053).sum := by decide
  have hdescent : baseEnd_5500053 < baseStart_5500053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500056 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 1, 2, 3]
def baseStart_5500056 : Nat := 118140960795 + 5500056 * 2 ^ 59
def prefixEnd_5500056 : Nat := 4983230072969 + 3 ^ 40 * 5500056 * 2
def baseEnd_5500056 : Nat := 2824172354645238239305709

theorem tailTrace_5500056 : CollatzResearch.WordTrace tailWord_5500056 prefixEnd_5500056 2824172354645238239305709 := by
  unfold tailWord_5500056
  simp only [CollatzResearch.WordTrace]
  refine ⟨100301761281121960812824011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133735681708162614417098681 100301761281121960812824011)
  ·
    refine ⟨150452641921682941219236017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100301761281121960812824011 150452641921682941219236017)
    ·
      refine ⟨112839481441262205914427013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150452641921682941219236017 112839481441262205914427013)
      ·
        refine ⟨21157402770236663608955065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112839481441262205914427013 21157402770236663608955065)
        ·
          refine ⟨15868052077677497706716299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21157402770236663608955065 15868052077677497706716299)
          ·
            refine ⟨23802078116516246560074449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15868052077677497706716299 23802078116516246560074449)
            ·
              refine ⟨17851558587387184920055837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23802078116516246560074449 17851558587387184920055837)
              ·
                refine ⟨6694334470270194345020939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17851558587387184920055837 6694334470270194345020939)
                ·
                  refine ⟨10041501705405291517531409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6694334470270194345020939 10041501705405291517531409)
                  ·
                    refine ⟨7531126279053968638148557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10041501705405291517531409 7531126279053968638148557)
                    ·
                      refine ⟨2824172354645238239305709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7531126279053968638148557 2824172354645238239305709)
                      ·
                        rfl

theorem cell23_5500056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_5500056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500056 prefixEnd_5500056 := by exact prefixLift 5500056
  have htrace : WordTrace (prefixWord ++ tailWord_5500056) baseStart_5500056 baseEnd_5500056 := by
    simpa [prefixWord, tailWord_5500056, baseEnd_5500056] using wordTrace_append hprefix tailTrace_5500056
  have hstable : (prefixWord ++ tailWord_5500056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500056).length < 2 ^ (prefixWord ++ tailWord_5500056).sum := by decide
  have hdescent : baseEnd_5500056 < baseStart_5500056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500122 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_5500122 : Nat := 118140960795 + 5500122 * 2 ^ 59
def prefixEnd_5500122 : Nat := 4983230072969 + 3 ^ 40 * 5500122 * 2
def baseEnd_5500122 : Nat := 2824206244368434981080405

theorem tailTrace_5500122 : CollatzResearch.WordTrace tailWord_5500122 prefixEnd_5500122 2824206244368434981080405 := by
  unfold tailWord_5500122
  simp only [CollatzResearch.WordTrace]
  refine ⟨50151482445001203724387655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133737286520003209931700413 50151482445001203724387655)
  ·
    refine ⟨75227223667501805586581483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50151482445001203724387655 75227223667501805586581483)
    ·
      refine ⟨112840835501252708379872225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75227223667501805586581483 112840835501252708379872225)
      ·
        refine ⟨84630626625939531284904169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112840835501252708379872225 84630626625939531284904169)
        ·
          refine ⟨63472969969454648463678127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84630626625939531284904169 63472969969454648463678127)
          ·
            refine ⟨95209454954181972695517191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63472969969454648463678127 95209454954181972695517191)
            ·
              refine ⟨142814182431272959043275787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95209454954181972695517191 142814182431272959043275787)
              ·
                refine ⟨214221273646909438564913681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142814182431272959043275787 214221273646909438564913681)
                ·
                  refine ⟨160665955235182078923685261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214221273646909438564913681 160665955235182078923685261)
                  ·
                    refine ⟨60249733213193279596381973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160665955235182078923685261 60249733213193279596381973)
                    ·
                      refine ⟨2824206244368434981080405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60249733213193279596381973 2824206244368434981080405)
                      ·
                        rfl

theorem cell23_5500122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_5500122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500122 prefixEnd_5500122 := by exact prefixLift 5500122
  have htrace : WordTrace (prefixWord ++ tailWord_5500122) baseStart_5500122 baseEnd_5500122 := by
    simpa [prefixWord, tailWord_5500122, baseEnd_5500122] using wordTrace_append hprefix tailTrace_5500122
  have hstable : (prefixWord ++ tailWord_5500122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500122).length < 2 ^ (prefixWord ++ tailWord_5500122).sum := by decide
  have hdescent : baseEnd_5500122 < baseStart_5500122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500129 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_5500129 : Nat := 118140960795 + 5500129 * 2 ^ 59
def prefixEnd_5500129 : Nat := 4983230072969 + 3 ^ 40 * 5500129 * 2
def baseEnd_5500129 : Nat := 2824209838733016453692873

theorem tailTrace_5500129 : CollatzResearch.WordTrace tailWord_5500129 prefixEnd_5500129 2824209838733016453692873 := by
  unfold tailWord_5500129
  simp only [CollatzResearch.WordTrace]
  refine ⟨200606185090979455093055441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133737456727319636728703627 200606185090979455093055441)
  ·
    refine ⟨150454638818234591319791581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200606185090979455093055441 150454638818234591319791581)
    ·
      refine ⟨56420489556837971744921843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150454638818234591319791581 56420489556837971744921843)
      ·
        refine ⟨84630734335256957617382765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56420489556837971744921843 84630734335256957617382765)
        ·
          refine ⟨31736525375721359106518537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84630734335256957617382765 31736525375721359106518537)
          ·
            refine ⟨23802394031791019329888903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31736525375721359106518537 23802394031791019329888903)
            ·
              refine ⟨35703591047686528994833355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23802394031791019329888903 35703591047686528994833355)
              ·
                refine ⟨53555386571529793492250033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35703591047686528994833355 53555386571529793492250033)
                ·
                  refine ⟨40166539928647345119187525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53555386571529793492250033 40166539928647345119187525)
                  ·
                    refine ⟨7531226236621377209847661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40166539928647345119187525 7531226236621377209847661)
                    ·
                      refine ⟨2824209838733016453692873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7531226236621377209847661 2824209838733016453692873)
                      ·
                        rfl

theorem cell23_5500129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_5500129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500129 prefixEnd_5500129 := by exact prefixLift 5500129
  have htrace : WordTrace (prefixWord ++ tailWord_5500129) baseStart_5500129 baseEnd_5500129 := by
    simpa [prefixWord, tailWord_5500129, baseEnd_5500129] using wordTrace_append hprefix tailTrace_5500129
  have hstable : (prefixWord ++ tailWord_5500129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500129).length < 2 ^ (prefixWord ++ tailWord_5500129).sum := by decide
  have hdescent : baseEnd_5500129 < baseStart_5500129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500139 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 4]
def baseStart_5500139 : Nat := 118140960795 + 5500139 * 2 ^ 59
def prefixEnd_5500139 : Nat := 4983230072969 + 3 ^ 40 * 5500139 * 2
def baseEnd_5500139 : Nat := 2824214973539561414567827

theorem tailTrace_5500139 : CollatzResearch.WordTrace tailWord_5500139 prefixEnd_5500139 2824214973539561414567827 := by
  unfold tailWord_5500139
  simp only [CollatzResearch.WordTrace]
  refine ⟨200606549820943226800919471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133737699880628817867279647 200606549820943226800919471)
  ·
    refine ⟨300909824731414840201379207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200606549820943226800919471 300909824731414840201379207)
    ·
      refine ⟨451364737097122260302068811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300909824731414840201379207 451364737097122260302068811)
      ·
        refine ⟨677047105645683390453103217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451364737097122260302068811 677047105645683390453103217)
        ·
          refine ⟨507785329234262542839827413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677047105645683390453103217 507785329234262542839827413)
          ·
            refine ⟨11901218653928028347808455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 507785329234262542839827413 11901218653928028347808455)
            ·
              refine ⟨17851827980892042521712683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11901218653928028347808455 17851827980892042521712683)
              ·
                refine ⟨26777741971338063782569025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17851827980892042521712683 26777741971338063782569025)
                ·
                  refine ⟨20083306478503547836926769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26777741971338063782569025 20083306478503547836926769)
                  ·
                    refine ⟨15062479858877660877695077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20083306478503547836926769 15062479858877660877695077)
                    ·
                      refine ⟨2824214973539561414567827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15062479858877660877695077 2824214973539561414567827)
                      ·
                        rfl

theorem cell23_5500139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 4].length) (baseStart_5500139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500139 prefixEnd_5500139 := by exact prefixLift 5500139
  have htrace : WordTrace (prefixWord ++ tailWord_5500139) baseStart_5500139 baseEnd_5500139 := by
    simpa [prefixWord, tailWord_5500139, baseEnd_5500139] using wordTrace_append hprefix tailTrace_5500139
  have hstable : (prefixWord ++ tailWord_5500139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500139).length < 2 ^ (prefixWord ++ tailWord_5500139).sum := by decide
  have hdescent : baseEnd_5500139 < baseStart_5500139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500143 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 1, 4, 2]
def baseStart_5500143 : Nat := 118140960795 + 5500143 * 2 ^ 59
def prefixEnd_5500143 : Nat := 4983230072969 + 3 ^ 40 * 5500143 * 2
def baseEnd_5500143 : Nat := 2824217027462179398917809

theorem tailTrace_5500143 : CollatzResearch.WordTrace tailWord_5500143 prefixEnd_5500143 2824217027462179398917809 := by
  unfold tailWord_5500143
  simp only [CollatzResearch.WordTrace]
  refine ⟨200606695712928735484065083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133737797141952490322710055 200606695712928735484065083)
  ·
    refine ⟨300910043569393103226097625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200606695712928735484065083 300910043569393103226097625)
    ·
      refine ⟨225682532677044827419573219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300910043569393103226097625 225682532677044827419573219)
      ·
        refine ⟨338523799015567241129359829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225682532677044827419573219 338523799015567241129359829)
        ·
          refine ⟨7934151539427357213969371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 338523799015567241129359829 7934151539427357213969371)
          ·
            refine ⟨11901227309141035820954057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7934151539427357213969371 11901227309141035820954057)
            ·
              refine ⟨8925920481855776865715543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11901227309141035820954057 8925920481855776865715543)
              ·
                refine ⟨13388880722783665298573315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8925920481855776865715543 13388880722783665298573315)
                ·
                  refine ⟨20083321084175497947859973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13388880722783665298573315 20083321084175497947859973)
                  ·
                    refine ⟨3765622703282905865223745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20083321084175497947859973 3765622703282905865223745)
                    ·
                      refine ⟨2824217027462179398917809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765622703282905865223745 2824217027462179398917809)
                      ·
                        rfl

theorem cell23_5500143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 4, 2].length) (baseStart_5500143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500143 prefixEnd_5500143 := by exact prefixLift 5500143
  have htrace : WordTrace (prefixWord ++ tailWord_5500143) baseStart_5500143 baseEnd_5500143 := by
    simpa [prefixWord, tailWord_5500143, baseEnd_5500143] using wordTrace_append hprefix tailTrace_5500143
  have hstable : (prefixWord ++ tailWord_5500143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500143).length < 2 ^ (prefixWord ++ tailWord_5500143).sum := by decide
  have hdescent : baseEnd_5500143 < baseStart_5500143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500236 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 4, 2, 3]
def baseStart_5500236 : Nat := 118140960795 + 5500236 * 2 ^ 59
def prefixEnd_5500236 : Nat := 4983230072969 + 3 ^ 40 * 5500236 * 2
def baseEnd_5500236 : Nat := 2824264781163047535054881

theorem tailTrace_5500236 : CollatzResearch.WordTrace tailWord_5500236 prefixEnd_5500236 2824264781163047535054881 := by
  unfold tailWord_5500236
  simp only [CollatzResearch.WordTrace]
  refine ⟨100305043850795906183600281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133740058467727874911467041 100305043850795906183600281)
  ·
    refine ⟨75228782888096929637700211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100305043850795906183600281 75228782888096929637700211)
    ·
      refine ⟨112843174332145394456550317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75228782888096929637700211 112843174332145394456550317)
      ·
        refine ⟨42316190374554522921206369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112843174332145394456550317 42316190374554522921206369)
        ·
          refine ⟨31737142780915892190904777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42316190374554522921206369 31737142780915892190904777)
          ·
            refine ⟨23802857085686919143178583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31737142780915892190904777 23802857085686919143178583)
            ·
              refine ⟨35704285628530378714767875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23802857085686919143178583 35704285628530378714767875)
              ·
                refine ⟨53556428442795568072151813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35704285628530378714767875 53556428442795568072151813)
                ·
                  refine ⟨10041830333024169013528465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53556428442795568072151813 10041830333024169013528465)
                  ·
                    refine ⟨7531372749768126760146349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10041830333024169013528465 7531372749768126760146349)
                    ·
                      refine ⟨2824264781163047535054881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7531372749768126760146349 2824264781163047535054881)
                      ·
                        rfl

theorem cell23_5500236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_5500236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500236 prefixEnd_5500236 := by exact prefixLift 5500236
  have htrace : WordTrace (prefixWord ++ tailWord_5500236) baseStart_5500236 baseEnd_5500236 := by
    simpa [prefixWord, tailWord_5500236, baseEnd_5500236] using wordTrace_append hprefix tailTrace_5500236
  have hstable : (prefixWord ++ tailWord_5500236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500236).length < 2 ^ (prefixWord ++ tailWord_5500236).sum := by decide
  have hdescent : baseEnd_5500236 < baseStart_5500236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500256 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 6]
def baseStart_5500256 : Nat := 118140960795 + 5500256 * 2 ^ 59
def prefixEnd_5500256 : Nat := 4983230072969 + 3 ^ 40 * 5500256 * 2
def baseEnd_5500256 : Nat := 313808338975126384089421

theorem tailTrace_5500256 : CollatzResearch.WordTrace tailWord_5500256 prefixEnd_5500256 313808338975126384089421 := by
  unfold tailWord_5500256
  simp only [CollatzResearch.WordTrace]
  refine ⟨100305408580759677891464311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133740544774346237188619081 100305408580759677891464311)
  ·
    refine ⟨150458112871139516837196467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100305408580759677891464311 150458112871139516837196467)
    ·
      refine ⟨225687169306709275255794701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150458112871139516837196467 225687169306709275255794701)
      ·
        refine ⟨84632688490015978220923013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225687169306709275255794701 84632688490015978220923013)
        ·
          refine ⟨15868629091877995916423065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84632688490015978220923013 15868629091877995916423065)
          ·
            refine ⟨11901471818908496937317299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15868629091877995916423065 11901471818908496937317299)
            ·
              refine ⟨17852207728362745405975949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11901471818908496937317299 17852207728362745405975949)
              ·
                refine ⟨6694577898136029527240981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17852207728362745405975949 6694577898136029527240981)
                ·
                  refine ⟨313808338975126384089421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6694577898136029527240981 313808338975126384089421)
                  ·
                    rfl

theorem cell23_5500256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 6].length) (baseStart_5500256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500256 prefixEnd_5500256 := by exact prefixLift 5500256
  have htrace : WordTrace (prefixWord ++ tailWord_5500256) baseStart_5500256 baseEnd_5500256 := by
    simpa [prefixWord, tailWord_5500256, baseEnd_5500256] using wordTrace_append hprefix tailTrace_5500256
  have hstable : (prefixWord ++ tailWord_5500256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500256).length < 2 ^ (prefixWord ++ tailWord_5500256).sum := by decide
  have hdescent : baseEnd_5500256 < baseStart_5500256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500290 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 6]
def baseStart_5500290 : Nat := 118140960795 + 5500290 * 2 ^ 59
def prefixEnd_5500290 : Nat := 4983230072969 + 3 ^ 40 * 5500290 * 2
def baseEnd_5500290 : Nat := 313810278790932258197737

theorem tailTrace_5500290 : CollatzResearch.WordTrace tailWord_5500290 prefixEnd_5500290 313810278790932258197737 := by
  unfold tailWord_5500290
  simp only [CollatzResearch.WordTrace]
  refine ⟨50153014310849044897416581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133741371495597453059777549 50153014310849044897416581)
  ·
    refine ⟨9403690183284195918265609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50153014310849044897416581 9403690183284195918265609)
    ·
      refine ⟨7052767637463146938699207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9403690183284195918265609 7052767637463146938699207)
      ·
        refine ⟨10579151456194720408048811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7052767637463146938699207 10579151456194720408048811)
        ·
          refine ⟨15868727184292080612073217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10579151456194720408048811 15868727184292080612073217)
          ·
            refine ⟨11901545388219060459054913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15868727184292080612073217 11901545388219060459054913)
            ·
              refine ⟨8926159041164295344291185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11901545388219060459054913 8926159041164295344291185)
              ·
                refine ⟨6694619280873221508218389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8926159041164295344291185 6694619280873221508218389)
                ·
                  refine ⟨313810278790932258197737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6694619280873221508218389 313810278790932258197737)
                  ·
                    rfl

theorem cell23_5500290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_5500290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500290 prefixEnd_5500290 := by exact prefixLift 5500290
  have htrace : WordTrace (prefixWord ++ tailWord_5500290) baseStart_5500290 baseEnd_5500290 := by
    simpa [prefixWord, tailWord_5500290, baseEnd_5500290] using wordTrace_append hprefix tailTrace_5500290
  have hstable : (prefixWord ++ tailWord_5500290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500290).length < 2 ^ (prefixWord ++ tailWord_5500290).sum := by decide
  have hdescent : baseEnd_5500290 < baseStart_5500290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500293 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 2, 3, 2]
def baseStart_5500293 : Nat := 118140960795 + 5500293 * 2 ^ 59
def prefixEnd_5500293 : Nat := 4983230072969 + 3 ^ 40 * 5500293 * 2
def baseEnd_5500293 : Nat := 2824294049560353812042119

theorem tailTrace_5500293 : CollatzResearch.WordTrace tailWord_5500293 prefixEnd_5500293 2824294049560353812042119 := by
  unfold tailWord_5500293
  simp only [CollatzResearch.WordTrace]
  refine ⟨200612166662385311102025533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133741444441590207401350355 200612166662385311102025533)
  ·
    refine ⟨75229562498394491663259575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200612166662385311102025533 75229562498394491663259575)
    ·
      refine ⟨112844343747591737494889363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75229562498394491663259575 112844343747591737494889363)
      ·
        refine ⟨169266515621387606242334045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112844343747591737494889363 169266515621387606242334045)
        ·
          refine ⟨63474943358020352340875267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169266515621387606242334045 63474943358020352340875267)
          ·
            refine ⟨95212415037030528511312901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63474943358020352340875267 95212415037030528511312901)
            ·
              refine ⟨17852327819443224095871169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95212415037030528511312901 17852327819443224095871169)
              ·
                refine ⟨13389245864582418071903377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17852327819443224095871169 13389245864582418071903377)
                ·
                  refine ⟨10041934398436813553927533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13389245864582418071903377 10041934398436813553927533)
                  ·
                    refine ⟨3765725399413805082722825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10041934398436813553927533 3765725399413805082722825)
                    ·
                      refine ⟨2824294049560353812042119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765725399413805082722825 2824294049560353812042119)
                      ·
                        rfl

theorem cell23_5500293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 3, 2].length) (baseStart_5500293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500293 prefixEnd_5500293 := by exact prefixLift 5500293
  have htrace : WordTrace (prefixWord ++ tailWord_5500293) baseStart_5500293 baseEnd_5500293 := by
    simpa [prefixWord, tailWord_5500293, baseEnd_5500293] using wordTrace_append hprefix tailTrace_5500293
  have hstable : (prefixWord ++ tailWord_5500293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500293).length < 2 ^ (prefixWord ++ tailWord_5500293).sum := by decide
  have hdescent : baseEnd_5500293 < baseStart_5500293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500299 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 3, 6]
def baseStart_5500299 : Nat := 118140960795 + 5500299 * 2 ^ 59
def prefixEnd_5500299 : Nat := 4983230072969 + 3 ^ 40 * 5500299 * 2
def baseEnd_5500299 : Nat := 941432376814760262855697

theorem tailTrace_5500299 : CollatzResearch.WordTrace tailWord_5500299 prefixEnd_5500299 941432376814760262855697 := by
  unfold tailWord_5500299
  simp only [CollatzResearch.WordTrace]
  refine ⟨200612385500363574126743951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133741590333575716084495967 200612385500363574126743951)
  ·
    refine ⟨300918578250545361190115927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200612385500363574126743951 300918578250545361190115927)
    ·
      refine ⟨451377867375818041785173891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300918578250545361190115927 451377867375818041785173891)
      ·
        refine ⟨677066801063727062677760837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451377867375818041785173891 677066801063727062677760837)
        ·
          refine ⟨126950025199448824252080157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 677066801063727062677760837 126950025199448824252080157)
          ·
            refine ⟨47606259449793309094530059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126950025199448824252080157 47606259449793309094530059)
            ·
              refine ⟨71409389174689963641795089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47606259449793309094530059 71409389174689963641795089)
              ·
                refine ⟨53557041881017472731346317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71409389174689963641795089 53557041881017472731346317)
                ·
                  refine ⟨20083890705381552274254869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53557041881017472731346317 20083890705381552274254869)
                  ·
                    refine ⟨941432376814760262855697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20083890705381552274254869 941432376814760262855697)
                    ·
                      rfl

theorem cell23_5500299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 6].length) (baseStart_5500299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500299 prefixEnd_5500299 := by exact prefixLift 5500299
  have htrace : WordTrace (prefixWord ++ tailWord_5500299) baseStart_5500299 baseEnd_5500299 := by
    simpa [prefixWord, tailWord_5500299, baseEnd_5500299] using wordTrace_append hprefix tailTrace_5500299
  have hstable : (prefixWord ++ tailWord_5500299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500299).length < 2 ^ (prefixWord ++ tailWord_5500299).sum := by decide
  have hdescent : baseEnd_5500299 < baseStart_5500299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500300 : List Nat := [2, 2, 1, 2, 1, 3, 3, 4, 1, 1, 3]
def baseStart_5500300 : Nat := 118140960795 + 5500300 * 2 ^ 59
def prefixEnd_5500300 : Nat := 4983230072969 + 3 ^ 40 * 5500300 * 2
def baseEnd_5500300 : Nat := 2824297643924935284654587

theorem tailTrace_5500300 : CollatzResearch.WordTrace tailWord_5500300 prefixEnd_5500300 2824297643924935284654587 := by
  unfold tailWord_5500300
  simp only [CollatzResearch.WordTrace]
  refine ⟨100306210986679975648765177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133741614648906634198353569 100306210986679975648765177)
  ·
    refine ⟨75229658240009981736573883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100306210986679975648765177 75229658240009981736573883)
    ·
      refine ⟨112844487360014972604860825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75229658240009981736573883 112844487360014972604860825)
      ·
        refine ⟨84633365520011229453645619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112844487360014972604860825 84633365520011229453645619)
        ·
          refine ⟨126950048280016844180468429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84633365520011229453645619 126950048280016844180468429)
          ·
            refine ⟨47606268105006316567675661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126950048280016844180468429 47606268105006316567675661)
            ·
              refine ⟨17852350539377368712878373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47606268105006316567675661 17852350539377368712878373)
              ·
                refine ⟨3347315726133256633664695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17852350539377368712878373 3347315726133256633664695)
                ·
                  refine ⟨5020973589199884950497043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347315726133256633664695 5020973589199884950497043)
                  ·
                    refine ⟨7531460383799827425745565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5020973589199884950497043 7531460383799827425745565)
                    ·
                      refine ⟨2824297643924935284654587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7531460383799827425745565 2824297643924935284654587)
                      ·
                        rfl

theorem cell23_5500300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_5500300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500300 prefixEnd_5500300 := by exact prefixLift 5500300
  have htrace : WordTrace (prefixWord ++ tailWord_5500300) baseStart_5500300 baseEnd_5500300 := by
    simpa [prefixWord, tailWord_5500300, baseEnd_5500300] using wordTrace_append hprefix tailTrace_5500300
  have hstable : (prefixWord ++ tailWord_5500300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500300).length < 2 ^ (prefixWord ++ tailWord_5500300).sum := by decide
  have hdescent : baseEnd_5500300 < baseStart_5500300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500333 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_5500333 : Nat := 118140960795 + 5500333 * 2 ^ 59
def prefixEnd_5500333 : Nat := 4983230072969 + 3 ^ 40 * 5500333 * 2
def baseEnd_5500333 : Nat := 941438196262177885180645

theorem tailTrace_5500333 : CollatzResearch.WordTrace tailWord_5500333 prefixEnd_5500333 941438196262177885180645 := by
  unfold tailWord_5500333
  simp only [CollatzResearch.WordTrace]
  refine ⟨200613625582240397933481653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133742417054826931955654435 200613625582240397933481653)
  ·
    refine ⟨18807527398335037306263905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200613625582240397933481653 18807527398335037306263905)
    ·
      refine ⟨14105645548751277979697929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18807527398335037306263905 14105645548751277979697929)
      ·
        refine ⟨10579234161563458484773447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14105645548751277979697929 10579234161563458484773447)
        ·
          refine ⟨15868851242345187727160171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10579234161563458484773447 15868851242345187727160171)
          ·
            refine ⟨23803276863517781590740257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15868851242345187727160171 23803276863517781590740257)
            ·
              refine ⟨17852457647638336193055193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23803276863517781590740257 17852457647638336193055193)
              ·
                refine ⟨13389343235728752144791395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17852457647638336193055193 13389343235728752144791395)
                ·
                  refine ⟨20084014853593128217187093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13389343235728752144791395 20084014853593128217187093)
                  ·
                    refine ⟨941438196262177885180645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20084014853593128217187093 941438196262177885180645)
                    ·
                      rfl

theorem cell23_5500333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_5500333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500333 prefixEnd_5500333 := by exact prefixLift 5500333
  have htrace : WordTrace (prefixWord ++ tailWord_5500333) baseStart_5500333 baseEnd_5500333 := by
    simpa [prefixWord, tailWord_5500333, baseEnd_5500333] using wordTrace_append hprefix tailTrace_5500333
  have hstable : (prefixWord ++ tailWord_5500333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500333).length < 2 ^ (prefixWord ++ tailWord_5500333).sum := by decide
  have hdescent : baseEnd_5500333 < baseStart_5500333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500343 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 3]
def baseStart_5500343 : Nat := 118140960795 + 5500343 * 2 ^ 59
def prefixEnd_5500343 : Nat := 4983230072969 + 3 ^ 40 * 5500343 * 2
def baseEnd_5500343 : Nat := 2824319723593078616416889

theorem tailTrace_5500343 : CollatzResearch.WordTrace tailWord_5500343 prefixEnd_5500343 2824319723593078616416889 := by
  unfold tailWord_5500343
  simp only [CollatzResearch.WordTrace]
  refine ⟨200613990312204169641345683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133742660208136113094230455 200613990312204169641345683)
  ·
    refine ⟨300920985468306254462018525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200613990312204169641345683 300920985468306254462018525)
    ·
      refine ⟨112845369550614845423256947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300920985468306254462018525 112845369550614845423256947)
      ·
        refine ⟨169268054325922268134885421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112845369550614845423256947 169268054325922268134885421)
        ·
          refine ⟨63475520372220850550582033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169268054325922268134885421 63475520372220850550582033)
          ·
            refine ⟨47606640279165637912936525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63475520372220850550582033 47606640279165637912936525)
            ·
              refine ⟨17852490104687114217351197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47606640279165637912936525 17852490104687114217351197)
              ·
                refine ⟨6694683789257667831506699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17852490104687114217351197 6694683789257667831506699)
                ·
                  refine ⟨10042025683886501747260049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6694683789257667831506699 10042025683886501747260049)
                  ·
                    refine ⟨7531519262914876310445037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10042025683886501747260049 7531519262914876310445037)
                    ·
                      refine ⟨2824319723593078616416889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7531519262914876310445037 2824319723593078616416889)
                      ·
                        rfl

theorem cell23_5500343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_5500343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500343 prefixEnd_5500343 := by exact prefixLift 5500343
  have htrace : WordTrace (prefixWord ++ tailWord_5500343) baseStart_5500343 baseEnd_5500343 := by
    simpa [prefixWord, tailWord_5500343, baseEnd_5500343] using wordTrace_append hprefix tailTrace_5500343
  have hstable : (prefixWord ++ tailWord_5500343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500343).length < 2 ^ (prefixWord ++ tailWord_5500343).sum := by decide
  have hdescent : baseEnd_5500343 < baseStart_5500343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500400 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 1, 3, 2]
def baseStart_5500400 : Nat := 118140960795 + 5500400 * 2 ^ 59
def prefixEnd_5500400 : Nat := 4983230072969 + 3 ^ 40 * 5500400 * 2
def baseEnd_5500400 : Nat := 2824348991990384893404127

theorem tailTrace_5500400 : CollatzResearch.WordTrace tailWord_5500400 prefixEnd_5500400 2824348991990384893404127 := by
  unfold tailWord_5500400
  simp only [CollatzResearch.WordTrace]
  refine ⟨100308034636498834188085327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133744046181998445584113769 100308034636498834188085327)
  ·
    refine ⟨150462051954748251282127991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100308034636498834188085327 150462051954748251282127991)
    ·
      refine ⟨225693077932122376923191987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150462051954748251282127991 225693077932122376923191987)
      ·
        refine ⟨338539616898183565384787981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225693077932122376923191987 338539616898183565384787981)
        ·
          refine ⟨126952356336818837019295493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338539616898183565384787981 126952356336818837019295493)
          ·
            refine ⟨23803566813153531941117905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126952356336818837019295493 23803566813153531941117905)
            ·
              refine ⟨17852675109865148955838429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23803566813153531941117905 17852675109865148955838429)
              ·
                refine ⟨6694753166199430858439411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17852675109865148955838429 6694753166199430858439411)
                ·
                  refine ⟨10042129749299146287659117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6694753166199430858439411 10042129749299146287659117)
                  ·
                    refine ⟨3765798655987179857872169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10042129749299146287659117 3765798655987179857872169)
                    ·
                      refine ⟨2824348991990384893404127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3765798655987179857872169 2824348991990384893404127)
                      ·
                        rfl

theorem cell23_5500400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 3, 2].length) (baseStart_5500400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500400 prefixEnd_5500400 := by exact prefixLift 5500400
  have htrace : WordTrace (prefixWord ++ tailWord_5500400) baseStart_5500400 baseEnd_5500400 := by
    simpa [prefixWord, tailWord_5500400, baseEnd_5500400] using wordTrace_append hprefix tailTrace_5500400
  have hstable : (prefixWord ++ tailWord_5500400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500400).length < 2 ^ (prefixWord ++ tailWord_5500400).sum := by decide
  have hdescent : baseEnd_5500400 < baseStart_5500400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500453 : List Nat := [1, 3, 1, 2, 2, 1, 1, 7, 5]
def baseStart_5500453 : Nat := 118140960795 + 5500453 * 2 ^ 59
def prefixEnd_5500453 : Nat := 4983230072969 + 3 ^ 40 * 5500453 * 2
def baseEnd_5500453 : Nat := 313819578496119242893487

theorem tailTrace_5500453 : CollatzResearch.WordTrace tailWord_5500453 prefixEnd_5500453 313819578496119242893487 := by
  unfold tailWord_5500453
  simp only [CollatzResearch.WordTrace]
  refine ⟨200618002341805658427850013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133745334894537105618566675 200618002341805658427850013)
  ·
    refine ⟨75231750878177121910443755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200618002341805658427850013 75231750878177121910443755)
    ·
      refine ⟨112847626317265682865665633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75231750878177121910443755 112847626317265682865665633)
      ·
        refine ⟨84635719737949262149249225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112847626317265682865665633 84635719737949262149249225)
        ·
          refine ⟨63476789803461946611936919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84635719737949262149249225 63476789803461946611936919)
          ·
            refine ⟨95215184705192919917905379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63476789803461946611936919 95215184705192919917905379)
            ·
              refine ⟨142822777057789379876858069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95215184705192919917905379 142822777057789379876858069)
              ·
                refine ⟨3347408837291938590863861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 142822777057789379876858069 3347408837291938590863861)
                ·
                  refine ⟨313819578496119242893487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3347408837291938590863861 313819578496119242893487)
                  ·
                    rfl

theorem cell23_5500453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_5500453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500453 prefixEnd_5500453 := by exact prefixLift 5500453
  have htrace : WordTrace (prefixWord ++ tailWord_5500453) baseStart_5500453 baseEnd_5500453 := by
    simpa [prefixWord, tailWord_5500453, baseEnd_5500453] using wordTrace_append hprefix tailTrace_5500453
  have hstable : (prefixWord ++ tailWord_5500453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500453).length < 2 ^ (prefixWord ++ tailWord_5500453).sum := by decide
  have hdescent : baseEnd_5500453 < baseStart_5500453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500466 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_5500466 : Nat := 118140960795 + 5500466 * 2 ^ 59
def prefixEnd_5500466 : Nat := 4983230072969 + 3 ^ 40 * 5500466 * 2
def baseEnd_5500466 : Nat := 941460960571193878392941

theorem tailTrace_5500466 : CollatzResearch.WordTrace tailWord_5500466 prefixEnd_5500466 941460960571193878392941 := by
  unfold tailWord_5500466
  simp only [CollatzResearch.WordTrace]
  refine ⟨50154619122689640412018313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133745650993839041098715501 50154619122689640412018313)
  ·
    refine ⟨37615964342017230309013735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50154619122689640412018313 37615964342017230309013735)
    ·
      refine ⟨56423946513025845463520603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37615964342017230309013735 56423946513025845463520603)
      ·
        refine ⟨84635919769538768195280905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56423946513025845463520603 84635919769538768195280905)
        ·
          refine ⟨63476939827154076146460679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84635919769538768195280905 63476939827154076146460679)
          ·
            refine ⟨95215409740731114219691019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63476939827154076146460679 95215409740731114219691019)
            ·
              refine ⟨142823114611096671329536529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95215409740731114219691019 142823114611096671329536529)
              ·
                refine ⟨107117335958322503497152397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142823114611096671329536529 107117335958322503497152397)
                ·
                  refine ⟨40169000984370938811432149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107117335958322503497152397 40169000984370938811432149)
                  ·
                    refine ⟨941460960571193878392941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40169000984370938811432149 941460960571193878392941)
                    ·
                      rfl

theorem cell23_5500466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_5500466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500466 prefixEnd_5500466 := by exact prefixLift 5500466
  have htrace : WordTrace (prefixWord ++ tailWord_5500466) baseStart_5500466 baseEnd_5500466 := by
    simpa [prefixWord, tailWord_5500466, baseEnd_5500466] using wordTrace_append hprefix tailTrace_5500466
  have hstable : (prefixWord ++ tailWord_5500466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500466).length < 2 ^ (prefixWord ++ tailWord_5500466).sum := by decide
  have hdescent : baseEnd_5500466 < baseStart_5500466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500503 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_5500503 : Nat := 118140960795 + 5500503 * 2 ^ 59
def prefixEnd_5500503 : Nat := 4983230072969 + 3 ^ 40 * 5500503 * 2
def baseEnd_5500503 : Nat := 2824401880497797990416153

theorem tailTrace_5500503 : CollatzResearch.WordTrace tailWord_5500503 prefixEnd_5500503 2824401880497797990416153 := by
  unfold tailWord_5500503
  simp only [CollatzResearch.WordTrace]
  refine ⟨200619825991624516967170163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133746550661083011311446775 200619825991624516967170163)
  ·
    refine ⟨300929738987436775450755245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200619825991624516967170163 300929738987436775450755245)
    ·
      refine ⟨112848652120288790794033217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300929738987436775450755245 112848652120288790794033217)
      ·
        refine ⟨84636489090216593095524913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112848652120288790794033217 84636489090216593095524913)
        ·
          refine ⟨63477366817662444821643685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84636489090216593095524913 63477366817662444821643685)
          ·
            refine ⟨11902006278311708404058191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63477366817662444821643685 11902006278311708404058191)
            ·
              refine ⟨17853009417467562606087287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11902006278311708404058191 17853009417467562606087287)
              ·
                refine ⟨26779514126201343909130931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17853009417467562606087287 26779514126201343909130931)
                ·
                  refine ⟨40169271189302015863696397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26779514126201343909130931 40169271189302015863696397)
                  ·
                    refine ⟨15063476695988255948886149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40169271189302015863696397 15063476695988255948886149)
                    ·
                      refine ⟨2824401880497797990416153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15063476695988255948886149 2824401880497797990416153)
                      ·
                        rfl

theorem cell23_5500503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_5500503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500503 prefixEnd_5500503 := by exact prefixLift 5500503
  have htrace : WordTrace (prefixWord ++ tailWord_5500503) baseStart_5500503 baseEnd_5500503 := by
    simpa [prefixWord, tailWord_5500503, baseEnd_5500503] using wordTrace_append hprefix tailTrace_5500503
  have hstable : (prefixWord ++ tailWord_5500503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500503).length < 2 ^ (prefixWord ++ tailWord_5500503).sum := by decide
  have hdescent : baseEnd_5500503 < baseStart_5500503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500513 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 5, 4]
def baseStart_5500513 : Nat := 118140960795 + 5500513 * 2 ^ 59
def prefixEnd_5500513 : Nat := 4983230072969 + 3 ^ 40 * 5500513 * 2
def baseEnd_5500513 : Nat := 941469005101447650430369

theorem tailTrace_5500513 : CollatzResearch.WordTrace tailWord_5500513 prefixEnd_5500513 941469005101447650430369 := by
  unfold tailWord_5500513
  simp only [CollatzResearch.WordTrace]
  refine ⟨200620190721588288675034193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133746793814392192450022795 200620190721588288675034193)
  ·
    refine ⟨150465143041191216506275645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200620190721588288675034193 150465143041191216506275645)
    ·
      refine ⟨56424428640446706189853367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150465143041191216506275645 56424428640446706189853367)
      ·
        refine ⟨84636642960670059284780051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56424428640446706189853367 84636642960670059284780051)
        ·
          refine ⟨126954964441005088927170077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84636642960670059284780051 126954964441005088927170077)
          ·
            refine ⟨47608111665376908347688779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126954964441005088927170077 47608111665376908347688779)
            ·
              refine ⟨71412167498065362521533169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47608111665376908347688779 71412167498065362521533169)
              ·
                refine ⟨53559125623549021891149877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71412167498065362521533169 53559125623549021891149877)
                ·
                  refine ⟨5021168027207720802295301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53559125623549021891149877 5021168027207720802295301)
                  ·
                    refine ⟨941469005101447650430369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5021168027207720802295301 941469005101447650430369)
                    ·
                      rfl

theorem cell23_5500513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_5500513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500513 prefixEnd_5500513 := by exact prefixLift 5500513
  have htrace : WordTrace (prefixWord ++ tailWord_5500513) baseStart_5500513 baseEnd_5500513 := by
    simpa [prefixWord, tailWord_5500513, baseEnd_5500513] using wordTrace_append hprefix tailTrace_5500513
  have hstable : (prefixWord ++ tailWord_5500513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500513).length < 2 ^ (prefixWord ++ tailWord_5500513).sum := by decide
  have hdescent : baseEnd_5500513 < baseStart_5500513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500530 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_5500530 : Nat := 118140960795 + 5500530 * 2 ^ 59
def prefixEnd_5500530 : Nat := 4983230072969 + 3 ^ 40 * 5500530 * 2
def baseEnd_5500530 : Nat := 941471914825156461592843

theorem tailTrace_5500530 : CollatzResearch.WordTrace tailWord_5500530 prefixEnd_5500530 941471914825156461592843 := by
  unfold tailWord_5500530
  simp only [CollatzResearch.WordTrace]
  refine ⟨50155202690631675144600761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133747207175017800385602029 50155202690631675144600761)
  ·
    refine ⟨37616402017973756358450571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50155202690631675144600761 37616402017973756358450571)
    ·
      refine ⟨56424603026960634537675857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37616402017973756358450571 56424603026960634537675857)
      ·
        refine ⟨42318452270220475903256893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56424603026960634537675857 42318452270220475903256893)
        ·
          refine ⟨15869419601332678463721335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42318452270220475903256893 15869419601332678463721335)
          ·
            refine ⟨23804129401999017695582003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15869419601332678463721335 23804129401999017695582003)
            ·
              refine ⟨35706194102998526543373005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23804129401999017695582003 35706194102998526543373005)
              ·
                refine ⟨13389822788624447453764877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35706194102998526543373005 13389822788624447453764877)
                ·
                  refine ⟨5021183545734167795161829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13389822788624447453764877 5021183545734167795161829)
                  ·
                    refine ⟨941471914825156461592843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5021183545734167795161829 941471914825156461592843)
                    ·
                      rfl

theorem cell23_5500530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_5500530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500530 prefixEnd_5500530 := by exact prefixLift 5500530
  have htrace : WordTrace (prefixWord ++ tailWord_5500530) baseStart_5500530 baseEnd_5500530 := by
    simpa [prefixWord, tailWord_5500530, baseEnd_5500530] using wordTrace_append hprefix tailTrace_5500530
  have hstable : (prefixWord ++ tailWord_5500530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500530).length < 2 ^ (prefixWord ++ tailWord_5500530).sum := by decide
  have hdescent : baseEnd_5500530 < baseStart_5500530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500573 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_5500573 : Nat := 118140960795 + 5500573 * 2 ^ 59
def prefixEnd_5500573 : Nat := 4983230072969 + 3 ^ 40 * 5500573 * 2
def baseEnd_5500573 : Nat := 941479274714537572180277

theorem tailTrace_5500573 : CollatzResearch.WordTrace tailWord_5500573 prefixEnd_5500573 941479274714537572180277 := by
  unfold tailWord_5500573
  simp only [CollatzResearch.WordTrace]
  refine ⟨200622379101370918922218373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133748252734247279281478915 200622379101370918922218373)
  ·
    refine ⟨37616696081507047297915945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200622379101370918922218373 37616696081507047297915945)
    ·
      refine ⟨28212522061130285473436959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37616696081507047297915945 28212522061130285473436959)
      ·
        refine ⟨42318783091695428210155439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28212522061130285473436959 42318783091695428210155439)
        ·
          refine ⟨63478174637543142315233159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42318783091695428210155439 63478174637543142315233159)
          ·
            refine ⟨95217261956314713472849739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63478174637543142315233159 95217261956314713472849739)
            ·
              refine ⟨142825892934472070209274609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95217261956314713472849739 142825892934472070209274609)
              ·
                refine ⟨107119419700854052656955957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142825892934472070209274609 107119419700854052656955957)
                ·
                  refine ⟨10042445596955067436589621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107119419700854052656955957 10042445596955067436589621)
                  ·
                    refine ⟨941479274714537572180277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10042445596955067436589621 941479274714537572180277)
                    ·
                      rfl

theorem cell23_5500573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_5500573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500573 prefixEnd_5500573 := by exact prefixLift 5500573
  have htrace : WordTrace (prefixWord ++ tailWord_5500573) baseStart_5500573 baseEnd_5500573 := by
    simpa [prefixWord, tailWord_5500573, baseEnd_5500573] using wordTrace_append hprefix tailTrace_5500573
  have hstable : (prefixWord ++ tailWord_5500573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500573).length < 2 ^ (prefixWord ++ tailWord_5500573).sum := by decide
  have hdescent : baseEnd_5500573 < baseStart_5500573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500613 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 2, 6, 3]
def baseStart_5500613 : Nat := 118140960795 + 5500613 * 2 ^ 59
def prefixEnd_5500613 : Nat := 4983230072969 + 3 ^ 40 * 5500613 * 2
def baseEnd_5500613 : Nat := 2824458363369792560040647

theorem tailTrace_5500613 : CollatzResearch.WordTrace tailWord_5500613 prefixEnd_5500613 2824458363369792560040647 := by
  unfold tailWord_5500613
  simp only [CollatzResearch.WordTrace]
  refine ⟨200623838021226005753674493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133749225347484003835782995 200623838021226005753674493)
  ·
    refine ⟨75233939257959752157627935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200623838021226005753674493 75233939257959752157627935)
    ·
      refine ⟨112850908886939628236441903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75233939257959752157627935 112850908886939628236441903)
      ·
        refine ⟨169276363330409442354662855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112850908886939628236441903 169276363330409442354662855)
        ·
          refine ⟨253914544995614163531994283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169276363330409442354662855 253914544995614163531994283)
          ·
            refine ⟨380871817493421245297991425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253914544995614163531994283 380871817493421245297991425)
            ·
              refine ⟨285653863120065933973493569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380871817493421245297991425 285653863120065933973493569)
              ·
                refine ⟨214240397340049450480120177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285653863120065933973493569 214240397340049450480120177)
                ·
                  refine ⟨160680298005037087860090133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214240397340049450480120177 160680298005037087860090133)
                  ·
                    refine ⟨7531888968986113493441725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 160680298005037087860090133 7531888968986113493441725)
                    ·
                      refine ⟨2824458363369792560040647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7531888968986113493441725 2824458363369792560040647)
                      ·
                        rfl

theorem cell23_5500613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_5500613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500613 prefixEnd_5500613 := by exact prefixLift 5500613
  have htrace : WordTrace (prefixWord ++ tailWord_5500613) baseStart_5500613 baseEnd_5500613 := by
    simpa [prefixWord, tailWord_5500613, baseEnd_5500613] using wordTrace_append hprefix tailTrace_5500613
  have hstable : (prefixWord ++ tailWord_5500613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500613).length < 2 ^ (prefixWord ++ tailWord_5500613).sum := by decide
  have hdescent : baseEnd_5500613 < baseStart_5500613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500757 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 7]
def baseStart_5500757 : Nat := 118140960795 + 5500757 * 2 ^ 59
def prefixEnd_5500757 : Nat := 4983230072969 + 3 ^ 40 * 5500757 * 2
def baseEnd_5500757 : Nat := 313836922731559999626665

theorem tailTrace_5500757 : CollatzResearch.WordTrace tailWord_5500757 prefixEnd_5500757 313836922731559999626665 := by
  unfold tailWord_5500757
  simp only [CollatzResearch.WordTrace]
  refine ⟨200629090132704318346916525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133752726755136212231277683 200629090132704318346916525)
  ·
    refine ⟨75235908799764119380093697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200629090132704318346916525 75235908799764119380093697)
    ·
      refine ⟨56426931599823089535070273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75235908799764119380093697 56426931599823089535070273)
      ·
        refine ⟨42320198699867317151302705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56426931599823089535070273 42320198699867317151302705)
        ·
          refine ⟨31740149024900487863477029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42320198699867317151302705 31740149024900487863477029)
          ·
            refine ⟨5951277942168841474401943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31740149024900487863477029 5951277942168841474401943)
            ·
              refine ⟨8926916913253262211602915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5951277942168841474401943 8926916913253262211602915)
              ·
                refine ⟨13390375369879893317404373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8926916913253262211602915 13390375369879893317404373)
                ·
                  refine ⟨313836922731559999626665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13390375369879893317404373 313836922731559999626665)
                  ·
                    rfl

theorem cell23_5500757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_5500757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500757 prefixEnd_5500757 := by exact prefixLift 5500757
  have htrace : WordTrace (prefixWord ++ tailWord_5500757) baseStart_5500757 baseEnd_5500757 := by
    simpa [prefixWord, tailWord_5500757, baseEnd_5500757] using wordTrace_append hprefix tailTrace_5500757
  have hstable : (prefixWord ++ tailWord_5500757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500757).length < 2 ^ (prefixWord ++ tailWord_5500757).sum := by decide
  have hdescent : baseEnd_5500757 < baseStart_5500757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500768 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 2, 2, 2]
def baseStart_5500768 : Nat := 118140960795 + 5500768 * 2 ^ 59
def prefixEnd_5500768 : Nat := 4983230072969 + 3 ^ 40 * 5500768 * 2
def baseEnd_5500768 : Nat := 2824537952871239453602435

theorem tailTrace_5500768 : CollatzResearch.WordTrace tailWord_5500768 prefixEnd_5500768 2824537952871239453602435 := by
  unfold tailWord_5500768
  simp only [CollatzResearch.WordTrace]
  refine ⟨100314745667832233612783479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133752994223776311483711305 100314745667832233612783479)
  ·
    refine ⟨150472118501748350419175219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100314745667832233612783479 150472118501748350419175219)
    ·
      refine ⟨225708177752622525628762829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150472118501748350419175219 225708177752622525628762829)
      ·
        refine ⟨84640566657233447110786061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225708177752622525628762829 84640566657233447110786061)
        ·
          refine ⟨31740212496462542666544773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84640566657233447110786061 31740212496462542666544773)
          ·
            refine ⟨5951289843086726749977145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31740212496462542666544773 5951289843086726749977145)
            ·
              refine ⟨4463467382315045062482859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5951289843086726749977145 4463467382315045062482859)
              ·
                refine ⟨6695201073472567593724289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4463467382315045062482859 6695201073472567593724289)
                ·
                  refine ⟨5021400805104425695293217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6695201073472567593724289 5021400805104425695293217)
                  ·
                    refine ⟨3766050603828319271469913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5021400805104425695293217 3766050603828319271469913)
                    ·
                      refine ⟨2824537952871239453602435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3766050603828319271469913 2824537952871239453602435)
                      ·
                        rfl

theorem cell23_5500768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_5500768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500768 prefixEnd_5500768 := by exact prefixLift 5500768
  have htrace : WordTrace (prefixWord ++ tailWord_5500768) baseStart_5500768 baseEnd_5500768 := by
    simpa [prefixWord, tailWord_5500768, baseEnd_5500768] using wordTrace_append hprefix tailTrace_5500768
  have hstable : (prefixWord ++ tailWord_5500768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500768).length < 2 ^ (prefixWord ++ tailWord_5500768).sum := by decide
  have hdescent : baseEnd_5500768 < baseStart_5500768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500808 : List Nat := [2, 1, 3, 3, 4, 1, 2, 2, 5]
def baseStart_5500808 : Nat := 118140960795 + 5500808 * 2 ^ 59
def prefixEnd_5500808 : Nat := 4983230072969 + 3 ^ 40 * 5500808 * 2
def baseEnd_5500808 : Nat := 313839832455268810789139

theorem tailTrace_5500808 : CollatzResearch.WordTrace tailWord_5500808 prefixEnd_5500808 313839832455268810789139 := by
  unfold tailWord_5500808
  simp only [CollatzResearch.WordTrace]
  refine ⟨100315475127759777028511539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133753966837013036038015385 100315475127759777028511539)
  ·
    refine ⟨150473212691639665542767309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100315475127759777028511539 150473212691639665542767309)
    ·
      refine ⟨56427454759364874578537741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150473212691639665542767309 56427454759364874578537741)
      ·
        refine ⟨21160295534761827966951653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56427454759364874578537741 21160295534761827966951653)
        ·
          refine ⟨3967555412767842743803435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21160295534761827966951653 3967555412767842743803435)
          ·
            refine ⟨5951333119151764115705153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967555412767842743803435 5951333119151764115705153)
            ·
              refine ⟨4463499839363823086778865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5951333119151764115705153 4463499839363823086778865)
              ·
                refine ⟨3347624879522867315084149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4463499839363823086778865 3347624879522867315084149)
                ·
                  refine ⟨313839832455268810789139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3347624879522867315084149 313839832455268810789139)
                  ·
                    rfl

theorem cell23_5500808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 5].length) (baseStart_5500808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500808 prefixEnd_5500808 := by exact prefixLift 5500808
  have htrace : WordTrace (prefixWord ++ tailWord_5500808) baseStart_5500808 baseEnd_5500808 := by
    simpa [prefixWord, tailWord_5500808, baseEnd_5500808] using wordTrace_append hprefix tailTrace_5500808
  have hstable : (prefixWord ++ tailWord_5500808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500808).length < 2 ^ (prefixWord ++ tailWord_5500808).sum := by decide
  have hdescent : baseEnd_5500808 < baseStart_5500808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500850 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_5500850 : Nat := 118140960795 + 5500850 * 2 ^ 59
def prefixEnd_5500850 : Nat := 4983230072969 + 3 ^ 40 * 5500850 * 2
def baseEnd_5500850 : Nat := 2824580058284908132777057

theorem tailTrace_5500850 : CollatzResearch.WordTrace tailWord_5500850 prefixEnd_5500850 2824580058284908132777057 := by
  unfold tailWord_5500850
  simp only [CollatzResearch.WordTrace]
  refine ⟨50158120530341848807513001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133754988080911596820034669 50158120530341848807513001)
  ·
    refine ⟨37618590397756386605634751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50158120530341848807513001 37618590397756386605634751)
    ·
      refine ⟨56427885596634579908452127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37618590397756386605634751 56427885596634579908452127)
      ·
        refine ⟨84641828394951869862678191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56427885596634579908452127 84641828394951869862678191)
        ·
          refine ⟨126962742592427804794017287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84641828394951869862678191 126962742592427804794017287)
          ·
            refine ⟨190444113888641707191025931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126962742592427804794017287 190444113888641707191025931)
            ·
              refine ⟨285666170832962560786538897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190444113888641707191025931 285666170832962560786538897)
              ·
                refine ⟨214249628124721920589904173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285666170832962560786538897 214249628124721920589904173)
                ·
                  refine ⟨80343610546770720221214065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214249628124721920589904173 80343610546770720221214065)
                  ·
                    refine ⟨60257707910078040165910549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80343610546770720221214065 60257707910078040165910549)
                    ·
                      refine ⟨2824580058284908132777057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60257707910078040165910549 2824580058284908132777057)
                      ·
                        rfl

theorem cell23_5500850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_5500850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500850 prefixEnd_5500850 := by exact prefixLift 5500850
  have htrace : WordTrace (prefixWord ++ tailWord_5500850) baseStart_5500850 baseEnd_5500850 := by
    simpa [prefixWord, tailWord_5500850, baseEnd_5500850] using wordTrace_append hprefix tailTrace_5500850
  have hstable : (prefixWord ++ tailWord_5500850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500850).length < 2 ^ (prefixWord ++ tailWord_5500850).sum := by decide
  have hdescent : baseEnd_5500850 < baseStart_5500850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500867 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 5, 5, 2]
def baseStart_5500867 : Nat := 118140960795 + 5500867 * 2 ^ 59
def prefixEnd_5500867 : Nat := 4983230072969 + 3 ^ 40 * 5500867 * 2
def baseEnd_5500867 : Nat := 2824588787456034566264479

theorem tailTrace_5500867 : CollatzResearch.WordTrace tailWord_5500867 prefixEnd_5500867 2824588787456034566264479 := by
  unfold tailWord_5500867
  simp only [CollatzResearch.WordTrace]
  refine ⟨200633102162305807133420855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133755401441537204755613903 200633102162305807133420855)
  ·
    refine ⟨300949653243458710700131283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200633102162305807133420855 300949653243458710700131283)
    ·
      refine ⟨451424479865188066050196925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300949653243458710700131283 451424479865188066050196925)
      ·
        refine ⟨169284179949445524768823847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451424479865188066050196925 169284179949445524768823847)
        ·
          refine ⟨253926269924168287153235771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169284179949445524768823847 253926269924168287153235771)
          ·
            refine ⟨380889404886252430729853657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253926269924168287153235771 380889404886252430729853657)
            ·
              refine ⟨285667053664689323047390243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380889404886252430729853657 285667053664689323047390243)
              ·
                refine ⟨428500580497033984571085365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285667053664689323047390243 428500580497033984571085365)
                ·
                  refine ⟨40171929421596936053539253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428500580497033984571085365 40171929421596936053539253)
                  ·
                    refine ⟨3766118383274712755019305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40171929421596936053539253 3766118383274712755019305)
                    ·
                      refine ⟨2824588787456034566264479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3766118383274712755019305 2824588787456034566264479)
                      ·
                        rfl

theorem cell23_5500867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 5, 2].length) (baseStart_5500867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500867 prefixEnd_5500867 := by exact prefixLift 5500867
  have htrace : WordTrace (prefixWord ++ tailWord_5500867) baseStart_5500867 baseEnd_5500867 := by
    simpa [prefixWord, tailWord_5500867, baseEnd_5500867] using wordTrace_append hprefix tailTrace_5500867
  have hstable : (prefixWord ++ tailWord_5500867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500867).length < 2 ^ (prefixWord ++ tailWord_5500867).sum := by decide
  have hdescent : baseEnd_5500867 < baseStart_5500867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500874 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_5500874 : Nat := 118140960795 + 5500874 * 2 ^ 59
def prefixEnd_5500874 : Nat := 4983230072969 + 3 ^ 40 * 5500874 * 2
def baseEnd_5500874 : Nat := 2824592381820616038876947

theorem tailTrace_5500874 : CollatzResearch.WordTrace tailWord_5500874 prefixEnd_5500874 2824592381820616038876947 := by
  unfold tailWord_5500874
  simp only [CollatzResearch.WordTrace]
  refine ⟨50158339368320111832231419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133755571648853631552617117 50158339368320111832231419)
  ·
    refine ⟨75237509052480167748347129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50158339368320111832231419 75237509052480167748347129)
    ·
      refine ⟨56428131789360125811260347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75237509052480167748347129 56428131789360125811260347)
      ·
        refine ⟨84642197684040188716890521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56428131789360125811260347 84642197684040188716890521)
        ·
          refine ⟨63481648263030141537667891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84642197684040188716890521 63481648263030141537667891)
          ·
            refine ⟨95222472394545212306501837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63481648263030141537667891 95222472394545212306501837)
            ·
              refine ⟨35708427147954454614938189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95222472394545212306501837 35708427147954454614938189)
              ·
                refine ⟨13390660180482920480601821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35708427147954454614938189 13390660180482920480601821)
                ·
                  refine ⟨5021497567681095180225683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13390660180482920480601821 5021497567681095180225683)
                  ·
                    refine ⟨7532246351521642770338525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5021497567681095180225683 7532246351521642770338525)
                    ·
                      refine ⟨2824592381820616038876947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7532246351521642770338525 2824592381820616038876947)
                      ·
                        rfl

theorem cell23_5500874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_5500874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500874 prefixEnd_5500874 := by exact prefixLift 5500874
  have htrace : WordTrace (prefixWord ++ tailWord_5500874) baseStart_5500874 baseEnd_5500874 := by
    simpa [prefixWord, tailWord_5500874, baseEnd_5500874] using wordTrace_append hprefix tailTrace_5500874
  have hstable : (prefixWord ++ tailWord_5500874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500874).length < 2 ^ (prefixWord ++ tailWord_5500874).sum := by decide
  have hdescent : baseEnd_5500874 < baseStart_5500874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500884 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_5500884 : Nat := 118140960795 + 5500884 * 2 ^ 59
def prefixEnd_5500884 : Nat := 4983230072969 + 3 ^ 40 * 5500884 * 2
def baseEnd_5500884 : Nat := 2824597516627160999751901

theorem tailTrace_5500884 : CollatzResearch.WordTrace tailWord_5500884 prefixEnd_5500884 2824597516627160999751901 := by
  unfold tailWord_5500884
  simp only [CollatzResearch.WordTrace]
  refine ⟨100316861101622109518394853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133755814802162812691193137 100316861101622109518394853)
  ·
    refine ⟨18809411456554145534699035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100316861101622109518394853 18809411456554145534699035)
    ·
      refine ⟨28214117184831218302048553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18809411456554145534699035 28214117184831218302048553)
      ·
        refine ⟨21160587888623413726536415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28214117184831218302048553 21160587888623413726536415)
        ·
          refine ⟨31740881832935120589804623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21160587888623413726536415 31740881832935120589804623)
          ·
            refine ⟨47611322749402680884706935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31740881832935120589804623 47611322749402680884706935)
            ·
              refine ⟨71416984124104021327060403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47611322749402680884706935 71416984124104021327060403)
              ·
                refine ⟨107125476186156031990590605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71416984124104021327060403 107125476186156031990590605)
                ·
                  refine ⟨40172053569808511996471477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107125476186156031990590605 40172053569808511996471477)
                  ·
                    refine ⟨3766130022169547999669201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40172053569808511996471477 3766130022169547999669201)
                    ·
                      refine ⟨2824597516627160999751901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3766130022169547999669201 2824597516627160999751901)
                      ·
                        rfl

theorem cell23_5500884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_5500884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500884 prefixEnd_5500884 := by exact prefixLift 5500884
  have htrace : WordTrace (prefixWord ++ tailWord_5500884) baseStart_5500884 baseEnd_5500884 := by
    simpa [prefixWord, tailWord_5500884, baseEnd_5500884] using wordTrace_append hprefix tailTrace_5500884
  have hstable : (prefixWord ++ tailWord_5500884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500884).length < 2 ^ (prefixWord ++ tailWord_5500884).sum := by decide
  have hdescent : baseEnd_5500884 < baseStart_5500884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500897 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_5500897 : Nat := 118140960795 + 5500897 * 2 ^ 59
def prefixEnd_5500897 : Nat := 4983230072969 + 3 ^ 40 * 5500897 * 2
def baseEnd_5500897 : Nat := 2824604191875669448889341

theorem tailTrace_5500897 : CollatzResearch.WordTrace tailWord_5500897 prefixEnd_5500897 2824604191875669448889341 := by
  unfold tailWord_5500897
  simp only [CollatzResearch.WordTrace]
  refine ⟨200634196352197122257012945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133756130901464748171341963 200634196352197122257012945)
  ·
    refine ⟨150475647264147841692759709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200634196352197122257012945 150475647264147841692759709)
    ·
      refine ⟨56428367724055440634784891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150475647264147841692759709 56428367724055440634784891)
      ·
        refine ⟨84642551586083160952177337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56428367724055440634784891 84642551586083160952177337)
        ·
          refine ⟨63481913689562370714133003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84642551586083160952177337 63481913689562370714133003)
          ·
            refine ⟨95222870534343556071199505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63481913689562370714133003 95222870534343556071199505)
            ·
              refine ⟨71417152900757667053399629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95222870534343556071199505 71417152900757667053399629)
              ·
                refine ⟨26781432337784125145024861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71417152900757667053399629 26781432337784125145024861)
                ·
                  refine ⟨10043037126669046929384323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26781432337784125145024861 10043037126669046929384323)
                  ·
                    refine ⟨15064555690003570394076485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10043037126669046929384323 15064555690003570394076485)
                    ·
                      refine ⟨2824604191875669448889341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15064555690003570394076485 2824604191875669448889341)
                      ·
                        rfl

theorem cell23_5500897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_5500897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500897 prefixEnd_5500897 := by exact prefixLift 5500897
  have htrace : WordTrace (prefixWord ++ tailWord_5500897) baseStart_5500897 baseEnd_5500897 := by
    simpa [prefixWord, tailWord_5500897, baseEnd_5500897] using wordTrace_append hprefix tailTrace_5500897
  have hstable : (prefixWord ++ tailWord_5500897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500897).length < 2 ^ (prefixWord ++ tailWord_5500897).sum := by decide
  have hdescent : baseEnd_5500897 < baseStart_5500897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500918 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_5500918 : Nat := 118140960795 + 5500918 * 2 ^ 59
def prefixEnd_5500918 : Nat := 4983230072969 + 3 ^ 40 * 5500918 * 2
def baseEnd_5500918 : Nat := 2824614974969413866726745

theorem tailTrace_5500918 : CollatzResearch.WordTrace tailWord_5500918 prefixEnd_5500918 2824614974969413866726745 := by
  unfold tailWord_5500918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12539685142820065177720463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133756641523414028562351605 12539685142820065177720463)
  ·
    refine ⟨18809527714230097766580695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12539685142820065177720463 18809527714230097766580695)
    ·
      refine ⟨28214291571345146649871043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18809527714230097766580695 28214291571345146649871043)
      ·
        refine ⟨42321437357017719974806565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28214291571345146649871043 42321437357017719974806565)
        ·
          refine ⟨7935269504440822495276231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42321437357017719974806565 7935269504440822495276231)
          ·
            refine ⟨11902904256661233742914347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7935269504440822495276231 11902904256661233742914347)
            ·
              refine ⟨17854356384991850614371521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11902904256661233742914347 17854356384991850614371521)
              ·
                refine ⟨13390767288743887960778641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17854356384991850614371521 13390767288743887960778641)
                ·
                  refine ⟨10043075466557915970583981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13390767288743887960778641 10043075466557915970583981)
                  ·
                    refine ⟨3766153299959218488968993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10043075466557915970583981 3766153299959218488968993)
                    ·
                      refine ⟨2824614974969413866726745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3766153299959218488968993 2824614974969413866726745)
                      ·
                        rfl

theorem cell23_5500918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_5500918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500918 prefixEnd_5500918 := by exact prefixLift 5500918
  have htrace : WordTrace (prefixWord ++ tailWord_5500918) baseStart_5500918 baseEnd_5500918 := by
    simpa [prefixWord, tailWord_5500918, baseEnd_5500918] using wordTrace_append hprefix tailTrace_5500918
  have hstable : (prefixWord ++ tailWord_5500918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500918).length < 2 ^ (prefixWord ++ tailWord_5500918).sum := by decide
  have hdescent : baseEnd_5500918 < baseStart_5500918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500920 : List Nat := [2, 1, 2, 1, 1, 3, 13]
def baseStart_5500920 : Nat := 118140960795 + 5500920 * 2 ^ 59
def prefixEnd_5500920 : Nat := 4983230072969 + 3 ^ 40 * 5500920 * 2
def baseEnd_5500920 : Nat := 34871802492971887146935

theorem tailTrace_5500920 : CollatzResearch.WordTrace tailWord_5500920 prefixEnd_5500920 34871802492971887146935 := by
  unfold tailWord_5500920
  simp only [CollatzResearch.WordTrace]
  refine ⟨100317517615556898592550107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133756690154075864790066809 100317517615556898592550107)
  ·
    refine ⟨150476276423335347888825161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100317517615556898592550107 150476276423335347888825161)
    ·
      refine ⟨112857207317501510916618871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150476276423335347888825161 112857207317501510916618871)
      ·
        refine ⟨169285810976252266374928307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112857207317501510916618871 169285810976252266374928307)
        ·
          refine ⟨253928716464378399562392461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169285810976252266374928307 253928716464378399562392461)
          ·
            refine ⟨95223268674141899835897173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253928716464378399562392461 95223268674141899835897173)
            ·
              refine ⟨34871802492971887146935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 95223268674141899835897173 34871802492971887146935)
              ·
                rfl

theorem cell23_5500920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 13].length) (baseStart_5500920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500920 prefixEnd_5500920 := by exact prefixLift 5500920
  have htrace : WordTrace (prefixWord ++ tailWord_5500920) baseStart_5500920 baseEnd_5500920 := by
    simpa [prefixWord, tailWord_5500920, baseEnd_5500920] using wordTrace_append hprefix tailTrace_5500920
  have hstable : (prefixWord ++ tailWord_5500920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500920).length < 2 ^ (prefixWord ++ tailWord_5500920).sum := by decide
  have hdescent : baseEnd_5500920 < baseStart_5500920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500924 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 2, 4]
def baseStart_5500924 : Nat := 118140960795 + 5500924 * 2 ^ 59
def prefixEnd_5500924 : Nat := 4983230072969 + 3 ^ 40 * 5500924 * 2
def baseEnd_5500924 : Nat := 941539351951113614417239

theorem tailTrace_5500924 : CollatzResearch.WordTrace tailWord_5500924 prefixEnd_5500924 941539351951113614417239 := by
  unfold tailWord_5500924
  simp only [CollatzResearch.WordTrace]
  refine ⟨100317590561549652934122913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133756787415399537245497217 100317590561549652934122913)
  ·
    refine ⟨75238192921162239700592185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100317590561549652934122913 75238192921162239700592185)
    ·
      refine ⟨56428644690871679775444139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75238192921162239700592185 56428644690871679775444139)
      ·
        refine ⟨84642967036307519663166209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56428644690871679775444139 84642967036307519663166209)
        ·
          refine ⟨63482225277230639747374657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84642967036307519663166209 63482225277230639747374657)
          ·
            refine ⟨47611668957922979810530993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63482225277230639747374657 47611668957922979810530993)
            ·
              refine ⟨35708751718442234857898245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47611668957922979810530993 35708751718442234857898245)
              ·
                refine ⟨6695390947207919035855921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35708751718442234857898245 6695390947207919035855921)
                ·
                  refine ⟨5021543210405939276891941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6695390947207919035855921 5021543210405939276891941)
                  ·
                    refine ⟨941539351951113614417239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5021543210405939276891941 941539351951113614417239)
                    ·
                      rfl

theorem cell23_5500924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_5500924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500924 prefixEnd_5500924 := by exact prefixLift 5500924
  have htrace : WordTrace (prefixWord ++ tailWord_5500924) baseStart_5500924 baseEnd_5500924 := by
    simpa [prefixWord, tailWord_5500924, baseEnd_5500924] using wordTrace_append hprefix tailTrace_5500924
  have hstable : (prefixWord ++ tailWord_5500924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500924).length < 2 ^ (prefixWord ++ tailWord_5500924).sum := by decide
  have hdescent : baseEnd_5500924 < baseStart_5500924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500948 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_5500948 : Nat := 118140960795 + 5500948 * 2 ^ 59
def prefixEnd_5500948 : Nat := 4983230072969 + 3 ^ 40 * 5500948 * 2
def baseEnd_5500948 : Nat := 2824630379389048749351607

theorem tailTrace_5500948 : CollatzResearch.WordTrace tailWord_5500948 prefixEnd_5500948 2824630379389048749351607 := by
  unfold tailWord_5500948
  simp only [CollatzResearch.WordTrace]
  refine ⟨100318028237506178983559749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133757370983341571978079665 100318028237506178983559749)
  ·
    refine ⟨18809630294532408559417453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100318028237506178983559749 18809630294532408559417453)
    ·
      refine ⟨7053611360449653209781545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18809630294532408559417453 7053611360449653209781545)
      ·
        refine ⟨5290208520337239907336159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7053611360449653209781545 5290208520337239907336159)
        ·
          refine ⟨7935312780505859861004239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5290208520337239907336159 7935312780505859861004239)
          ·
            refine ⟨11902969170758789791506359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7935312780505859861004239 11902969170758789791506359)
            ·
              refine ⟨17854453756138184687259539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11902969170758789791506359 17854453756138184687259539)
              ·
                refine ⟨26781680634207277030889309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17854453756138184687259539 26781680634207277030889309)
                ·
                  refine ⟨10043130237827728886583491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26781680634207277030889309 10043130237827728886583491)
                  ·
                    refine ⟨15064695356741593329875237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10043130237827728886583491 15064695356741593329875237)
                    ·
                      refine ⟨2824630379389048749351607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15064695356741593329875237 2824630379389048749351607)
                      ·
                        rfl

theorem cell23_5500948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_5500948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500948 prefixEnd_5500948 := by exact prefixLift 5500948
  have htrace : WordTrace (prefixWord ++ tailWord_5500948) baseStart_5500948 baseEnd_5500948 := by
    simpa [prefixWord, tailWord_5500948, baseEnd_5500948] using wordTrace_append hprefix tailTrace_5500948
  have hstable : (prefixWord ++ tailWord_5500948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500948).length < 2 ^ (prefixWord ++ tailWord_5500948).sum := by decide
  have hdescent : baseEnd_5500948 < baseStart_5500948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500951 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 3]
def baseStart_5500951 : Nat := 118140960795 + 5500951 * 2 ^ 59
def prefixEnd_5500951 : Nat := 4983230072969 + 3 ^ 40 * 5500951 * 2
def baseEnd_5500951 : Nat := 2824631919831012237614093

theorem tailTrace_5500951 : CollatzResearch.WordTrace tailWord_5500951 prefixEnd_5500951 2824631919831012237614093 := by
  unfold tailWord_5500951
  simp only [CollatzResearch.WordTrace]
  refine ⟨200636165894001489479478707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133757443929334326319652471 200636165894001489479478707)
  ·
    refine ⟨300954248841002234219218061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200636165894001489479478707 300954248841002234219218061)
    ·
      refine ⟨112857843315375837832206773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300954248841002234219218061 112857843315375837832206773)
      ·
        refine ⟨10580422810816484796769385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112857843315375837832206773 10580422810816484796769385)
        ·
          refine ⟨7935317108112363597577039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10580422810816484796769385 7935317108112363597577039)
          ·
            refine ⟨11902975662168545396365559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7935317108112363597577039 11902975662168545396365559)
            ·
              refine ⟨17854463493252818094548339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11902975662168545396365559 17854463493252818094548339)
              ·
                refine ⟨26781695239879227141822509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17854463493252818094548339 26781695239879227141822509)
                ·
                  refine ⟨10043135714954710178183441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26781695239879227141822509 10043135714954710178183441)
                  ·
                    refine ⟨7532351786216032633637581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10043135714954710178183441 7532351786216032633637581)
                    ·
                      refine ⟨2824631919831012237614093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7532351786216032633637581 2824631919831012237614093)
                      ·
                        rfl

theorem cell23_5500951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_5500951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500951 prefixEnd_5500951 := by exact prefixLift 5500951
  have htrace : WordTrace (prefixWord ++ tailWord_5500951) baseStart_5500951 baseEnd_5500951 := by
    simpa [prefixWord, tailWord_5500951, baseEnd_5500951] using wordTrace_append hprefix tailTrace_5500951
  have hstable : (prefixWord ++ tailWord_5500951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500951).length < 2 ^ (prefixWord ++ tailWord_5500951).sum := by decide
  have hdescent : baseEnd_5500951 < baseStart_5500951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500968 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5500968 : Nat := 118140960795 + 5500968 * 2 ^ 59
def prefixEnd_5500968 : Nat := 4983230072969 + 3 ^ 40 * 5500968 * 2
def baseEnd_5500968 : Nat := 2824640649002138671101515

theorem tailTrace_5500968 : CollatzResearch.WordTrace tailWord_5500968 prefixEnd_5500968 2824640649002138671101515 := by
  unfold tailWord_5500968
  simp only [CollatzResearch.WordTrace]
  refine ⟨100318392967469950691423779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133757857289959934255231705 100318392967469950691423779)
  ·
    refine ⟨150477589451204926037135669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100318392967469950691423779 150477589451204926037135669)
    ·
      refine ⟨14107274011050461815981469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150477589451204926037135669 14107274011050461815981469)
      ·
        refine ⟨5290227754143923180993051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14107274011050461815981469 5290227754143923180993051)
        ·
          refine ⟨7935341631215884771489577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5290227754143923180993051 7935341631215884771489577)
          ·
            refine ⟨5951506223411913578617183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7935341631215884771489577 5951506223411913578617183)
            ·
              refine ⟨8927259335117870367925775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5951506223411913578617183 8927259335117870367925775)
              ·
                refine ⟨13390889002676805551888663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8927259335117870367925775 13390889002676805551888663)
                ·
                  refine ⟨20086333504015208327832995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13390889002676805551888663 20086333504015208327832995)
                  ·
                    refine ⟨30129500256022812491749493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20086333504015208327832995 30129500256022812491749493)
                    ·
                      refine ⟨2824640649002138671101515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30129500256022812491749493 2824640649002138671101515)
                      ·
                        rfl

theorem cell23_5500968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5500968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500968 prefixEnd_5500968 := by exact prefixLift 5500968
  have htrace : WordTrace (prefixWord ++ tailWord_5500968) baseStart_5500968 baseEnd_5500968 := by
    simpa [prefixWord, tailWord_5500968, baseEnd_5500968] using wordTrace_append hprefix tailTrace_5500968
  have hstable : (prefixWord ++ tailWord_5500968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500968).length < 2 ^ (prefixWord ++ tailWord_5500968).sum := by decide
  have hdescent : baseEnd_5500968 < baseStart_5500968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500981 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_5500981 : Nat := 118140960795 + 5500981 * 2 ^ 59
def prefixEnd_5500981 : Nat := 4983230072969 + 3 ^ 40 * 5500981 * 2
def baseEnd_5500981 : Nat := 2824647324250647120238955

theorem tailTrace_5500981 : CollatzResearch.WordTrace tailWord_5500981 prefixEnd_5500981 2824647324250647120238955 := by
  unfold tailWord_5500981
  simp only [CollatzResearch.WordTrace]
  refine ⟨200637260083892804603070797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133758173389261869735380531 200637260083892804603070797)
  ·
    refine ⟨75238972531459801726151549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200637260083892804603070797 75238972531459801726151549)
    ·
      refine ⟨28214614699297425647306831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75238972531459801726151549 28214614699297425647306831)
      ·
        refine ⟨42321922048946138470960247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28214614699297425647306831 42321922048946138470960247)
        ·
          refine ⟨63482883073419207706440371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42321922048946138470960247 63482883073419207706440371)
          ·
            refine ⟨95224324610128811559660557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63482883073419207706440371 95224324610128811559660557)
            ·
              refine ⟨35709121728798304334872709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95224324610128811559660557 35709121728798304334872709)
              ·
                refine ⟨6695460324149682062788633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35709121728798304334872709 6695460324149682062788633)
                ·
                  refine ⟨5021595243112261547091475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6695460324149682062788633 5021595243112261547091475)
                  ·
                    refine ⟨7532392864668392320637213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5021595243112261547091475 7532392864668392320637213)
                    ·
                      refine ⟨2824647324250647120238955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7532392864668392320637213 2824647324250647120238955)
                      ·
                        rfl

theorem cell23_5500981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_5500981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500981 prefixEnd_5500981 := by exact prefixLift 5500981
  have htrace : WordTrace (prefixWord ++ tailWord_5500981) baseStart_5500981 baseEnd_5500981 := by
    simpa [prefixWord, tailWord_5500981, baseEnd_5500981] using wordTrace_append hprefix tailTrace_5500981
  have hstable : (prefixWord ++ tailWord_5500981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500981).length < 2 ^ (prefixWord ++ tailWord_5500981).sum := by decide
  have hdescent : baseEnd_5500981 < baseStart_5500981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5500998 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_5500998 : Nat := 118140960795 + 5500998 * 2 ^ 59
def prefixEnd_5500998 : Nat := 4983230072969 + 3 ^ 40 * 5500998 * 2
def baseEnd_5500998 : Nat := 2824656053421773553726377

theorem tailTrace_5500998 : CollatzResearch.WordTrace tailWord_5500998 prefixEnd_5500998 2824656053421773553726377 := by
  unfold tailWord_5500998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6269933753900975515826239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133758586749887477670959765 6269933753900975515826239)
  ·
    refine ⟨9404900630851463273739359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6269933753900975515826239 9404900630851463273739359)
    ·
      refine ⟨14107350946277194910609039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9404900630851463273739359 14107350946277194910609039)
      ·
        refine ⟨21161026419415792365913559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14107350946277194910609039 21161026419415792365913559)
        ·
          refine ⟨31741539629123688548870339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21161026419415792365913559 31741539629123688548870339)
          ·
            refine ⟨47612309443685532823305509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31741539629123688548870339 47612309443685532823305509)
            ·
              refine ⟨8927308020691037404369783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47612309443685532823305509 8927308020691037404369783)
              ·
                refine ⟨13390962031036556106554675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8927308020691037404369783 13390962031036556106554675)
                ·
                  refine ⟨20086443046554834159832013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13390962031036556106554675 20086443046554834159832013)
                  ·
                    refine ⟨7532416142458062809937005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20086443046554834159832013 7532416142458062809937005)
                    ·
                      refine ⟨2824656053421773553726377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7532416142458062809937005 2824656053421773553726377)
                      ·
                        rfl

theorem cell23_5500998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_5500998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5500998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5500998 prefixEnd_5500998 := by exact prefixLift 5500998
  have htrace : WordTrace (prefixWord ++ tailWord_5500998) baseStart_5500998 baseEnd_5500998 := by
    simpa [prefixWord, tailWord_5500998, baseEnd_5500998] using wordTrace_append hprefix tailTrace_5500998
  have hstable : (prefixWord ++ tailWord_5500998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5500998).length < 2 ^ (prefixWord ++ tailWord_5500998).sum := by decide
  have hdescent : baseEnd_5500998 < baseStart_5500998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5500998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501017 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 4]
def baseStart_5501017 : Nat := 118140960795 + 5501017 * 2 ^ 59
def prefixEnd_5501017 : Nat := 4983230072969 + 3 ^ 40 * 5501017 * 2
def baseEnd_5501017 : Nat := 2824665809554208979388789

theorem tailTrace_5501017 : CollatzResearch.WordTrace tailWord_5501017 prefixEnd_5501017 2824665809554208979388789 := by
  unfold tailWord_5501017
  simp only [CollatzResearch.WordTrace]
  refine ⟨200638573111762382751381305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133759048741174921834254203 200638573111762382751381305)
  ·
    refine ⟨150478929833821787063535979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200638573111762382751381305 150478929833821787063535979)
    ·
      refine ⟨225718394750732680595303969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150478929833821787063535979 225718394750732680595303969)
      ·
        refine ⟨169288796063049510446477977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225718394750732680595303969 169288796063049510446477977)
        ·
          refine ⟨126966597047287132834858483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169288796063049510446477977 126966597047287132834858483)
          ·
            refine ⟨190449895570930699252287725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126966597047287132834858483 190449895570930699252287725)
            ·
              refine ⟨71418710839099012219607897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190449895570930699252287725 71418710839099012219607897)
              ·
                refine ⟨53564033129324259164705923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71418710839099012219607897 53564033129324259164705923)
                ·
                  refine ⟨80346049693986388747058885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53564033129324259164705923 80346049693986388747058885)
                  ·
                    refine ⟨15064884317622447890073541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80346049693986388747058885 15064884317622447890073541)
                    ·
                      refine ⟨2824665809554208979388789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15064884317622447890073541 2824665809554208979388789)
                      ·
                        rfl

theorem cell23_5501017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_5501017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501017 prefixEnd_5501017 := by exact prefixLift 5501017
  have htrace : WordTrace (prefixWord ++ tailWord_5501017) baseStart_5501017 baseEnd_5501017 := by
    simpa [prefixWord, tailWord_5501017, baseEnd_5501017] using wordTrace_append hprefix tailTrace_5501017
  have hstable : (prefixWord ++ tailWord_5501017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501017).length < 2 ^ (prefixWord ++ tailWord_5501017).sum := by decide
  have hdescent : baseEnd_5501017 < baseStart_5501017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501038 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_5501038 : Nat := 118140960795 + 5501038 * 2 ^ 59
def prefixEnd_5501038 : Nat := 4983230072969 + 3 ^ 40 * 5501038 * 2
def baseEnd_5501038 : Nat := 2824676592647953397226193

theorem tailTrace_5501038 : CollatzResearch.WordTrace tailWord_5501038 prefixEnd_5501038 2824676592647953397226193 := by
  unfold tailWord_5501038
  simp only [CollatzResearch.WordTrace]
  refine ⟨25079917380585787917236971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133759559363124202225263845 25079917380585787917236971)
  ·
    refine ⟨37619876070878681875855457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25079917380585787917236971 37619876070878681875855457)
    ·
      refine ⟨28214907053159011406891593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37619876070878681875855457 28214907053159011406891593)
      ·
        refine ⟨21161180289869258555168695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28214907053159011406891593 21161180289869258555168695)
        ·
          refine ⟨31741770434803887832753043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21161180289869258555168695 31741770434803887832753043)
          ·
            refine ⟨47612655652205831749129565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31741770434803887832753043 47612655652205831749129565)
            ·
              refine ⟨17854745869577186905923587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47612655652205831749129565 17854745869577186905923587)
              ·
                refine ⟨26782118804365780358885381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17854745869577186905923587 26782118804365780358885381)
                ·
                  refine ⟨5021647275818583817291009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26782118804365780358885381 5021647275818583817291009)
                  ·
                    refine ⟨3766235456863937862968257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5021647275818583817291009 3766235456863937862968257)
                    ·
                      refine ⟨2824676592647953397226193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3766235456863937862968257 2824676592647953397226193)
                      ·
                        rfl

theorem cell23_5501038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_5501038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501038 prefixEnd_5501038 := by exact prefixLift 5501038
  have htrace : WordTrace (prefixWord ++ tailWord_5501038) baseStart_5501038 baseEnd_5501038 := by
    simpa [prefixWord, tailWord_5501038, baseEnd_5501038] using wordTrace_append hprefix tailTrace_5501038
  have hstable : (prefixWord ++ tailWord_5501038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501038).length < 2 ^ (prefixWord ++ tailWord_5501038).sum := by decide
  have hdescent : baseEnd_5501038 < baseStart_5501038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501067 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 5]
def baseStart_5501067 : Nat := 118140960795 + 5501067 * 2 ^ 59
def prefixEnd_5501067 : Nat := 4983230072969 + 3 ^ 40 * 5501067 * 2
def baseEnd_5501067 : Nat := 2824691483586933783763559

theorem tailTrace_5501067 : CollatzResearch.WordTrace tailWord_5501067 prefixEnd_5501067 2824691483586933783763559 := by
  unfold tailWord_5501067
  simp only [CollatzResearch.WordTrace]
  refine ⟨200640396761581241290701455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133760264507720827527134303 200640396761581241290701455)
  ·
    refine ⟨300960595142371861936052183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200640396761581241290701455 300960595142371861936052183)
    ·
      refine ⟨451440892713557792904078275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300960595142371861936052183 451440892713557792904078275)
      ·
        refine ⟨677161339070336689356117413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451440892713557792904078275 677161339070336689356117413)
        ·
          refine ⟨126967751075688129254272015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 677161339070336689356117413 126967751075688129254272015)
          ·
            refine ⟨190451626613532193881408023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126967751075688129254272015 190451626613532193881408023)
            ·
              refine ⟨285677439920298290822112035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190451626613532193881408023 285677439920298290822112035)
              ·
                refine ⟨428516159880447436233168053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285677439920298290822112035 428516159880447436233168053)
                ·
                  refine ⟨40173389988791947146859505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428516159880447436233168053 40173389988791947146859505)
                  ·
                    refine ⟨30130042491593960360144629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40173389988791947146859505 30130042491593960360144629)
                    ·
                      refine ⟨2824691483586933783763559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30130042491593960360144629 2824691483586933783763559)
                      ·
                        rfl

theorem cell23_5501067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_5501067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501067 prefixEnd_5501067 := by exact prefixLift 5501067
  have htrace : WordTrace (prefixWord ++ tailWord_5501067) baseStart_5501067 baseEnd_5501067 := by
    simpa [prefixWord, tailWord_5501067, baseEnd_5501067] using wordTrace_append hprefix tailTrace_5501067
  have hstable : (prefixWord ++ tailWord_5501067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501067).length < 2 ^ (prefixWord ++ tailWord_5501067).sum := by decide
  have hdescent : baseEnd_5501067 < baseStart_5501067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501074 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_5501074 : Nat := 118140960795 + 5501074 * 2 ^ 59
def prefixEnd_5501074 : Nat := 4983230072969 + 3 ^ 40 * 5501074 * 2
def baseEnd_5501074 : Nat := 941565025983838418792009

theorem tailTrace_5501074 : CollatzResearch.WordTrace tailWord_5501074 prefixEnd_5501074 941565025983838418792009 := by
  unfold tailWord_5501074
  simp only [CollatzResearch.WordTrace]
  refine ⟨50160163018138970371551569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133760434715037254324137517 50160163018138970371551569)
  ·
    refine ⟨37620122263604227778663677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50160163018138970371551569 37620122263604227778663677)
    ·
      refine ⟨14107545848851585416998879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37620122263604227778663677 14107545848851585416998879)
      ·
        refine ⟨21161318773277378125498319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14107545848851585416998879 21161318773277378125498319)
        ·
          refine ⟨31741978159916067188247479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21161318773277378125498319 31741978159916067188247479)
          ·
            refine ⟨47612967239874100782371219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31741978159916067188247479 47612967239874100782371219)
            ·
              refine ⟨71419450859811151173556829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47612967239874100782371219 71419450859811151173556829)
              ·
                refine ⟨26782294072429181690083811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71419450859811151173556829 26782294072429181690083811)
                ·
                  refine ⟨40173441108643772535125717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26782294072429181690083811 40173441108643772535125717)
                  ·
                    refine ⟨941565025983838418792009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40173441108643772535125717 941565025983838418792009)
                    ·
                      rfl

theorem cell23_5501074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_5501074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501074 prefixEnd_5501074 := by exact prefixLift 5501074
  have htrace : WordTrace (prefixWord ++ tailWord_5501074) baseStart_5501074 baseEnd_5501074 := by
    simpa [prefixWord, tailWord_5501074, baseEnd_5501074] using wordTrace_append hprefix tailTrace_5501074
  have hstable : (prefixWord ++ tailWord_5501074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501074).length < 2 ^ (prefixWord ++ tailWord_5501074).sum := by decide
  have hdescent : baseEnd_5501074 < baseStart_5501074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501084 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_5501084 : Nat := 118140960795 + 5501084 * 2 ^ 59
def prefixEnd_5501084 : Nat := 4983230072969 + 3 ^ 40 * 5501084 * 2
def baseEnd_5501084 : Nat := 2824700212758060217250981

theorem tailTrace_5501084 : CollatzResearch.WordTrace tailWord_5501084 prefixEnd_5501084 2824700212758060217250981 := by
  unfold tailWord_5501084
  simp only [CollatzResearch.WordTrace]
  refine ⟨100320508401259826597035153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133760677868346435462713537 100320508401259826597035153)
  ·
    refine ⟨75240381300944869947776365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100320508401259826597035153 75240381300944869947776365)
    ·
      refine ⟨28215142987854326230416137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75240381300944869947776365 28215142987854326230416137)
      ·
        refine ⟨21161357240890744672812103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28215142987854326230416137 21161357240890744672812103)
        ·
          refine ⟨31742035861336117009218155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21161357240890744672812103 31742035861336117009218155)
          ·
            refine ⟨47613053792004175513827233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31742035861336117009218155 47613053792004175513827233)
            ·
              refine ⟨35709790344003131635370425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47613053792004175513827233 35709790344003131635370425)
              ·
                refine ⟨26782342758002348726527819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35709790344003131635370425 26782342758002348726527819)
                ·
                  refine ⟨40173514137003523089791729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26782342758002348726527819 40173514137003523089791729)
                  ·
                    refine ⟨30130135602752642317343797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40173514137003523089791729 30130135602752642317343797)
                    ·
                      refine ⟨2824700212758060217250981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30130135602752642317343797 2824700212758060217250981)
                      ·
                        rfl

theorem cell23_5501084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_5501084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501084 prefixEnd_5501084 := by exact prefixLift 5501084
  have htrace : WordTrace (prefixWord ++ tailWord_5501084) baseStart_5501084 baseEnd_5501084 := by
    simpa [prefixWord, tailWord_5501084, baseEnd_5501084] using wordTrace_append hprefix tailTrace_5501084
  have hstable : (prefixWord ++ tailWord_5501084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501084).length < 2 ^ (prefixWord ++ tailWord_5501084).sum := by decide
  have hdescent : baseEnd_5501084 < baseStart_5501084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501095 : List Nat := [1, 1, 6, 2, 2, 1, 3, 2, 5]
def baseStart_5501095 : Nat := 118140960795 + 5501095 * 2 ^ 59
def prefixEnd_5501095 : Nat := 4983230072969 + 3 ^ 40 * 5501095 * 2
def baseEnd_5501095 : Nat := 313856206782806630468159

theorem tailTrace_5501095 : CollatzResearch.WordTrace tailWord_5501095 prefixEnd_5501095 313856206782806630468159 := by
  unfold tailWord_5501095
  simp only [CollatzResearch.WordTrace]
  refine ⟨200641418005479802072720739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133760945336986534715147159 200641418005479802072720739)
  ·
    refine ⟨300962127008219703109081109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200641418005479802072720739 300962127008219703109081109)
    ·
      refine ⟨14107599703510298583238177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 300962127008219703109081109 14107599703510298583238177)
      ·
        refine ⟨10580699777632723937428633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14107599703510298583238177 10580699777632723937428633)
        ·
          refine ⟨7935524833224542953071475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10580699777632723937428633 7935524833224542953071475)
          ·
            refine ⟨11903287249836814429607213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7935524833224542953071475 11903287249836814429607213)
            ·
              refine ⟨4463732718688805411102705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11903287249836814429607213 4463732718688805411102705)
              ·
                refine ⟨3347799539016604058327029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4463732718688805411102705 3347799539016604058327029)
                ·
                  refine ⟨313856206782806630468159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3347799539016604058327029 313856206782806630468159)
                  ·
                    rfl

theorem cell23_5501095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 5].length) (baseStart_5501095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501095 prefixEnd_5501095 := by exact prefixLift 5501095
  have htrace : WordTrace (prefixWord ++ tailWord_5501095) baseStart_5501095 baseEnd_5501095 := by
    simpa [prefixWord, tailWord_5501095, baseEnd_5501095] using wordTrace_append hprefix tailTrace_5501095
  have hstable : (prefixWord ++ tailWord_5501095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501095).length < 2 ^ (prefixWord ++ tailWord_5501095).sum := by decide
  have hdescent : baseEnd_5501095 < baseStart_5501095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501101 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_5501101 : Nat := 118140960795 + 5501101 * 2 ^ 59
def prefixEnd_5501101 : Nat := 4983230072969 + 3 ^ 40 * 5501101 * 2
def baseEnd_5501101 : Nat := 2824708941929186650738403

theorem tailTrace_5501101 : CollatzResearch.WordTrace tailWord_5501101 prefixEnd_5501101 2824708941929186650738403 := by
  unfold tailWord_5501101
  simp only [CollatzResearch.WordTrace]
  refine ⟨200641636843458065097439157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133761091228972043398292771 200641636843458065097439157)
  ·
    refine ⟨18810153454074193602884921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200641636843458065097439157 18810153454074193602884921)
    ·
      refine ⟨14107615090555645202163691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18810153454074193602884921 14107615090555645202163691)
      ·
        refine ⟨21161422635833467803245537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14107615090555645202163691 21161422635833467803245537)
        ·
          refine ⟨15871066976875100852434153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21161422635833467803245537 15871066976875100852434153)
          ·
            refine ⟨11903300232656325639325615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15871066976875100852434153 11903300232656325639325615)
            ·
              refine ⟨17854950348984488458988423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11903300232656325639325615 17854950348984488458988423)
              ·
                refine ⟨26782425523476732688482635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17854950348984488458988423 26782425523476732688482635)
                ·
                  refine ⟨40173638285215099032723953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26782425523476732688482635 40173638285215099032723953)
                  ·
                    refine ⟨30130228713911324274542965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40173638285215099032723953 30130228713911324274542965)
                    ·
                      refine ⟨2824708941929186650738403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30130228713911324274542965 2824708941929186650738403)
                      ·
                        rfl

theorem cell23_5501101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_5501101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501101 prefixEnd_5501101 := by exact prefixLift 5501101
  have htrace : WordTrace (prefixWord ++ tailWord_5501101) baseStart_5501101 baseEnd_5501101 := by
    simpa [prefixWord, tailWord_5501101, baseEnd_5501101] using wordTrace_append hprefix tailTrace_5501101
  have hstable : (prefixWord ++ tailWord_5501101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501101).length < 2 ^ (prefixWord ++ tailWord_5501101).sum := by decide
  have hdescent : baseEnd_5501101 < baseStart_5501101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501114 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3]
def baseStart_5501114 : Nat := 118140960795 + 5501114 * 2 ^ 59
def prefixEnd_5501114 : Nat := 4983230072969 + 3 ^ 40 * 5501114 * 2
def baseEnd_5501114 : Nat := 2824715617177695099875843

theorem tailTrace_5501114 : CollatzResearch.WordTrace tailWord_5501114 prefixEnd_5501114 2824715617177695099875843 := by
  unfold tailWord_5501114
  simp only [CollatzResearch.WordTrace]
  refine ⟨50160527748102742079415599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133761407328273978878441597 50160527748102742079415599)
  ·
    refine ⟨75240791622154113119123399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50160527748102742079415599 75240791622154113119123399)
    ·
      refine ⟨112861187433231169678685099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75240791622154113119123399 112861187433231169678685099)
      ·
        refine ⟨169291781149846754518027649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112861187433231169678685099 169291781149846754518027649)
        ·
          refine ⟨126968835862385065888520737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169291781149846754518027649 126968835862385065888520737)
          ·
            refine ⟨95226626896788799416390553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126968835862385065888520737 95226626896788799416390553)
            ·
              refine ⟨71419970172591599562292915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95226626896788799416390553 71419970172591599562292915)
              ·
                refine ⟨107129955258887399343439373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71419970172591599562292915 107129955258887399343439373)
                ·
                  refine ⟨40173733222082774753789765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107129955258887399343439373 40173733222082774753789765)
                  ·
                    refine ⟨7532574979140520266335581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40173733222082774753789765 7532574979140520266335581)
                    ·
                      refine ⟨2824715617177695099875843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7532574979140520266335581 2824715617177695099875843)
                      ·
                        rfl

theorem cell23_5501114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_5501114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501114 prefixEnd_5501114 := by exact prefixLift 5501114
  have htrace : WordTrace (prefixWord ++ tailWord_5501114) baseStart_5501114 baseEnd_5501114 := by
    simpa [prefixWord, tailWord_5501114, baseEnd_5501114] using wordTrace_append hprefix tailTrace_5501114
  have hstable : (prefixWord ++ tailWord_5501114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501114).length < 2 ^ (prefixWord ++ tailWord_5501114).sum := by decide
  have hdescent : baseEnd_5501114 < baseStart_5501114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501131 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 3]
def baseStart_5501131 : Nat := 118140960795 + 5501131 * 2 ^ 59
def prefixEnd_5501131 : Nat := 4983230072969 + 3 ^ 40 * 5501131 * 2
def baseEnd_5501131 : Nat := 2824724346348821533363265

theorem tailTrace_5501131 : CollatzResearch.WordTrace tailWord_5501131 prefixEnd_5501131 2824724346348821533363265 := by
  unfold tailWord_5501131
  simp only [CollatzResearch.WordTrace]
  refine ⟨200642731033349380221031247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133761820688899586814020831 200642731033349380221031247)
  ·
    refine ⟨300964096550024070331546871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200642731033349380221031247 300964096550024070331546871)
    ·
      refine ⟨451446144825036105497320307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300964096550024070331546871 451446144825036105497320307)
      ·
        refine ⟨677169217237554158245980461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451446144825036105497320307 677169217237554158245980461)
        ·
          refine ⟨253938456464082809342242673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 677169217237554158245980461 253938456464082809342242673)
          ·
            refine ⟨190453842348062107006682005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253938456464082809342242673 190453842348062107006682005)
            ·
              refine ⟨8927523860065411265938219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 190453842348062107006682005 8927523860065411265938219)
              ·
                refine ⟨13391285790098116898907329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8927523860065411265938219 13391285790098116898907329)
                ·
                  refine ⟨10043464342573587674180497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13391285790098116898907329 10043464342573587674180497)
                  ·
                    refine ⟨7532598256930190755635373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10043464342573587674180497 7532598256930190755635373)
                    ·
                      refine ⟨2824724346348821533363265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7532598256930190755635373 2824724346348821533363265)
                      ·
                        rfl

theorem cell23_5501131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 3].length) (baseStart_5501131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501131 prefixEnd_5501131 := by exact prefixLift 5501131
  have htrace : WordTrace (prefixWord ++ tailWord_5501131) baseStart_5501131 baseEnd_5501131 := by
    simpa [prefixWord, tailWord_5501131, baseEnd_5501131] using wordTrace_append hprefix tailTrace_5501131
  have hstable : (prefixWord ++ tailWord_5501131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501131).length < 2 ^ (prefixWord ++ tailWord_5501131).sum := by decide
  have hdescent : baseEnd_5501131 < baseStart_5501131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501164 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_5501164 : Nat := 118140960795 + 5501164 * 2 ^ 59
def prefixEnd_5501164 : Nat := 4983230072969 + 3 ^ 40 * 5501164 * 2
def baseEnd_5501164 : Nat := 941580430403473301416871

theorem tailTrace_5501164 : CollatzResearch.WordTrace tailWord_5501164 prefixEnd_5501164 941580430403473301416871 := by
  unfold tailWord_5501164
  simp only [CollatzResearch.WordTrace]
  refine ⟨100321967321114913428491273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133762623094819884571321697 100321967321114913428491273)
  ·
    refine ⟨75241475490836185071368455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100321967321114913428491273 75241475490836185071368455)
    ·
      refine ⟨112862213236254277607052683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75241475490836185071368455 112862213236254277607052683)
      ·
        refine ⟨169293319854381416410579025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112862213236254277607052683 169293319854381416410579025)
        ·
          refine ⟨126969989890786062307934269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169293319854381416410579025 126969989890786062307934269)
          ·
            refine ⟨47613746209044773365475351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126969989890786062307934269 47613746209044773365475351)
            ·
              refine ⟨71420619313567160048213027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47613746209044773365475351 71420619313567160048213027)
              ·
                refine ⟨107130928970350740072319541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71420619313567160048213027 107130928970350740072319541)
                ·
                  refine ⟨10043524590970381881779957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107130928970350740072319541 10043524590970381881779957)
                  ·
                    refine ⟨941580430403473301416871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10043524590970381881779957 941580430403473301416871)
                    ·
                      rfl

theorem cell23_5501164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_5501164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501164 prefixEnd_5501164 := by exact prefixLift 5501164
  have htrace : WordTrace (prefixWord ++ tailWord_5501164) baseStart_5501164 baseEnd_5501164 := by
    simpa [prefixWord, tailWord_5501164, baseEnd_5501164] using wordTrace_append hprefix tailTrace_5501164
  have hstable : (prefixWord ++ tailWord_5501164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501164).length < 2 ^ (prefixWord ++ tailWord_5501164).sum := by decide
  have hdescent : baseEnd_5501164 < baseStart_5501164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501171 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 1, 5, 2]
def baseStart_5501171 : Nat := 118140960795 + 5501171 * 2 ^ 59
def prefixEnd_5501171 : Nat := 4983230072969 + 3 ^ 40 * 5501171 * 2
def baseEnd_5501171 : Nat := 2824744885575001376863081

theorem tailTrace_5501171 : CollatzResearch.WordTrace tailWord_5501171 prefixEnd_5501171 2824744885575001376863081 := by
  unfold tailWord_5501171
  simp only [CollatzResearch.WordTrace]
  refine ⟨200644189953204467052487367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133762793302136311368324911 200644189953204467052487367)
  ·
    refine ⟨300966284929806700578731051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200644189953204467052487367 300966284929806700578731051)
    ·
      refine ⟨451449427394710050868096577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300966284929806700578731051 451449427394710050868096577)
      ·
        refine ⟨338587070546032538151072433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451449427394710050868096577 338587070546032538151072433)
        ·
          refine ⟨253940302909524403613304325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338587070546032538151072433 253940302909524403613304325)
          ·
            refine ⟨47613806795535825677494561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253940302909524403613304325 47613806795535825677494561)
            ·
              refine ⟨35710355096651869258120921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47613806795535825677494561 35710355096651869258120921)
              ·
                refine ⟨26782766322488901943590691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35710355096651869258120921 26782766322488901943590691)
                ·
                  refine ⟨40174149483733352915386037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26782766322488901943590691 40174149483733352915386037)
                  ·
                    refine ⟨3766326514100001835817441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40174149483733352915386037 3766326514100001835817441)
                    ·
                      refine ⟨2824744885575001376863081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3766326514100001835817441 2824744885575001376863081)
                      ·
                        rfl

theorem cell23_5501171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 5, 2].length) (baseStart_5501171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501171 prefixEnd_5501171 := by exact prefixLift 5501171
  have htrace : WordTrace (prefixWord ++ tailWord_5501171) baseStart_5501171 baseEnd_5501171 := by
    simpa [prefixWord, tailWord_5501171, baseEnd_5501171] using wordTrace_append hprefix tailTrace_5501171
  have hstable : (prefixWord ++ tailWord_5501171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501171).length < 2 ^ (prefixWord ++ tailWord_5501171).sum := by decide
  have hdescent : baseEnd_5501171 < baseStart_5501171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501178 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3]
def baseStart_5501178 : Nat := 118140960795 + 5501178 * 2 ^ 59
def prefixEnd_5501178 : Nat := 4983230072969 + 3 ^ 40 * 5501178 * 2
def baseEnd_5501178 : Nat := 2824748479939582849475549

theorem tailTrace_5501178 : CollatzResearch.WordTrace tailWord_5501178 prefixEnd_5501178 2824748479939582849475549 := by
  unfold tailWord_5501178
  simp only [CollatzResearch.WordTrace]
  refine ⟨50161111316044776811998047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133762963509452738165328125 50161111316044776811998047)
  ·
    refine ⟨75241666974067165217997071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50161111316044776811998047 75241666974067165217997071)
    ·
      refine ⟨112862500461100747826995607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75241666974067165217997071 112862500461100747826995607)
      ·
        refine ⟨169293750691651121740493411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112862500461100747826995607 169293750691651121740493411)
        ·
          refine ⟨253940626037476682610740117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169293750691651121740493411 253940626037476682610740117)
          ·
            refine ⟨11903466845506719497378443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 253940626037476682610740117 11903466845506719497378443)
            ·
              refine ⟨17855200268260079246067665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11903466845506719497378443 17855200268260079246067665)
              ·
                refine ⟨13391400201195059434550749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17855200268260079246067665 13391400201195059434550749)
                ·
                  refine ⟨5021775075448147287956531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13391400201195059434550749 5021775075448147287956531)
                  ·
                    refine ⟨7532662613172220931934797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5021775075448147287956531 7532662613172220931934797)
                    ·
                      refine ⟨2824748479939582849475549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7532662613172220931934797 2824748479939582849475549)
                      ·
                        rfl

theorem cell23_5501178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_5501178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501178 prefixEnd_5501178 := by exact prefixLift 5501178
  have htrace : WordTrace (prefixWord ++ tailWord_5501178) baseStart_5501178 baseEnd_5501178 := by
    simpa [prefixWord, tailWord_5501178, baseEnd_5501178] using wordTrace_append hprefix tailTrace_5501178
  have hstable : (prefixWord ++ tailWord_5501178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501178).length < 2 ^ (prefixWord ++ tailWord_5501178).sum := by decide
  have hdescent : baseEnd_5501178 < baseStart_5501178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501195 : List Nat := [1, 1, 1, 1, 5, 2, 4, 3, 1, 1, 3]
def baseStart_5501195 : Nat := 118140960795 + 5501195 * 2 ^ 59
def prefixEnd_5501195 : Nat := 4983230072969 + 3 ^ 40 * 5501195 * 2
def baseEnd_5501195 : Nat := 2824757209110709282962971

theorem tailTrace_5501195 : CollatzResearch.WordTrace tailWord_5501195 prefixEnd_5501195 2824757209110709282962971 := by
  unfold tailWord_5501195
  simp only [CollatzResearch.WordTrace]
  refine ⟨200645065305117519151361039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133763376870078346100907359 200645065305117519151361039)
  ·
    refine ⟨300967597957676278727041559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200645065305117519151361039 300967597957676278727041559)
    ·
      refine ⟨451451396936514418090562339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300967597957676278727041559 451451396936514418090562339)
      ·
        refine ⟨677177095404771627135843509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451451396936514418090562339 677177095404771627135843509)
        ·
          refine ⟨63485352694197340043985329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 677177095404771627135843509 63485352694197340043985329)
          ·
            refine ⟨47614014520648005032988997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63485352694197340043985329 47614014520648005032988997)
            ·
              refine ⟨8927627722621500943685437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47614014520648005032988997 8927627722621500943685437)
              ·
                refine ⟨3347860395983062853882039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8927627722621500943685437 3347860395983062853882039)
                ·
                  refine ⟨5021790593974594280823059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3347860395983062853882039 5021790593974594280823059)
                  ·
                    refine ⟨7532685890961891421234589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5021790593974594280823059 7532685890961891421234589)
                    ·
                      refine ⟨2824757209110709282962971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7532685890961891421234589 2824757209110709282962971)
                      ·
                        rfl

theorem cell23_5501195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 1, 1, 3].length) (baseStart_5501195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501195 prefixEnd_5501195 := by exact prefixLift 5501195
  have htrace : WordTrace (prefixWord ++ tailWord_5501195) baseStart_5501195 baseEnd_5501195 := by
    simpa [prefixWord, tailWord_5501195, baseEnd_5501195] using wordTrace_append hprefix tailTrace_5501195
  have hstable : (prefixWord ++ tailWord_5501195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501195).length < 2 ^ (prefixWord ++ tailWord_5501195).sum := by decide
  have hdescent : baseEnd_5501195 < baseStart_5501195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501231 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 4]
def baseStart_5501231 : Nat := 118140960795 + 5501231 * 2 ^ 59
def prefixEnd_5501231 : Nat := 4983230072969 + 3 ^ 40 * 5501231 * 2
def baseEnd_5501231 : Nat := 2824775694414271142112805

theorem tailTrace_5501231 : CollatzResearch.WordTrace tailWord_5501231 prefixEnd_5501231 2824775694414271142112805 := by
  unfold tailWord_5501231
  simp only [CollatzResearch.WordTrace]
  refine ⟨200646378332987097299671547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133764252221991398199781031 200646378332987097299671547)
  ·
    refine ⟨300969567499480645949507321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200646378332987097299671547 300969567499480645949507321)
    ·
      refine ⟨225727175624610484462130491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300969567499480645949507321 225727175624610484462130491)
      ·
        refine ⟨338590763436915726693195737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225727175624610484462130491 338590763436915726693195737)
        ·
          refine ⟨253943072577686795019896803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338590763436915726693195737 253943072577686795019896803)
          ·
            refine ⟨380914608866530192529845205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253943072577686795019896803 380914608866530192529845205)
            ·
              refine ⟨8927686145309301387418247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 380914608866530192529845205 8927686145309301387418247)
              ·
                refine ⟨13391529217963952081127371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8927686145309301387418247 13391529217963952081127371)
                ·
                  refine ⟨20087293826945928121691057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13391529217963952081127371 20087293826945928121691057)
                  ·
                    refine ⟨15065470370209446091268293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20087293826945928121691057 15065470370209446091268293)
                    ·
                      refine ⟨2824775694414271142112805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15065470370209446091268293 2824775694414271142112805)
                      ·
                        rfl

theorem cell23_5501231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 4].length) (baseStart_5501231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501231 prefixEnd_5501231 := by exact prefixLift 5501231
  have htrace : WordTrace (prefixWord ++ tailWord_5501231) baseStart_5501231 baseEnd_5501231 := by
    simpa [prefixWord, tailWord_5501231, baseEnd_5501231] using wordTrace_append hprefix tailTrace_5501231
  have hstable : (prefixWord ++ tailWord_5501231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501231).length < 2 ^ (prefixWord ++ tailWord_5501231).sum := by decide
  have hdescent : baseEnd_5501231 < baseStart_5501231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501241 : List Nat := [1, 2, 1, 6, 1, 2, 1, 9]
def baseStart_5501241 : Nat := 118140960795 + 5501241 * 2 ^ 59
def prefixEnd_5501241 : Nat := 4983230072969 + 3 ^ 40 * 5501241 * 2
def baseEnd_5501241 : Nat := 104621512193363559369917

theorem tailTrace_5501241 : CollatzResearch.WordTrace tailWord_5501241 prefixEnd_5501241 104621512193363559369917 := by
  unfold tailWord_5501241
  simp only [CollatzResearch.WordTrace]
  refine ⟨200646743062950869007535577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133764495375300579338357051 200646743062950869007535577)
  ·
    refine ⟨150485057297213151755651683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200646743062950869007535577 150485057297213151755651683)
    ·
      refine ⟨225727585945819727633477525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150485057297213151755651683 225727585945819727633477525)
      ·
        refine ⟨10580980591210299732819259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 225727585945819727633477525 10580980591210299732819259)
        ·
          refine ⟨15871470886815449599228889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10580980591210299732819259 15871470886815449599228889)
          ·
            refine ⟨11903603165111587199421667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15871470886815449599228889 11903603165111587199421667)
            ·
              refine ⟨17855404747667380799132501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11903603165111587199421667 17855404747667380799132501)
              ·
                refine ⟨104621512193363559369917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17855404747667380799132501 104621512193363559369917)
                ·
                  rfl

theorem cell23_5501241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 9].length) (baseStart_5501241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501241 prefixEnd_5501241 := by exact prefixLift 5501241
  have htrace : WordTrace (prefixWord ++ tailWord_5501241) baseStart_5501241 baseEnd_5501241 := by
    simpa [prefixWord, tailWord_5501241, baseEnd_5501241] using wordTrace_append hprefix tailTrace_5501241
  have hstable : (prefixWord ++ tailWord_5501241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501241).length < 2 ^ (prefixWord ++ tailWord_5501241).sum := by decide
  have hdescent : baseEnd_5501241 < baseStart_5501241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501251 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 3]
def baseStart_5501251 : Nat := 118140960795 + 5501251 * 2 ^ 59
def prefixEnd_5501251 : Nat := 4983230072969 + 3 ^ 40 * 5501251 * 2
def baseEnd_5501251 : Nat := 2824785964027361063862713

theorem tailTrace_5501251 : CollatzResearch.WordTrace tailWord_5501251 prefixEnd_5501251 2824785964027361063862713 := by
  unfold tailWord_5501251
  simp only [CollatzResearch.WordTrace]
  refine ⟨200647107792914640715399607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133764738528609760476933071 200647107792914640715399607)
  ·
    refine ⟨300970661689371961073099411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200647107792914640715399607 300970661689371961073099411)
    ·
      refine ⟨451455992534057941609649117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300970661689371961073099411 451455992534057941609649117)
      ·
        refine ⟨169295997200271728103618419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451455992534057941609649117 169295997200271728103618419)
        ·
          refine ⟨253943995800407592155427629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169295997200271728103618419 253943995800407592155427629)
          ·
            refine ⟨95228998425152847058285361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253943995800407592155427629 95228998425152847058285361)
            ·
              refine ⟨71421748818864635293714021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95228998425152847058285361 71421748818864635293714021)
              ·
                refine ⟨13391577903537119117571379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71421748818864635293714021 13391577903537119117571379)
                ·
                  refine ⟨20087366855305678676357069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13391577903537119117571379 20087366855305678676357069)
                  ·
                    refine ⟨7532762570739629503633901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20087366855305678676357069 7532762570739629503633901)
                    ·
                      refine ⟨2824785964027361063862713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7532762570739629503633901 2824785964027361063862713)
                      ·
                        rfl

theorem cell23_5501251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_5501251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501251 prefixEnd_5501251 := by exact prefixLift 5501251
  have htrace : WordTrace (prefixWord ++ tailWord_5501251) baseStart_5501251 baseEnd_5501251 := by
    simpa [prefixWord, tailWord_5501251, baseEnd_5501251] using wordTrace_append hprefix tailTrace_5501251
  have hstable : (prefixWord ++ tailWord_5501251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501251).length < 2 ^ (prefixWord ++ tailWord_5501251).sum := by decide
  have hdescent : baseEnd_5501251 < baseStart_5501251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501269 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 3, 2, 2]
def baseStart_5501269 : Nat := 118140960795 + 5501269 * 2 ^ 59
def prefixEnd_5501269 : Nat := 4983230072969 + 3 ^ 40 * 5501269 * 2
def baseEnd_5501269 : Nat := 2824795206679141993437631

theorem tailTrace_5501269 : CollatzResearch.WordTrace tailWord_5501269 prefixEnd_5501269 2824795206679141993437631 := by
  unfold tailWord_5501269
  simp only [CollatzResearch.WordTrace]
  refine ⟨200647764306849429789554861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133765176204566286526369907 200647764306849429789554861)
  ·
    refine ⟨75242911615068536171083073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200647764306849429789554861 75242911615068536171083073)
    ·
      refine ⟨56432183711301402128312305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75242911615068536171083073 56432183711301402128312305)
      ·
        refine ⟨42324137783476051596234229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56432183711301402128312305 42324137783476051596234229)
        ·
          refine ⟨3967887917200879837146959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42324137783476051596234229 3967887917200879837146959)
          ·
            refine ⟨5951831875801319755720439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967887917200879837146959 5951831875801319755720439)
            ·
              refine ⟨8927747813701979633580659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5951831875801319755720439 8927747813701979633580659)
              ·
                refine ⟨13391621720552969450370989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8927747813701979633580659 13391621720552969450370989)
                ·
                  refine ⟨5021858145207363543889121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13391621720552969450370989 5021858145207363543889121)
                  ·
                    refine ⟨3766393608905522657916841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5021858145207363543889121 3766393608905522657916841)
                    ·
                      refine ⟨2824795206679141993437631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3766393608905522657916841 2824795206679141993437631)
                      ·
                        rfl

theorem cell23_5501269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_5501269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501269 prefixEnd_5501269 := by exact prefixLift 5501269
  have htrace : WordTrace (prefixWord ++ tailWord_5501269) baseStart_5501269 baseEnd_5501269 := by
    simpa [prefixWord, tailWord_5501269, baseEnd_5501269] using wordTrace_append hprefix tailTrace_5501269
  have hstable : (prefixWord ++ tailWord_5501269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501269).length < 2 ^ (prefixWord ++ tailWord_5501269).sum := by decide
  have hdescent : baseEnd_5501269 < baseStart_5501269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501285 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 2, 1, 3]
def baseStart_5501285 : Nat := 118140960795 + 5501285 * 2 ^ 59
def prefixEnd_5501285 : Nat := 4983230072969 + 3 ^ 40 * 5501285 * 2
def baseEnd_5501285 : Nat := 2824803422369613930837557

theorem tailTrace_5501285 : CollatzResearch.WordTrace tailWord_5501285 prefixEnd_5501285 2824803422369613930837557 := by
  unfold tailWord_5501285
  simp only [CollatzResearch.WordTrace]
  refine ⟨200648347874791464522137309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133765565249860976348091539 200648347874791464522137309)
  ·
    refine ⟨75243130453046799195801491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200648347874791464522137309 75243130453046799195801491)
    ·
      refine ⟨112864695679570198793702237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75243130453046799195801491 112864695679570198793702237)
      ·
        refine ⟨42324260879838824547638339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112864695679570198793702237 42324260879838824547638339)
        ·
          refine ⟨63486391319758236821457509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42324260879838824547638339 63486391319758236821457509)
          ·
            refine ⟨11903698372454669404023283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63486391319758236821457509 11903698372454669404023283)
            ·
              refine ⟨17855547558682004106034925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11903698372454669404023283 17855547558682004106034925)
              ·
                refine ⟨6695830334505751539763097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17855547558682004106034925 6695830334505751539763097)
                ·
                  refine ⟨5021872750879313654822323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6695830334505751539763097 5021872750879313654822323)
                  ·
                    refine ⟨7532809126318970482233485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5021872750879313654822323 7532809126318970482233485)
                    ·
                      refine ⟨2824803422369613930837557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7532809126318970482233485 2824803422369613930837557)
                      ·
                        rfl

theorem cell23_5501285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_5501285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501285 prefixEnd_5501285 := by exact prefixLift 5501285
  have htrace : WordTrace (prefixWord ++ tailWord_5501285) baseStart_5501285 baseEnd_5501285 := by
    simpa [prefixWord, tailWord_5501285, baseEnd_5501285] using wordTrace_append hprefix tailTrace_5501285
  have hstable : (prefixWord ++ tailWord_5501285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501285).length < 2 ^ (prefixWord ++ tailWord_5501285).sum := by decide
  have hdescent : baseEnd_5501285 < baseStart_5501285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501302 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5501302 : Nat := 118140960795 + 5501302 * 2 ^ 59
def prefixEnd_5501302 : Nat := 4983230072969 + 3 ^ 40 * 5501302 * 2
def baseEnd_5501302 : Nat := 2824812151540740364324979

theorem tailTrace_5501302 : CollatzResearch.WordTrace tailWord_5501302 prefixEnd_5501302 2824812151540740364324979 := by
  unfold tailWord_5501302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12540560494733117276594135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133765978610486584283670773 12540560494733117276594135)
  ·
    refine ⟨18810840742099675914891203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12540560494733117276594135 18810840742099675914891203)
    ·
      refine ⟨28216261113149513872336805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18810840742099675914891203 28216261113149513872336805)
      ·
        refine ⟨5290548958715533851063151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28216261113149513872336805 5290548958715533851063151)
        ·
          refine ⟨7935823438073300776594727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5290548958715533851063151 7935823438073300776594727)
          ·
            refine ⟨11903735157109951164892091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7935823438073300776594727 11903735157109951164892091)
            ·
              refine ⟨17855602735664926747338137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11903735157109951164892091 17855602735664926747338137)
              ·
                refine ⟨13391702051748695060503603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17855602735664926747338137 13391702051748695060503603)
                ·
                  refine ⟨20087553077623042590755405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13391702051748695060503603 20087553077623042590755405)
                  ·
                    refine ⟨7532832404108640971533277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20087553077623042590755405 7532832404108640971533277)
                    ·
                      refine ⟨2824812151540740364324979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7532832404108640971533277 2824812151540740364324979)
                      ·
                        rfl

theorem cell23_5501302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5501302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501302 prefixEnd_5501302 := by exact prefixLift 5501302
  have htrace : WordTrace (prefixWord ++ tailWord_5501302) baseStart_5501302 baseEnd_5501302 := by
    simpa [prefixWord, tailWord_5501302, baseEnd_5501302] using wordTrace_append hprefix tailTrace_5501302
  have hstable : (prefixWord ++ tailWord_5501302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501302).length < 2 ^ (prefixWord ++ tailWord_5501302).sum := by decide
  have hdescent : baseEnd_5501302 < baseStart_5501302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501338 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_5501338 : Nat := 118140960795 + 5501338 * 2 ^ 59
def prefixEnd_5501338 : Nat := 4983230072969 + 3 ^ 40 * 5501338 * 2
def baseEnd_5501338 : Nat := 2824830636844302223474813

theorem tailTrace_5501338 : CollatzResearch.WordTrace tailWord_5501338 prefixEnd_5501338 2824830636844302223474813 := by
  unfold tailWord_5501338
  simp only [CollatzResearch.WordTrace]
  refine ⟨50162570235899863643454167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133766853962399636382544445 50162570235899863643454167)
  ·
    refine ⟨75243855353849795465181251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50162570235899863643454167 75243855353849795465181251)
    ·
      refine ⟨112865783030774693197771877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75243855353849795465181251 112865783030774693197771877)
      ·
        refine ⟨21162334318270254974582227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112865783030774693197771877 21162334318270254974582227)
        ·
          refine ⟨31743501477405382461873341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21162334318270254974582227 31743501477405382461873341)
          ·
            refine ⟨11903813054027018423202503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31743501477405382461873341 11903813054027018423202503)
            ·
              refine ⟨17855719581040527634803755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11903813054027018423202503 17855719581040527634803755)
              ·
                refine ⟨26783579371560791452205633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17855719581040527634803755 26783579371560791452205633)
                ·
                  refine ⟨20087684528670593589154225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26783579371560791452205633 20087684528670593589154225)
                  ·
                    refine ⟨15065763396502945191865669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20087684528670593589154225 15065763396502945191865669)
                    ·
                      refine ⟨2824830636844302223474813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15065763396502945191865669 2824830636844302223474813)
                      ·
                        rfl

theorem cell23_5501338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_5501338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501338 prefixEnd_5501338 := by exact prefixLift 5501338
  have htrace : WordTrace (prefixWord ++ tailWord_5501338) baseStart_5501338 baseEnd_5501338 := by
    simpa [prefixWord, tailWord_5501338, baseEnd_5501338] using wordTrace_append hprefix tailTrace_5501338
  have hstable : (prefixWord ++ tailWord_5501338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501338).length < 2 ^ (prefixWord ++ tailWord_5501338).sum := by decide
  have hdescent : baseEnd_5501338 < baseStart_5501338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501342 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_5501342 : Nat := 118140960795 + 5501342 * 2 ^ 59
def prefixEnd_5501342 : Nat := 4983230072969 + 3 ^ 40 * 5501342 * 2
def baseEnd_5501342 : Nat := 2824832690766920207824795

theorem tailTrace_5501342 : CollatzResearch.WordTrace tailWord_5501342 prefixEnd_5501342 2824832690766920207824795 := by
  unfold tailWord_5501342
  simp only [CollatzResearch.WordTrace]
  refine ⟨25081303354448120407120285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133766951223723308837974853 25081303354448120407120285)
  ·
    refine ⟨9405488757918045152670107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25081303354448120407120285 9405488757918045152670107)
    ·
      refine ⟨14108233136877067729005161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9405488757918045152670107 14108233136877067729005161)
      ·
        refine ⟨10581174852657800796753871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14108233136877067729005161 10581174852657800796753871)
        ·
          refine ⟨15871762278986701195130807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10581174852657800796753871 15871762278986701195130807)
          ·
            refine ⟨23807643418480051792696211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15871762278986701195130807 23807643418480051792696211)
            ·
              refine ⟨35711465127720077689044317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23807643418480051792696211 35711465127720077689044317)
              ·
                refine ⟨13391799422895029133391619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35711465127720077689044317 13391799422895029133391619)
                ·
                  refine ⟨20087699134342543700087429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13391799422895029133391619 20087699134342543700087429)
                  ·
                    refine ⟨3766443587689226943766393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20087699134342543700087429 3766443587689226943766393)
                    ·
                      refine ⟨2824832690766920207824795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3766443587689226943766393 2824832690766920207824795)
                      ·
                        rfl

theorem cell23_5501342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_5501342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501342 prefixEnd_5501342 := by exact prefixLift 5501342
  have htrace : WordTrace (prefixWord ++ tailWord_5501342) baseStart_5501342 baseEnd_5501342 := by
    simpa [prefixWord, tailWord_5501342, baseEnd_5501342] using wordTrace_append hprefix tailTrace_5501342
  have hstable : (prefixWord ++ tailWord_5501342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501342).length < 2 ^ (prefixWord ++ tailWord_5501342).sum := by decide
  have hdescent : baseEnd_5501342 < baseStart_5501342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501408 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 3, 4]
def baseStart_5501408 : Nat := 118140960795 + 5501408 * 2 ^ 59
def prefixEnd_5501408 : Nat := 4983230072969 + 3 ^ 40 * 5501408 * 2
def baseEnd_5501408 : Nat := 941622193496705649866497

theorem tailTrace_5501408 : CollatzResearch.WordTrace tailWord_5501408 prefixEnd_5501408 941622193496705649866497 := by
  unfold tailWord_5501408
  simp only [CollatzResearch.WordTrace]
  refine ⟨100326417026672928264432439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133768556035563904352576585 100326417026672928264432439)
  ·
    refine ⟨150489625540009392396648659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100326417026672928264432439 150489625540009392396648659)
    ·
      refine ⟨225734438310014088594972989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150489625540009392396648659 225734438310014088594972989)
      ·
        refine ⟨84650414366255283223114871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225734438310014088594972989 84650414366255283223114871)
        ·
          refine ⟨126975621549382924834672307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84650414366255283223114871 126975621549382924834672307)
          ·
            refine ⟨190463432324074387252008461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126975621549382924834672307 190463432324074387252008461)
            ·
              refine ⟨71423787121527895219503173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190463432324074387252008461 71423787121527895219503173)
              ·
                refine ⟨13391960085286480353656845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71423787121527895219503173 13391960085286480353656845)
                ·
                  refine ⟨5021985031982430132621317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13391960085286480353656845 5021985031982430132621317)
                  ·
                    refine ⟨941622193496705649866497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5021985031982430132621317 941622193496705649866497)
                    ·
                      rfl

theorem cell23_5501408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3, 4].length) (baseStart_5501408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501408 prefixEnd_5501408 := by exact prefixLift 5501408
  have htrace : WordTrace (prefixWord ++ tailWord_5501408) baseStart_5501408 baseEnd_5501408 := by
    simpa [prefixWord, tailWord_5501408, baseEnd_5501408] using wordTrace_append hprefix tailTrace_5501408
  have hstable : (prefixWord ++ tailWord_5501408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501408).length < 2 ^ (prefixWord ++ tailWord_5501408).sum := by decide
  have hdescent : baseEnd_5501408 < baseStart_5501408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501505 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_5501505 : Nat := 118140960795 + 5501505 * 2 ^ 59
def prefixEnd_5501505 : Nat := 4983230072969 + 3 ^ 40 * 5501505 * 2
def baseEnd_5501505 : Nat := 2824916388113603070086545

theorem tailTrace_5501505 : CollatzResearch.WordTrace tailWord_5501505 prefixEnd_5501505 2824916388113603070086545 := by
  unfold tailWord_5501505
  simp only [CollatzResearch.WordTrace]
  refine ⟨200656371933994442095145969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133770914622662961396763979 200656371933994442095145969)
  ·
    refine ⟨150492278950495831571359477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200656371933994442095145969 150492278950495831571359477)
    ·
      refine ⟨14108651151608984209814951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150492278950495831571359477 14108651151608984209814951)
      ·
        refine ⟨21162976727413476314722427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14108651151608984209814951 21162976727413476314722427)
        ·
          refine ⟨31744465091120214472083641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21162976727413476314722427 31744465091120214472083641)
          ·
            refine ⟨23808348818340160854062731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31744465091120214472083641 23808348818340160854062731)
            ·
              refine ⟨35712523227510241281094097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23808348818340160854062731 35712523227510241281094097)
              ·
                refine ⟨26784392420632680960820573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35712523227510241281094097 26784392420632680960820573)
                ·
                  refine ⟨10044147157737255360307715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26784392420632680960820573 10044147157737255360307715)
                  ·
                    refine ⟨15066220736605883040461573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10044147157737255360307715 15066220736605883040461573)
                    ·
                      refine ⟨2824916388113603070086545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15066220736605883040461573 2824916388113603070086545)
                      ·
                        rfl

theorem cell23_5501505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_5501505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501505 prefixEnd_5501505 := by exact prefixLift 5501505
  have htrace : WordTrace (prefixWord ++ tailWord_5501505) baseStart_5501505 baseEnd_5501505 := by
    simpa [prefixWord, tailWord_5501505, baseEnd_5501505] using wordTrace_append hprefix tailTrace_5501505
  have hstable : (prefixWord ++ tailWord_5501505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501505).length < 2 ^ (prefixWord ++ tailWord_5501505).sum := by decide
  have hdescent : baseEnd_5501505 < baseStart_5501505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501515 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 2, 4]
def baseStart_5501515 : Nat := 118140960795 + 5501515 * 2 ^ 59
def prefixEnd_5501515 : Nat := 4983230072969 + 3 ^ 40 * 5501515 * 2
def baseEnd_5501515 : Nat := 941640507640049343653833

theorem tailTrace_5501515 : CollatzResearch.WordTrace tailWord_5501515 prefixEnd_5501515 941640507640049343653833 := by
  unfold tailWord_5501515
  simp only [CollatzResearch.WordTrace]
  refine ⟨200656736663958213803009999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133771157775972142535339999 200656736663958213803009999)
  ·
    refine ⟨300985104995937320704514999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200656736663958213803009999 300985104995937320704514999)
    ·
      refine ⟨451477657493905981056772499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300985104995937320704514999 451477657493905981056772499)
      ·
        refine ⟨677216486240858971585158749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451477657493905981056772499 677216486240858971585158749)
        ·
          refine ⟨253956182340322114344434531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 677216486240858971585158749 253956182340322114344434531)
          ·
            refine ⟨380934273510483171516651797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253956182340322114344434531 380934273510483171516651797)
            ·
              refine ⟨17856294070803898664843053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 380934273510483171516651797 17856294070803898664843053)
              ·
                refine ⟨6696110276551461999316145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17856294070803898664843053 6696110276551461999316145)
                ·
                  refine ⟨5022082707413596499487109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6696110276551461999316145 5022082707413596499487109)
                  ·
                    refine ⟨941640507640049343653833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5022082707413596499487109 941640507640049343653833)
                    ·
                      rfl

theorem cell23_5501515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 4].length) (baseStart_5501515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501515 prefixEnd_5501515 := by exact prefixLift 5501515
  have htrace : WordTrace (prefixWord ++ tailWord_5501515) baseStart_5501515 baseEnd_5501515 := by
    simpa [prefixWord, tailWord_5501515, baseEnd_5501515] using wordTrace_append hprefix tailTrace_5501515
  have hstable : (prefixWord ++ tailWord_5501515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501515).length < 2 ^ (prefixWord ++ tailWord_5501515).sum := by decide
  have hdescent : baseEnd_5501515 < baseStart_5501515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501518 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_5501518 : Nat := 118140960795 + 5501518 * 2 ^ 59
def prefixEnd_5501518 : Nat := 4983230072969 + 3 ^ 40 * 5501518 * 2
def baseEnd_5501518 : Nat := 2824923063362111519223985

theorem tailTrace_5501518 : CollatzResearch.WordTrace tailWord_5501518 prefixEnd_5501518 2824923063362111519223985 := by
  unfold tailWord_5501518
  simp only [CollatzResearch.WordTrace]
  refine ⟨25082105760368418164421151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133771230721964896876912805 25082105760368418164421151)
  ·
    refine ⟨37623158640552627246631727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25082105760368418164421151 37623158640552627246631727)
    ·
      refine ⟨56434737960828940869947591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37623158640552627246631727 56434737960828940869947591)
      ·
        refine ⟨84652106941243411304921387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56434737960828940869947591 84652106941243411304921387)
        ·
          refine ⟨126978160411865116957382081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84652106941243411304921387 126978160411865116957382081)
          ·
            refine ⟨95233620308898837718036561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126978160411865116957382081 95233620308898837718036561)
            ·
              refine ⟨71425215231674128288527421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95233620308898837718036561 71425215231674128288527421)
              ·
                refine ⟨26784455711877798108197783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71425215231674128288527421 26784455711877798108197783)
                ·
                  refine ⟨40176683567816697162296675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26784455711877798108197783 40176683567816697162296675)
                  ·
                    refine ⟨60265025351725045743445013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40176683567816697162296675 60265025351725045743445013)
                    ·
                      refine ⟨2824923063362111519223985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60265025351725045743445013 2824923063362111519223985)
                      ·
                        rfl

theorem cell23_5501518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_5501518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501518 prefixEnd_5501518 := by exact prefixLift 5501518
  have htrace : WordTrace (prefixWord ++ tailWord_5501518) baseStart_5501518 baseEnd_5501518 := by
    simpa [prefixWord, tailWord_5501518, baseEnd_5501518] using wordTrace_append hprefix tailTrace_5501518
  have hstable : (prefixWord ++ tailWord_5501518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501518).length < 2 ^ (prefixWord ++ tailWord_5501518).sum := by decide
  have hdescent : baseEnd_5501518 < baseStart_5501518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501525 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_5501525 : Nat := 118140960795 + 5501525 * 2 ^ 59
def prefixEnd_5501525 : Nat := 4983230072969 + 3 ^ 40 * 5501525 * 2
def baseEnd_5501525 : Nat := 2824926657726692991836453

theorem tailTrace_5501525 : CollatzResearch.WordTrace tailWord_5501525 prefixEnd_5501525 2824926657726692991836453 := by
  unfold tailWord_5501525
  simp only [CollatzResearch.WordTrace]
  refine ⟨200657101393921985510874029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133771400929281323673916019 200657101393921985510874029)
  ·
    refine ⟨75246413022720744566577761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200657101393921985510874029 75246413022720744566577761)
    ·
      refine ⟨56434809767040558424933321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75246413022720744566577761 56434809767040558424933321)
      ·
        refine ⟨42326107325280418818699991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56434809767040558424933321 42326107325280418818699991)
        ·
          refine ⟨63489160987920628228049987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42326107325280418818699991 63489160987920628228049987)
          ·
            refine ⟨95233741481880942342074981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63489160987920628228049987 95233741481880942342074981)
            ·
              refine ⟨17856326527852676689139059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95233741481880942342074981 17856326527852676689139059)
              ·
                refine ⟨26784489791779015033708589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17856326527852676689139059 26784489791779015033708589)
                ·
                  refine ⟨10044183671917130637640721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26784489791779015033708589 10044183671917130637640721)
                  ·
                    refine ⟨7533137753937847978230541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10044183671917130637640721 7533137753937847978230541)
                    ·
                      refine ⟨2824926657726692991836453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7533137753937847978230541 2824926657726692991836453)
                      ·
                        rfl

theorem cell23_5501525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_5501525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501525 prefixEnd_5501525 := by exact prefixLift 5501525
  have htrace : WordTrace (prefixWord ++ tailWord_5501525) baseStart_5501525 baseEnd_5501525 := by
    simpa [prefixWord, tailWord_5501525, baseEnd_5501525] using wordTrace_append hprefix tailTrace_5501525
  have hstable : (prefixWord ++ tailWord_5501525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501525).length < 2 ^ (prefixWord ++ tailWord_5501525).sum := by decide
  have hdescent : baseEnd_5501525 < baseStart_5501525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501549 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_5501549 : Nat := 118140960795 + 5501549 * 2 ^ 59
def prefixEnd_5501549 : Nat := 4983230072969 + 3 ^ 40 * 5501549 * 2
def baseEnd_5501549 : Nat := 941646327087466965978781

theorem tailTrace_5501549 : CollatzResearch.WordTrace tailWord_5501549 prefixEnd_5501549 941646327087466965978781 := by
  unfold tailWord_5501549
  simp only [CollatzResearch.WordTrace]
  refine ⟨200657976745835037609747701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133771984497223358406498467 200657976745835037609747701)
  ·
    refine ⟨18811685319922034775913847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200657976745835037609747701 18811685319922034775913847)
    ·
      refine ⟨28217527979883052163870771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18811685319922034775913847 28217527979883052163870771)
      ·
        refine ⟨42326291969824578245806157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28217527979883052163870771 42326291969824578245806157)
        ·
          refine ⟨15872359488684216842177309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42326291969824578245806157 15872359488684216842177309)
          ·
            refine ⟨5952134808256581315816491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15872359488684216842177309 5952134808256581315816491)
            ·
              refine ⟨8928202212384871973724737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5952134808256581315816491 8928202212384871973724737)
              ·
                refine ⟨6696151659288653980293553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8928202212384871973724737 6696151659288653980293553)
                ·
                  refine ⟨5022113744466490485220165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6696151659288653980293553 5022113744466490485220165)
                  ·
                    refine ⟨941646327087466965978781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5022113744466490485220165 941646327087466965978781)
                    ·
                      rfl

theorem cell23_5501549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_5501549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501549 prefixEnd_5501549 := by exact prefixLift 5501549
  have htrace : WordTrace (prefixWord ++ tailWord_5501549) baseStart_5501549 baseEnd_5501549 := by
    simpa [prefixWord, tailWord_5501549, baseEnd_5501549] using wordTrace_append hprefix tailTrace_5501549
  have hstable : (prefixWord ++ tailWord_5501549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501549).length < 2 ^ (prefixWord ++ tailWord_5501549).sum := by decide
  have hdescent : baseEnd_5501549 < baseStart_5501549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501572 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_5501572 : Nat := 118140960795 + 5501572 * 2 ^ 59
def prefixEnd_5501572 : Nat := 4983230072969 + 3 ^ 40 * 5501572 * 2
def baseEnd_5501572 : Nat := 2824950791317454307948737

theorem tailTrace_5501572 : CollatzResearch.WordTrace tailWord_5501572 prefixEnd_5501572 2824950791317454307948737 := by
  unfold tailWord_5501572
  simp only [CollatzResearch.WordTrace]
  refine ⟨100329407812375856268917485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133772543749834475025223313 100329407812375856268917485)
  ·
    refine ⟨37623527929640946100844057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100329407812375856268917485 37623527929640946100844057)
    ·
      refine ⟨28217645947230709575633043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37623527929640946100844057 28217645947230709575633043)
      ·
        refine ⟨42326468920846064363449565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28217645947230709575633043 42326468920846064363449565)
        ·
          refine ⟨15872425845317274136293587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42326468920846064363449565 15872425845317274136293587)
          ·
            refine ⟨23808638767975911204440381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15872425845317274136293587 23808638767975911204440381)
            ·
              refine ⟨8928239537990966701665143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23808638767975911204440381 8928239537990966701665143)
              ·
                refine ⟨13392359306986450052497715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8928239537990966701665143 13392359306986450052497715)
                ·
                  refine ⟨20088538960479675078746573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13392359306986450052497715 20088538960479675078746573)
                  ·
                    refine ⟨7533202110179878154529965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20088538960479675078746573 7533202110179878154529965)
                    ·
                      refine ⟨2824950791317454307948737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7533202110179878154529965 2824950791317454307948737)
                      ·
                        rfl

theorem cell23_5501572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_5501572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501572 prefixEnd_5501572 := by exact prefixLift 5501572
  have htrace : WordTrace (prefixWord ++ tailWord_5501572) baseStart_5501572 baseEnd_5501572 := by
    simpa [prefixWord, tailWord_5501572, baseEnd_5501572] using wordTrace_append hprefix tailTrace_5501572
  have hstable : (prefixWord ++ tailWord_5501572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501572).length < 2 ^ (prefixWord ++ tailWord_5501572).sum := by decide
  have hdescent : baseEnd_5501572 < baseStart_5501572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501595 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 7, 4, 2]
def baseStart_5501595 : Nat := 118140960795 + 5501595 * 2 ^ 59
def prefixEnd_5501595 : Nat := 4983230072969 + 3 ^ 40 * 5501595 * 2
def baseEnd_5501595 : Nat := 2824962601372507717961131

theorem tailTrace_5501595 : CollatzResearch.WordTrace tailWord_5501595 prefixEnd_5501595 2824962601372507717961131 := by
  unfold tailWord_5501595
  simp only [CollatzResearch.WordTrace]
  refine ⟨200659654503668387465922239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133773103002445591643948159 200659654503668387465922239)
  ·
    refine ⟨300989481755502581198883359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200659654503668387465922239 300989481755502581198883359)
    ·
      refine ⟨451484222633253871798325039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300989481755502581198883359 451484222633253871798325039)
      ·
        refine ⟨677226333949880807697487559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451484222633253871798325039 677226333949880807697487559)
        ·
          refine ⟨1015839500924821211546231339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677226333949880807697487559 1015839500924821211546231339)
          ·
            refine ⟨1523759251387231817319347009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015839500924821211546231339 1523759251387231817319347009)
            ·
              refine ⟨1142819438540423862989510257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523759251387231817319347009 1142819438540423862989510257)
              ·
                refine ⟨857114578905317897242132693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142819438540423862989510257 857114578905317897242132693)
                ·
                  refine ⟨20088622943093388216612485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 857114578905317897242132693 20088622943093388216612485)
                  ·
                    refine ⟨3766616801830010290614841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20088622943093388216612485 3766616801830010290614841)
                    ·
                      refine ⟨2824962601372507717961131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3766616801830010290614841 2824962601372507717961131)
                      ·
                        rfl

theorem cell23_5501595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 4, 2].length) (baseStart_5501595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501595 prefixEnd_5501595 := by exact prefixLift 5501595
  have htrace : WordTrace (prefixWord ++ tailWord_5501595) baseStart_5501595 baseEnd_5501595 := by
    simpa [prefixWord, tailWord_5501595, baseEnd_5501595] using wordTrace_append hprefix tailTrace_5501595
  have hstable : (prefixWord ++ tailWord_5501595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501595).length < 2 ^ (prefixWord ++ tailWord_5501595).sum := by decide
  have hdescent : baseEnd_5501595 < baseStart_5501595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501623 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 2, 1, 3]
def baseStart_5501623 : Nat := 118140960795 + 5501623 * 2 ^ 59
def prefixEnd_5501623 : Nat := 4983230072969 + 3 ^ 40 * 5501623 * 2
def baseEnd_5501623 : Nat := 2824976978830833608411003

theorem tailTrace_5501623 : CollatzResearch.WordTrace tailWord_5501623 prefixEnd_5501623 2824976978830833608411003 := by
  unfold tailWord_5501623
  simp only [CollatzResearch.WordTrace]
  refine ⟨200660675747566948247941523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133773783831711298831961015 200660675747566948247941523)
  ·
    refine ⟨300991013621350422371912285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200660675747566948247941523 300991013621350422371912285)
    ·
      refine ⟨112871630108006408389467107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300991013621350422371912285 112871630108006408389467107)
      ·
        refine ⟨169307445162009612584200661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112871630108006408389467107 169307445162009612584200661)
        ·
          refine ⟨3968143245984600294942203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 169307445162009612584200661 3968143245984600294942203)
          ·
            refine ⟨5952214868976900442413305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3968143245984600294942203 5952214868976900442413305)
            ·
              refine ⟨4464161151732675331809979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5952214868976900442413305 4464161151732675331809979)
              ·
                refine ⟨6696241727599012997714969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4464161151732675331809979 6696241727599012997714969)
                ·
                  refine ⟨5022181295699259748286227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6696241727599012997714969 5022181295699259748286227)
                  ·
                    refine ⟨7533271943548889622429341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5022181295699259748286227 7533271943548889622429341)
                    ·
                      refine ⟨2824976978830833608411003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7533271943548889622429341 2824976978830833608411003)
                      ·
                        rfl

theorem cell23_5501623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 2, 1, 3].length) (baseStart_5501623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501623 prefixEnd_5501623 := by exact prefixLift 5501623
  have htrace : WordTrace (prefixWord ++ tailWord_5501623) baseStart_5501623 baseEnd_5501623 := by
    simpa [prefixWord, tailWord_5501623, baseEnd_5501623] using wordTrace_append hprefix tailTrace_5501623
  have hstable : (prefixWord ++ tailWord_5501623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501623).length < 2 ^ (prefixWord ++ tailWord_5501623).sum := by decide
  have hdescent : baseEnd_5501623 < baseStart_5501623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501648 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 5, 7]
def baseStart_5501648 : Nat := 118140960795 + 5501648 * 2 ^ 59
def prefixEnd_5501648 : Nat := 4983230072969 + 3 ^ 40 * 5501648 * 2
def baseEnd_5501648 : Nat := 941663271949065336866129

theorem tailTrace_5501648 : CollatzResearch.WordTrace tailWord_5501648 prefixEnd_5501648 941663271949065336866129 := by
  unfold tailWord_5501648
  simp only [CollatzResearch.WordTrace]
  refine ⟨100330793786238188758800799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133774391714984251678401065 100330793786238188758800799)
  ·
    refine ⟨150496190679357283138201199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100330793786238188758800799 150496190679357283138201199)
    ·
      refine ⟨225744286019035924707301799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150496190679357283138201199 225744286019035924707301799)
      ·
        refine ⟨338616429028553887060952699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225744286019035924707301799 338616429028553887060952699)
        ·
          refine ⟨507924643542830830591429049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338616429028553887060952699 507924643542830830591429049)
          ·
            refine ⟨380943482657123122943571787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507924643542830830591429049 380943482657123122943571787)
            ·
              refine ⟨571415223985684684415357681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380943482657123122943571787 571415223985684684415357681)
              ·
                refine ⟨428561417989263513311518261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 571415223985684684415357681 428561417989263513311518261)
                ·
                  refine ⟨40177632936493454372954837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428561417989263513311518261 40177632936493454372954837)
                  ·
                    refine ⟨941663271949065336866129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40177632936493454372954837 941663271949065336866129)
                    ·
                      rfl

theorem cell23_5501648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_5501648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501648 prefixEnd_5501648 := by exact prefixLift 5501648
  have htrace : WordTrace (prefixWord ++ tailWord_5501648) baseStart_5501648 baseEnd_5501648 := by
    simpa [prefixWord, tailWord_5501648, baseEnd_5501648] using wordTrace_append hprefix tailTrace_5501648
  have hstable : (prefixWord ++ tailWord_5501648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501648).length < 2 ^ (prefixWord ++ tailWord_5501648).sum := by decide
  have hdescent : baseEnd_5501648 < baseStart_5501648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501669 : List Nat := [1, 3, 1, 4, 1, 2, 4, 2, 5]
def baseStart_5501669 : Nat := 118140960795 + 5501669 * 2 ^ 59
def prefixEnd_5501669 : Nat := 4983230072969 + 3 ^ 40 * 5501669 * 2
def baseEnd_5501669 : Nat := 313888955437882269826199

theorem tailTrace_5501669 : CollatzResearch.WordTrace tailWord_5501669 prefixEnd_5501669 313888955437882269826199 := by
  unfold tailWord_5501669
  simp only [CollatzResearch.WordTrace]
  refine ⟨200662353505400298104116061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133774902336933532069410707 200662353505400298104116061)
  ·
    refine ⟨75248382564525111789043523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200662353505400298104116061 75248382564525111789043523)
    ·
      refine ⟨112872573846787667683565285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75248382564525111789043523 112872573846787667683565285)
      ·
        refine ⟨21163607596272687690668491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112872573846787667683565285 21163607596272687690668491)
        ·
          refine ⟨31745411394409031536002737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21163607596272687690668491 31745411394409031536002737)
          ·
            refine ⟨23809058545806773652002053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31745411394409031536002737 23809058545806773652002053)
            ·
              refine ⟨4464198477338770059750385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23809058545806773652002053 4464198477338770059750385)
              ·
                refine ⟨3348148858004077544812789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4464198477338770059750385 3348148858004077544812789)
                ·
                  refine ⟨313888955437882269826199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3348148858004077544812789 313888955437882269826199)
                  ·
                    rfl

theorem cell23_5501669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_5501669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501669 prefixEnd_5501669 := by exact prefixLift 5501669
  have htrace : WordTrace (prefixWord ++ tailWord_5501669) baseStart_5501669 baseEnd_5501669 := by
    simpa [prefixWord, tailWord_5501669, baseEnd_5501669] using wordTrace_append hprefix tailTrace_5501669
  have hstable : (prefixWord ++ tailWord_5501669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501669).length < 2 ^ (prefixWord ++ tailWord_5501669).sum := by decide
  have hdescent : baseEnd_5501669 < baseStart_5501669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501722 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3]
def baseStart_5501722 : Nat := 118140960795 + 5501722 * 2 ^ 59
def prefixEnd_5501722 : Nat := 4983230072969 + 3 ^ 40 * 5501722 * 2
def baseEnd_5501722 : Nat := 2825027813415628721073047

theorem tailTrace_5501722 : CollatzResearch.WordTrace tailWord_5501722 prefixEnd_5501722 2825027813415628721073047 := by
  unfold tailWord_5501722
  simp only [CollatzResearch.WordTrace]
  refine ⟨50166071643552072038948855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133776191049472192103863613 50166071643552072038948855)
  ·
    refine ⟨75249107465328108058423283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50166071643552072038948855 75249107465328108058423283)
    ·
      refine ⟨112873661197992162087634925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75249107465328108058423283 112873661197992162087634925)
      ·
        refine ⟨42327622949247060782863097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112873661197992162087634925 42327622949247060782863097)
        ·
          refine ⟨31745717211935295587147323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42327622949247060782863097 31745717211935295587147323)
          ·
            refine ⟨47618575817902943380720985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31745717211935295587147323 47618575817902943380720985)
            ·
              refine ⟨35713931863427207535540739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47618575817902943380720985 35713931863427207535540739)
              ·
                refine ⟨53570897795140811303311109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35713931863427207535540739 53570897795140811303311109)
                ·
                  refine ⟨10044543336588902119370833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53570897795140811303311109 10044543336588902119370833)
                  ·
                    refine ⟨7533407502441676589528125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10044543336588902119370833 7533407502441676589528125)
                    ·
                      refine ⟨2825027813415628721073047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7533407502441676589528125 2825027813415628721073047)
                      ·
                        rfl

theorem cell23_5501722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_5501722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501722 prefixEnd_5501722 := by exact prefixLift 5501722
  have htrace : WordTrace (prefixWord ++ tailWord_5501722) baseStart_5501722 baseEnd_5501722 := by
    simpa [prefixWord, tailWord_5501722, baseEnd_5501722] using wordTrace_append hprefix tailTrace_5501722
  have hstable : (prefixWord ++ tailWord_5501722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501722).length < 2 ^ (prefixWord ++ tailWord_5501722).sum := by decide
  have hdescent : baseEnd_5501722 < baseStart_5501722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501729 : List Nat := [1, 2, 3, 2, 1, 2, 1, 6, 1, 4]
def baseStart_5501729 : Nat := 118140960795 + 5501729 * 2 ^ 59
def prefixEnd_5501729 : Nat := 4983230072969 + 3 ^ 40 * 5501729 * 2
def baseEnd_5501729 : Nat := 941677135926736731228505

theorem tailTrace_5501729 : CollatzResearch.WordTrace tailWord_5501729 prefixEnd_5501729 941677135926736731228505 := by
  unfold tailWord_5501729
  simp only [CollatzResearch.WordTrace]
  refine ⟨200664541885182928351300241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133776361256788618900866827 200664541885182928351300241)
  ·
    refine ⟨150498406413887196263475181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200664541885182928351300241 150498406413887196263475181)
    ·
      refine ⟨56436902405207698598803193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150498406413887196263475181 56436902405207698598803193)
      ·
        refine ⟨42327676803905773949102395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56436902405207698598803193 42327676803905773949102395)
        ·
          refine ⟨63491515205858660923653593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42327676803905773949102395 63491515205858660923653593)
          ·
            refine ⟨47618636404393995692740195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63491515205858660923653593 47618636404393995692740195)
            ·
              refine ⟨71427954606590993539110293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47618636404393995692740195 71427954606590993539110293)
              ·
                refine ⟨3348185372183952822145795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71427954606590993539110293 3348185372183952822145795)
                ·
                  refine ⟨5022278058275929233218693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348185372183952822145795 5022278058275929233218693)
                  ·
                    refine ⟨941677135926736731228505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5022278058275929233218693 941677135926736731228505)
                    ·
                      rfl

theorem cell23_5501729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_5501729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501729 prefixEnd_5501729 := by exact prefixLift 5501729
  have htrace : WordTrace (prefixWord ++ tailWord_5501729) baseStart_5501729 baseEnd_5501729 := by
    simpa [prefixWord, tailWord_5501729, baseEnd_5501729] using wordTrace_append hprefix tailTrace_5501729
  have hstable : (prefixWord ++ tailWord_5501729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501729).length < 2 ^ (prefixWord ++ tailWord_5501729).sum := by decide
  have hdescent : baseEnd_5501729 < baseStart_5501729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501745 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_5501745 : Nat := 118140960795 + 5501745 * 2 ^ 59
def prefixEnd_5501745 : Nat := 4983230072969 + 3 ^ 40 * 5501745 * 2
def baseEnd_5501745 : Nat := 2825039623470682131085441

theorem tailTrace_5501745 : CollatzResearch.WordTrace tailWord_5501745 prefixEnd_5501745 2825039623470682131085441 := by
  unfold tailWord_5501745
  simp only [CollatzResearch.WordTrace]
  refine ⟨200665125453124963083882689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133776750302083308722588459 200665125453124963083882689)
  ·
    refine ⟨150498844089843722312912017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200665125453124963083882689 150498844089843722312912017)
    ·
      refine ⟨112874133067382791734684013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150498844089843722312912017 112874133067382791734684013)
      ·
        refine ⟨42327799900268546900506505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112874133067382791734684013 42327799900268546900506505)
        ·
          refine ⟨31745849925201410175379879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42327799900268546900506505 31745849925201410175379879)
          ·
            refine ⟨47618774887802115263069819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31745849925201410175379879 47618774887802115263069819)
            ·
              refine ⟨71428162331703172894604729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47618774887802115263069819 71428162331703172894604729)
              ·
                refine ⟨53571121748777379670953547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71428162331703172894604729 53571121748777379670953547)
                ·
                  refine ⟨80356682623166069506430321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53571121748777379670953547 80356682623166069506430321)
                  ·
                    refine ⟨60267511967374552129822741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80356682623166069506430321 60267511967374552129822741)
                    ·
                      refine ⟨2825039623470682131085441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60267511967374552129822741 2825039623470682131085441)
                      ·
                        rfl

theorem cell23_5501745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_5501745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501745 prefixEnd_5501745 := by exact prefixLift 5501745
  have htrace : WordTrace (prefixWord ++ tailWord_5501745) baseStart_5501745 baseEnd_5501745 := by
    simpa [prefixWord, tailWord_5501745, baseEnd_5501745] using wordTrace_append hprefix tailTrace_5501745
  have hstable : (prefixWord ++ tailWord_5501745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501745).length < 2 ^ (prefixWord ++ tailWord_5501745).sum := by decide
  have hdescent : baseEnd_5501745 < baseStart_5501745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501786 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3]
def baseStart_5501786 : Nat := 118140960795 + 5501786 * 2 ^ 59
def prefixEnd_5501786 : Nat := 4983230072969 + 3 ^ 40 * 5501786 * 2
def baseEnd_5501786 : Nat := 2825060676177516470672753

theorem tailTrace_5501786 : CollatzResearch.WordTrace tailWord_5501786 prefixEnd_5501786 2825060676177516470672753 := by
  unfold tailWord_5501786
  simp only [CollatzResearch.WordTrace]
  refine ⟨50166655211494106771531303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133777747230650951390750141 50166655211494106771531303)
  ·
    refine ⟨75249982817241160157296955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50166655211494106771531303 75249982817241160157296955)
    ·
      refine ⟨112874974225861740235945433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75249982817241160157296955 112874974225861740235945433)
      ·
        refine ⟨84656230669396305176959075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112874974225861740235945433 84656230669396305176959075)
        ·
          refine ⟨126984346004094457765438613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84656230669396305176959075 126984346004094457765438613)
          ·
            refine ⟨5952391218941927707754935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126984346004094457765438613 5952391218941927707754935)
            ·
              refine ⟨8928586828412891561632403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5952391218941927707754935 8928586828412891561632403)
              ·
                refine ⟨13392880242619337342448605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8928586828412891561632403 13392880242619337342448605)
                ·
                  refine ⟨5022330090982251503418227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13392880242619337342448605 5022330090982251503418227)
                  ·
                    refine ⟨7533495136473377255127341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5022330090982251503418227 7533495136473377255127341)
                    ·
                      refine ⟨2825060676177516470672753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7533495136473377255127341 2825060676177516470672753)
                      ·
                        rfl

theorem cell23_5501786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_5501786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501786 prefixEnd_5501786 := by exact prefixLift 5501786
  have htrace : WordTrace (prefixWord ++ tailWord_5501786) baseStart_5501786 baseEnd_5501786 := by
    simpa [prefixWord, tailWord_5501786, baseEnd_5501786] using wordTrace_append hprefix tailTrace_5501786
  have hstable : (prefixWord ++ tailWord_5501786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501786).length < 2 ^ (prefixWord ++ tailWord_5501786).sum := by decide
  have hdescent : baseEnd_5501786 < baseStart_5501786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501792 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 4]
def baseStart_5501792 : Nat := 118140960795 + 5501792 * 2 ^ 59
def prefixEnd_5501792 : Nat := 4983230072969 + 3 ^ 40 * 5501792 * 2
def baseEnd_5501792 : Nat := 2825063757061443447197725

theorem tailTrace_5501792 : CollatzResearch.WordTrace tailWord_5501792 prefixEnd_5501792 2825063757061443447197725 := by
  unfold tailWord_5501792
  simp only [CollatzResearch.WordTrace]
  refine ⟨100333419841977345055421815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133777893122636460073895753 100333419841977345055421815)
  ·
    refine ⟨150500129762966017583132723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100333419841977345055421815 150500129762966017583132723)
    ·
      refine ⟨225750194644449026374699085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150500129762966017583132723 225750194644449026374699085)
      ·
        refine ⟨84656322991668384890512157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225750194644449026374699085 84656322991668384890512157)
        ·
          refine ⟨31746121121875644333942059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84656322991668384890512157 31746121121875644333942059)
          ·
            refine ⟨47619181682813466500913089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31746121121875644333942059 47619181682813466500913089)
            ·
              refine ⟨35714386262110099875684817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47619181682813466500913089 35714386262110099875684817)
              ·
                refine ⟨26785789696582574906763613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35714386262110099875684817 26785789696582574906763613)
                ·
                  refine ⟨10044671136218465590036355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26785789696582574906763613 10044671136218465590036355)
                  ·
                    refine ⟨15067006704327698385054533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10044671136218465590036355 15067006704327698385054533)
                    ·
                      refine ⟨2825063757061443447197725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15067006704327698385054533 2825063757061443447197725)
                      ·
                        rfl

theorem cell23_5501792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_5501792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501792 prefixEnd_5501792 := by exact prefixLift 5501792
  have htrace : WordTrace (prefixWord ++ tailWord_5501792) baseStart_5501792 baseEnd_5501792 := by
    simpa [prefixWord, tailWord_5501792, baseEnd_5501792] using wordTrace_append hprefix tailTrace_5501792
  have hstable : (prefixWord ++ tailWord_5501792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501792).length < 2 ^ (prefixWord ++ tailWord_5501792).sum := by decide
  have hdescent : baseEnd_5501792 < baseStart_5501792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501809 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 4]
def baseStart_5501809 : Nat := 118140960795 + 5501809 * 2 ^ 59
def prefixEnd_5501809 : Nat := 4983230072969 + 3 ^ 40 * 5501809 * 2
def baseEnd_5501809 : Nat := 2825072486232569880685147

theorem tailTrace_5501809 : CollatzResearch.WordTrace tailWord_5501809 prefixEnd_5501809 2825072486232569880685147 := by
  unfold tailWord_5501809
  simp only [CollatzResearch.WordTrace]
  refine ⟨200667459724893102014212481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133778306483262068009474987 200667459724893102014212481)
  ·
    refine ⟨150500594793669826510659361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200667459724893102014212481 150500594793669826510659361)
    ·
      refine ⟨112875446095252369882994521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150500594793669826510659361 112875446095252369882994521)
      ·
        refine ⟨84656584571439277412245891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112875446095252369882994521 84656584571439277412245891)
        ·
          refine ⟨126984876857158916118368837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84656584571439277412245891 126984876857158916118368837)
          ·
            refine ⟨23809664410717296772194157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126984876857158916118368837 23809664410717296772194157)
            ·
              refine ⟨8928624154018986289572809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23809664410717296772194157 8928624154018986289572809)
              ·
                refine ⟨6696468115514239717179607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8928624154018986289572809 6696468115514239717179607)
                ·
                  refine ⟨10044702173271359575769411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6696468115514239717179607 10044702173271359575769411)
                  ·
                    refine ⟨15067053259907039363654117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10044702173271359575769411 15067053259907039363654117)
                    ·
                      refine ⟨2825072486232569880685147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15067053259907039363654117 2825072486232569880685147)
                      ·
                        rfl

theorem cell23_5501809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_5501809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501809 prefixEnd_5501809 := by exact prefixLift 5501809
  have htrace : WordTrace (prefixWord ++ tailWord_5501809) baseStart_5501809 baseEnd_5501809 := by
    simpa [prefixWord, tailWord_5501809, baseEnd_5501809] using wordTrace_append hprefix tailTrace_5501809
  have hstable : (prefixWord ++ tailWord_5501809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501809).length < 2 ^ (prefixWord ++ tailWord_5501809).sum := by decide
  have hdescent : baseEnd_5501809 < baseStart_5501809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501829 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 5]
def baseStart_5501829 : Nat := 118140960795 + 5501829 * 2 ^ 59
def prefixEnd_5501829 : Nat := 4983230072969 + 3 ^ 40 * 5501829 * 2
def baseEnd_5501829 : Nat := 2825082755845659802435055

theorem tailTrace_5501829 : CollatzResearch.WordTrace tailWord_5501829 prefixEnd_5501829 2825082755845659802435055 := by
  unfold tailWord_5501829
  simp only [CollatzResearch.WordTrace]
  refine ⟨200668189184820645429940541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133778792789880430286627027 200668189184820645429940541)
  ·
    refine ⟨75250570944307742036227703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200668189184820645429940541 75250570944307742036227703)
    ·
      refine ⟨112875856416461613054341555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75250570944307742036227703 112875856416461613054341555)
      ·
        refine ⟨169313784624692419581512333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112875856416461613054341555 169313784624692419581512333)
        ·
          refine ⟨63492669234259657343067125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169313784624692419581512333 63492669234259657343067125)
          ·
            refine ⟨5952437740711842875912543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63492669234259657343067125 5952437740711842875912543)
            ·
              refine ⟨8928656611067764313868815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5952437740711842875912543 8928656611067764313868815)
              ·
                refine ⟨13392984916601646470803223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8928656611067764313868815 13392984916601646470803223)
                ·
                  refine ⟨20089477374902469706204835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13392984916601646470803223 20089477374902469706204835)
                  ·
                    refine ⟨30134216062353704559307253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20089477374902469706204835 30134216062353704559307253)
                    ·
                      refine ⟨2825082755845659802435055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30134216062353704559307253 2825082755845659802435055)
                      ·
                        rfl

theorem cell23_5501829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_5501829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501829 prefixEnd_5501829 := by exact prefixLift 5501829
  have htrace : WordTrace (prefixWord ++ tailWord_5501829) baseStart_5501829 baseEnd_5501829 := by
    simpa [prefixWord, tailWord_5501829, baseEnd_5501829] using wordTrace_append hprefix tailTrace_5501829
  have hstable : (prefixWord ++ tailWord_5501829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501829).length < 2 ^ (prefixWord ++ tailWord_5501829).sum := by decide
  have hdescent : baseEnd_5501829 < baseStart_5501829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5501986 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_5501986 : Nat := 118140960795 + 5501986 * 2 ^ 59
def prefixEnd_5501986 : Nat := 4983230072969 + 3 ^ 40 * 5501986 * 2
def baseEnd_5501986 : Nat := 941721124102805229390611

theorem tailTrace_5501986 : CollatzResearch.WordTrace tailWord_5501986 prefixEnd_5501986 941721124102805229390611 := by
  unfold tailWord_5501986
  simp only [CollatzResearch.WordTrace]
  refine ⟨50168478861312965310851453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133782610296834574162270541 50168478861312965310851453)
  ·
    refine ⟨18813179572992361991569295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50168478861312965310851453 18813179572992361991569295)
    ·
      refine ⟨28219769359488542987353943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18813179572992361991569295 28219769359488542987353943)
      ·
        refine ⟨42329654039232814481030915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28219769359488542987353943 42329654039232814481030915)
        ·
          refine ⟨63494481058849221721546373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42329654039232814481030915 63494481058849221721546373)
          ·
            refine ⟨11905215198534229072789945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63494481058849221721546373 11905215198534229072789945)
            ·
              refine ⟨8928911398900671804592459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11905215198534229072789945 8928911398900671804592459)
              ·
                refine ⟨13393367098351007706888689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8928911398900671804592459 13393367098351007706888689)
                ·
                  refine ⟨10045025323763255780166517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13393367098351007706888689 10045025323763255780166517)
                  ·
                    refine ⟨941721124102805229390611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10045025323763255780166517 941721124102805229390611)
                    ·
                      rfl

theorem cell23_5501986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_5501986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5501986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5501986 prefixEnd_5501986 := by exact prefixLift 5501986
  have htrace : WordTrace (prefixWord ++ tailWord_5501986) baseStart_5501986 baseEnd_5501986 := by
    simpa [prefixWord, tailWord_5501986, baseEnd_5501986] using wordTrace_append hprefix tailTrace_5501986
  have hstable : (prefixWord ++ tailWord_5501986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5501986).length < 2 ^ (prefixWord ++ tailWord_5501986).sum := by decide
  have hdescent : baseEnd_5501986 < baseStart_5501986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5501986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502050 : List Nat := [3, 3, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_5502050 : Nat := 118140960795 + 5502050 * 2 ^ 59
def prefixEnd_5502050 : Nat := 4983230072969 + 3 ^ 40 * 5502050 * 2
def baseEnd_5502050 : Nat := 941732078356767812590513

theorem tailTrace_5502050 : CollatzResearch.WordTrace tailWord_5502050 prefixEnd_5502050 941732078356767812590513 := by
  unfold tailWord_5502050
  simp only [CollatzResearch.WordTrace]
  refine ⟨50169062429255000043433901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133784166478013333449157069 50169062429255000043433901)
  ·
    refine ⟨18813398410970625016287713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50169062429255000043433901 18813398410970625016287713)
    ·
      refine ⟨14110048808227968762215785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18813398410970625016287713 14110048808227968762215785)
      ·
        refine ⟨10582536606170976571661839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14110048808227968762215785 10582536606170976571661839)
        ·
          refine ⟨15873804909256464857492759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10582536606170976571661839 15873804909256464857492759)
          ·
            refine ⟨23810707363884697286239139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15873804909256464857492759 23810707363884697286239139)
            ·
              refine ⟨35716061045827045929358709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23810707363884697286239139 35716061045827045929358709)
              ·
                refine ⟨3348380723046285555877379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35716061045827045929358709 3348380723046285555877379)
                ·
                  refine ⟨5022571084569428333816069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348380723046285555877379 5022571084569428333816069)
                  ·
                    refine ⟨941732078356767812590513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5022571084569428333816069 941732078356767812590513)
                    ·
                      rfl

theorem cell23_5502050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_5502050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502050 prefixEnd_5502050 := by exact prefixLift 5502050
  have htrace : WordTrace (prefixWord ++ tailWord_5502050) baseStart_5502050 baseEnd_5502050 := by
    simpa [prefixWord, tailWord_5502050, baseEnd_5502050] using wordTrace_append hprefix tailTrace_5502050
  have hstable : (prefixWord ++ tailWord_5502050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502050).length < 2 ^ (prefixWord ++ tailWord_5502050).sum := by decide
  have hdescent : baseEnd_5502050 < baseStart_5502050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502116 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_5502116 : Nat := 118140960795 + 5502116 * 2 ^ 59
def prefixEnd_5502116 : Nat := 4983230072969 + 3 ^ 40 * 5502116 * 2
def baseEnd_5502116 : Nat := 2825230124793500179546235

theorem tailTrace_5502116 : CollatzResearch.WordTrace tailWord_5502116 prefixEnd_5502116 2825230124793500179546235 := by
  unfold tailWord_5502116
  simp only [CollatzResearch.WordTrace]
  refine ⟨100339328467390446722819101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133785771289853928963758801 100339328467390446722819101)
  ·
    refine ⟨37627248175271417521057163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100339328467390446722819101 37627248175271417521057163)
    ·
      refine ⟨56440872262907126281585745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37627248175271417521057163 56440872262907126281585745)
      ·
        refine ⟨42330654197180344711189309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56440872262907126281585745 42330654197180344711189309)
        ·
          refine ⟨15873995323942629266695991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42330654197180344711189309 15873995323942629266695991)
          ·
            refine ⟨23810992985913943900043987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15873995323942629266695991 23810992985913943900043987)
            ·
              refine ⟨35716489478870915850065981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23810992985913943900043987 35716489478870915850065981)
              ·
                refine ⟨13393683554576593443774743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35716489478870915850065981 13393683554576593443774743)
                ·
                  refine ⟨20090525331864890165662115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13393683554576593443774743 20090525331864890165662115)
                  ·
                    refine ⟨30135787997797335248493173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20090525331864890165662115 30135787997797335248493173)
                    ·
                      refine ⟨2825230124793500179546235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30135787997797335248493173 2825230124793500179546235)
                      ·
                        rfl

theorem cell23_5502116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_5502116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502116 prefixEnd_5502116 := by exact prefixLift 5502116
  have htrace : WordTrace (prefixWord ++ tailWord_5502116) baseStart_5502116 baseEnd_5502116 := by
    simpa [prefixWord, tailWord_5502116, baseEnd_5502116] using wordTrace_append hprefix tailTrace_5502116
  have hstable : (prefixWord ++ tailWord_5502116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502116).length < 2 ^ (prefixWord ++ tailWord_5502116).sum := by decide
  have hdescent : baseEnd_5502116 < baseStart_5502116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502130 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2]
def baseStart_5502130 : Nat := 118140960795 + 5502130 * 2 ^ 59
def prefixEnd_5502130 : Nat := 4983230072969 + 3 ^ 40 * 5502130 * 2
def baseEnd_5502130 : Nat := 2825237313522663124771171

theorem tailTrace_5502130 : CollatzResearch.WordTrace tailWord_5502130 prefixEnd_5502130 2825237313522663124771171 := by
  unfold tailWord_5502130
  simp only [CollatzResearch.WordTrace]
  refine ⟨50169791889182543459161961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133786111704486782557765229 50169791889182543459161961)
  ·
    refine ⟨37627343916886907594371471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50169791889182543459161961 37627343916886907594371471)
    ·
      refine ⟨56441015875330361391557207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37627343916886907594371471 56441015875330361391557207)
      ·
        refine ⟨84661523812995542087335811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56441015875330361391557207 84661523812995542087335811)
        ·
          refine ⟨126992285719493313131003717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84661523812995542087335811 126992285719493313131003717)
          ·
            refine ⟨23811053572404996212063197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126992285719493313131003717 23811053572404996212063197)
            ·
              refine ⟨8929145089651873579523699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23811053572404996212063197 8929145089651873579523699)
              ·
                refine ⟨13393717634477810369285549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8929145089651873579523699 13393717634477810369285549)
                ·
                  refine ⟨5022644112929178888482081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13393717634477810369285549 5022644112929178888482081)
                  ·
                    refine ⟨3766983084696884166361561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5022644112929178888482081 3766983084696884166361561)
                    ·
                      refine ⟨2825237313522663124771171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3766983084696884166361561 2825237313522663124771171)
                      ·
                        rfl

theorem cell23_5502130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_5502130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502130 prefixEnd_5502130 := by exact prefixLift 5502130
  have htrace : WordTrace (prefixWord ++ tailWord_5502130) baseStart_5502130 baseEnd_5502130 := by
    simpa [prefixWord, tailWord_5502130, baseEnd_5502130] using wordTrace_append hprefix tailTrace_5502130
  have hstable : (prefixWord ++ tailWord_5502130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502130).length < 2 ^ (prefixWord ++ tailWord_5502130).sum := by decide
  have hdescent : baseEnd_5502130 < baseStart_5502130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502140 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 2, 4]
def baseStart_5502140 : Nat := 118140960795 + 5502140 * 2 ^ 59
def prefixEnd_5502140 : Nat := 4983230072969 + 3 ^ 40 * 5502140 * 2
def baseEnd_5502140 : Nat := 941747482776402695215375

theorem tailTrace_5502140 : CollatzResearch.WordTrace tailWord_5502140 prefixEnd_5502140 941747482776402695215375 := by
  unfold tailWord_5502140
  simp only [CollatzResearch.WordTrace]
  refine ⟨100339766143346972772255937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133786354857795963696341249 100339766143346972772255937)
  ·
    refine ⟨75254824607510229579191953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100339766143346972772255937 75254824607510229579191953)
    ·
      refine ⟨56441118455632672184393965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75254824607510229579191953 56441118455632672184393965)
      ·
        refine ⟨21165419420862252069147737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56441118455632672184393965 21165419420862252069147737)
        ·
          refine ⟨15874064565646689051860803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21165419420862252069147737 15874064565646689051860803)
          ·
            refine ⟨23811096848470033577791205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15874064565646689051860803 23811096848470033577791205)
            ·
              refine ⟨4464580659088131295835851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23811096848470033577791205 4464580659088131295835851)
              ·
                refine ⟨6696870988632196943753777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4464580659088131295835851 6696870988632196943753777)
                ·
                  refine ⟨5022653241474147707815333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6696870988632196943753777 5022653241474147707815333)
                  ·
                    refine ⟨941747482776402695215375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5022653241474147707815333 941747482776402695215375)
                    ·
                      rfl

theorem cell23_5502140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_5502140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502140 prefixEnd_5502140 := by exact prefixLift 5502140
  have htrace : WordTrace (prefixWord ++ tailWord_5502140) baseStart_5502140 baseEnd_5502140 := by
    simpa [prefixWord, tailWord_5502140, baseEnd_5502140] using wordTrace_append hprefix tailTrace_5502140
  have hstable : (prefixWord ++ tailWord_5502140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502140).length < 2 ^ (prefixWord ++ tailWord_5502140).sum := by decide
  have hdescent : baseEnd_5502140 < baseStart_5502140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502159 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_5502159 : Nat := 118140960795 + 5502159 * 2 ^ 59
def prefixEnd_5502159 : Nat := 4983230072969 + 3 ^ 40 * 5502159 * 2
def baseEnd_5502159 : Nat := 2825252204461643511308537

theorem tailTrace_5502159 : CollatzResearch.WordTrace tailWord_5502159 prefixEnd_5502159 2825252204461643511308537 := by
  unfold tailWord_5502159
  simp only [CollatzResearch.WordTrace]
  refine ⟨200680225273625111789453531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133786816849083407859635687 200680225273625111789453531)
  ·
    refine ⟨301020337910437667684180297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200680225273625111789453531 301020337910437667684180297)
    ·
      refine ⟨225765253432828250763135223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301020337910437667684180297 225765253432828250763135223)
      ·
        refine ⟨338647880149242376144702835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225765253432828250763135223 338647880149242376144702835)
        ·
          refine ⟨507971820223863564217054253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338647880149242376144702835 507971820223863564217054253)
          ·
            refine ⟨190489432583948836581395345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 507971820223863564217054253 190489432583948836581395345)
            ·
              refine ⟨142867074437961627436046509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190489432583948836581395345 142867074437961627436046509)
              ·
                refine ⟨53575152914235610288517441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142867074437961627436046509 53575152914235610288517441)
                ·
                  refine ⟨40181364685676707716388081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53575152914235610288517441 40181364685676707716388081)
                  ·
                    refine ⟨30136023514257530787291061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40181364685676707716388081 30136023514257530787291061)
                    ·
                      refine ⟨2825252204461643511308537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30136023514257530787291061 2825252204461643511308537)
                      ·
                        rfl

theorem cell23_5502159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_5502159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502159 prefixEnd_5502159 := by exact prefixLift 5502159
  have htrace : WordTrace (prefixWord ++ tailWord_5502159) baseStart_5502159 baseEnd_5502159 := by
    simpa [prefixWord, tailWord_5502159, baseEnd_5502159] using wordTrace_append hprefix tailTrace_5502159
  have hstable : (prefixWord ++ tailWord_5502159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502159).length < 2 ^ (prefixWord ++ tailWord_5502159).sum := by decide
  have hdescent : baseEnd_5502159 < baseStart_5502159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502181 : List Nat := [1, 3, 1, 4, 3, 2, 2, 2, 1, 2, 2]
def baseStart_5502181 : Nat := 118140960795 + 5502181 * 2 ^ 59
def prefixEnd_5502181 : Nat := 4983230072969 + 3 ^ 40 * 5502181 * 2
def baseEnd_5502181 : Nat := 2825263501036042425233437

theorem tailTrace_5502181 : CollatzResearch.WordTrace tailWord_5502181 prefixEnd_5502181 2825263501036042425233437 := by
  unfold tailWord_5502181
  simp only [CollatzResearch.WordTrace]
  refine ⟨200681027679545409546754397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133787351786363606364502931 200681027679545409546754397)
  ·
    refine ⟨75255385379829528580032899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200681027679545409546754397 75255385379829528580032899)
    ·
      refine ⟨112883078069744292870049349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75255385379829528580032899 112883078069744292870049349)
      ·
        refine ⟨21165577138077054913134253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112883078069744292870049349 21165577138077054913134253)
        ·
          refine ⟨7937091426778895592425345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21165577138077054913134253 7937091426778895592425345)
          ·
            refine ⟨5952818570084171694319009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7937091426778895592425345 5952818570084171694319009)
            ·
              refine ⟨4464613927563128770739257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5952818570084171694319009 4464613927563128770739257)
              ·
                refine ⟨3348460445672346578054443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4464613927563128770739257 3348460445672346578054443)
                ·
                  refine ⟨5022690668508519867081665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348460445672346578054443 5022690668508519867081665)
                  ·
                    refine ⟨3767018001381389900311249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5022690668508519867081665 3767018001381389900311249)
                    ·
                      refine ⟨2825263501036042425233437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767018001381389900311249 2825263501036042425233437)
                      ·
                        rfl

theorem cell23_5502181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_5502181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502181 prefixEnd_5502181 := by exact prefixLift 5502181
  have htrace : WordTrace (prefixWord ++ tailWord_5502181) baseStart_5502181 baseEnd_5502181 := by
    simpa [prefixWord, tailWord_5502181, baseEnd_5502181] using wordTrace_append hprefix tailTrace_5502181
  have hstable : (prefixWord ++ tailWord_5502181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502181).length < 2 ^ (prefixWord ++ tailWord_5502181).sum := by decide
  have hdescent : baseEnd_5502181 < baseStart_5502181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502186 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_5502186 : Nat := 118140960795 + 5502186 * 2 ^ 59
def prefixEnd_5502186 : Nat := 4983230072969 + 3 ^ 40 * 5502186 * 2
def baseEnd_5502186 : Nat := 2825266068439314905670913

theorem tailTrace_5502186 : CollatzResearch.WordTrace tailWord_5502186 prefixEnd_5502186 2825266068439314905670913 := by
  unfold tailWord_5502186
  simp only [CollatzResearch.WordTrace]
  refine ⟨50170302511131823850171603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133787473363018196933790941 50170302511131823850171603)
  ·
    refine ⟨75255453766697735775257405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50170302511131823850171603 75255453766697735775257405)
    ·
      refine ⟨28220795162511650915721527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75255453766697735775257405 28220795162511650915721527)
      ·
        refine ⟨42331192743767476373582291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28220795162511650915721527 42331192743767476373582291)
        ·
          refine ⟨63496789115651214560373437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42331192743767476373582291 63496789115651214560373437)
          ·
            refine ⟨23811295918369205460140039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63496789115651214560373437 23811295918369205460140039)
            ·
              refine ⟨35716943877553808190210059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23811295918369205460140039 35716943877553808190210059)
              ·
                refine ⟨53575415816330712285315089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35716943877553808190210059 53575415816330712285315089)
                ·
                  refine ⟨40181561862248034213986317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53575415816330712285315089 40181561862248034213986317)
                  ·
                    refine ⟨15068085698343012830244869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40181561862248034213986317 15068085698343012830244869)
                    ·
                      refine ⟨2825266068439314905670913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15068085698343012830244869 2825266068439314905670913)
                      ·
                        rfl

theorem cell23_5502186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_5502186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502186 prefixEnd_5502186 := by exact prefixLift 5502186
  have htrace : WordTrace (prefixWord ++ tailWord_5502186) baseStart_5502186 baseEnd_5502186 := by
    simpa [prefixWord, tailWord_5502186, baseEnd_5502186] using wordTrace_append hprefix tailTrace_5502186
  have hstable : (prefixWord ++ tailWord_5502186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502186).length < 2 ^ (prefixWord ++ tailWord_5502186).sum := by decide
  have hdescent : baseEnd_5502186 < baseStart_5502186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502199 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_5502199 : Nat := 118140960795 + 5502199 * 2 ^ 59
def prefixEnd_5502199 : Nat := 4983230072969 + 3 ^ 40 * 5502199 * 2
def baseEnd_5502199 : Nat := 2825272743687823354808353

theorem tailTrace_5502199 : CollatzResearch.WordTrace tailWord_5502199 prefixEnd_5502199 2825272743687823354808353 := by
  unfold tailWord_5502199
  simp only [CollatzResearch.WordTrace]
  refine ⟨200681684193480198620909651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133787789462320132413939767 200681684193480198620909651)
  ·
    refine ⟨301022526290220297931364477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200681684193480198620909651 301022526290220297931364477)
    ·
      refine ⟨112883447358832611724261679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301022526290220297931364477 112883447358832611724261679)
      ·
        refine ⟨169325171038248917586392519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112883447358832611724261679 169325171038248917586392519)
        ·
          refine ⟨253987756557373376379588779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169325171038248917586392519 253987756557373376379588779)
          ·
            refine ⟨380981634836060064569383169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253987756557373376379588779 380981634836060064569383169)
            ·
              refine ⟨285736226127045048427037377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380981634836060064569383169 285736226127045048427037377)
              ·
                refine ⟨214302169595283786320278033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285736226127045048427037377 214302169595283786320278033)
                ·
                  refine ⟨160726627196462839740208525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214302169595283786320278033 160726627196462839740208525)
                  ·
                    refine ⟨60272485198673564902578197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160726627196462839740208525 60272485198673564902578197)
                    ·
                      refine ⟨2825272743687823354808353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60272485198673564902578197 2825272743687823354808353)
                      ·
                        rfl

theorem cell23_5502199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_5502199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502199 prefixEnd_5502199 := by exact prefixLift 5502199
  have htrace : WordTrace (prefixWord ++ tailWord_5502199) baseStart_5502199 baseEnd_5502199 := by
    simpa [prefixWord, tailWord_5502199, baseEnd_5502199] using wordTrace_append hprefix tailTrace_5502199
  have hstable : (prefixWord ++ tailWord_5502199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502199).length < 2 ^ (prefixWord ++ tailWord_5502199).sum := by decide
  have hdescent : baseEnd_5502199 < baseStart_5502199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502237 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_5502237 : Nat := 118140960795 + 5502237 * 2 ^ 59
def prefixEnd_5502237 : Nat := 4983230072969 + 3 ^ 40 * 5502237 * 2
def baseEnd_5502237 : Nat := 2825292255952694206133179

theorem tailTrace_5502237 : CollatzResearch.WordTrace tailWord_5502237 prefixEnd_5502237 2825292255952694206133179 := by
  unfold tailWord_5502237
  simp only [CollatzResearch.WordTrace]
  refine ⟨200683070167342531110792965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133788713444895020740528643 200683070167342531110792965)
  ·
    refine ⟨37628075656376724583273681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200683070167342531110792965 37628075656376724583273681)
    ·
      refine ⟨28221056742282543437455261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37628075656376724583273681 28221056742282543437455261)
      ·
        refine ⟨10582896278355953789045723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28221056742282543437455261 10582896278355953789045723)
        ·
          refine ⟨15874344417533930683568585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10582896278355953789045723 15874344417533930683568585)
          ·
            refine ⟨11905758313150448012676439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15874344417533930683568585 11905758313150448012676439)
            ·
              refine ⟨17858637469725672019014659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11905758313150448012676439 17858637469725672019014659)
              ·
                refine ⟨26787956204588508028521989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17858637469725672019014659 26787956204588508028521989)
                ·
                  refine ⟨5022741788360345255347873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26787956204588508028521989 5022741788360345255347873)
                  ·
                    refine ⟨3767056341270258941510905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5022741788360345255347873 3767056341270258941510905)
                    ·
                      refine ⟨2825292255952694206133179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767056341270258941510905 2825292255952694206133179)
                      ·
                        rfl

theorem cell23_5502237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_5502237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502237 prefixEnd_5502237 := by exact prefixLift 5502237
  have htrace : WordTrace (prefixWord ++ tailWord_5502237) baseStart_5502237 baseEnd_5502237 := by
    simpa [prefixWord, tailWord_5502237, baseEnd_5502237] using wordTrace_append hprefix tailTrace_5502237
  have hstable : (prefixWord ++ tailWord_5502237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502237).length < 2 ^ (prefixWord ++ tailWord_5502237).sum := by decide
  have hdescent : baseEnd_5502237 < baseStart_5502237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502243 : List Nat := [1, 1, 1, 4, 2, 3, 2, 4, 5]
def baseStart_5502243 : Nat := 118140960795 + 5502243 * 2 ^ 59
def prefixEnd_5502243 : Nat := 4983230072969 + 3 ^ 40 * 5502243 * 2
def baseEnd_5502243 : Nat := 313921704092957909184239

theorem tailTrace_5502243 : CollatzResearch.WordTrace tailWord_5502243 prefixEnd_5502243 313921704092957909184239 := by
  unfold tailWord_5502243
  simp only [CollatzResearch.WordTrace]
  refine ⟨200683289005320794135511383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133788859336880529423674255 200683289005320794135511383)
  ·
    refine ⟨301024933507981191203267075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200683289005320794135511383 301024933507981191203267075)
    ·
      refine ⟨451537400261971786804900613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301024933507981191203267075 451537400261971786804900613)
      ·
        refine ⟨84663262549119710025918865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 451537400261971786804900613 84663262549119710025918865)
        ·
          refine ⟨63497446911839782519439149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84663262549119710025918865 63497446911839782519439149)
          ·
            refine ⟨23811542591939918444789681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63497446911839782519439149 23811542591939918444789681)
            ·
              refine ⟨17858656943954938833592261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23811542591939918444789681 17858656943954938833592261)
              ·
                refine ⟨3348498176991551031298549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17858656943954938833592261 3348498176991551031298549)
                ·
                  refine ⟨313921704092957909184239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3348498176991551031298549 313921704092957909184239)
                  ·
                    rfl

theorem cell23_5502243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 5].length) (baseStart_5502243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502243 prefixEnd_5502243 := by exact prefixLift 5502243
  have htrace : WordTrace (prefixWord ++ tailWord_5502243) baseStart_5502243 baseEnd_5502243 := by
    simpa [prefixWord, tailWord_5502243, baseEnd_5502243] using wordTrace_append hprefix tailTrace_5502243
  have hstable : (prefixWord ++ tailWord_5502243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502243).length < 2 ^ (prefixWord ++ tailWord_5502243).sum := by decide
  have hdescent : baseEnd_5502243 < baseStart_5502243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502273 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 1, 7]
def baseStart_5502273 : Nat := 118140960795 + 5502273 * 2 ^ 59
def prefixEnd_5502273 : Nat := 4983230072969 + 3 ^ 40 * 5502273 * 2
def baseEnd_5502273 : Nat := 941770247085418688427671

theorem tailTrace_5502273 : CollatzResearch.WordTrace tailWord_5502273 prefixEnd_5502273 941770247085418688427671 := by
  unfold tailWord_5502273
  simp only [CollatzResearch.WordTrace]
  refine ⟨200684383195212109259103473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133789588796808072839402315 200684383195212109259103473)
  ·
    refine ⟨150513287396409081944327605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200684383195212109259103473 150513287396409081944327605)
    ·
      refine ⟨14110620693413351432280713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150513287396409081944327605 14110620693413351432280713)
      ·
        refine ⟨10582965520060013574210535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14110620693413351432280713 10582965520060013574210535)
        ·
          refine ⟨15874448280090020361315803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10582965520060013574210535 15874448280090020361315803)
          ·
            refine ⟨23811672420135030541973705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15874448280090020361315803 23811672420135030541973705)
            ·
              refine ⟨17858754315101272906480279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23811672420135030541973705 17858754315101272906480279)
              ·
                refine ⟨26788131472651909359720419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17858754315101272906480279 26788131472651909359720419)
                ·
                  refine ⟨40182197208977864039580629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26788131472651909359720419 40182197208977864039580629)
                  ·
                    refine ⟨941770247085418688427671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40182197208977864039580629 941770247085418688427671)
                    ·
                      rfl

theorem cell23_5502273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_5502273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502273 prefixEnd_5502273 := by exact prefixLift 5502273
  have htrace : WordTrace (prefixWord ++ tailWord_5502273) baseStart_5502273 baseEnd_5502273 := by
    simpa [prefixWord, tailWord_5502273, baseEnd_5502273] using wordTrace_append hprefix tailTrace_5502273
  have hstable : (prefixWord ++ tailWord_5502273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502273).length < 2 ^ (prefixWord ++ tailWord_5502273).sum := by decide
  have hdescent : baseEnd_5502273 < baseStart_5502273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502293 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_5502293 : Nat := 118140960795 + 5502293 * 2 ^ 59
def prefixEnd_5502293 : Nat := 4983230072969 + 3 ^ 40 * 5502293 * 2
def baseEnd_5502293 : Nat := 2825321010869345987032921

theorem tailTrace_5502293 : CollatzResearch.WordTrace tailWord_5502293 prefixEnd_5502293 2825321010869345987032921 := by
  unfold tailWord_5502293
  simp only [CollatzResearch.WordTrace]
  refine ⟨200685112655139652674831533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133790075103426435116554355 200685112655139652674831533)
  ·
    refine ⟨75256917245677369753061825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200685112655139652674831533 75256917245677369753061825)
    ·
      refine ⟨56442687934258027314796369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75256917245677369753061825 56442687934258027314796369)
      ·
        refine ⟨42332015950693520486097277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56442687934258027314796369 42332015950693520486097277)
        ·
          refine ⟨15874505981510070182286479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42332015950693520486097277 15874505981510070182286479)
          ·
            refine ⟨23811758972265105273429719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15874505981510070182286479 23811758972265105273429719)
            ·
              refine ⟨35717638458397657910144579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23811758972265105273429719 35717638458397657910144579)
              ·
                refine ⟨53576457687596486865216869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35717638458397657910144579 53576457687596486865216869)
                ·
                  refine ⟨10045585816424341287228163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53576457687596486865216869 10045585816424341287228163)
                  ·
                    refine ⟨15068378724636511930842245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10045585816424341287228163 15068378724636511930842245)
                    ·
                      refine ⟨2825321010869345987032921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15068378724636511930842245 2825321010869345987032921)
                      ·
                        rfl

theorem cell23_5502293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_5502293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502293 prefixEnd_5502293 := by exact prefixLift 5502293
  have htrace : WordTrace (prefixWord ++ tailWord_5502293) baseStart_5502293 baseEnd_5502293 := by
    simpa [prefixWord, tailWord_5502293, baseEnd_5502293] using wordTrace_append hprefix tailTrace_5502293
  have hstable : (prefixWord ++ tailWord_5502293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502293).length < 2 ^ (prefixWord ++ tailWord_5502293).sum := by decide
  have hdescent : baseEnd_5502293 < baseStart_5502293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502410 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 4, 4]
def baseStart_5502410 : Nat := 118140960795 + 5502410 * 2 ^ 59
def prefixEnd_5502410 : Nat := 4983230072969 + 3 ^ 40 * 5502410 * 2
def baseEnd_5502410 : Nat := 941793696035307343089961

theorem tailTrace_5502410 : CollatzResearch.WordTrace tailWord_5502410 prefixEnd_5502410 941793696035307343089961 := by
  unfold tailWord_5502410
  simp only [CollatzResearch.WordTrace]
  refine ⟨50172344998928945414210171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133792919997143854437893789 50172344998928945414210171)
  ·
    refine ⟨75258517498393418121315257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50172344998928945414210171 75258517498393418121315257)
    ·
      refine ⟨56443888123795063590986443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75258517498393418121315257 56443888123795063590986443)
      ·
        refine ⟨84665832185692595386479665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56443888123795063590986443 84665832185692595386479665)
        ·
          refine ⟨63499374139269446539859749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84665832185692595386479665 63499374139269446539859749)
          ·
            refine ⟨11906132651113021226223703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63499374139269446539859749 11906132651113021226223703)
            ·
              refine ⟨17859198976669531839335555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11906132651113021226223703 17859198976669531839335555)
              ·
                refine ⟨26788798465004297759003333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17859198976669531839335555 26788798465004297759003333)
                ·
                  refine ⟨5022899712188305829813125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26788798465004297759003333 5022899712188305829813125)
                  ·
                    refine ⟨941793696035307343089961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5022899712188305829813125 941793696035307343089961)
                    ·
                      rfl

theorem cell23_5502410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_5502410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502410 prefixEnd_5502410 := by exact prefixLift 5502410
  have htrace : WordTrace (prefixWord ++ tailWord_5502410) baseStart_5502410 baseEnd_5502410 := by
    simpa [prefixWord, tailWord_5502410, baseEnd_5502410] using wordTrace_append hprefix tailTrace_5502410
  have hstable : (prefixWord ++ tailWord_5502410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502410).length < 2 ^ (prefixWord ++ tailWord_5502410).sum := by decide
  have hdescent : baseEnd_5502410 < baseStart_5502410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502437 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 1, 2, 3]
def baseStart_5502437 : Nat := 118140960795 + 5502437 * 2 ^ 59
def prefixEnd_5502437 : Nat := 4983230072969 + 3 ^ 40 * 5502437 * 2
def baseEnd_5502437 : Nat := 2825394952083593423632259

theorem tailTrace_5502437 : CollatzResearch.WordTrace tailWord_5502437 prefixEnd_5502437 2825394952083593423632259 := by
  unfold tailWord_5502437
  simp only [CollatzResearch.WordTrace]
  refine ⟨200690364766617965268073565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133793576511078643512049043 200690364766617965268073565)
  ·
    refine ⟨75258886787481736975527587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200690364766617965268073565 75258886787481736975527587)
    ·
      refine ⟨112888330181222605463291381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75258886787481736975527587 112888330181222605463291381)
      ·
        refine ⟨10583280954489619262183567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112888330181222605463291381 10583280954489619262183567)
        ·
          refine ⟨15874921431734428893275351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10583280954489619262183567 15874921431734428893275351)
          ·
            refine ⟨23812382147601643339913027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15874921431734428893275351 23812382147601643339913027)
            ·
              refine ⟨35718573221402465009869541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23812382147601643339913027 35718573221402465009869541)
              ·
                refine ⟨6697232479012962189350539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35718573221402465009869541 6697232479012962189350539)
                ·
                  refine ⟨10045848718519443284025809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6697232479012962189350539 10045848718519443284025809)
                  ·
                    refine ⟨7534386538889582463019357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10045848718519443284025809 7534386538889582463019357)
                    ·
                      refine ⟨2825394952083593423632259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7534386538889582463019357 2825394952083593423632259)
                      ·
                        rfl

theorem cell23_5502437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_5502437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502437 prefixEnd_5502437 := by exact prefixLift 5502437
  have htrace : WordTrace (prefixWord ++ tailWord_5502437) baseStart_5502437 baseEnd_5502437 := by
    simpa [prefixWord, tailWord_5502437, baseEnd_5502437] using wordTrace_append hprefix tailTrace_5502437
  have hstable : (prefixWord ++ tailWord_5502437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502437).length < 2 ^ (prefixWord ++ tailWord_5502437).sum := by decide
  have hdescent : baseEnd_5502437 < baseStart_5502437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502468 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_5502468 : Nat := 118140960795 + 5502468 * 2 ^ 59
def prefixEnd_5502468 : Nat := 4983230072969 + 3 ^ 40 * 5502468 * 2
def baseEnd_5502468 : Nat := 2825410869983882802344617

theorem tailTrace_5502468 : CollatzResearch.WordTrace tailWord_5502468 prefixEnd_5502468 2825410869983882802344617 := by
  unfold tailWord_5502468
  simp only [CollatzResearch.WordTrace]
  refine ⟨100345747714752828781226029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133794330286337105041634705 100345747714752828781226029)
  ·
    refine ⟨37629655393032310792959761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100345747714752828781226029 37629655393032310792959761)
    ·
      refine ⟨28222241544774233094719821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37629655393032310792959761 28222241544774233094719821)
      ·
        refine ⟨10583340579290337410519933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28222241544774233094719821 10583340579290337410519933)
        ·
          refine ⟨3968752717233876528944975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10583340579290337410519933 3968752717233876528944975)
          ·
            refine ⟨5953129075850814793417463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3968752717233876528944975 5953129075850814793417463)
            ·
              refine ⟨8929693613776222190126195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5953129075850814793417463 8929693613776222190126195)
              ·
                refine ⟨13394540420664333285189293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8929693613776222190126195 13394540420664333285189293)
                ·
                  refine ⟨5022952657749124981945985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13394540420664333285189293 5022952657749124981945985)
                  ·
                    refine ⟨3767214493311843736459489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5022952657749124981945985 3767214493311843736459489)
                    ·
                      refine ⟨2825410869983882802344617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767214493311843736459489 2825410869983882802344617)
                      ·
                        rfl

theorem cell23_5502468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_5502468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502468 prefixEnd_5502468 := by exact prefixLift 5502468
  have htrace : WordTrace (prefixWord ++ tailWord_5502468) baseStart_5502468 baseEnd_5502468 := by
    simpa [prefixWord, tailWord_5502468, baseEnd_5502468] using wordTrace_append hprefix tailTrace_5502468
  have hstable : (prefixWord ++ tailWord_5502468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502468).length < 2 ^ (prefixWord ++ tailWord_5502468).sum := by decide
  have hdescent : baseEnd_5502468 < baseStart_5502468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502473 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 4]
def baseStart_5502473 : Nat := 118140960795 + 5502473 * 2 ^ 59
def prefixEnd_5502473 : Nat := 4983230072969 + 3 ^ 40 * 5502473 * 2
def baseEnd_5502473 : Nat := 2825413437387155282782093

theorem tailTrace_5502473 : CollatzResearch.WordTrace tailWord_5502473 prefixEnd_5502473 2825413437387155282782093 := by
  unfold tailWord_5502473
  simp only [CollatzResearch.WordTrace]
  refine ⟨200691677794487543416384073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133794451862991695610922715 200691677794487543416384073)
  ·
    refine ⟨150518758345865657562288055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200691677794487543416384073 150518758345865657562288055)
    ·
      refine ⟨225778137518798486343432083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150518758345865657562288055 225778137518798486343432083)
      ·
        refine ⟨338667206278197729515148125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225778137518798486343432083 338667206278197729515148125)
        ·
          refine ⟨127000202354324148568180547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338667206278197729515148125 127000202354324148568180547)
          ·
            refine ⟨190500303531486222852270821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127000202354324148568180547 190500303531486222852270821)
            ·
              refine ⟨35718806912153666784800779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190500303531486222852270821 35718806912153666784800779)
              ·
                refine ⟨53578210368230500177201169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35718806912153666784800779 53578210368230500177201169)
                ·
                  refine ⟨40183657776172875132900877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53578210368230500177201169 40183657776172875132900877)
                  ·
                    refine ⟨15068871666064828174837829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40183657776172875132900877 15068871666064828174837829)
                    ·
                      refine ⟨2825413437387155282782093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15068871666064828174837829 2825413437387155282782093)
                      ·
                        rfl

theorem cell23_5502473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_5502473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502473 prefixEnd_5502473 := by exact prefixLift 5502473
  have htrace : WordTrace (prefixWord ++ tailWord_5502473) baseStart_5502473 baseEnd_5502473 := by
    simpa [prefixWord, tailWord_5502473, baseEnd_5502473] using wordTrace_append hprefix tailTrace_5502473
  have hstable : (prefixWord ++ tailWord_5502473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502473).length < 2 ^ (prefixWord ++ tailWord_5502473).sum := by decide
  have hdescent : baseEnd_5502473 < baseStart_5502473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502534 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_5502534 : Nat := 118140960795 + 5502534 * 2 ^ 59
def prefixEnd_5502534 : Nat := 4983230072969 + 3 ^ 40 * 5502534 * 2
def baseEnd_5502534 : Nat := 941814919902359848039771

theorem tailTrace_5502534 : CollatzResearch.WordTrace tailWord_5502534 prefixEnd_5502534 941814919902359848039771 := by
  unfold tailWord_5502534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6271684457727079713573583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133795935098177700556236437 6271684457727079713573583)
  ·
    refine ⟨9407526686590619570360375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6271684457727079713573583 9407526686590619570360375)
    ·
      refine ⟨14111290029885929355540563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9407526686590619570360375 14111290029885929355540563)
      ·
        refine ⟨21166935044828894033310845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14111290029885929355540563 21166935044828894033310845)
        ·
          refine ⟨7937600641810835262491567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21166935044828894033310845 7937600641810835262491567)
          ·
            refine ⟨11906400962716252893737351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7937600641810835262491567 11906400962716252893737351)
            ·
              refine ⟨17859601444074379340606027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11906400962716252893737351 17859601444074379340606027)
              ·
                refine ⟨26789402166111569010909041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17859601444074379340606027 26789402166111569010909041)
                ·
                  refine ⟨20092051624583676758181781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26789402166111569010909041 20092051624583676758181781)
                  ·
                    refine ⟨941814919902359848039771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20092051624583676758181781 941814919902359848039771)
                    ·
                      rfl

theorem cell23_5502534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_5502534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502534 prefixEnd_5502534 := by exact prefixLift 5502534
  have htrace : WordTrace (prefixWord ++ tailWord_5502534) baseStart_5502534 baseEnd_5502534 := by
    simpa [prefixWord, tailWord_5502534, baseEnd_5502534] using wordTrace_append hprefix tailTrace_5502534
  have hstable : (prefixWord ++ tailWord_5502534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502534).length < 2 ^ (prefixWord ++ tailWord_5502534).sum := by decide
  have hdescent : baseEnd_5502534 < baseStart_5502534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502540 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 1, 5, 3]
def baseStart_5502540 : Nat := 118140960795 + 5502540 * 2 ^ 59
def prefixEnd_5502540 : Nat := 4983230072969 + 3 ^ 40 * 5502540 * 2
def baseEnd_5502540 : Nat := 2825447840591006520644285

theorem tailTrace_5502540 : CollatzResearch.WordTrace tailWord_5502540 prefixEnd_5502540 2825447840591006520644285 := by
  unfold tailWord_5502540
  simp only [CollatzResearch.WordTrace]
  refine ⟨100347060742622406929536537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133796080990163209239382049 100347060742622406929536537)
  ·
    refine ⟨75260295556966805197152403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100347060742622406929536537 75260295556966805197152403)
    ·
      refine ⟨112890443335450207795728605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75260295556966805197152403 112890443335450207795728605)
      ·
        refine ⟨42333916250793827923398227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112890443335450207795728605 42333916250793827923398227)
        ·
          refine ⟨63500874376190741885097341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42333916250793827923398227 63500874376190741885097341)
          ·
            refine ⟨23812827891071528206911503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63500874376190741885097341 23812827891071528206911503)
            ·
              refine ⟨35719241836607292310367255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23812827891071528206911503 35719241836607292310367255)
              ·
                refine ⟨53578862754910938465550883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35719241836607292310367255 53578862754910938465550883)
                ·
                  refine ⟨80368294132366407698326325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53578862754910938465550883 80368294132366407698326325)
                  ·
                    refine ⟨7534527574909350721718093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80368294132366407698326325 7534527574909350721718093)
                    ·
                      refine ⟨2825447840591006520644285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7534527574909350721718093 2825447840591006520644285)
                      ·
                        rfl

theorem cell23_5502540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_5502540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502540 prefixEnd_5502540 := by exact prefixLift 5502540
  have htrace : WordTrace (prefixWord ++ tailWord_5502540) baseStart_5502540 baseEnd_5502540 := by
    simpa [prefixWord, tailWord_5502540, baseEnd_5502540] using wordTrace_append hprefix tailTrace_5502540
  have hstable : (prefixWord ++ tailWord_5502540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502540).length < 2 ^ (prefixWord ++ tailWord_5502540).sum := by decide
  have hdescent : baseEnd_5502540 < baseStart_5502540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502541 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_5502541 : Nat := 118140960795 + 5502541 * 2 ^ 59
def prefixEnd_5502541 : Nat := 4983230072969 + 3 ^ 40 * 5502541 * 2
def baseEnd_5502541 : Nat := 2825448354071661016731781

theorem tailTrace_5502541 : CollatzResearch.WordTrace tailWord_5502541 prefixEnd_5502541 2825448354071661016731781 := by
  unfold tailWord_5502541
  simp only [CollatzResearch.WordTrace]
  refine ⟨200694157958241191029859477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133796105305494127353239651 200694157958241191029859477)
  ·
    refine ⟨9407538654292555829524663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 200694157958241191029859477 9407538654292555829524663)
    ·
      refine ⟨14111307981438833744286995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9407538654292555829524663 14111307981438833744286995)
      ·
        refine ⟨21166961972158250616430493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14111307981438833744286995 21166961972158250616430493)
        ·
          refine ⟨7937610739559343981161435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21166961972158250616430493 7937610739559343981161435)
          ·
            refine ⟨11906416109339015971742153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7937610739559343981161435 11906416109339015971742153)
            ·
              refine ⟨8929812082004261978806615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11906416109339015971742153 8929812082004261978806615)
              ·
                refine ⟨13394718123006392968209923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8929812082004261978806615 13394718123006392968209923)
                ·
                  refine ⟨20092077184509589452314885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13394718123006392968209923 20092077184509589452314885)
                  ·
                    refine ⟨3767264472095548022309041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20092077184509589452314885 3767264472095548022309041)
                    ·
                      refine ⟨2825448354071661016731781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767264472095548022309041 2825448354071661016731781)
                      ·
                        rfl

theorem cell23_5502541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_5502541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502541 prefixEnd_5502541 := by exact prefixLift 5502541
  have htrace : WordTrace (prefixWord ++ tailWord_5502541) baseStart_5502541 baseEnd_5502541 := by
    simpa [prefixWord, tailWord_5502541, baseEnd_5502541] using wordTrace_append hprefix tailTrace_5502541
  have hstable : (prefixWord ++ tailWord_5502541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502541).length < 2 ^ (prefixWord ++ tailWord_5502541).sum := by decide
  have hdescent : baseEnd_5502541 < baseStart_5502541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502543 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 1, 7]
def baseStart_5502543 : Nat := 118140960795 + 5502543 * 2 ^ 59
def prefixEnd_5502543 : Nat := 4983230072969 + 3 ^ 40 * 5502543 * 2
def baseEnd_5502543 : Nat := 941816460344323336302257

theorem tailTrace_5502543 : CollatzResearch.WordTrace tailWord_5502543 prefixEnd_5502543 941816460344323336302257 := by
  unfold tailWord_5502543
  simp only [CollatzResearch.WordTrace]
  refine ⟨200694230904233945371432283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133796153936155963580954855 200694230904233945371432283)
  ·
    refine ⟨301041346356350918057148425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200694230904233945371432283 301041346356350918057148425)
    ·
      refine ⟨225781009767263188542861319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301041346356350918057148425 225781009767263188542861319)
      ·
        refine ⟨338671514650894782814291979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225781009767263188542861319 338671514650894782814291979)
        ·
          refine ⟨508007271976342174221437969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338671514650894782814291979 508007271976342174221437969)
          ·
            refine ⟨381005453982256630666078477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508007271976342174221437969 381005453982256630666078477)
            ·
              refine ⟨142877045243346236499779429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 381005453982256630666078477 142877045243346236499779429)
              ·
                refine ⟨26789445983127419343708643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142877045243346236499779429 26789445983127419343708643)
                ·
                  refine ⟨40184168974691129015562965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26789445983127419343708643 40184168974691129015562965)
                  ·
                    refine ⟨941816460344323336302257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40184168974691129015562965 941816460344323336302257)
                    ·
                      rfl

theorem cell23_5502543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_5502543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502543 prefixEnd_5502543 := by exact prefixLift 5502543
  have htrace : WordTrace (prefixWord ++ tailWord_5502543) baseStart_5502543 baseEnd_5502543 := by
    simpa [prefixWord, tailWord_5502543, baseEnd_5502543] using wordTrace_append hprefix tailTrace_5502543
  have hstable : (prefixWord ++ tailWord_5502543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502543).length < 2 ^ (prefixWord ++ tailWord_5502543).sum := by decide
  have hdescent : baseEnd_5502543 < baseStart_5502543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502553 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_5502553 : Nat := 118140960795 + 5502553 * 2 ^ 59
def prefixEnd_5502553 : Nat := 4983230072969 + 3 ^ 40 * 5502553 * 2
def baseEnd_5502553 : Nat := 2825454515839514969781725

theorem tailTrace_5502553 : CollatzResearch.WordTrace tailWord_5502553 prefixEnd_5502553 2825454515839514969781725 := by
  unfold tailWord_5502553
  simp only [CollatzResearch.WordTrace]
  refine ⟨200694595634197717079296313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133796397089465144719530875 200694595634197717079296313)
  ·
    refine ⟨150520946725648287809472235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200694595634197717079296313 150520946725648287809472235)
    ·
      refine ⟨225781420088472431714208353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150520946725648287809472235 225781420088472431714208353)
      ·
        refine ⟨169336065066354323785656265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225781420088472431714208353 169336065066354323785656265)
        ·
          refine ⟨127002048799765742839242199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169336065066354323785656265 127002048799765742839242199)
          ·
            refine ⟨190503073199648614258863299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127002048799765742839242199 190503073199648614258863299)
            ·
              refine ⟨285754609799472921388294949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190503073199648614258863299 285754609799472921388294949)
              ·
                refine ⟨53578989337401172760305303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 285754609799472921388294949 53578989337401172760305303)
                ·
                  refine ⟨80368484006101759140457955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53578989337401172760305303 80368484006101759140457955)
                  ·
                    refine ⟨120552726009152638710686933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80368484006101759140457955 120552726009152638710686933)
                    ·
                      refine ⟨2825454515839514969781725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120552726009152638710686933 2825454515839514969781725)
                      ·
                        rfl

theorem cell23_5502553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_5502553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502553 prefixEnd_5502553 := by exact prefixLift 5502553
  have htrace : WordTrace (prefixWord ++ tailWord_5502553) baseStart_5502553 baseEnd_5502553 := by
    simpa [prefixWord, tailWord_5502553, baseEnd_5502553] using wordTrace_append hprefix tailTrace_5502553
  have hstable : (prefixWord ++ tailWord_5502553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502553).length < 2 ^ (prefixWord ++ tailWord_5502553).sum := by decide
  have hdescent : baseEnd_5502553 < baseStart_5502553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502597 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 2, 4, 2]
def baseStart_5502597 : Nat := 118140960795 + 5502597 * 2 ^ 59
def prefixEnd_5502597 : Nat := 4983230072969 + 3 ^ 40 * 5502597 * 2
def baseEnd_5502597 : Nat := 2825477108988312797631523

theorem tailTrace_5502597 : CollatzResearch.WordTrace tailWord_5502597 prefixEnd_5502597 2825477108988312797631523 := by
  unfold tailWord_5502597
  simp only [CollatzResearch.WordTrace]
  refine ⟨200696200446038312593898045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133797466964025541729265363 200696200446038312593898045)
  ·
    refine ⟨75261075167264367222711767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200696200446038312593898045 75261075167264367222711767)
    ·
      refine ⟨112891612750896550834067651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75261075167264367222711767 112891612750896550834067651)
      ·
        refine ⟨169337419126344826251101477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112891612750896550834067651 169337419126344826251101477)
        ·
          refine ⟨31750766086189654922081527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169337419126344826251101477 31750766086189654922081527)
          ·
            refine ⟨47626149129284482383122291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31750766086189654922081527 47626149129284482383122291)
            ·
              refine ⟨71439223693926723574683437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47626149129284482383122291 71439223693926723574683437)
              ·
                refine ⟨26789708885222521340506289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71439223693926723574683437 26789708885222521340506289)
                ·
                  refine ⟨20092281663916891005379717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26789708885222521340506289 20092281663916891005379717)
                  ·
                    refine ⟨3767302811984417063508697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20092281663916891005379717 3767302811984417063508697)
                    ·
                      refine ⟨2825477108988312797631523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767302811984417063508697 2825477108988312797631523)
                      ·
                        rfl

theorem cell23_5502597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 4, 2].length) (baseStart_5502597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502597 prefixEnd_5502597 := by exact prefixLift 5502597
  have htrace : WordTrace (prefixWord ++ tailWord_5502597) baseStart_5502597 baseEnd_5502597 := by
    simpa [prefixWord, tailWord_5502597, baseEnd_5502597] using wordTrace_append hprefix tailTrace_5502597
  have hstable : (prefixWord ++ tailWord_5502597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502597).length < 2 ^ (prefixWord ++ tailWord_5502597).sum := by decide
  have hdescent : baseEnd_5502597 < baseStart_5502597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502637 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 6]
def baseStart_5502637 : Nat := 118140960795 + 5502637 * 2 ^ 59
def prefixEnd_5502637 : Nat := 4983230072969 + 3 ^ 40 * 5502637 * 2
def baseEnd_5502637 : Nat := 313944183134943626792371

theorem tailTrace_5502637 : CollatzResearch.WordTrace tailWord_5502637 prefixEnd_5502637 313944183134943626792371 := by
  unfold tailWord_5502637
  simp only [CollatzResearch.WordTrace]
  refine ⟨200697659365893399425354165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133798439577262266283569443 200697659365893399425354165)
  ·
    refine ⟨18815405565552506196126953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200697659365893399425354165 18815405565552506196126953)
    ·
      refine ⟨14111554174164379647095215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18815405565552506196126953 14111554174164379647095215)
      ·
        refine ⟨21167331261246569470642823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14111554174164379647095215 21167331261246569470642823)
        ·
          refine ⟨31750996891869854205964235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21167331261246569470642823 31750996891869854205964235)
          ·
            refine ⟨47626495337804781308946353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31750996891869854205964235 47626495337804781308946353)
            ·
              refine ⟨35719871503353585981709765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47626495337804781308946353 35719871503353585981709765)
              ·
                refine ⟨6697475906878797371570581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35719871503353585981709765 6697475906878797371570581)
                ·
                  refine ⟨313944183134943626792371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6697475906878797371570581 313944183134943626792371)
                  ·
                    rfl

theorem cell23_5502637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_5502637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502637 prefixEnd_5502637 := by exact prefixLift 5502637
  have htrace : WordTrace (prefixWord ++ tailWord_5502637) baseStart_5502637 baseEnd_5502637 := by
    simpa [prefixWord, tailWord_5502637, baseEnd_5502637] using wordTrace_append hprefix tailTrace_5502637
  have hstable : (prefixWord ++ tailWord_5502637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502637).length < 2 ^ (prefixWord ++ tailWord_5502637).sum := by decide
  have hdescent : baseEnd_5502637 < baseStart_5502637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502654 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_5502654 : Nat := 118140960795 + 5502654 * 2 ^ 59
def prefixEnd_5502654 : Nat := 4983230072969 + 3 ^ 40 * 5502654 * 2
def baseEnd_5502654 : Nat := 313945153042846563846529

theorem tailTrace_5502654 : CollatzResearch.WordTrace tailWord_5502654 prefixEnd_5502654 313945153042846563846529 := by
  unfold tailWord_5502654
  simp only [CollatzResearch.WordTrace]
  refine ⟨25087284925853976416090377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133798852937887874219148677 25087284925853976416090377)
  ·
    refine ⟨18815463694390482312067783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25087284925853976416090377 18815463694390482312067783)
    ·
      refine ⟨28223195541585723468101675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18815463694390482312067783 28223195541585723468101675)
      ·
        refine ⟨42334793312378585202152513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28223195541585723468101675 42334793312378585202152513)
        ·
          refine ⟨31751094984283938901614385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42334793312378585202152513 31751094984283938901614385)
          ·
            refine ⟨23813321238212954176210789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31751094984283938901614385 23813321238212954176210789)
            ·
              refine ⟨4464997732164928908039523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23813321238212954176210789 4464997732164928908039523)
              ·
                refine ⟨6697496598247393362059285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4464997732164928908039523 6697496598247393362059285)
                ·
                  refine ⟨313945153042846563846529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6697496598247393362059285 313945153042846563846529)
                  ·
                    rfl

theorem cell23_5502654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_5502654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502654 prefixEnd_5502654 := by exact prefixLift 5502654
  have htrace : WordTrace (prefixWord ++ tailWord_5502654) baseStart_5502654 baseEnd_5502654 := by
    simpa [prefixWord, tailWord_5502654, baseEnd_5502654] using wordTrace_append hprefix tailTrace_5502654
  have hstable : (prefixWord ++ tailWord_5502654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502654).length < 2 ^ (prefixWord ++ tailWord_5502654).sum := by decide
  have hdescent : baseEnd_5502654 < baseStart_5502654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502698 : List Nat := [3, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_5502698 : Nat := 118140960795 + 5502698 * 2 ^ 59
def prefixEnd_5502698 : Nat := 4983230072969 + 3 ^ 40 * 5502698 * 2
def baseEnd_5502698 : Nat := 2825528970534416902468559

theorem tailTrace_5502698 : CollatzResearch.WordTrace tailWord_5502698 prefixEnd_5502698 2825528970534416902468559 := by
  unfold tailWord_5502698
  simp only [CollatzResearch.WordTrace]
  refine ⟨50174971054668101710831187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133799922812448271228883165 50174971054668101710831187)
  ·
    refine ⟨75262456582002152566246781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50174971054668101710831187 75262456582002152566246781)
    ·
      refine ⟨28223421218250807212342543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75262456582002152566246781 28223421218250807212342543)
      ·
        refine ⟨42335131827376210818513815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28223421218250807212342543 42335131827376210818513815)
        ·
          refine ⟨63502697741064316227770723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42335131827376210818513815 63502697741064316227770723)
          ·
            refine ⟨95254046611596474341656085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63502697741064316227770723 95254046611596474341656085)
            ·
              refine ⟨4465033434918584734765129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95254046611596474341656085 4465033434918584734765129)
              ·
                refine ⟨3348775076188938551073847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4465033434918584734765129 3348775076188938551073847)
                ·
                  refine ⟨5023162614283407826610771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348775076188938551073847 5023162614283407826610771)
                  ·
                    refine ⟨7534743921425111739916157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5023162614283407826610771 7534743921425111739916157)
                    ·
                      refine ⟨2825528970534416902468559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7534743921425111739916157 2825528970534416902468559)
                      ·
                        rfl

theorem cell23_5502698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_5502698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502698 prefixEnd_5502698 := by exact prefixLift 5502698
  have htrace : WordTrace (prefixWord ++ tailWord_5502698) baseStart_5502698 baseEnd_5502698 := by
    simpa [prefixWord, tailWord_5502698, baseEnd_5502698] using wordTrace_append hprefix tailTrace_5502698
  have hstable : (prefixWord ++ tailWord_5502698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502698).length < 2 ^ (prefixWord ++ tailWord_5502698).sum := by decide
  have hdescent : baseEnd_5502698 < baseStart_5502698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502700 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_5502700 : Nat := 118140960795 + 5502700 * 2 ^ 59
def prefixEnd_5502700 : Nat := 4983230072969 + 3 ^ 40 * 5502700 * 2
def baseEnd_5502700 : Nat := 2825529997495725894643549

theorem tailTrace_5502700 : CollatzResearch.WordTrace tailWord_5502700 prefixEnd_5502700 2825529997495725894643549 := by
  unfold tailWord_5502700
  simp only [CollatzResearch.WordTrace]
  refine ⟨100349978582332580592448777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133799971443110107456598369 100349978582332580592448777)
  ·
    refine ⟨75262483936749435444336583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100349978582332580592448777 75262483936749435444336583)
    ·
      refine ⟨112893725905124153166504875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75262483936749435444336583 112893725905124153166504875)
      ·
        refine ⟨169340588857686229749757313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112893725905124153166504875 169340588857686229749757313)
        ·
          refine ⟨127005441643264672312317985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169340588857686229749757313 127005441643264672312317985)
          ·
            refine ⟨95254081232448504234238489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127005441643264672312317985 95254081232448504234238489)
            ·
              refine ⟨71440560924336378175678867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95254081232448504234238489 71440560924336378175678867)
              ·
                refine ⟨107160841386504567263518301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71440560924336378175678867 107160841386504567263518301)
                ·
                  refine ⟨40185315519939212723819363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107160841386504567263518301 40185315519939212723819363)
                  ·
                    refine ⟨60277973279908819085729045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40185315519939212723819363 60277973279908819085729045)
                    ·
                      refine ⟨2825529997495725894643549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60277973279908819085729045 2825529997495725894643549)
                      ·
                        rfl

theorem cell23_5502700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_5502700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502700 prefixEnd_5502700 := by exact prefixLift 5502700
  have htrace : WordTrace (prefixWord ++ tailWord_5502700) baseStart_5502700 baseEnd_5502700 := by
    simpa [prefixWord, tailWord_5502700, baseEnd_5502700] using wordTrace_append hprefix tailTrace_5502700
  have hstable : (prefixWord ++ tailWord_5502700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502700).length < 2 ^ (prefixWord ++ tailWord_5502700).sum := by decide
  have hdescent : baseEnd_5502700 < baseStart_5502700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502707 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 3]
def baseStart_5502707 : Nat := 118140960795 + 5502707 * 2 ^ 59
def prefixEnd_5502707 : Nat := 4983230072969 + 3 ^ 40 * 5502707 * 2
def baseEnd_5502707 : Nat := 2825533591860307367256017

theorem tailTrace_5502707 : CollatzResearch.WordTrace tailWord_5502707 prefixEnd_5502707 2825533591860307367256017 := by
  unfold tailWord_5502707
  simp only [CollatzResearch.WordTrace]
  refine ⟨200700212475639801380402375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133800141650426534253601583 200700212475639801380402375)
  ·
    refine ⟨301050318713459702070603563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200700212475639801380402375 301050318713459702070603563)
    ·
      refine ⟨451575478070189553105905345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301050318713459702070603563 451575478070189553105905345)
      ·
        refine ⟨338681608552642164829429009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451575478070189553105905345 338681608552642164829429009)
        ·
          refine ⟨254011206414481623622071757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338681608552642164829429009 254011206414481623622071757)
          ·
            refine ⟨95254202405430608858276909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254011206414481623622071757 95254202405430608858276909)
            ·
              refine ⟨35720325902036478321853841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95254202405430608858276909 35720325902036478321853841)
              ·
                refine ⟨26790244426527358741390381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35720325902036478321853841 26790244426527358741390381)
                ·
                  refine ⟨10046341659947759528021393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26790244426527358741390381 10046341659947759528021393)
                  ·
                    refine ⟨7534756244960819646016045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10046341659947759528021393 7534756244960819646016045)
                    ·
                      refine ⟨2825533591860307367256017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7534756244960819646016045 2825533591860307367256017)
                      ·
                        rfl

theorem cell23_5502707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 3].length) (baseStart_5502707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502707 prefixEnd_5502707 := by exact prefixLift 5502707
  have htrace : WordTrace (prefixWord ++ tailWord_5502707) baseStart_5502707 baseEnd_5502707 := by
    simpa [prefixWord, tailWord_5502707, baseEnd_5502707] using wordTrace_append hprefix tailTrace_5502707
  have hstable : (prefixWord ++ tailWord_5502707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502707).length < 2 ^ (prefixWord ++ tailWord_5502707).sum := by decide
  have hdescent : baseEnd_5502707 < baseStart_5502707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502724 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_5502724 : Nat := 118140960795 + 5502724 * 2 ^ 59
def prefixEnd_5502724 : Nat := 4983230072969 + 3 ^ 40 * 5502724 * 2
def baseEnd_5502724 : Nat := 2825542321031433800743439

theorem tailTrace_5502724 : CollatzResearch.WordTrace tailWord_5502724 prefixEnd_5502724 2825542321031433800743439 := by
  unfold tailWord_5502724
  simp only [CollatzResearch.WordTrace]
  refine ⟨100350416258289106641885613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133800555011052142189180817 100350416258289106641885613)
  ·
    refine ⟨37631406096858414990707105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100350416258289106641885613 37631406096858414990707105)
    ·
      refine ⟨28223554572643811243030329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37631406096858414990707105 28223554572643811243030329)
      ·
        refine ⟨21167665929482858432272747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28223554572643811243030329 21167665929482858432272747)
        ·
          refine ⟨31751498894224287648409121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21167665929482858432272747 31751498894224287648409121)
          ·
            refine ⟨23813624170668215736306841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31751498894224287648409121 23813624170668215736306841)
            ·
              refine ⟨17860218128001161802230131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23813624170668215736306841 17860218128001161802230131)
              ·
                refine ⟨26790327192001742703345197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17860218128001161802230131 26790327192001742703345197)
                ·
                  refine ⟨10046372697000653513754449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26790327192001742703345197 10046372697000653513754449)
                  ·
                    refine ⟨7534779522750490135315837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10046372697000653513754449 7534779522750490135315837)
                    ·
                      refine ⟨2825542321031433800743439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7534779522750490135315837 2825542321031433800743439)
                      ·
                        rfl

theorem cell23_5502724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_5502724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502724 prefixEnd_5502724 := by exact prefixLift 5502724
  have htrace : WordTrace (prefixWord ++ tailWord_5502724) baseStart_5502724 baseEnd_5502724 := by
    simpa [prefixWord, tailWord_5502724, baseEnd_5502724] using wordTrace_append hprefix tailTrace_5502724
  have hstable : (prefixWord ++ tailWord_5502724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502724).length < 2 ^ (prefixWord ++ tailWord_5502724).sum := by decide
  have hdescent : baseEnd_5502724 < baseStart_5502724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502738 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_5502738 : Nat := 118140960795 + 5502738 * 2 ^ 59
def prefixEnd_5502738 : Nat := 4983230072969 + 3 ^ 40 * 5502738 * 2
def baseEnd_5502738 : Nat := 2825549509760596745968375

theorem tailTrace_5502738 : CollatzResearch.WordTrace tailWord_5502738 prefixEnd_5502738 2825549509760596745968375 := by
  unfold tailWord_5502738
  simp only [CollatzResearch.WordTrace]
  refine ⟨50175335784631873418695217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133800895425684995783187245 50175335784631873418695217)
  ·
    refine ⟨37631501838473905064021413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50175335784631873418695217 37631501838473905064021413)
    ·
      refine ⟨7055906594713857199504015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37631501838473905064021413 7055906594713857199504015)
      ·
        refine ⟨10583859892070785799256023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7055906594713857199504015 10583859892070785799256023)
        ·
          refine ⟨15875789838106178698884035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10583859892070785799256023 15875789838106178698884035)
          ·
            refine ⟨23813684757159268048326053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15875789838106178698884035 23813684757159268048326053)
            ·
              refine ⟨4465065891967362759061135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23813684757159268048326053 4465065891967362759061135)
              ·
                refine ⟨6697598837951044138591703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465065891967362759061135 6697598837951044138591703)
                ·
                  refine ⟨10046398256926566207887555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6697598837951044138591703 10046398256926566207887555)
                  ·
                    refine ⟨15069597385389849311831333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10046398256926566207887555 15069597385389849311831333)
                    ·
                      refine ⟨2825549509760596745968375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15069597385389849311831333 2825549509760596745968375)
                      ·
                        rfl

theorem cell23_5502738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_5502738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502738 prefixEnd_5502738 := by exact prefixLift 5502738
  have htrace : WordTrace (prefixWord ++ tailWord_5502738) baseStart_5502738 baseEnd_5502738 := by
    simpa [prefixWord, tailWord_5502738, baseEnd_5502738] using wordTrace_append hprefix tailTrace_5502738
  have hstable : (prefixWord ++ tailWord_5502738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502738).length < 2 ^ (prefixWord ++ tailWord_5502738).sum := by decide
  have hdescent : baseEnd_5502738 < baseStart_5502738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502741 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 1, 2, 3]
def baseStart_5502741 : Nat := 118140960795 + 5502741 * 2 ^ 59
def prefixEnd_5502741 : Nat := 4983230072969 + 3 ^ 40 * 5502741 * 2
def baseEnd_5502741 : Nat := 2825551050202560234230861

theorem tailTrace_5502741 : CollatzResearch.WordTrace tailWord_5502741 prefixEnd_5502741 2825551050202560234230861 := by
  unfold tailWord_5502741
  simp only [CollatzResearch.WordTrace]
  refine ⟨200701452557516625187140077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133800968371677750124760051 200701452557516625187140077)
  ·
    refine ⟨75263044709068734445177529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200701452557516625187140077 75263044709068734445177529)
    ·
      refine ⟨56447283531801550833883147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75263044709068734445177529 56447283531801550833883147)
      ·
        refine ⟨84670925297702326250824721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56447283531801550833883147 84670925297702326250824721)
        ·
          refine ⟨63503193973276744688118541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84670925297702326250824721 63503193973276744688118541)
          ·
            refine ⟨23813697739978779258044453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63503193973276744688118541 23813697739978779258044453)
            ·
              refine ⟨4465068326246021110883335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23813697739978779258044453 4465068326246021110883335)
              ·
                refine ⟨6697602489369031666325003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465068326246021110883335 6697602489369031666325003)
                ·
                  refine ⟨10046403734053547499487505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6697602489369031666325003 10046403734053547499487505)
                  ·
                    refine ⟨7534802800540160624615629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10046403734053547499487505 7534802800540160624615629)
                    ·
                      refine ⟨2825551050202560234230861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7534802800540160624615629 2825551050202560234230861)
                      ·
                        rfl

theorem cell23_5502741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_5502741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502741 prefixEnd_5502741 := by exact prefixLift 5502741
  have htrace : WordTrace (prefixWord ++ tailWord_5502741) baseStart_5502741 baseEnd_5502741 := by
    simpa [prefixWord, tailWord_5502741, baseEnd_5502741] using wordTrace_append hprefix tailTrace_5502741
  have hstable : (prefixWord ++ tailWord_5502741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502741).length < 2 ^ (prefixWord ++ tailWord_5502741).sum := by decide
  have hdescent : baseEnd_5502741 < baseStart_5502741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502771 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 1, 3, 3]
def baseStart_5502771 : Nat := 118140960795 + 5502771 * 2 ^ 59
def prefixEnd_5502771 : Nat := 4983230072969 + 3 ^ 40 * 5502771 * 2
def baseEnd_5502771 : Nat := 2825566454622195116855723

theorem tailTrace_5502771 : CollatzResearch.WordTrace tailWord_5502771 prefixEnd_5502771 2825566454622195116855723 := by
  unfold tailWord_5502771
  simp only [CollatzResearch.WordTrace]
  refine ⟨200702546747407940310732167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133801697831605293540488111 200702546747407940310732167)
  ·
    refine ⟨301053820121111910466098251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200702546747407940310732167 301053820121111910466098251)
    ·
      refine ⟨451580730181667865699147377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301053820121111910466098251 451580730181667865699147377)
      ·
        refine ⟨338685547636250899274360533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451580730181667865699147377 338685547636250899274360533)
        ·
          refine ⟨7937942522724630451742825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 338685547636250899274360533 7937942522724630451742825)
          ·
            refine ⟨5953456892043472838807119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7937942522724630451742825 5953456892043472838807119)
            ·
              refine ⟨8930185338065209258210679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5953456892043472838807119 8930185338065209258210679)
              ·
                refine ⟨13395278007097813887316019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8930185338065209258210679 13395278007097813887316019)
                ·
                  refine ⟨20092917010646720830974029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13395278007097813887316019 20092917010646720830974029)
                  ·
                    refine ⟨7534843878992520311615261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20092917010646720830974029 7534843878992520311615261)
                    ·
                      refine ⟨2825566454622195116855723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7534843878992520311615261 2825566454622195116855723)
                      ·
                        rfl

theorem cell23_5502771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 3, 3].length) (baseStart_5502771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502771 prefixEnd_5502771 := by exact prefixLift 5502771
  have htrace : WordTrace (prefixWord ++ tailWord_5502771) baseStart_5502771 baseEnd_5502771 := by
    simpa [prefixWord, tailWord_5502771, baseEnd_5502771] using wordTrace_append hprefix tailTrace_5502771
  have hstable : (prefixWord ++ tailWord_5502771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502771).length < 2 ^ (prefixWord ++ tailWord_5502771).sum := by decide
  have hdescent : baseEnd_5502771 < baseStart_5502771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502794 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2]
def baseStart_5502794 : Nat := 118140960795 + 5502794 * 2 ^ 59
def prefixEnd_5502794 : Nat := 4983230072969 + 3 ^ 40 * 5502794 * 2
def baseEnd_5502794 : Nat := 2825578264677248526868117

theorem tailTrace_5502794 : CollatzResearch.WordTrace tailWord_5502794 prefixEnd_5502794 2825578264677248526868117 := by
  unfold tailWord_5502794
  simp only [CollatzResearch.WordTrace]
  refine ⟨50175846406581153809704859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133802257084216410159212957 50175846406581153809704859)
  ·
    refine ⟨75263769609871730714557289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50175846406581153809704859 75263769609871730714557289)
    ·
      refine ⟨56447827207403798035917967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75263769609871730714557289 56447827207403798035917967)
      ·
        refine ⟨84671740811105697053876951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56447827207403798035917967 84671740811105697053876951)
        ·
          refine ⟨127007611216658545580815427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84671740811105697053876951 127007611216658545580815427)
          ·
            refine ⟨190511416824987818371223141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127007611216658545580815427 190511416824987818371223141)
            ·
              refine ⟨35720890654685215944604339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190511416824987818371223141 35720890654685215944604339)
              ·
                refine ⟨53581335982027823916906509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35720890654685215944604339 53581335982027823916906509)
                ·
                  refine ⟨20093000993260433968839941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53581335982027823916906509 20093000993260433968839941)
                  ·
                    refine ⟨3767437686236331369157489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20093000993260433968839941 3767437686236331369157489)
                    ·
                      refine ⟨2825578264677248526868117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767437686236331369157489 2825578264677248526868117)
                      ·
                        rfl

theorem cell23_5502794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_5502794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502794 prefixEnd_5502794 := by exact prefixLift 5502794
  have htrace : WordTrace (prefixWord ++ tailWord_5502794) baseStart_5502794 baseEnd_5502794 := by
    simpa [prefixWord, tailWord_5502794, baseEnd_5502794] using wordTrace_append hprefix tailTrace_5502794
  have hstable : (prefixWord ++ tailWord_5502794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502794).length < 2 ^ (prefixWord ++ tailWord_5502794).sum := by decide
  have hdescent : baseEnd_5502794 < baseStart_5502794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502827 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 3]
def baseStart_5502827 : Nat := 118140960795 + 5502827 * 2 ^ 59
def prefixEnd_5502827 : Nat := 4983230072969 + 3 ^ 40 * 5502827 * 2
def baseEnd_5502827 : Nat := 2825595209538846897755465

theorem tailTrace_5502827 : CollatzResearch.WordTrace tailWord_5502827 prefixEnd_5502827 2825595209538846897755465 := by
  unfold tailWord_5502827
  simp only [CollatzResearch.WordTrace]
  refine ⟨200704589235205061874770735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133803059490136707916513823 200704589235205061874770735)
  ·
    refine ⟨301056883852807592812156103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200704589235205061874770735 301056883852807592812156103)
    ·
      refine ⟨451585325779211389218234155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301056883852807592812156103 451585325779211389218234155)
      ·
        refine ⟨677377988668817083827351233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451585325779211389218234155 677377988668817083827351233)
        ·
          refine ⟨508033491501612812870513425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677377988668817083827351233 508033491501612812870513425)
          ·
            refine ⟨381025118626209609652885069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508033491501612812870513425 381025118626209609652885069)
            ·
              refine ⟨142884419484828603619831901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 381025118626209609652885069 142884419484828603619831901)
              ·
                refine ⟨53581657306810726357436963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142884419484828603619831901 53581657306810726357436963)
                ·
                  refine ⟨80372485960216089536155445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53581657306810726357436963 80372485960216089536155445)
                  ·
                    refine ⟨7534920558770258394014573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80372485960216089536155445 7534920558770258394014573)
                    ·
                      refine ⟨2825595209538846897755465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7534920558770258394014573 2825595209538846897755465)
                      ·
                        rfl

theorem cell23_5502827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 3].length) (baseStart_5502827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502827 prefixEnd_5502827 := by exact prefixLift 5502827
  have htrace : WordTrace (prefixWord ++ tailWord_5502827) baseStart_5502827 baseEnd_5502827 := by
    simpa [prefixWord, tailWord_5502827, baseEnd_5502827] using wordTrace_append hprefix tailTrace_5502827
  have hstable : (prefixWord ++ tailWord_5502827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502827).length < 2 ^ (prefixWord ++ tailWord_5502827).sum := by decide
  have hdescent : baseEnd_5502827 < baseStart_5502827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502828 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 2, 2, 2]
def baseStart_5502828 : Nat := 118140960795 + 5502828 * 2 ^ 59
def prefixEnd_5502828 : Nat := 4983230072969 + 3 ^ 40 * 5502828 * 2
def baseEnd_5502828 : Nat := 2825595723019501393842961

theorem tailTrace_5502828 : CollatzResearch.WordTrace tailWord_5502828 prefixEnd_5502828 2825595723019501393842961 := by
  unfold tailWord_5502828
  simp only [CollatzResearch.WordTrace]
  refine ⟨100352312854100719522778569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133803083805467626030371425 100352312854100719522778569)
  ·
    refine ⟨75264234640575539642083927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100352312854100719522778569 75264234640575539642083927)
    ·
      refine ⟨112896351960863309463125891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75264234640575539642083927 112896351960863309463125891)
      ·
        refine ⟨169344527941294964194688837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112896351960863309463125891 169344527941294964194688837)
        ·
          refine ⟨31752098988992805786504157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169344527941294964194688837 31752098988992805786504157)
          ·
            refine ⟨11907037120872302169939059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31752098988992805786504157 11907037120872302169939059)
            ·
              refine ⟨17860555681308453254908589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11907037120872302169939059 17860555681308453254908589)
              ·
                refine ⟨6697708380490669970590721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17860555681308453254908589 6697708380490669970590721)
                ·
                  refine ⟨5023281285368002477943041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6697708380490669970590721 5023281285368002477943041)
                  ·
                    refine ⟨3767460964026001858457281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5023281285368002477943041 3767460964026001858457281)
                    ·
                      refine ⟨2825595723019501393842961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767460964026001858457281 2825595723019501393842961)
                      ·
                        rfl

theorem cell23_5502828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 2, 2].length) (baseStart_5502828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502828 prefixEnd_5502828 := by exact prefixLift 5502828
  have htrace : WordTrace (prefixWord ++ tailWord_5502828) baseStart_5502828 baseEnd_5502828 := by
    simpa [prefixWord, tailWord_5502828, baseEnd_5502828] using wordTrace_append hprefix tailTrace_5502828
  have hstable : (prefixWord ++ tailWord_5502828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502828).length < 2 ^ (prefixWord ++ tailWord_5502828).sum := by decide
  have hdescent : baseEnd_5502828 < baseStart_5502828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502857 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_5502857 : Nat := 118140960795 + 5502857 * 2 ^ 59
def prefixEnd_5502857 : Nat := 4983230072969 + 3 ^ 40 * 5502857 * 2
def baseEnd_5502857 : Nat := 2825610613958481780380327

theorem tailTrace_5502857 : CollatzResearch.WordTrace tailWord_5502857 prefixEnd_5502857 2825610613958481780380327 := by
  unfold tailWord_5502857
  simp only [CollatzResearch.WordTrace]
  refine ⟨200705683425096376998362825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133803788950064251332241883 200705683425096376998362825)
  ·
    refine ⟨150529262568822282748772119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200705683425096376998362825 150529262568822282748772119)
    ·
      refine ⟨225793893853233424123158179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150529262568822282748772119 225793893853233424123158179)
      ·
        refine ⟨338690840779850136184737269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225793893853233424123158179 338690840779850136184737269)
        ·
          refine ⟨31752266323110950267319119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 338690840779850136184737269 31752266323110950267319119)
          ·
            refine ⟨47628399484666425400978679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31752266323110950267319119 47628399484666425400978679)
            ·
              refine ⟨71442599226999638101468019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47628399484666425400978679 71442599226999638101468019)
              ·
                refine ⟨107163898840499457152202029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71442599226999638101468019 107163898840499457152202029)
                ·
                  refine ⟨40186462065187296432075761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107163898840499457152202029 40186462065187296432075761)
                  ·
                    refine ⟨30139846548890472324056821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40186462065187296432075761 30139846548890472324056821)
                    ·
                      refine ⟨2825610613958481780380327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30139846548890472324056821 2825610613958481780380327)
                      ·
                        rfl

theorem cell23_5502857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_5502857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502857 prefixEnd_5502857 := by exact prefixLift 5502857
  have htrace : WordTrace (prefixWord ++ tailWord_5502857) baseStart_5502857 baseEnd_5502857 := by
    simpa [prefixWord, tailWord_5502857, baseEnd_5502857] using wordTrace_append hprefix tailTrace_5502857
  have hstable : (prefixWord ++ tailWord_5502857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502857).length < 2 ^ (prefixWord ++ tailWord_5502857).sum := by decide
  have hdescent : baseEnd_5502857 < baseStart_5502857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502862 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5502862 : Nat := 118140960795 + 5502862 * 2 ^ 59
def prefixEnd_5502862 : Nat := 4983230072969 + 3 ^ 40 * 5502862 * 2
def baseEnd_5502862 : Nat := 2825613181361754260817805

theorem tailTrace_5502862 : CollatzResearch.WordTrace tailWord_5502862 prefixEnd_5502862 2825613181361754260817805 := by
  unfold tailWord_5502862
  simp only [CollatzResearch.WordTrace]
  refine ⟨25088233223759782856536855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133803910526718841901529893 25088233223759782856536855)
  ·
    refine ⟨37632349835639674284805283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25088233223759782856536855 37632349835639674284805283)
    ·
      refine ⟨56448524753459511427207925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37632349835639674284805283 56448524753459511427207925)
      ·
        refine ⟨5292049195636829196300743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56448524753459511427207925 5292049195636829196300743)
        ·
          refine ⟨7938073793455243794451115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5292049195636829196300743 7938073793455243794451115)
          ·
            refine ⟨11907110690182865691676673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7938073793455243794451115 11907110690182865691676673)
            ·
              refine ⟨8930333017637149268757505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11907110690182865691676673 8930333017637149268757505)
              ·
                refine ⟨6697749763227861951568129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8930333017637149268757505 6697749763227861951568129)
                ·
                  refine ⟨5023312322420896463676097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6697749763227861951568129 5023312322420896463676097)
                  ·
                    refine ⟨3767484241815672347757073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5023312322420896463676097 3767484241815672347757073)
                    ·
                      refine ⟨2825613181361754260817805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767484241815672347757073 2825613181361754260817805)
                      ·
                        rfl

theorem cell23_5502862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5502862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502862 prefixEnd_5502862 := by exact prefixLift 5502862
  have htrace : WordTrace (prefixWord ++ tailWord_5502862) baseStart_5502862 baseEnd_5502862 := by
    simpa [prefixWord, tailWord_5502862, baseEnd_5502862] using wordTrace_append hprefix tailTrace_5502862
  have hstable : (prefixWord ++ tailWord_5502862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502862).length < 2 ^ (prefixWord ++ tailWord_5502862).sum := by decide
  have hdescent : baseEnd_5502862 < baseStart_5502862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502868 : List Nat := [2, 4, 2, 1, 1, 2, 4, 2, 5]
def baseStart_5502868 : Nat := 118140960795 + 5502868 * 2 ^ 59
def prefixEnd_5502868 : Nat := 4983230072969 + 3 ^ 40 * 5502868 * 2
def baseEnd_5502868 : Nat := 313957362471742359704753

theorem tailTrace_5502868 : CollatzResearch.WordTrace tailWord_5502868 prefixEnd_5502868 313957362471742359704753 := by
  unfold tailWord_5502868
  simp only [CollatzResearch.WordTrace]
  refine ⟨100353042314028262938506629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133804056418704350584675505 100353042314028262938506629)
  ·
    refine ⟨18816195433880299300969993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100353042314028262938506629 18816195433880299300969993)
    ·
      refine ⟨14112146575410224475727495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18816195433880299300969993 14112146575410224475727495)
      ·
        refine ⟨21168219863115336713591243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14112146575410224475727495 21168219863115336713591243)
        ·
          refine ⟨31752329794673005070386865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21168219863115336713591243 31752329794673005070386865)
          ·
            refine ⟨23814247346004753802790149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31752329794673005070386865 23814247346004753802790149)
            ·
              refine ⟨4465171377375891338023153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23814247346004753802790149 4465171377375891338023153)
              ·
                refine ⟨3348878533031918503517365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4465171377375891338023153 3348878533031918503517365)
                ·
                  refine ⟨313957362471742359704753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3348878533031918503517365 313957362471742359704753)
                  ·
                    rfl

theorem cell23_5502868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_5502868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502868 prefixEnd_5502868 := by exact prefixLift 5502868
  have htrace : WordTrace (prefixWord ++ tailWord_5502868) baseStart_5502868 baseEnd_5502868 := by
    simpa [prefixWord, tailWord_5502868, baseEnd_5502868] using wordTrace_append hprefix tailTrace_5502868
  have hstable : (prefixWord ++ tailWord_5502868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502868).length < 2 ^ (prefixWord ++ tailWord_5502868).sum := by decide
  have hdescent : baseEnd_5502868 < baseStart_5502868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502874 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_5502874 : Nat := 118140960795 + 5502874 * 2 ^ 59
def prefixEnd_5502874 : Nat := 4983230072969 + 3 ^ 40 * 5502874 * 2
def baseEnd_5502874 : Nat := 2825619343129608213867749

theorem tailTrace_5502874 : CollatzResearch.WordTrace tailWord_5502874 prefixEnd_5502874 2825619343129608213867749 := by
  unfold tailWord_5502874
  simp only [CollatzResearch.WordTrace]
  refine ⟨50176575866508697225432919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133804202310689859267821117 50176575866508697225432919)
  ·
    refine ⟨75264863799763045838149379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50176575866508697225432919 75264863799763045838149379)
    ·
      refine ⟨112897295699644568757224069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75264863799763045838149379 112897295699644568757224069)
      ·
        refine ⟨21168242943683356641979513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112897295699644568757224069 21168242943683356641979513)
        ·
          refine ⟨15876182207762517481484635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21168242943683356641979513 15876182207762517481484635)
          ·
            refine ⟨23814273311643776222226953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15876182207762517481484635 23814273311643776222226953)
            ·
              refine ⟨17860704983732832166670215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23814273311643776222226953 17860704983732832166670215)
              ·
                refine ⟨26791057475599248250005323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17860704983732832166670215 26791057475599248250005323)
                ·
                  refine ⟨40186586213398872375007985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26791057475599248250005323 40186586213398872375007985)
                  ·
                    refine ⟨30139939660049154281255989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40186586213398872375007985 30139939660049154281255989)
                    ·
                      refine ⟨2825619343129608213867749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30139939660049154281255989 2825619343129608213867749)
                      ·
                        rfl

theorem cell23_5502874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_5502874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502874 prefixEnd_5502874 := by exact prefixLift 5502874
  have htrace : WordTrace (prefixWord ++ tailWord_5502874) baseStart_5502874 baseEnd_5502874 := by
    simpa [prefixWord, tailWord_5502874, baseEnd_5502874] using wordTrace_append hprefix tailTrace_5502874
  have hstable : (prefixWord ++ tailWord_5502874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502874).length < 2 ^ (prefixWord ++ tailWord_5502874).sum := by decide
  have hdescent : baseEnd_5502874 < baseStart_5502874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502901 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_5502901 : Nat := 118140960795 + 5502901 * 2 ^ 59
def prefixEnd_5502901 : Nat := 4983230072969 + 3 ^ 40 * 5502901 * 2
def baseEnd_5502901 : Nat := 2825633207107279608230125

theorem tailTrace_5502901 : CollatzResearch.WordTrace tailWord_5502901 prefixEnd_5502901 2825633207107279608230125 := by
  unfold tailWord_5502901
  simp only [CollatzResearch.WordTrace]
  refine ⟨200707288236936972512964557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133804858824624648341976371 200707288236936972512964557)
  ·
    refine ⟨75265233088851364692361709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200707288236936972512964557 75265233088851364692361709)
    ·
      refine ⟨28224462408319261759635641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75265233088851364692361709 28224462408319261759635641)
      ·
        refine ⟨21168346806239446319726731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28224462408319261759635641 21168346806239446319726731)
        ·
          refine ⟨31752520209359169479590097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21168346806239446319726731 31752520209359169479590097)
          ·
            refine ⟨23814390157019377109692573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31752520209359169479590097 23814390157019377109692573)
            ·
              refine ⟨8930396308882266416134715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23814390157019377109692573 8930396308882266416134715)
              ·
                refine ⟨13395594463323399624202073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8930396308882266416134715 13395594463323399624202073)
                ·
                  refine ⟨10046695847492549718151555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13395594463323399624202073 10046695847492549718151555)
                  ·
                    refine ⟨15070043771238824577227333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10046695847492549718151555 15070043771238824577227333)
                    ·
                      refine ⟨2825633207107279608230125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15070043771238824577227333 2825633207107279608230125)
                      ·
                        rfl

theorem cell23_5502901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_5502901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502901 prefixEnd_5502901 := by exact prefixLift 5502901
  have htrace : WordTrace (prefixWord ++ tailWord_5502901) baseStart_5502901 baseEnd_5502901 := by
    simpa [prefixWord, tailWord_5502901, baseEnd_5502901] using wordTrace_append hprefix tailTrace_5502901
  have hstable : (prefixWord ++ tailWord_5502901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502901).length < 2 ^ (prefixWord ++ tailWord_5502901).sum := by decide
  have hdescent : baseEnd_5502901 < baseStart_5502901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502904 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 1, 4, 3]
def baseStart_5502904 : Nat := 118140960795 + 5502904 * 2 ^ 59
def prefixEnd_5502904 : Nat := 4983230072969 + 3 ^ 40 * 5502904 * 2
def baseEnd_5502904 : Nat := 2825634747549243096492611

theorem tailTrace_5502904 : CollatzResearch.WordTrace tailWord_5502904 prefixEnd_5502904 2825634747549243096492611 := by
  unfold tailWord_5502904
  simp only [CollatzResearch.WordTrace]
  refine ⟨100353698827963052012661883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133804931770617402683549177 100353698827963052012661883)
  ·
    refine ⟨150530548241944578018992825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100353698827963052012661883 150530548241944578018992825)
    ·
      refine ⟨112897911181458433514244619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150530548241944578018992825 112897911181458433514244619)
      ·
        refine ⟨169346866772187650271366929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112897911181458433514244619 169346866772187650271366929)
        ·
          refine ⟨127010150079140737703525197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169346866772187650271366929 127010150079140737703525197)
          ·
            refine ⟨47628806279677776638821949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127010150079140737703525197 47628806279677776638821949)
            ·
              refine ⟨17860802354879166239558231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47628806279677776638821949 17860802354879166239558231)
              ·
                refine ⟨26791203532318749359337347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17860802354879166239558231 26791203532318749359337347)
                ·
                  refine ⟨40186805298478124039006021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26791203532318749359337347 40186805298478124039006021)
                  ·
                    refine ⟨7535025993464648257313629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40186805298478124039006021 7535025993464648257313629)
                    ·
                      refine ⟨2825634747549243096492611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7535025993464648257313629 2825634747549243096492611)
                      ·
                        rfl

theorem cell23_5502904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_5502904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502904 prefixEnd_5502904 := by exact prefixLift 5502904
  have htrace : WordTrace (prefixWord ++ tailWord_5502904) baseStart_5502904 baseEnd_5502904 := by
    simpa [prefixWord, tailWord_5502904, baseEnd_5502904] using wordTrace_append hprefix tailTrace_5502904
  have hstable : (prefixWord ++ tailWord_5502904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502904).length < 2 ^ (prefixWord ++ tailWord_5502904).sum := by decide
  have hdescent : baseEnd_5502904 < baseStart_5502904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502924 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 8]
def baseStart_5502924 : Nat := 118140960795 + 5502924 * 2 ^ 59
def prefixEnd_5502924 : Nat := 4983230072969 + 3 ^ 40 * 5502924 * 2
def baseEnd_5502924 : Nat := 313960557462481446471391

theorem tailTrace_5502924 : CollatzResearch.WordTrace tailWord_5502924 prefixEnd_5502924 313960557462481446471391 := by
  unfold tailWord_5502924
  simp only [CollatzResearch.WordTrace]
  refine ⟨100354063557926823720525913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133805418077235764960701217 100354063557926823720525913)
  ·
    refine ⟨75265547668445117790394435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100354063557926823720525913 75265547668445117790394435)
    ·
      refine ⟨112898321502667676685591653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75265547668445117790394435 112898321502667676685591653)
      ·
        refine ⟨21168435281750189378548435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112898321502667676685591653 21168435281750189378548435)
        ·
          refine ⟨31752652922625284067822653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21168435281750189378548435 31752652922625284067822653)
          ·
            refine ⟨11907244845984481525433495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31752652922625284067822653 11907244845984481525433495)
            ·
              refine ⟨17860867268976722288150243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11907244845984481525433495 17860867268976722288150243)
              ·
                refine ⟨26791300903465083432225365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17860867268976722288150243 26791300903465083432225365)
                ·
                  refine ⟨313960557462481446471391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26791300903465083432225365 313960557462481446471391)
                  ·
                    rfl

theorem cell23_5502924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_5502924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502924 prefixEnd_5502924 := by exact prefixLift 5502924
  have htrace : WordTrace (prefixWord ++ tailWord_5502924) baseStart_5502924 baseEnd_5502924 := by
    simpa [prefixWord, tailWord_5502924, baseEnd_5502924] using wordTrace_append hprefix tailTrace_5502924
  have hstable : (prefixWord ++ tailWord_5502924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502924).length < 2 ^ (prefixWord ++ tailWord_5502924).sum := by decide
  have hdescent : baseEnd_5502924 < baseStart_5502924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5502927 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_5502927 : Nat := 118140960795 + 5502927 * 2 ^ 59
def prefixEnd_5502927 : Nat := 4983230072969 + 3 ^ 40 * 5502927 * 2
def baseEnd_5502927 : Nat := 2825646557604296506505005

theorem tailTrace_5502927 : CollatzResearch.WordTrace tailWord_5502927 prefixEnd_5502927 2825646557604296506505005 := by
  unfold tailWord_5502927
  simp only [CollatzResearch.WordTrace]
  refine ⟨200708236534842778953411035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133805491023228519302274023 200708236534842778953411035)
  ·
    refine ⟨301062354802264168430116553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200708236534842778953411035 301062354802264168430116553)
    ·
      refine ⟨225796766101698126322587415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301062354802264168430116553 225796766101698126322587415)
      ·
        refine ⟨338695149152547189483881123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225796766101698126322587415 338695149152547189483881123)
        ·
          refine ⟨508042723728820784225821685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338695149152547189483881123 508042723728820784225821685)
          ·
            refine ⟨47629005349576948521170783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 508042723728820784225821685 47629005349576948521170783)
            ·
              refine ⟨71443508024365422781756175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47629005349576948521170783 71443508024365422781756175)
              ·
                refine ⟨107165262036548134172634263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71443508024365422781756175 107165262036548134172634263)
                ·
                  refine ⟨160747893054822201258951395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107165262036548134172634263 160747893054822201258951395)
                  ·
                    refine ⟨241121839582233301888427093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 160747893054822201258951395 241121839582233301888427093)
                    ·
                      refine ⟨2825646557604296506505005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 241121839582233301888427093 2825646557604296506505005)
                      ·
                        rfl

theorem cell23_5502927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_5502927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5502927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5502927 prefixEnd_5502927 := by exact prefixLift 5502927
  have htrace : WordTrace (prefixWord ++ tailWord_5502927) baseStart_5502927 baseEnd_5502927 := by
    simpa [prefixWord, tailWord_5502927, baseEnd_5502927] using wordTrace_append hprefix tailTrace_5502927
  have hstable : (prefixWord ++ tailWord_5502927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5502927).length < 2 ^ (prefixWord ++ tailWord_5502927).sum := by decide
  have hdescent : baseEnd_5502927 < baseStart_5502927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5502927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503011 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 3]
def baseStart_5503011 : Nat := 118140960795 + 5503011 * 2 ^ 59
def prefixEnd_5503011 : Nat := 4983230072969 + 3 ^ 40 * 5503011 * 2
def baseEnd_5503011 : Nat := 2825689689979274177854619

theorem tailTrace_5503011 : CollatzResearch.WordTrace tailWord_5503011 prefixEnd_5503011 2825689689979274177854619 := by
  unfold tailWord_5503011
  simp only [CollatzResearch.WordTrace]
  refine ⟨200711300266538461299468887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133807533511025640866312591 200711300266538461299468887)
  ·
    refine ⟨301066950399807691949203331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200711300266538461299468887 301066950399807691949203331)
    ·
      refine ⟨451600425599711537923804997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301066950399807691949203331 451600425599711537923804997)
      ·
        refine ⟨84675079799945913360713437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 451600425599711537923804997 84675079799945913360713437)
        ·
          refine ⟨31753154924979717510267539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84675079799945913360713437 31753154924979717510267539)
          ·
            refine ⟨47629732387469576265401309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31753154924979717510267539 47629732387469576265401309)
            ·
              refine ⟨17861149645301091099525491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47629732387469576265401309 17861149645301091099525491)
              ·
                refine ⟨26791724467951636649288237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17861149645301091099525491 26791724467951636649288237)
                ·
                  refine ⟨10046896675481863743483089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26791724467951636649288237 10046896675481863743483089)
                  ·
                    refine ⟨7535172506611397807612317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10046896675481863743483089 7535172506611397807612317)
                    ·
                      refine ⟨2825689689979274177854619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7535172506611397807612317 2825689689979274177854619)
                      ·
                        rfl

theorem cell23_5503011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_5503011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503011 prefixEnd_5503011 := by exact prefixLift 5503011
  have htrace : WordTrace (prefixWord ++ tailWord_5503011) baseStart_5503011 baseEnd_5503011 := by
    simpa [prefixWord, tailWord_5503011, baseEnd_5503011] using wordTrace_append hprefix tailTrace_5503011
  have hstable : (prefixWord ++ tailWord_5503011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503011).length < 2 ^ (prefixWord ++ tailWord_5503011).sum := by decide
  have hdescent : baseEnd_5503011 < baseStart_5503011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503085 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_5503085 : Nat := 118140960795 + 5503085 * 2 ^ 59
def prefixEnd_5503085 : Nat := 4983230072969 + 3 ^ 40 * 5503085 * 2
def baseEnd_5503085 : Nat := 2825727687547706888329279

theorem tailTrace_5503085 : CollatzResearch.WordTrace tailWord_5503085 prefixEnd_5503085 2825727687547706888329279 := by
  unfold tailWord_5503085
  simp only [CollatzResearch.WordTrace]
  refine ⟨200713999268270371937662709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133809332845513581291775139 200713999268270371937662709)
  ·
    refine ⟨18816937431400347369155879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200713999268270371937662709 18816937431400347369155879)
    ·
      refine ⟨28225406147100521053733819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18816937431400347369155879 28225406147100521053733819)
      ·
        refine ⟨42338109220650781580600729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28225406147100521053733819 42338109220650781580600729)
        ·
          refine ⟨31753581915488086185450547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42338109220650781580600729 31753581915488086185450547)
          ·
            refine ⟨47630372873232129278175821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31753581915488086185450547 47630372873232129278175821)
            ·
              refine ⟨17861389827462048479315933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47630372873232129278175821 17861389827462048479315933)
              ·
                refine ⟨6698021185298268179743475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17861389827462048479315933 6698021185298268179743475)
                ·
                  refine ⟨10047031777947402269615213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6698021185298268179743475 10047031777947402269615213)
                  ·
                    refine ⟨3767636916730275851105705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10047031777947402269615213 3767636916730275851105705)
                    ·
                      refine ⟨2825727687547706888329279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767636916730275851105705 2825727687547706888329279)
                      ·
                        rfl

theorem cell23_5503085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_5503085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503085 prefixEnd_5503085 := by exact prefixLift 5503085
  have htrace : WordTrace (prefixWord ++ tailWord_5503085) baseStart_5503085 baseEnd_5503085 := by
    simpa [prefixWord, tailWord_5503085, baseEnd_5503085] using wordTrace_append hprefix tailTrace_5503085
  have hstable : (prefixWord ++ tailWord_5503085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503085).length < 2 ^ (prefixWord ++ tailWord_5503085).sum := by decide
  have hdescent : baseEnd_5503085 < baseStart_5503085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503111 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_5503111 : Nat := 118140960795 + 5503111 * 2 ^ 59
def prefixEnd_5503111 : Nat := 4983230072969 + 3 ^ 40 * 5503111 * 2
def baseEnd_5503111 : Nat := 2825741038044723786604159

theorem tailTrace_5503111 : CollatzResearch.WordTrace tailWord_5503111 prefixEnd_5503111 2825741038044723786604159 := by
  unfold tailWord_5503111
  simp only [CollatzResearch.WordTrace]
  refine ⟨200714947566176178378109187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133809965044117452252072791 200714947566176178378109187)
  ·
    refine ⟨301072421349264267567163781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200714947566176178378109187 301072421349264267567163781)
    ·
      refine ⟨56451079002987050168843209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301072421349264267567163781 56451079002987050168843209)
      ·
        refine ⟨42338309252240287626632407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56451079002987050168843209 42338309252240287626632407)
        ·
          refine ⟨63507463878360431439948611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42338309252240287626632407 63507463878360431439948611)
          ·
            refine ⟨95261195817540647159922917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63507463878360431439948611 95261195817540647159922917)
            ·
              refine ⟨17861474215788871342485547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95261195817540647159922917 17861474215788871342485547)
              ·
                refine ⟨26792211323683307013728321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17861474215788871342485547 26792211323683307013728321)
                ·
                  refine ⟨20094158492762480260296241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26792211323683307013728321 20094158492762480260296241)
                  ·
                    refine ⟨15070618869571860195222181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20094158492762480260296241 15070618869571860195222181)
                    ·
                      refine ⟨2825741038044723786604159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15070618869571860195222181 2825741038044723786604159)
                      ·
                        rfl

theorem cell23_5503111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_5503111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503111 prefixEnd_5503111 := by exact prefixLift 5503111
  have htrace : WordTrace (prefixWord ++ tailWord_5503111) baseStart_5503111 baseEnd_5503111 := by
    simpa [prefixWord, tailWord_5503111, baseEnd_5503111] using wordTrace_append hprefix tailTrace_5503111
  have hstable : (prefixWord ++ tailWord_5503111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503111).length < 2 ^ (prefixWord ++ tailWord_5503111).sum := by decide
  have hdescent : baseEnd_5503111 < baseStart_5503111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503161 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 5]
def baseStart_5503161 : Nat := 118140960795 + 5503161 * 2 ^ 59
def prefixEnd_5503161 : Nat := 4983230072969 + 3 ^ 40 * 5503161 * 2
def baseEnd_5503161 : Nat := 2825766712077448590978929

theorem tailTrace_5503161 : CollatzResearch.WordTrace tailWord_5503161 prefixEnd_5503161 2825766712077448590978929 := by
  unfold tailWord_5503161
  simp only [CollatzResearch.WordTrace]
  refine ⟨200716771215995036917429337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133811180810663357944952891 200716771215995036917429337)
  ·
    refine ⟨150537578411996277688072003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200716771215995036917429337 150537578411996277688072003)
    ·
      refine ⟨225806367617994416532108005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150537578411996277688072003 225806367617994416532108005)
      ·
        refine ⟨42338693928373953099770251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225806367617994416532108005 42338693928373953099770251)
        ·
          refine ⟨63508040892560929649655377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42338693928373953099770251 63508040892560929649655377)
          ·
            refine ⟨47631030669420697237241533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63508040892560929649655377 47631030669420697237241533)
            ·
              refine ⟨17861636501032761463965575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47631030669420697237241533 17861636501032761463965575)
              ·
                refine ⟨26792454751549142195948363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17861636501032761463965575 26792454751549142195948363)
                ·
                  refine ⟨40188682127323713293922545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26792454751549142195948363 40188682127323713293922545)
                  ·
                    refine ⟨30141511595492784970441909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40188682127323713293922545 30141511595492784970441909)
                    ·
                      refine ⟨2825766712077448590978929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30141511595492784970441909 2825766712077448590978929)
                      ·
                        rfl

theorem cell23_5503161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_5503161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503161 prefixEnd_5503161 := by exact prefixLift 5503161
  have htrace : WordTrace (prefixWord ++ tailWord_5503161) baseStart_5503161 baseEnd_5503161 := by
    simpa [prefixWord, tailWord_5503161, baseEnd_5503161] using wordTrace_append hprefix tailTrace_5503161
  have hstable : (prefixWord ++ tailWord_5503161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503161).length < 2 ^ (prefixWord ++ tailWord_5503161).sum := by decide
  have hdescent : baseEnd_5503161 < baseStart_5503161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503166 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_5503166 : Nat := 118140960795 + 5503166 * 2 ^ 59
def prefixEnd_5503166 : Nat := 4983230072969 + 3 ^ 40 * 5503166 * 2
def baseEnd_5503166 : Nat := 2825769279480721071416407

theorem tailTrace_5503166 : CollatzResearch.WordTrace tailWord_5503166 prefixEnd_5503166 2825769279480721071416407 := by
  unfold tailWord_5503166
  simp only [CollatzResearch.WordTrace]
  refine ⟨25089619197622115346420169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133811302387317948514240901 25089619197622115346420169)
  ·
    refine ⟨18817214398216586509815127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25089619197622115346420169 18817214398216586509815127)
    ·
      refine ⟨28225821597324879764722691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18817214398216586509815127 28225821597324879764722691)
      ·
        refine ⟨42338732395987319647084037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28225821597324879764722691 42338732395987319647084037)
        ·
          refine ⟨7938512324247622433828257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42338732395987319647084037 7938512324247622433828257)
          ·
            refine ⟨5953884243185716825371193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7938512324247622433828257 5953884243185716825371193)
            ·
              refine ⟨4465413182389287619028395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5953884243185716825371193 4465413182389287619028395)
              ·
                refine ⟨6698119773583931428542593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465413182389287619028395 6698119773583931428542593)
                ·
                  refine ⟨5023589830187948571406945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6698119773583931428542593 5023589830187948571406945)
                  ·
                    refine ⟨3767692372640961428555209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5023589830187948571406945 3767692372640961428555209)
                    ·
                      refine ⟨2825769279480721071416407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767692372640961428555209 2825769279480721071416407)
                      ·
                        rfl

theorem cell23_5503166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_5503166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503166 prefixEnd_5503166 := by exact prefixLift 5503166
  have htrace : WordTrace (prefixWord ++ tailWord_5503166) baseStart_5503166 baseEnd_5503166 := by
    simpa [prefixWord, tailWord_5503166, baseEnd_5503166] using wordTrace_append hprefix tailTrace_5503166
  have hstable : (prefixWord ++ tailWord_5503166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503166).length < 2 ^ (prefixWord ++ tailWord_5503166).sum := by decide
  have hdescent : baseEnd_5503166 < baseStart_5503166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503201 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_5503201 : Nat := 118140960795 + 5503201 * 2 ^ 59
def prefixEnd_5503201 : Nat := 4983230072969 + 3 ^ 40 * 5503201 * 2
def baseEnd_5503201 : Nat := 2825787251303628434478745

theorem tailTrace_5503201 : CollatzResearch.WordTrace tailWord_5503201 prefixEnd_5503201 2825787251303628434478745 := by
  unfold tailWord_5503201
  simp only [CollatzResearch.WordTrace]
  refine ⟨200718230135850123748885457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133812153423900082499256971 200718230135850123748885457)
  ·
    refine ⟨150538672601887592811664093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200718230135850123748885457 150538672601887592811664093)
    ·
      refine ⟨56452002225707847304374035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150538672601887592811664093 56452002225707847304374035)
      ·
        refine ⟨84678003338561770956561053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56452002225707847304374035 84678003338561770956561053)
        ·
          refine ⟨31754251251960664108710395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84678003338561770956561053 31754251251960664108710395)
          ·
            refine ⟨47631376877940996163065593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31754251251960664108710395 47631376877940996163065593)
            ·
              refine ⟨35723532658455747122299195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47631376877940996163065593 35723532658455747122299195)
              ·
                refine ⟨53585298987683620683448793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35723532658455747122299195 53585298987683620683448793)
                ·
                  refine ⟨40188974240762715512586595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53585298987683620683448793 40188974240762715512586595)
                  ·
                    refine ⟨60283461361144073268879893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40188974240762715512586595 60283461361144073268879893)
                    ·
                      refine ⟨2825787251303628434478745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60283461361144073268879893 2825787251303628434478745)
                      ·
                        rfl

theorem cell23_5503201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_5503201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503201 prefixEnd_5503201 := by exact prefixLift 5503201
  have htrace : WordTrace (prefixWord ++ tailWord_5503201) baseStart_5503201 baseEnd_5503201 := by
    simpa [prefixWord, tailWord_5503201, baseEnd_5503201] using wordTrace_append hprefix tailTrace_5503201
  have hstable : (prefixWord ++ tailWord_5503201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503201).length < 2 ^ (prefixWord ++ tailWord_5503201).sum := by decide
  have hdescent : baseEnd_5503201 < baseStart_5503201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503228 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 6]
def baseStart_5503228 : Nat := 118140960795 + 5503228 * 2 ^ 59
def prefixEnd_5503228 : Nat := 4983230072969 + 3 ^ 40 * 5503228 * 2
def baseEnd_5503228 : Nat := 313977901697922203204569

theorem tailTrace_5503228 : CollatzResearch.WordTrace tailWord_5503228 prefixEnd_5503228 313977901697922203204569 := by
  unfold tailWord_5503228
  simp only [CollatzResearch.WordTrace]
  refine ⟨100359607453376153680059169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133812809937834871573412225 100359607453376153680059169)
  ·
    refine ⟨75269705590032115260044377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100359607453376153680059169 75269705590032115260044377)
    ·
      refine ⟨56452279192524086445033283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75269705590032115260044377 56452279192524086445033283)
      ·
        refine ⟨84678418788786129667549925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56452279192524086445033283 84678418788786129667549925)
        ·
          refine ⟨15877203522897399312665611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84678418788786129667549925 15877203522897399312665611)
          ·
            refine ⟨23815805284346098968998417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15877203522897399312665611 23815805284346098968998417)
            ·
              refine ⟨17861853963259574226748813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23815805284346098968998417 17861853963259574226748813)
              ·
                refine ⟨6698195236222340335030805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17861853963259574226748813 6698195236222340335030805)
                ·
                  refine ⟨313977901697922203204569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6698195236222340335030805 313977901697922203204569)
                  ·
                    rfl

theorem cell23_5503228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_5503228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503228 prefixEnd_5503228 := by exact prefixLift 5503228
  have htrace : WordTrace (prefixWord ++ tailWord_5503228) baseStart_5503228 baseEnd_5503228 := by
    simpa [prefixWord, tailWord_5503228, baseEnd_5503228] using wordTrace_append hprefix tailTrace_5503228
  have hstable : (prefixWord ++ tailWord_5503228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503228).length < 2 ^ (prefixWord ++ tailWord_5503228).sum := by decide
  have hdescent : baseEnd_5503228 < baseStart_5503228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503239 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5503239 : Nat := 118140960795 + 5503239 * 2 ^ 59
def prefixEnd_5503239 : Nat := 4983230072969 + 3 ^ 40 * 5503239 * 2
def baseEnd_5503239 : Nat := 2825806763568499285803571

theorem tailTrace_5503239 : CollatzResearch.WordTrace tailWord_5503239 prefixEnd_5503239 2825806763568499285803571 := by
  unfold tailWord_5503239
  simp only [CollatzResearch.WordTrace]
  refine ⟨200719616109712456238768771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133813077406474970825845847 200719616109712456238768771)
  ·
    refine ⟨301079424164568684358153157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200719616109712456238768771 301079424164568684358153157)
    ·
      refine ⟨56452392030856628317153717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301079424164568684358153157 56452392030856628317153717)
      ·
        refine ⟨5292411752892808904733161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56452392030856628317153717 5292411752892808904733161)
        ·
          refine ⟨3969308814669606678549871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5292411752892808904733161 3969308814669606678549871)
          ·
            refine ⟨5953963222004410017824807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969308814669606678549871 5953963222004410017824807)
            ·
              refine ⟨8930944833006615026737211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5953963222004410017824807 8930944833006615026737211)
              ·
                refine ⟨13396417249509922540105817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8930944833006615026737211 13396417249509922540105817)
                ·
                  refine ⟨10047312937132441905079363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13396417249509922540105817 10047312937132441905079363)
                  ·
                    refine ⟨15070969405698662857619045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10047312937132441905079363 15070969405698662857619045)
                    ·
                      refine ⟨2825806763568499285803571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15070969405698662857619045 2825806763568499285803571)
                      ·
                        rfl

theorem cell23_5503239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5503239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503239 prefixEnd_5503239 := by exact prefixLift 5503239
  have htrace : WordTrace (prefixWord ++ tailWord_5503239) baseStart_5503239 baseEnd_5503239 := by
    simpa [prefixWord, tailWord_5503239, baseEnd_5503239] using wordTrace_append hprefix tailTrace_5503239
  have hstable : (prefixWord ++ tailWord_5503239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503239).length < 2 ^ (prefixWord ++ tailWord_5503239).sum := by decide
  have hdescent : baseEnd_5503239 < baseStart_5503239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503262 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_5503262 : Nat := 118140960795 + 5503262 * 2 ^ 59
def prefixEnd_5503262 : Nat := 4983230072969 + 3 ^ 40 * 5503262 * 2
def baseEnd_5503262 : Nat := 313979841513728077312885

theorem tailTrace_5503262 : CollatzResearch.WordTrace tailWord_5503262 prefixEnd_5503262 313979841513728077312885 := by
  unfold tailWord_5503262
  simp only [CollatzResearch.WordTrace]
  refine ⟨25090056873578641395857005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133813636659086087444570693 25090056873578641395857005)
  ·
    refine ⟨9408771327591990523446377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25090056873578641395857005 9408771327591990523446377)
    ·
      refine ⟨7056578495693992892584783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9408771327591990523446377 7056578495693992892584783)
      ·
        refine ⟨10584867743540989338877175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7056578495693992892584783 10584867743540989338877175)
        ·
          refine ⟨15877301615311484008315763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10584867743540989338877175 15877301615311484008315763)
          ·
            refine ⟨23815952422967226012473645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15877301615311484008315763 23815952422967226012473645)
            ·
              refine ⟨8930982158612709754677617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23815952422967226012473645 8930982158612709754677617)
              ·
                refine ⟨6698236618959532316008213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8930982158612709754677617 6698236618959532316008213)
                ·
                  refine ⟨313979841513728077312885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6698236618959532316008213 313979841513728077312885)
                  ·
                    rfl

theorem cell23_5503262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_5503262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503262 prefixEnd_5503262 := by exact prefixLift 5503262
  have htrace : WordTrace (prefixWord ++ tailWord_5503262) baseStart_5503262 baseEnd_5503262 := by
    simpa [prefixWord, tailWord_5503262, baseEnd_5503262] using wordTrace_append hprefix tailTrace_5503262
  have hstable : (prefixWord ++ tailWord_5503262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503262).length < 2 ^ (prefixWord ++ tailWord_5503262).sum := by decide
  have hdescent : baseEnd_5503262 < baseStart_5503262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503265 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 2, 3, 2]
def baseStart_5503265 : Nat := 118140960795 + 5503265 * 2 ^ 59
def prefixEnd_5503265 : Nat := 4983230072969 + 3 ^ 40 * 5503265 * 2
def baseEnd_5503265 : Nat := 2825820114065516184078451

theorem tailTrace_5503265 : CollatzResearch.WordTrace tailWord_5503265 prefixEnd_5503265 2825820114065516184078451 := by
  unfold tailWord_5503265
  simp only [CollatzResearch.WordTrace]
  refine ⟨200720564407618262679215249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133813709605078841786143499 200720564407618262679215249)
  ·
    refine ⟨150540423305713697009411437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200720564407618262679215249 150540423305713697009411437)
    ·
      refine ⟨56452658739642636378529289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150540423305713697009411437 56452658739642636378529289)
      ·
        refine ⟨42339494054731977283896967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56452658739642636378529289 42339494054731977283896967)
        ·
          refine ⟨63509241082097965925845451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42339494054731977283896967 63509241082097965925845451)
          ·
            refine ⟨95263861623146948888768177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63509241082097965925845451 95263861623146948888768177)
            ·
              refine ⟨71447896217360211666576133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95263861623146948888768177 71447896217360211666576133)
              ·
                refine ⟨13396480540755039687483025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71447896217360211666576133 13396480540755039687483025)
                ·
                  refine ⟨10047360405566279765612269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13396480540755039687483025 10047360405566279765612269)
                  ·
                    refine ⟨3767760152087354912104601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10047360405566279765612269 3767760152087354912104601)
                    ·
                      refine ⟨2825820114065516184078451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767760152087354912104601 2825820114065516184078451)
                      ·
                        rfl

theorem cell23_5503265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_5503265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503265 prefixEnd_5503265 := by exact prefixLift 5503265
  have htrace : WordTrace (prefixWord ++ tailWord_5503265) baseStart_5503265 baseEnd_5503265 := by
    simpa [prefixWord, tailWord_5503265, baseEnd_5503265] using wordTrace_append hprefix tailTrace_5503265
  have hstable : (prefixWord ++ tailWord_5503265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503265).length < 2 ^ (prefixWord ++ tailWord_5503265).sum := by decide
  have hdescent : baseEnd_5503265 < baseStart_5503265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503288 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 1, 6]
def baseStart_5503288 : Nat := 118140960795 + 5503288 * 2 ^ 59
def prefixEnd_5503288 : Nat := 4983230072969 + 3 ^ 40 * 5503288 * 2
def baseEnd_5503288 : Nat := 941943974706856531363615

theorem tailTrace_5503288 : CollatzResearch.WordTrace tailWord_5503288 prefixEnd_5503288 941943974706856531363615 := by
  unfold tailWord_5503288
  simp only [CollatzResearch.WordTrace]
  refine ⟨100360701643267468803651259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133814268857689958404868345 100360701643267468803651259)
  ·
    refine ⟨150541052464901203205476889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100360701643267468803651259 150541052464901203205476889)
    ·
      refine ⟨112905789348675902404107667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150541052464901203205476889 112905789348675902404107667)
      ·
        refine ⟨169358684023013853606161501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112905789348675902404107667 169358684023013853606161501)
        ·
          refine ⟨63509506508630195102310563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169358684023013853606161501 63509506508630195102310563)
          ·
            refine ⟨95264259762945292653465845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63509506508630195102310563 95264259762945292653465845)
            ·
              refine ⟨8931024352776121186262423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95264259762945292653465845 8931024352776121186262423)
              ·
                refine ⟨13396536529164181779393635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8931024352776121186262423 13396536529164181779393635)
                ·
                  refine ⟨20094804793746272669090453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13396536529164181779393635 20094804793746272669090453)
                  ·
                    refine ⟨941943974706856531363615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20094804793746272669090453 941943974706856531363615)
                    ·
                      rfl

theorem cell23_5503288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_5503288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503288 prefixEnd_5503288 := by exact prefixLift 5503288
  have htrace : WordTrace (prefixWord ++ tailWord_5503288) baseStart_5503288 baseEnd_5503288 := by
    simpa [prefixWord, tailWord_5503288, baseEnd_5503288] using wordTrace_append hprefix tailTrace_5503288
  have hstable : (prefixWord ++ tailWord_5503288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503288).length < 2 ^ (prefixWord ++ tailWord_5503288).sum := by decide
  have hdescent : baseEnd_5503288 < baseStart_5503288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503295 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 4]
def baseStart_5503295 : Nat := 118140960795 + 5503295 * 2 ^ 59
def prefixEnd_5503295 : Nat := 4983230072969 + 3 ^ 40 * 5503295 * 2
def baseEnd_5503295 : Nat := 2825835518485151066703313

theorem tailTrace_5503295 : CollatzResearch.WordTrace tailWord_5503295 prefixEnd_5503295 2825835518485151066703313 := by
  unfold tailWord_5503295
  simp only [CollatzResearch.WordTrace]
  refine ⟨200721658597509577802807339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133814439065006385201871559 200721658597509577802807339)
  ·
    refine ⟨301082487896264366704211009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200721658597509577802807339 301082487896264366704211009)
    ·
      refine ⟨225811865922198275028158257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301082487896264366704211009 225811865922198275028158257)
      ·
        refine ⟨169358899441648706271118693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225811865922198275028158257 169358899441648706271118693)
        ·
          refine ⟨31754793645309132425834755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169358899441648706271118693 31754793645309132425834755)
          ·
            refine ⟨47632190467963698638752133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31754793645309132425834755 47632190467963698638752133)
            ·
              refine ⟨8931035712743193494766025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47632190467963698638752133 8931035712743193494766025)
              ·
                refine ⟨6698276784557395121074519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8931035712743193494766025 6698276784557395121074519)
                ·
                  refine ⟨10047415176836092681611779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6698276784557395121074519 10047415176836092681611779)
                  ·
                    refine ⟨15071122765254139022417669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10047415176836092681611779 15071122765254139022417669)
                    ·
                      refine ⟨2825835518485151066703313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15071122765254139022417669 2825835518485151066703313)
                      ·
                        rfl

theorem cell23_5503295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_5503295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503295 prefixEnd_5503295 := by exact prefixLift 5503295
  have htrace : WordTrace (prefixWord ++ tailWord_5503295) baseStart_5503295 baseEnd_5503295 := by
    simpa [prefixWord, tailWord_5503295, baseEnd_5503295] using wordTrace_append hprefix tailTrace_5503295
  have hstable : (prefixWord ++ tailWord_5503295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503295).length < 2 ^ (prefixWord ++ tailWord_5503295).sum := by decide
  have hdescent : baseEnd_5503295 < baseStart_5503295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503308 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_5503308 : Nat := 118140960795 + 5503308 * 2 ^ 59
def prefixEnd_5503308 : Nat := 4983230072969 + 3 ^ 40 * 5503308 * 2
def baseEnd_5503308 : Nat := 2825842193733659515840753

theorem tailTrace_5503308 : CollatzResearch.WordTrace tailWord_5503308 prefixEnd_5503308 2825842193733659515840753 := by
  unfold tailWord_5503308
  simp only [CollatzResearch.WordTrace]
  refine ⟨100361066373231240511515289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133814755164308320682020385 100361066373231240511515289)
  ·
    refine ⟨75270799779923430383636467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100361066373231240511515289 75270799779923430383636467)
    ·
      refine ⟨112906199669885145575454701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75270799779923430383636467 112906199669885145575454701)
      ·
        refine ⟨42339824876206929590795513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112906199669885145575454701 42339824876206929590795513)
        ·
          refine ⟨31754868657155197193096635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42339824876206929590795513 31754868657155197193096635)
          ·
            refine ⟨47632302985732795789644953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31754868657155197193096635 47632302985732795789644953)
            ·
              refine ⟨35724227239299596842233715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47632302985732795789644953 35724227239299596842233715)
              ·
                refine ⟨53586340858949395263350573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35724227239299596842233715 53586340858949395263350573)
                ·
                  refine ⟨20094877822106023223756465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53586340858949395263350573 20094877822106023223756465)
                  ·
                    refine ⟨15071158366579517417817349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20094877822106023223756465 15071158366579517417817349)
                    ·
                      refine ⟨2825842193733659515840753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15071158366579517417817349 2825842193733659515840753)
                      ·
                        rfl

theorem cell23_5503308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_5503308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503308 prefixEnd_5503308 := by exact prefixLift 5503308
  have htrace : WordTrace (prefixWord ++ tailWord_5503308) baseStart_5503308 baseEnd_5503308 := by
    simpa [prefixWord, tailWord_5503308, baseEnd_5503308] using wordTrace_append hprefix tailTrace_5503308
  have hstable : (prefixWord ++ tailWord_5503308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503308).length < 2 ^ (prefixWord ++ tailWord_5503308).sum := by decide
  have hdescent : baseEnd_5503308 < baseStart_5503308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503349 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_5503349 : Nat := 118140960795 + 5503349 * 2 ^ 59
def prefixEnd_5503349 : Nat := 4983230072969 + 3 ^ 40 * 5503349 * 2
def baseEnd_5503349 : Nat := 2825863246440493855428065

theorem tailTrace_5503349 : CollatzResearch.WordTrace tailWord_5503349 prefixEnd_5503349 2825863246440493855428065 := by
  unfold tailWord_5503349
  simp only [CollatzResearch.WordTrace]
  refine ⟨200723628139313945025273101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133815752092875963350182067 200723628139313945025273101)
  ·
    refine ⟨75271360552242729384477413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200723628139313945025273101 75271360552242729384477413)
    ·
      refine ⟨14113380103545511759589515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75271360552242729384477413 14113380103545511759589515)
      ·
        refine ⟨21170070155318267639384273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14113380103545511759589515 21170070155318267639384273)
        ·
          refine ⟨15877552616488700729538205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21170070155318267639384273 15877552616488700729538205)
          ·
            refine ⟨5954082231183262773576827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15877552616488700729538205 5954082231183262773576827)
            ·
              refine ⟨8931123346774894160365241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5954082231183262773576827 8931123346774894160365241)
              ·
                refine ⟨6698342510081170620273931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8931123346774894160365241 6698342510081170620273931)
                ·
                  refine ⟨10047513765121755930410897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6698342510081170620273931 10047513765121755930410897)
                  ·
                    refine ⟨7535635323841316947808173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10047513765121755930410897 7535635323841316947808173)
                    ·
                      refine ⟨2825863246440493855428065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7535635323841316947808173 2825863246440493855428065)
                      ·
                        rfl

theorem cell23_5503349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_5503349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503349 prefixEnd_5503349 := by exact prefixLift 5503349
  have htrace : WordTrace (prefixWord ++ tailWord_5503349) baseStart_5503349 baseEnd_5503349 := by
    simpa [prefixWord, tailWord_5503349, baseEnd_5503349] using wordTrace_append hprefix tailTrace_5503349
  have hstable : (prefixWord ++ tailWord_5503349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503349).length < 2 ^ (prefixWord ++ tailWord_5503349).sum := by decide
  have hdescent : baseEnd_5503349 < baseStart_5503349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503380 : List Nat := [2, 4, 2, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_5503380 : Nat := 118140960795 + 5503380 * 2 ^ 59
def prefixEnd_5503380 : Nat := 4983230072969 + 3 ^ 40 * 5503380 * 2
def baseEnd_5503380 : Nat := 2825879164340783234140423

theorem tailTrace_5503380 : CollatzResearch.WordTrace tailWord_5503380 prefixEnd_5503380 2825879164340783234140423 := by
  unfold tailWord_5503380
  simp only [CollatzResearch.WordTrace]
  refine ⟨100362379401100818659825797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133816505868134424879767729 100362379401100818659825797)
  ·
    refine ⟨18817946137706403498717337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100362379401100818659825797 18817946137706403498717337)
    ·
      refine ⟨14113459603279802624038003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18817946137706403498717337 14113459603279802624038003)
      ·
        refine ⟨21170189404919703936057005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14113459603279802624038003 21170189404919703936057005)
        ·
          refine ⟨7938821026844888976021377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21170189404919703936057005 7938821026844888976021377)
          ·
            refine ⟨5954115770133666732016033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7938821026844888976021377 5954115770133666732016033)
            ·
              refine ⟨4465586827600250049012025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5954115770133666732016033 4465586827600250049012025)
              ·
                refine ⟨3349190120700187536759019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4465586827600250049012025 3349190120700187536759019)
                ·
                  refine ⟨5023785181050281305138529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3349190120700187536759019 5023785181050281305138529)
                  ·
                    refine ⟨3767838885787710978853897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5023785181050281305138529 3767838885787710978853897)
                    ·
                      refine ⟨2825879164340783234140423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767838885787710978853897 2825879164340783234140423)
                      ·
                        rfl

theorem cell23_5503380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_5503380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503380 prefixEnd_5503380 := by exact prefixLift 5503380
  have htrace : WordTrace (prefixWord ++ tailWord_5503380) baseStart_5503380 baseEnd_5503380 := by
    simpa [prefixWord, tailWord_5503380, baseEnd_5503380] using wordTrace_append hprefix tailTrace_5503380
  have hstable : (prefixWord ++ tailWord_5503380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503380).length < 2 ^ (prefixWord ++ tailWord_5503380).sum := by decide
  have hdescent : baseEnd_5503380 < baseStart_5503380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503385 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 3, 4, 2]
def baseStart_5503385 : Nat := 118140960795 + 5503385 * 2 ^ 59
def prefixEnd_5503385 : Nat := 4983230072969 + 3 ^ 40 * 5503385 * 2
def baseEnd_5503385 : Nat := 2825881731744055714577899

theorem tailTrace_5503385 : CollatzResearch.WordTrace tailWord_5503385 prefixEnd_5503385 2825881731744055714577899 := by
  unfold tailWord_5503385
  simp only [CollatzResearch.WordTrace]
  refine ⟨200724941167183523173583609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133816627444789015449055739 200724941167183523173583609)
  ·
    refine ⟨150543705875387642380187707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200724941167183523173583609 150543705875387642380187707)
    ·
      refine ⟨225815558813081463570281561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150543705875387642380187707 225815558813081463570281561)
      ·
        refine ⟨169361669109811097677711171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225815558813081463570281561 169361669109811097677711171)
        ·
          refine ⟨254042503664716646516566757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169361669109811097677711171 254042503664716646516566757)
          ·
            refine ⟨47632969437134371221856267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254042503664716646516566757 47632969437134371221856267)
            ·
              refine ⟨71449454155701556832784401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47632969437134371221856267 71449454155701556832784401)
              ·
                refine ⟨53587090616776167624588301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71449454155701556832784401 53587090616776167624588301)
                ·
                  refine ⟨20095158981291062859220613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53587090616776167624588301 20095158981291062859220613)
                  ·
                    refine ⟨3767842308992074286103865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20095158981291062859220613 3767842308992074286103865)
                    ·
                      refine ⟨2825881731744055714577899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3767842308992074286103865 2825881731744055714577899)
                      ·
                        rfl

theorem cell23_5503385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 4, 2].length) (baseStart_5503385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503385 prefixEnd_5503385 := by exact prefixLift 5503385
  have htrace : WordTrace (prefixWord ++ tailWord_5503385) baseStart_5503385 baseEnd_5503385 := by
    simpa [prefixWord, tailWord_5503385, baseEnd_5503385] using wordTrace_append hprefix tailTrace_5503385
  have hstable : (prefixWord ++ tailWord_5503385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503385).length < 2 ^ (prefixWord ++ tailWord_5503385).sum := by decide
  have hdescent : baseEnd_5503385 < baseStart_5503385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503448 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_5503448 : Nat := 118140960795 + 5503448 * 2 ^ 59
def prefixEnd_5503448 : Nat := 4983230072969 + 3 ^ 40 * 5503448 * 2
def baseEnd_5503448 : Nat := 2825914081025288968090109

theorem tailTrace_5503448 : CollatzResearch.WordTrace tailWord_5503448 prefixEnd_5503448 2825914081025288968090109 := by
  unfold tailWord_5503448
  simp only [CollatzResearch.WordTrace]
  refine ⟨100363619482977642466563499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133818159310636856622084665 100363619482977642466563499)
  ·
    refine ⟨150545429224466463699845249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100363619482977642466563499 150545429224466463699845249)
    ·
      refine ⟨112909071918349847774883937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150545429224466463699845249 112909071918349847774883937)
      ·
        refine ⟨84681803938762385831162953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112909071918349847774883937 84681803938762385831162953)
        ·
          refine ⟨63511352954071789373372215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84681803938762385831162953 63511352954071789373372215)
          ·
            refine ⟨95267029431107684060058323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63511352954071789373372215 95267029431107684060058323)
            ·
              refine ⟨142900544146661526090087485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95267029431107684060058323 142900544146661526090087485)
              ·
                refine ⟨53587704054998072283782807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142900544146661526090087485 53587704054998072283782807)
                ·
                  refine ⟨80381556082497108425674211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53587704054998072283782807 80381556082497108425674211)
                  ·
                    refine ⟨120572334123745662638511317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80381556082497108425674211 120572334123745662638511317)
                    ·
                      refine ⟨2825914081025288968090109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120572334123745662638511317 2825914081025288968090109)
                      ·
                        rfl

theorem cell23_5503448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_5503448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503448 prefixEnd_5503448 := by exact prefixLift 5503448
  have htrace : WordTrace (prefixWord ++ tailWord_5503448) baseStart_5503448 baseEnd_5503448 := by
    simpa [prefixWord, tailWord_5503448, baseEnd_5503448] using wordTrace_append hprefix tailTrace_5503448
  have hstable : (prefixWord ++ tailWord_5503448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503448).length < 2 ^ (prefixWord ++ tailWord_5503448).sum := by decide
  have hdescent : baseEnd_5503448 < baseStart_5503448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503468 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_5503468 : Nat := 118140960795 + 5503468 * 2 ^ 59
def prefixEnd_5503468 : Nat := 4983230072969 + 3 ^ 40 * 5503468 * 2
def baseEnd_5503468 : Nat := 941974783546126296613339

theorem tailTrace_5503468 : CollatzResearch.WordTrace tailWord_5503468 prefixEnd_5503468 941974783546126296613339 := by
  unfold tailWord_5503468
  simp only [CollatzResearch.WordTrace]
  refine ⟨100363984212941414174427529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133818645617255218899236705 100363984212941414174427529)
  ·
    refine ⟨75272988159706060630820647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100363984212941414174427529 75272988159706060630820647)
    ·
      refine ⟨112909482239559090946230971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75272988159706060630820647 112909482239559090946230971)
      ·
        refine ⟨169364223359338636419346457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112909482239559090946230971 169364223359338636419346457)
        ·
          refine ⟨127023167519503977314509843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169364223359338636419346457 127023167519503977314509843)
          ·
            refine ⟨190534751279255965971764765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127023167519503977314509843 190534751279255965971764765)
            ·
              refine ⟨71450531729720987239411787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190534751279255965971764765 71450531729720987239411787)
              ·
                refine ⟨107175797594581480859117681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71450531729720987239411787 107175797594581480859117681)
                ·
                  refine ⟨80381848195936110644338261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107175797594581480859117681 80381848195936110644338261)
                  ·
                    refine ⟨941974783546126296613339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80381848195936110644338261 941974783546126296613339)
                    ·
                      rfl

theorem cell23_5503468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_5503468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503468 prefixEnd_5503468 := by exact prefixLift 5503468
  have htrace : WordTrace (prefixWord ++ tailWord_5503468) baseStart_5503468 baseEnd_5503468 := by
    simpa [prefixWord, tailWord_5503468, baseEnd_5503468] using wordTrace_append hprefix tailTrace_5503468
  have hstable : (prefixWord ++ tailWord_5503468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503468).length < 2 ^ (prefixWord ++ tailWord_5503468).sum := by decide
  have hdescent : baseEnd_5503468 < baseStart_5503468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503475 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 4]
def baseStart_5503475 : Nat := 118140960795 + 5503475 * 2 ^ 59
def prefixEnd_5503475 : Nat := 4983230072969 + 3 ^ 40 * 5503475 * 2
def baseEnd_5503475 : Nat := 2825927945002960362452485

theorem tailTrace_5503475 : CollatzResearch.WordTrace tailWord_5503475 prefixEnd_5503475 2825927945002960362452485 := by
  unfold tailWord_5503475
  simp only [CollatzResearch.WordTrace]
  refine ⟨200728223736857468544359879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133818815824571645696239919 200728223736857468544359879)
  ·
    refine ⟨301092335605286202816539819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200728223736857468544359879 301092335605286202816539819)
    ·
      refine ⟨451638503407929304224809729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301092335605286202816539819 451638503407929304224809729)
      ·
        refine ⟨338728877555946978168607297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451638503407929304224809729 338728877555946978168607297)
        ·
          refine ⟨254046658166960233626455473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338728877555946978168607297 254046658166960233626455473)
          ·
            refine ⟨190534993625220175219841605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254046658166960233626455473 190534993625220175219841605)
            ·
              refine ⟨35725311304728782853720301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190534993625220175219841605 35725311304728782853720301)
              ·
                refine ⟨13396991739273293570145113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35725311304728782853720301 13396991739273293570145113)
                ·
                  refine ⟨10047743804454970177608835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13396991739273293570145113 10047743804454970177608835)
                  ·
                    refine ⟨15071615706682455266413253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10047743804454970177608835 15071615706682455266413253)
                    ·
                      refine ⟨2825927945002960362452485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15071615706682455266413253 2825927945002960362452485)
                      ·
                        rfl

theorem cell23_5503475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_5503475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503475 prefixEnd_5503475 := by exact prefixLift 5503475
  have htrace : WordTrace (prefixWord ++ tailWord_5503475) baseStart_5503475 baseEnd_5503475 := by
    simpa [prefixWord, tailWord_5503475, baseEnd_5503475] using wordTrace_append hprefix tailTrace_5503475
  have hstable : (prefixWord ++ tailWord_5503475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503475).length < 2 ^ (prefixWord ++ tailWord_5503475).sum := by decide
  have hdescent : baseEnd_5503475 < baseStart_5503475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503492 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5503492 : Nat := 118140960795 + 5503492 * 2 ^ 59
def prefixEnd_5503492 : Nat := 4983230072969 + 3 ^ 40 * 5503492 * 2
def baseEnd_5503492 : Nat := 2825936674174086795939907

theorem tailTrace_5503492 : CollatzResearch.WordTrace tailWord_5503492 prefixEnd_5503492 2825936674174086795939907 := by
  unfold tailWord_5503492
  simp only [CollatzResearch.WordTrace]
  refine ⟨100364421888897940223864365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133819229185197253631819153 100364421888897940223864365)
  ·
    refine ⟨37636658208336727583949137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100364421888897940223864365 37636658208336727583949137)
    ·
      refine ⟨28227493656252545687961853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37636658208336727583949137 28227493656252545687961853)
      ·
        refine ⟨10585310121094704632985695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28227493656252545687961853 10585310121094704632985695)
        ·
          refine ⟨15877965181642056949478543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10585310121094704632985695 15877965181642056949478543)
          ·
            refine ⟨23816947772463085424217815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15877965181642056949478543 23816947772463085424217815)
            ·
              refine ⟨35725421658694628136326723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23816947772463085424217815 35725421658694628136326723)
              ·
                refine ⟨53588132488041942204490085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35725421658694628136326723 53588132488041942204490085)
                ·
                  refine ⟨10047774841507864163341891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53588132488041942204490085 10047774841507864163341891)
                  ·
                    refine ⟨15071662262261796245012837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10047774841507864163341891 15071662262261796245012837)
                    ·
                      refine ⟨2825936674174086795939907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15071662262261796245012837 2825936674174086795939907)
                      ·
                        rfl

theorem cell23_5503492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5503492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503492 prefixEnd_5503492 := by exact prefixLift 5503492
  have htrace : WordTrace (prefixWord ++ tailWord_5503492) baseStart_5503492 baseEnd_5503492 := by
    simpa [prefixWord, tailWord_5503492, baseEnd_5503492] using wordTrace_append hprefix tailTrace_5503492
  have hstable : (prefixWord ++ tailWord_5503492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503492).length < 2 ^ (prefixWord ++ tailWord_5503492).sum := by decide
  have hdescent : baseEnd_5503492 < baseStart_5503492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503525 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 2, 5, 3]
def baseStart_5503525 : Nat := 118140960795 + 5503525 * 2 ^ 59
def prefixEnd_5503525 : Nat := 4983230072969 + 3 ^ 40 * 5503525 * 2
def baseEnd_5503525 : Nat := 2825953619035685166827255

theorem tailTrace_5503525 : CollatzResearch.WordTrace tailWord_5503525 prefixEnd_5503525 2825953619035685166827255 := by
  unfold tailWord_5503525
  simp only [CollatzResearch.WordTrace]
  refine ⟨200730047386676327083680029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133820031591117551389120019 200730047386676327083680029)
  ·
    refine ⟨75273767770003622656380011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200730047386676327083680029 75273767770003622656380011)
    ·
      refine ⟨112910651655005433984570017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75273767770003622656380011 112910651655005433984570017)
      ·
        refine ⟨84682988741254075488427513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112910651655005433984570017 84682988741254075488427513)
        ·
          refine ⟨63512241555940556616320635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84682988741254075488427513 63512241555940556616320635)
          ·
            refine ⟨95268362333910834924480953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63512241555940556616320635 95268362333910834924480953)
            ·
              refine ⟨71451271750433126193360715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95268362333910834924480953 71451271750433126193360715)
              ·
                refine ⟨107176907625649689290041073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71451271750433126193360715 107176907625649689290041073)
                ·
                  refine ⟨80382680719237266967530805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107176907625649689290041073 80382680719237266967530805)
                  ·
                    refine ⟨7535876317428493778206013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80382680719237266967530805 7535876317428493778206013)
                    ·
                      refine ⟨2825953619035685166827255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7535876317428493778206013 2825953619035685166827255)
                      ·
                        rfl

theorem cell23_5503525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_5503525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503525 prefixEnd_5503525 := by exact prefixLift 5503525
  have htrace : WordTrace (prefixWord ++ tailWord_5503525) baseStart_5503525 baseEnd_5503525 := by
    simpa [prefixWord, tailWord_5503525, baseEnd_5503525] using wordTrace_append hprefix tailTrace_5503525
  have hstable : (prefixWord ++ tailWord_5503525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503525).length < 2 ^ (prefixWord ++ tailWord_5503525).sum := by decide
  have hdescent : baseEnd_5503525 < baseStart_5503525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503553 : List Nat := [1, 2, 5, 1, 1, 4, 2, 2, 1, 4]
def baseStart_5503553 : Nat := 118140960795 + 5503553 * 2 ^ 59
def prefixEnd_5503553 : Nat := 4983230072969 + 3 ^ 40 * 5503553 * 2
def baseEnd_5503553 : Nat := 941989332164670352425709

theorem tailTrace_5503553 : CollatzResearch.WordTrace tailWord_5503553 prefixEnd_5503553 941989332164670352425709 := by
  unfold tailWord_5503553
  simp only [CollatzResearch.WordTrace]
  refine ⟨200731068630574887865699313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133820712420383258577132875 200731068630574887865699313)
  ·
    refine ⟨150548301472931165899274485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200731068630574887865699313 150548301472931165899274485)
    ·
      refine ⟨14113903263087296803056983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150548301472931165899274485 14113903263087296803056983)
      ·
        refine ⟨21170854894630945204585475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14113903263087296803056983 21170854894630945204585475)
        ·
          refine ⟨31756282341946417806878213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21170854894630945204585475 31756282341946417806878213)
          ·
            refine ⟨5954302939114953338789665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31756282341946417806878213 5954302939114953338789665)
            ·
              refine ⟨4465727204336215004092249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5954302939114953338789665 4465727204336215004092249)
              ·
                refine ⟨3349295403252161253069187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4465727204336215004092249 3349295403252161253069187)
                ·
                  refine ⟨5023943104878241879603781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3349295403252161253069187 5023943104878241879603781)
                  ·
                    refine ⟨941989332164670352425709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5023943104878241879603781 941989332164670352425709)
                    ·
                      rfl

theorem cell23_5503553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_5503553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503553 prefixEnd_5503553 := by exact prefixLift 5503553
  have htrace : WordTrace (prefixWord ++ tailWord_5503553) baseStart_5503553 baseEnd_5503553 := by
    simpa [prefixWord, tailWord_5503553, baseEnd_5503553] using wordTrace_append hprefix tailTrace_5503553
  have hstable : (prefixWord ++ tailWord_5503553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503553).length < 2 ^ (prefixWord ++ tailWord_5503553).sum := by decide
  have hdescent : baseEnd_5503553 < baseStart_5503553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503595 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 4]
def baseStart_5503595 : Nat := 118140960795 + 5503595 * 2 ^ 59
def prefixEnd_5503595 : Nat := 4983230072969 + 3 ^ 40 * 5503595 * 2
def baseEnd_5503595 : Nat := 2825989562681499892951933

theorem tailTrace_5503595 : CollatzResearch.WordTrace tailWord_5503595 prefixEnd_5503595 2825989562681499892951933 := by
  unfold tailWord_5503595
  simp only [CollatzResearch.WordTrace]
  refine ⟨200732600496422729038728239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133821733664281819359152159 200732600496422729038728239)
  ·
    refine ⟨301098900744634093558092359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200732600496422729038728239 301098900744634093558092359)
    ·
      refine ⟨451648351116951140337138539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301098900744634093558092359 451648351116951140337138539)
      ·
        refine ⟨677472526675426710505707809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451648351116951140337138539 677472526675426710505707809)
        ·
          refine ⟨508104395006570032879280857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677472526675426710505707809 508104395006570032879280857)
          ·
            refine ⟨381078296254927524659460643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508104395006570032879280857 381078296254927524659460643)
            ·
              refine ⟨571617444382391286989190965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381078296254927524659460643 571617444382391286989190965)
              ·
                refine ⟨53589135410849183155236653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 571617444382391286989190965 53589135410849183155236653)
                ·
                  refine ⟨20095925779068443683213745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53589135410849183155236653 20095925779068443683213745)
                  ·
                    refine ⟨15071944334301332762410309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20095925779068443683213745 15071944334301332762410309)
                    ·
                      refine ⟨2825989562681499892951933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15071944334301332762410309 2825989562681499892951933)
                      ·
                        rfl

theorem cell23_5503595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 4].length) (baseStart_5503595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503595 prefixEnd_5503595 := by exact prefixLift 5503595
  have htrace : WordTrace (prefixWord ++ tailWord_5503595) baseStart_5503595 baseEnd_5503595 := by
    simpa [prefixWord, tailWord_5503595, baseEnd_5503595] using wordTrace_append hprefix tailTrace_5503595
  have hstable : (prefixWord ++ tailWord_5503595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503595).length < 2 ^ (prefixWord ++ tailWord_5503595).sum := by decide
  have hdescent : baseEnd_5503595 < baseStart_5503595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503599 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 1, 1, 4]
def baseStart_5503599 : Nat := 118140960795 + 5503599 * 2 ^ 59
def prefixEnd_5503599 : Nat := 4983230072969 + 3 ^ 40 * 5503599 * 2
def baseEnd_5503599 : Nat := 2825991616604117877301915

theorem tailTrace_5503599 : CollatzResearch.WordTrace tailWord_5503599 prefixEnd_5503599 2825991616604117877301915 := by
  unfold tailWord_5503599
  simp only [CollatzResearch.WordTrace]
  refine ⟨200732746388408237721873851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133821830925605491814582567 200732746388408237721873851)
  ·
    refine ⟨301099119582612356582810777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200732746388408237721873851 301099119582612356582810777)
    ·
      refine ⟨225824339686959267437108083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301099119582612356582810777 225824339686959267437108083)
      ·
        refine ⟨338736509530438901155662125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225824339686959267437108083 338736509530438901155662125)
        ·
          refine ⟨127026191073914587933373297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338736509530438901155662125 127026191073914587933373297)
          ·
            refine ⟨95269643305435940950029973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127026191073914587933373297 95269643305435940950029973)
            ·
              refine ⟨4465764529942309732032655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95269643305435940950029973 4465764529942309732032655)
              ·
                refine ⟨6698646794913464598048983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465764529942309732032655 6698646794913464598048983)
                ·
                  refine ⟨10047970192370196897073475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6698646794913464598048983 10047970192370196897073475)
                  ·
                    refine ⟨15071955288555295345610213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10047970192370196897073475 15071955288555295345610213)
                    ·
                      refine ⟨2825991616604117877301915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15071955288555295345610213 2825991616604117877301915)
                      ·
                        rfl

theorem cell23_5503599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 1, 4].length) (baseStart_5503599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503599 prefixEnd_5503599 := by exact prefixLift 5503599
  have htrace : WordTrace (prefixWord ++ tailWord_5503599) baseStart_5503599 baseEnd_5503599 := by
    simpa [prefixWord, tailWord_5503599, baseEnd_5503599] using wordTrace_append hprefix tailTrace_5503599
  have hstable : (prefixWord ++ tailWord_5503599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503599).length < 2 ^ (prefixWord ++ tailWord_5503599).sum := by decide
  have hdescent : baseEnd_5503599 < baseStart_5503599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503609 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 2, 4]
def baseStart_5503609 : Nat := 118140960795 + 5503609 * 2 ^ 59
def prefixEnd_5503609 : Nat := 4983230072969 + 3 ^ 40 * 5503609 * 2
def baseEnd_5503609 : Nat := 941998917136887612725623

theorem tailTrace_5503609 : CollatzResearch.WordTrace tailWord_5503609 prefixEnd_5503609 941998917136887612725623 := by
  unfold tailWord_5503609
  simp only [CollatzResearch.WordTrace]
  refine ⟨200733111118372009429737881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133822074078914672953158587 200733111118372009429737881)
  ·
    refine ⟨150549833338779007072303411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200733111118372009429737881 150549833338779007072303411)
    ·
      refine ⟨225824750008168510608455117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150549833338779007072303411 225824750008168510608455117)
      ·
        refine ⟨84684281253063191478170669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225824750008168510608455117 84684281253063191478170669)
        ·
          refine ⟨31756605469898696804314001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84684281253063191478170669 31756605469898696804314001)
          ·
            refine ⟨23817454102424022603235501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31756605469898696804314001 23817454102424022603235501)
            ·
              refine ⟨8931545288409008476213313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23817454102424022603235501 8931545288409008476213313)
              ·
                refine ⟨6698658966306756357159985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8931545288409008476213313 6698658966306756357159985)
                ·
                  refine ⟨5023994224730067267869989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6698658966306756357159985 5023994224730067267869989)
                  ·
                    refine ⟨941998917136887612725623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5023994224730067267869989 941998917136887612725623)
                    ·
                      rfl

theorem cell23_5503609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 4].length) (baseStart_5503609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503609 prefixEnd_5503609 := by exact prefixLift 5503609
  have htrace : WordTrace (prefixWord ++ tailWord_5503609) baseStart_5503609 baseEnd_5503609 := by
    simpa [prefixWord, tailWord_5503609, baseEnd_5503609] using wordTrace_append hprefix tailTrace_5503609
  have hstable : (prefixWord ++ tailWord_5503609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503609).length < 2 ^ (prefixWord ++ tailWord_5503609).sum := by decide
  have hdescent : baseEnd_5503609 < baseStart_5503609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503616 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 3, 2, 2]
def baseStart_5503616 : Nat := 118140960795 + 5503616 * 2 ^ 59
def prefixEnd_5503616 : Nat := 4983230072969 + 3 ^ 40 * 5503616 * 2
def baseEnd_5503616 : Nat := 2826000345775244310789337

theorem tailTrace_5503616 : CollatzResearch.WordTrace tailWord_5503616 prefixEnd_5503616 2826000345775244310789337 := by
  unfold tailWord_5503616
  simp only [CollatzResearch.WordTrace]
  refine ⟨100366683214673324812621351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133822244286231099750161801 100366683214673324812621351)
  ·
    refine ⟨150550024822009987218932027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100366683214673324812621351 150550024822009987218932027)
    ·
      refine ⟨225825037233014980828398041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150550024822009987218932027 225825037233014980828398041)
      ·
        refine ⟨169368777924761235621298531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225825037233014980828398041 169368777924761235621298531)
        ·
          refine ⟨254053166887141853431947797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169368777924761235621298531 254053166887141853431947797)
          ·
            refine ⟨11908742197834774379622553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 254053166887141853431947797 11908742197834774379622553)
            ·
              refine ⟨8931556648376080784716915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11908742197834774379622553 8931556648376080784716915)
              ·
                refine ⟨13397334972564121177075373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8931556648376080784716915 13397334972564121177075373)
                ·
                  refine ⟨5024000614711545441403265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13397334972564121177075373 5024000614711545441403265)
                  ·
                    refine ⟨3768000461033659081052449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5024000614711545441403265 3768000461033659081052449)
                    ·
                      refine ⟨2826000345775244310789337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3768000461033659081052449 2826000345775244310789337)
                      ·
                        rfl

theorem cell23_5503616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3, 2, 2].length) (baseStart_5503616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503616 prefixEnd_5503616 := by exact prefixLift 5503616
  have htrace : WordTrace (prefixWord ++ tailWord_5503616) baseStart_5503616 baseEnd_5503616 := by
    simpa [prefixWord, tailWord_5503616, baseEnd_5503616] using wordTrace_append hprefix tailTrace_5503616
  have hstable : (prefixWord ++ tailWord_5503616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503616).length < 2 ^ (prefixWord ++ tailWord_5503616).sum := by decide
  have hdescent : baseEnd_5503616 < baseStart_5503616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503626 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 1, 6]
def baseStart_5503626 : Nat := 118140960795 + 5503626 * 2 ^ 59
def prefixEnd_5503626 : Nat := 4983230072969 + 3 ^ 40 * 5503626 * 2
def baseEnd_5503626 : Nat := 942001826860596423888097

theorem tailTrace_5503626 : CollatzResearch.WordTrace tailWord_5503626 prefixEnd_5503626 942001826860596423888097 := by
  unfold tailWord_5503626
  simp only [CollatzResearch.WordTrace]
  refine ⟨50183432789827605333276683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133822487439540280888737821 50183432789827605333276683)
  ·
    refine ⟨75275149184741407999915025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50183432789827605333276683 75275149184741407999915025)
    ·
      refine ⟨56456361888556055999936269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75275149184741407999915025 56456361888556055999936269)
      ·
        refine ⟨21171135708208520999976101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56456361888556055999936269 21171135708208520999976101)
        ·
          refine ⟨3969587945289097687495519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21171135708208520999976101 3969587945289097687495519)
          ·
            refine ⟨5954381917933646531243279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969587945289097687495519 5954381917933646531243279)
            ·
              refine ⟨8931572876900469796864919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5954381917933646531243279 8931572876900469796864919)
              ·
                refine ⟨13397359315350704695297379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8931572876900469796864919 13397359315350704695297379)
                ·
                  refine ⟨20096038973026057042946069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13397359315350704695297379 20096038973026057042946069)
                  ·
                    refine ⟨942001826860596423888097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20096038973026057042946069 942001826860596423888097)
                    ·
                      rfl

theorem cell23_5503626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_5503626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503626 prefixEnd_5503626 := by exact prefixLift 5503626
  have htrace : WordTrace (prefixWord ++ tailWord_5503626) baseStart_5503626 baseEnd_5503626 := by
    simpa [prefixWord, tailWord_5503626, baseEnd_5503626] using wordTrace_append hprefix tailTrace_5503626
  have hstable : (prefixWord ++ tailWord_5503626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503626).length < 2 ^ (prefixWord ++ tailWord_5503626).sum := by decide
  have hdescent : baseEnd_5503626 < baseStart_5503626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503636 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_5503636 : Nat := 118140960795 + 5503636 * 2 ^ 59
def prefixEnd_5503636 : Nat := 4983230072969 + 3 ^ 40 * 5503636 * 2
def baseEnd_5503636 : Nat := 2826010615388334232539245

theorem tailTrace_5503636 : CollatzResearch.WordTrace tailWord_5503636 prefixEnd_5503636 2826010615388334232539245 := by
  unfold tailWord_5503636
  simp only [CollatzResearch.WordTrace]
  refine ⟨100367047944637096520485381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133822730592849462027313841 100367047944637096520485381)
  ·
    refine ⟨18818821489619455597591009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100367047944637096520485381 18818821489619455597591009)
    ·
      refine ⟨14114116117214591698193257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18818821489619455597591009 14114116117214591698193257)
      ·
        refine ⟨10585587087910943773644943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14114116117214591698193257 10585587087910943773644943)
        ·
          refine ⟨15878380631866415660467415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10585587087910943773644943 15878380631866415660467415)
          ·
            refine ⟨23817570947799623490701123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15878380631866415660467415 23817570947799623490701123)
            ·
              refine ⟨35726356421699435236051685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23817570947799623490701123 35726356421699435236051685)
              ·
                refine ⟨6698691829068644106759691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35726356421699435236051685 6698691829068644106759691)
                ·
                  refine ⟨10048037743602966160139537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6698691829068644106759691 10048037743602966160139537)
                  ·
                    refine ⟨7536028307702224620104653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10048037743602966160139537 7536028307702224620104653)
                    ·
                      refine ⟨2826010615388334232539245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7536028307702224620104653 2826010615388334232539245)
                      ·
                        rfl

theorem cell23_5503636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_5503636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503636 prefixEnd_5503636 := by exact prefixLift 5503636
  have htrace : WordTrace (prefixWord ++ tailWord_5503636) baseStart_5503636 baseEnd_5503636 := by
    simpa [prefixWord, tailWord_5503636, baseEnd_5503636] using wordTrace_append hprefix tailTrace_5503636
  have hstable : (prefixWord ++ tailWord_5503636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503636).length < 2 ^ (prefixWord ++ tailWord_5503636).sum := by decide
  have hdescent : baseEnd_5503636 < baseStart_5503636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503729 : List Nat := [1, 2, 2, 2, 2, 2, 3, 4, 5]
def baseStart_5503729 : Nat := 118140960795 + 5503729 * 2 ^ 59
def prefixEnd_5503729 : Nat := 4983230072969 + 3 ^ 40 * 5503729 * 2
def baseEnd_5503729 : Nat := 314006485454355818741813

theorem tailTrace_5503729 : CollatzResearch.WordTrace tailWord_5503729 prefixEnd_5503729 314006485454355818741813 := by
  unfold tailWord_5503729
  simp only [CollatzResearch.WordTrace]
  refine ⟨200737487877937269924106241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133824991918624846616070827 200737487877937269924106241)
  ·
    refine ⟨150553115908452952443079681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200737487877937269924106241 150553115908452952443079681)
    ·
      refine ⟨112914836931339714332309761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150553115908452952443079681 112914836931339714332309761)
      ·
        refine ⟨84686127698504785749232321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112914836931339714332309761 84686127698504785749232321)
        ·
          refine ⟨63514595773878589311924241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84686127698504785749232321 63514595773878589311924241)
          ·
            refine ⟨47635946830408941983943181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63514595773878589311924241 47635946830408941983943181)
            ·
              refine ⟨17863480061403353243978693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47635946830408941983943181 17863480061403353243978693)
              ·
                refine ⟨3349402511513128733246005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17863480061403353243978693 3349402511513128733246005)
                ·
                  refine ⟨314006485454355818741813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3349402511513128733246005 314006485454355818741813)
                  ·
                    rfl

theorem cell23_5503729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 5].length) (baseStart_5503729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503729 prefixEnd_5503729 := by exact prefixLift 5503729
  have htrace : WordTrace (prefixWord ++ tailWord_5503729) baseStart_5503729 baseEnd_5503729 := by
    simpa [prefixWord, tailWord_5503729, baseEnd_5503729] using wordTrace_append hprefix tailTrace_5503729
  have hstable : (prefixWord ++ tailWord_5503729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503729).length < 2 ^ (prefixWord ++ tailWord_5503729).sum := by decide
  have hdescent : baseEnd_5503729 < baseStart_5503729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503733 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5503733 : Nat := 118140960795 + 5503733 * 2 ^ 59
def prefixEnd_5503733 : Nat := 4983230072969 + 3 ^ 40 * 5503733 * 2
def baseEnd_5503733 : Nat := 942020141003940117675433

theorem tailTrace_5503733 : CollatzResearch.WordTrace tailWord_5503733 prefixEnd_5503733 942020141003940117675433 := by
  unfold tailWord_5503733
  simp only [CollatzResearch.WordTrace]
  refine ⟨200737633769922778607251853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133825089179948519071501235 200737633769922778607251853)
  ·
    refine ⟨75276612663721041977719445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200737633769922778607251853 75276612663721041977719445)
    ·
      refine ⟨3528591218611923842705599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75276612663721041977719445 3528591218611923842705599)
      ·
        refine ⟨5292886827917885764058399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3528591218611923842705599 5292886827917885764058399)
        ·
          refine ⟨7939330241876828646087599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5292886827917885764058399 7939330241876828646087599)
          ·
            refine ⟨11908995362815242969131399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7939330241876828646087599 11908995362815242969131399)
            ·
              refine ⟨17863493044222864453697099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11908995362815242969131399 17863493044222864453697099)
              ·
                refine ⟨26795239566334296680545649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17863493044222864453697099 26795239566334296680545649)
                ·
                  refine ⟨20096429674750722510409237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26795239566334296680545649 20096429674750722510409237)
                  ·
                    refine ⟨942020141003940117675433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20096429674750722510409237 942020141003940117675433)
                    ·
                      rfl

theorem cell23_5503733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5503733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503733 prefixEnd_5503733 := by exact prefixLift 5503733
  have htrace : WordTrace (prefixWord ++ tailWord_5503733) baseStart_5503733 baseEnd_5503733 := by
    simpa [prefixWord, tailWord_5503733, baseEnd_5503733] using wordTrace_append hprefix tailTrace_5503733
  have hstable : (prefixWord ++ tailWord_5503733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503733).length < 2 ^ (prefixWord ++ tailWord_5503733).sum := by decide
  have hdescent : baseEnd_5503733 < baseStart_5503733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503879 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 3, 6]
def baseStart_5503879 : Nat := 118140960795 + 5503879 * 2 ^ 59
def prefixEnd_5503879 : Nat := 4983230072969 + 3 ^ 40 * 5503879 * 2
def baseEnd_5503879 : Nat := 942045130395792260600209

theorem tailTrace_5503879 : CollatzResearch.WordTrace tailWord_5503879 prefixEnd_5503879 942045130395792260600209 := by
  unfold tailWord_5503879
  simp only [CollatzResearch.WordTrace]
  refine ⟨200742958827393845542066691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133828639218262563694711127 200742958827393845542066691)
  ·
    refine ⟨301114438241090768313100037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200742958827393845542066691 301114438241090768313100037)
    ·
      refine ⟨56458957170204519058706257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301114438241090768313100037 56458957170204519058706257)
      ·
        refine ⟨42344217877653389294029693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56458957170204519058706257 42344217877653389294029693)
        ·
          refine ⟨15879081704120020985261135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42344217877653389294029693 15879081704120020985261135)
          ·
            refine ⟨23818622556180031477891703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15879081704120020985261135 23818622556180031477891703)
            ·
              refine ⟨35727933834270047216837555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23818622556180031477891703 35727933834270047216837555)
              ·
                refine ⟨53591900751405070825256333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35727933834270047216837555 53591900751405070825256333)
                ·
                  refine ⟨20096962781776901559471125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53591900751405070825256333 20096962781776901559471125)
                  ·
                    refine ⟨942045130395792260600209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20096962781776901559471125 942045130395792260600209)
                    ·
                      rfl

theorem cell23_5503879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_5503879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503879 prefixEnd_5503879 := by exact prefixLift 5503879
  have htrace : WordTrace (prefixWord ++ tailWord_5503879) baseStart_5503879 baseEnd_5503879 := by
    simpa [prefixWord, tailWord_5503879, baseEnd_5503879] using wordTrace_append hprefix tailTrace_5503879
  have hstable : (prefixWord ++ tailWord_5503879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503879).length < 2 ^ (prefixWord ++ tailWord_5503879).sum := by decide
  have hdescent : baseEnd_5503879 < baseStart_5503879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503936 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 3]
def baseStart_5503936 : Nat := 118140960795 + 5503936 * 2 ^ 59
def prefixEnd_5503936 : Nat := 4983230072969 + 3 ^ 40 * 5503936 * 2
def baseEnd_5503936 : Nat := 2826164659584683058787865

theorem tailTrace_5503936 : CollatzResearch.WordTrace tailWord_5503936 prefixEnd_5503936 2826164659584683058787865 := by
  unfold tailWord_5503936
  simp only [CollatzResearch.WordTrace]
  refine ⟨100372518894093672138445831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133830025192124896184594441 100372518894093672138445831)
  ·
    refine ⟨150558778341140508207668747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100372518894093672138445831 150558778341140508207668747)
    ·
      refine ⟨225838167511710762311503121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150558778341140508207668747 225838167511710762311503121)
      ·
        refine ⟨169378625633783071733627341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225838167511710762311503121 169378625633783071733627341)
        ·
          refine ⟨63516984612668651900110253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169378625633783071733627341 63516984612668651900110253)
          ·
            refine ⟨23818869229750744462541345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63516984612668651900110253 23818869229750744462541345)
            ·
              refine ⟨17864151922313058346906009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23818869229750744462541345 17864151922313058346906009)
              ·
                refine ⟨13398113941734793760179507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17864151922313058346906009 13398113941734793760179507)
                ·
                  refine ⟨20097170912602190640269261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13398113941734793760179507 20097170912602190640269261)
                  ·
                    refine ⟨7536439092225821490100973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20097170912602190640269261 7536439092225821490100973)
                    ·
                      refine ⟨2826164659584683058787865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7536439092225821490100973 2826164659584683058787865)
                      ·
                        rfl

theorem cell23_5503936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_5503936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503936 prefixEnd_5503936 := by exact prefixLift 5503936
  have htrace : WordTrace (prefixWord ++ tailWord_5503936) baseStart_5503936 baseEnd_5503936 := by
    simpa [prefixWord, tailWord_5503936, baseEnd_5503936] using wordTrace_append hprefix tailTrace_5503936
  have hstable : (prefixWord ++ tailWord_5503936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503936).length < 2 ^ (prefixWord ++ tailWord_5503936).sum := by decide
  have hdescent : baseEnd_5503936 < baseStart_5503936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503959 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_5503959 : Nat := 118140960795 + 5503959 * 2 ^ 59
def prefixEnd_5503959 : Nat := 4983230072969 + 3 ^ 40 * 5503959 * 2
def baseEnd_5503959 : Nat := 2826176469639736468800259

theorem tailTrace_5503959 : CollatzResearch.WordTrace tailWord_5503959 prefixEnd_5503959 2826176469639736468800259 := by
  unfold tailWord_5503959
  simp only [CollatzResearch.WordTrace]
  refine ⟨200745876667104019204978931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133830584444736012803319287 200745876667104019204978931)
  ·
    refine ⟨301118815000656028807468397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200745876667104019204978931 301118815000656028807468397)
    ·
      refine ⟨112919555625246010802800649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301118815000656028807468397 112919555625246010802800649)
      ·
        refine ⟨84689666718934508102100487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112919555625246010802800649 84689666718934508102100487)
        ·
          refine ⟨127034500078401762153150731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84689666718934508102100487 127034500078401762153150731)
          ·
            refine ⟨190551750117602643229726097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127034500078401762153150731 190551750117602643229726097)
            ·
              refine ⟨142913812588201982422294573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190551750117602643229726097 142913812588201982422294573)
              ·
                refine ⟨53592679720575743408360465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142913812588201982422294573 53592679720575743408360465)
                ·
                  refine ⟨40194509790431807556270349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53592679720575743408360465 40194509790431807556270349)
                  ·
                    refine ⟨15072941171411927833601381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40194509790431807556270349 15072941171411927833601381)
                    ·
                      refine ⟨2826176469639736468800259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15072941171411927833601381 2826176469639736468800259)
                      ·
                        rfl

theorem cell23_5503959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_5503959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503959 prefixEnd_5503959 := by exact prefixLift 5503959
  have htrace : WordTrace (prefixWord ++ tailWord_5503959) baseStart_5503959 baseEnd_5503959 := by
    simpa [prefixWord, tailWord_5503959, baseEnd_5503959] using wordTrace_append hprefix tailTrace_5503959
  have hstable : (prefixWord ++ tailWord_5503959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503959).length < 2 ^ (prefixWord ++ tailWord_5503959).sum := by decide
  have hdescent : baseEnd_5503959 < baseStart_5503959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503970 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_5503970 : Nat := 118140960795 + 5503970 * 2 ^ 59
def prefixEnd_5503970 : Nat := 4983230072969 + 3 ^ 40 * 5503970 * 2
def baseEnd_5503970 : Nat := 2826182117926935925762709

theorem tailTrace_5503970 : CollatzResearch.WordTrace tailWord_5503970 prefixEnd_5503970 2826182117926935925762709 := by
  unfold tailWord_5503970
  simp only [CollatzResearch.WordTrace]
  refine ⟨50186569467516042020907341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133830851913376112055752909 50186569467516042020907341)
  ·
    refine ⟨18819963550318515757840253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50186569467516042020907341 18819963550318515757840253)
    ·
      refine ⟨7057486331369443409190095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18819963550318515757840253 7057486331369443409190095)
      ·
        refine ⟨10586229497054165113785143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7057486331369443409190095 10586229497054165113785143)
        ·
          refine ⟨15879344245581247670677715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10586229497054165113785143 15879344245581247670677715)
          ·
            refine ⟨23819016368371871506016573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15879344245581247670677715 23819016368371871506016573)
            ·
              refine ⟨8932131138139451814756215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23819016368371871506016573 8932131138139451814756215)
              ·
                refine ⟨13398196707209177722134323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8932131138139451814756215 13398196707209177722134323)
                ·
                  refine ⟨20097295060813766583201485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13398196707209177722134323 20097295060813766583201485)
                  ·
                    refine ⟨7536485647805162468700557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20097295060813766583201485 7536485647805162468700557)
                    ·
                      refine ⟨2826182117926935925762709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7536485647805162468700557 2826182117926935925762709)
                      ·
                        rfl

theorem cell23_5503970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_5503970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503970 prefixEnd_5503970 := by exact prefixLift 5503970
  have htrace : WordTrace (prefixWord ++ tailWord_5503970) baseStart_5503970 baseEnd_5503970 := by
    simpa [prefixWord, tailWord_5503970, baseEnd_5503970] using wordTrace_append hprefix tailTrace_5503970
  have hstable : (prefixWord ++ tailWord_5503970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503970).length < 2 ^ (prefixWord ++ tailWord_5503970).sum := by decide
  have hdescent : baseEnd_5503970 < baseStart_5503970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503993 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 6, 2, 2]
def baseStart_5503993 : Nat := 118140960795 + 5503993 * 2 ^ 59
def prefixEnd_5503993 : Nat := 4983230072969 + 3 ^ 40 * 5503993 * 2
def baseEnd_5503993 : Nat := 2826193927981989335775103

theorem tailTrace_5503993 : CollatzResearch.WordTrace tailWord_5503993 prefixEnd_5503993 2826193927981989335775103 := by
  unfold tailWord_5503993
  simp only [CollatzResearch.WordTrace]
  refine ⟨200747116748980843011716633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133831411165987228674477755 200747116748980843011716633)
  ·
    refine ⟨150560337561735632258787475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200747116748980843011716633 150560337561735632258787475)
    ·
      refine ⟨225840506342603448388181213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150560337561735632258787475 225840506342603448388181213)
      ·
        refine ⟨84690189878476293145567955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225840506342603448388181213 84690189878476293145567955)
        ·
          refine ⟨127035284817714439718351933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84690189878476293145567955 127035284817714439718351933)
          ·
            refine ⟨47638231806642914894381975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127035284817714439718351933 47638231806642914894381975)
            ·
              refine ⟨71457347709964372341572963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47638231806642914894381975 71457347709964372341572963)
              ·
                refine ⟨107186021564946558512359445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71457347709964372341572963 107186021564946558512359445)
                ·
                  refine ⟨5024344760856869930266849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107186021564946558512359445 5024344760856869930266849)
                  ·
                    refine ⟨3768258570642652447700137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5024344760856869930266849 3768258570642652447700137)
                    ·
                      refine ⟨2826193927981989335775103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3768258570642652447700137 2826193927981989335775103)
                      ·
                        rfl

theorem cell23_5503993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_5503993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503993 prefixEnd_5503993 := by exact prefixLift 5503993
  have htrace : WordTrace (prefixWord ++ tailWord_5503993) baseStart_5503993 baseEnd_5503993 := by
    simpa [prefixWord, tailWord_5503993, baseEnd_5503993] using wordTrace_append hprefix tailTrace_5503993
  have hstable : (prefixWord ++ tailWord_5503993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503993).length < 2 ^ (prefixWord ++ tailWord_5503993).sum := by decide
  have hdescent : baseEnd_5503993 < baseStart_5503993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5503996 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_5503996 : Nat := 118140960795 + 5503996 * 2 ^ 59
def prefixEnd_5503996 : Nat := 4983230072969 + 3 ^ 40 * 5503996 * 2
def baseEnd_5503996 : Nat := 2826195468423952824037589

theorem tailTrace_5503996 : CollatzResearch.WordTrace tailWord_5503996 prefixEnd_5503996 2826195468423952824037589 := by
  unfold tailWord_5503996
  simp only [CollatzResearch.WordTrace]
  refine ⟨100373613083984987262037921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133831484111979983016050561 100373613083984987262037921)
  ·
    refine ⟨75280209812988740446528441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100373613083984987262037921 75280209812988740446528441)
    ·
      refine ⟨56460157359741555334896331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75280209812988740446528441 56460157359741555334896331)
      ·
        refine ⟨84690236039612333002344497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56460157359741555334896331 84690236039612333002344497)
        ·
          refine ⟨63517677029709249751758373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84690236039612333002344497 63517677029709249751758373)
          ·
            refine ⟨11909564443070484328454695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63517677029709249751758373 11909564443070484328454695)
            ·
              refine ⟨17864346664605726492682043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11909564443070484328454695 17864346664605726492682043)
              ·
                refine ⟨26796519996908589739023065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17864346664605726492682043 26796519996908589739023065)
                ·
                  refine ⟨20097389997681442304267299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26796519996908589739023065 20097389997681442304267299)
                  ·
                    refine ⟨30146084996522163456400949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20097389997681442304267299 30146084996522163456400949)
                    ·
                      refine ⟨2826195468423952824037589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30146084996522163456400949 2826195468423952824037589)
                      ·
                        rfl

theorem cell23_5503996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_5503996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5503996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5503996 prefixEnd_5503996 := by exact prefixLift 5503996
  have htrace : WordTrace (prefixWord ++ tailWord_5503996) baseStart_5503996 baseEnd_5503996 := by
    simpa [prefixWord, tailWord_5503996, baseEnd_5503996] using wordTrace_append hprefix tailTrace_5503996
  have hstable : (prefixWord ++ tailWord_5503996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5503996).length < 2 ^ (prefixWord ++ tailWord_5503996).sum := by decide
  have hdescent : baseEnd_5503996 < baseStart_5503996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5503996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504010 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2]
def baseStart_5504010 : Nat := 118140960795 + 5504010 * 2 ^ 59
def prefixEnd_5504010 : Nat := 4983230072969 + 3 ^ 40 * 5504010 * 2
def baseEnd_5504010 : Nat := 2826202657153115769262525

theorem tailTrace_5504010 : CollatzResearch.WordTrace tailWord_5504010 prefixEnd_5504010 2826202657153115769262525 := by
  unfold tailWord_5504010
  simp only [CollatzResearch.WordTrace]
  refine ⟨50186934197479813728771371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133831824526612836610056989 50186934197479813728771371)
  ·
    refine ⟨75280401296219720593157057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50186934197479813728771371 75280401296219720593157057)
    ·
      refine ⟨56460300972164790444867793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75280401296219720593157057 56460300972164790444867793)
      ·
        refine ⟨42345225729123592833650845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56460300972164790444867793 42345225729123592833650845)
        ·
          refine ⟨15879459648421347312619067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42345225729123592833650845 15879459648421347312619067)
          ·
            refine ⟨23819189472632020968928601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15879459648421347312619067 23819189472632020968928601)
            ·
              refine ⟨17864392104474015726696451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23819189472632020968928601 17864392104474015726696451)
              ·
                refine ⟨26796588156711023590044677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17864392104474015726696451 26796588156711023590044677)
                ·
                  refine ⟨5024360279383316923133377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26796588156711023590044677 5024360279383316923133377)
                  ·
                    refine ⟨3768270209537487692350033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5024360279383316923133377 3768270209537487692350033)
                    ·
                      refine ⟨2826202657153115769262525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3768270209537487692350033 2826202657153115769262525)
                      ·
                        rfl

theorem cell23_5504010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_5504010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504010 prefixEnd_5504010 := by exact prefixLift 5504010
  have htrace : WordTrace (prefixWord ++ tailWord_5504010) baseStart_5504010 baseEnd_5504010 := by
    simpa [prefixWord, tailWord_5504010, baseEnd_5504010] using wordTrace_append hprefix tailTrace_5504010
  have hstable : (prefixWord ++ tailWord_5504010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504010).length < 2 ^ (prefixWord ++ tailWord_5504010).sum := by decide
  have hdescent : baseEnd_5504010 < baseStart_5504010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504026 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3]
def baseStart_5504026 : Nat := 118140960795 + 5504026 * 2 ^ 59
def prefixEnd_5504026 : Nat := 4983230072969 + 3 ^ 40 * 5504026 * 2
def baseEnd_5504026 : Nat := 2826210872843587706662451

theorem tailTrace_5504026 : CollatzResearch.WordTrace tailWord_5504026 prefixEnd_5504026 2826210872843587706662451 := by
  unfold tailWord_5504026
  simp only [CollatzResearch.WordTrace]
  refine ⟨50187080089465322411916983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133832213571907526431778621 50187080089465322411916983)
  ·
    refine ⟨75280620134197983617875475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50187080089465322411916983 75280620134197983617875475)
    ·
      refine ⟨112920930201296975426813213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75280620134197983617875475 112920930201296975426813213)
      ·
        refine ⟨42345348825486365785054955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112920930201296975426813213 42345348825486365785054955)
        ·
          refine ⟨63518023238229548677582433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42345348825486365785054955 63518023238229548677582433)
          ·
            refine ⟨47638517428672161508186825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63518023238229548677582433 47638517428672161508186825)
            ·
              refine ⟨35728888071504121131140119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47638517428672161508186825 35728888071504121131140119)
              ·
                refine ⟨53593332107256181696710179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35728888071504121131140119 53593332107256181696710179)
                ·
                  refine ⟨80389998160884272545065269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53593332107256181696710179 80389998160884272545065269)
                  ·
                    refine ⟨7536562327582900551099869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80389998160884272545065269 7536562327582900551099869)
                    ·
                      refine ⟨2826210872843587706662451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7536562327582900551099869 2826210872843587706662451)
                      ·
                        rfl

theorem cell23_5504026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_5504026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504026 prefixEnd_5504026 := by exact prefixLift 5504026
  have htrace : WordTrace (prefixWord ++ tailWord_5504026) baseStart_5504026 baseEnd_5504026 := by
    simpa [prefixWord, tailWord_5504026, baseEnd_5504026] using wordTrace_append hprefix tailTrace_5504026
  have hstable : (prefixWord ++ tailWord_5504026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504026).length < 2 ^ (prefixWord ++ tailWord_5504026).sum := by decide
  have hdescent : baseEnd_5504026 < baseStart_5504026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504056 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_5504056 : Nat := 118140960795 + 5504056 * 2 ^ 59
def prefixEnd_5504056 : Nat := 4983230072969 + 3 ^ 40 * 5504056 * 2
def baseEnd_5504056 : Nat := 2826226277263222589287313

theorem tailTrace_5504056 : CollatzResearch.WordTrace tailWord_5504056 prefixEnd_5504056 2826226277263222589287313 := by
  unfold tailWord_5504056
  simp only [CollatzResearch.WordTrace]
  refine ⟨100374707273876302385630011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133832943031835069847506681 100374707273876302385630011)
  ·
    refine ⟨150562060910814453578445017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100374707273876302385630011 150562060910814453578445017)
    ·
      refine ⟨112921545683110840183833763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150562060910814453578445017 112921545683110840183833763)
      ·
        refine ⟨169382318524666260275750645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112921545683110840183833763 169382318524666260275750645)
        ·
          refine ⟨15879592361687461900851623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169382318524666260275750645 15879592361687461900851623)
          ·
            refine ⟨23819388542531192851277435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15879592361687461900851623 23819388542531192851277435)
            ·
              refine ⟨35729082813796789276916153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23819388542531192851277435 35729082813796789276916153)
              ·
                refine ⟨26796812110347591957687115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35729082813796789276916153 26796812110347591957687115)
                ·
                  refine ⟨40195218165521387936530673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26796812110347591957687115 40195218165521387936530673)
                  ·
                    refine ⟨30146413624141040952398005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40195218165521387936530673 30146413624141040952398005)
                    ·
                      refine ⟨2826226277263222589287313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30146413624141040952398005 2826226277263222589287313)
                      ·
                        rfl

theorem cell23_5504056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_5504056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504056 prefixEnd_5504056 := by exact prefixLift 5504056
  have htrace : WordTrace (prefixWord ++ tailWord_5504056) baseStart_5504056 baseEnd_5504056 := by
    simpa [prefixWord, tailWord_5504056, baseEnd_5504056] using wordTrace_append hprefix tailTrace_5504056
  have hstable : (prefixWord ++ tailWord_5504056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504056).length < 2 ^ (prefixWord ++ tailWord_5504056).sum := by decide
  have hdescent : baseEnd_5504056 < baseStart_5504056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504103 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_5504103 : Nat := 118140960795 + 5504103 * 2 ^ 59
def prefixEnd_5504103 : Nat := 4983230072969 + 3 ^ 40 * 5504103 * 2
def baseEnd_5504103 : Nat := 2826250410853983905399597

theorem tailTrace_5504103 : CollatzResearch.WordTrace tailWord_5504103 prefixEnd_5504103 2826250410853983905399597 := by
  unfold tailWord_5504103
  simp only [CollatzResearch.WordTrace]
  refine ⟨200751128778582331798220963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133834085852388221198813975 200751128778582331798220963)
  ·
    refine ⟨301126693167873497697331445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200751128778582331798220963 301126693167873497697331445)
    ·
      refine ⟨28230627484488140409124823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 301126693167873497697331445 28230627484488140409124823)
      ·
        refine ⟨42345941226732210613687235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28230627484488140409124823 42345941226732210613687235)
        ·
          refine ⟨63518911840098315920530853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42345941226732210613687235 63518911840098315920530853)
          ·
            refine ⟨11909795970018434235099535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63518911840098315920530853 11909795970018434235099535)
            ·
              refine ⟨17864693955027651352649303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11909795970018434235099535 17864693955027651352649303)
              ·
                refine ⟨26797040932541477028973955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17864693955027651352649303 26797040932541477028973955)
                ·
                  refine ⟨40195561398812215543460933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26797040932541477028973955 40195561398812215543460933)
                  ·
                    refine ⟨7536667762277290414398925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40195561398812215543460933 7536667762277290414398925)
                    ·
                      refine ⟨2826250410853983905399597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7536667762277290414398925 2826250410853983905399597)
                      ·
                        rfl

theorem cell23_5504103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_5504103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504103 prefixEnd_5504103 := by exact prefixLift 5504103
  have htrace : WordTrace (prefixWord ++ tailWord_5504103) baseStart_5504103 baseEnd_5504103 := by
    simpa [prefixWord, tailWord_5504103, baseEnd_5504103] using wordTrace_append hprefix tailTrace_5504103
  have hstable : (prefixWord ++ tailWord_5504103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504103).length < 2 ^ (prefixWord ++ tailWord_5504103).sum := by decide
  have hdescent : baseEnd_5504103 < baseStart_5504103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504160 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 2, 3, 2]
def baseStart_5504160 : Nat := 118140960795 + 5504160 * 2 ^ 59
def prefixEnd_5504160 : Nat := 4983230072969 + 3 ^ 40 * 5504160 * 2
def baseEnd_5504160 : Nat := 2826279679251290182386835

theorem tailTrace_5504160 : CollatzResearch.WordTrace tailWord_5504160 prefixEnd_5504160 2826279679251290182386835 := by
  unfold tailWord_5504160
  simp only [CollatzResearch.WordTrace]
  refine ⟨100376603869687915266522967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133835471826250553688697289 100376603869687915266522967)
  ·
    refine ⟨150564905804531872899784451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100376603869687915266522967 150564905804531872899784451)
    ·
      refine ⟨225847358706797809349676677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150564905804531872899784451 225847358706797809349676677)
      ·
        refine ⟨42346379757524589253064377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225847358706797809349676677 42346379757524589253064377)
        ·
          refine ⟨31759784818143441939798283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42346379757524589253064377 31759784818143441939798283)
          ·
            refine ⟨47639677227215162909697425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31759784818143441939798283 47639677227215162909697425)
            ·
              refine ⟨35729757920411372182273069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47639677227215162909697425 35729757920411372182273069)
              ·
                refine ⟨13398659220154264568352401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35729757920411372182273069 13398659220154264568352401)
                ·
                  refine ⟨10048994415115698426264301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13398659220154264568352401 10048994415115698426264301)
                  ·
                    refine ⟨3768372905668386909849113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10048994415115698426264301 3768372905668386909849113)
                    ·
                      refine ⟨2826279679251290182386835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3768372905668386909849113 2826279679251290182386835)
                      ·
                        rfl

theorem cell23_5504160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_5504160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504160 prefixEnd_5504160 := by exact prefixLift 5504160
  have htrace : WordTrace (prefixWord ++ tailWord_5504160) baseStart_5504160 baseEnd_5504160 := by
    simpa [prefixWord, tailWord_5504160, baseEnd_5504160] using wordTrace_append hprefix tailTrace_5504160
  have hstable : (prefixWord ++ tailWord_5504160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504160).length < 2 ^ (prefixWord ++ tailWord_5504160).sum := by decide
  have hdescent : baseEnd_5504160 < baseStart_5504160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504176 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 5]
def baseStart_5504176 : Nat := 118140960795 + 5504176 * 2 ^ 59
def prefixEnd_5504176 : Nat := 4983230072969 + 3 ^ 40 * 5504176 * 2
def baseEnd_5504176 : Nat := 2826287894941762119786761

theorem tailTrace_5504176 : CollatzResearch.WordTrace tailWord_5504176 prefixEnd_5504176 2826287894941762119786761 := by
  unfold tailWord_5504176
  simp only [CollatzResearch.WordTrace]
  refine ⟨100376895653658932632814191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133835860871545243510418921 100376895653658932632814191)
  ·
    refine ⟨150565343480488398949221287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100376895653658932632814191 150565343480488398949221287)
    ·
      refine ⟨225848015220732598423831931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150565343480488398949221287 225848015220732598423831931)
      ·
        refine ⟨338772022831098897635747897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225848015220732598423831931 338772022831098897635747897)
        ·
          refine ⟨254079017123324173226810923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338772022831098897635747897 254079017123324173226810923)
          ·
            refine ⟨381118525684986259840216385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254079017123324173226810923 381118525684986259840216385)
            ·
              refine ⟨285838894263739694880162289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381118525684986259840216385 285838894263739694880162289)
              ·
                refine ⟨214379170697804771160121717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285838894263739694880162289 214379170697804771160121717)
                ·
                  refine ⟨20098047252919197296261411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214379170697804771160121717 20098047252919197296261411)
                  ·
                    refine ⟨30147070879378795944392117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20098047252919197296261411 30147070879378795944392117)
                    ·
                      refine ⟨2826287894941762119786761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30147070879378795944392117 2826287894941762119786761)
                      ·
                        rfl

theorem cell23_5504176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_5504176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504176 prefixEnd_5504176 := by exact prefixLift 5504176
  have htrace : WordTrace (prefixWord ++ tailWord_5504176) baseStart_5504176 baseEnd_5504176 := by
    simpa [prefixWord, tailWord_5504176, baseEnd_5504176] using wordTrace_append hprefix tailTrace_5504176
  have hstable : (prefixWord ++ tailWord_5504176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504176).length < 2 ^ (prefixWord ++ tailWord_5504176).sum := by decide
  have hdescent : baseEnd_5504176 < baseStart_5504176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504177 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 2, 3, 2]
def baseStart_5504177 : Nat := 118140960795 + 5504177 * 2 ^ 59
def prefixEnd_5504177 : Nat := 4983230072969 + 3 ^ 40 * 5504177 * 2
def baseEnd_5504177 : Nat := 2826288408422416615874257

theorem tailTrace_5504177 : CollatzResearch.WordTrace tailWord_5504177 prefixEnd_5504177 2826288408422416615874257 := by
  unfold tailWord_5504177
  simp only [CollatzResearch.WordTrace]
  refine ⟨200753827780314242436414785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133835885186876161624276523 200753827780314242436414785)
  ·
    refine ⟨150565370835235681827311089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200753827780314242436414785 150565370835235681827311089)
    ·
      refine ⟨112924028126426761370483317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150565370835235681827311089 112924028126426761370483317)
      ·
        refine ⟨10586627636852508878482811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112924028126426761370483317 10586627636852508878482811)
        ·
          refine ⟨15879941455278763317724217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10586627636852508878482811 15879941455278763317724217)
          ·
            refine ⟨11909956091459072488293163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15879941455278763317724217 11909956091459072488293163)
            ·
              refine ⟨17864934137188608732439745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11909956091459072488293163 17864934137188608732439745)
              ·
                refine ⟨13398700602891456549329809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17864934137188608732439745 13398700602891456549329809)
                ·
                  refine ⟨10049025452168592411997357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13398700602891456549329809 10049025452168592411997357)
                  ·
                    refine ⟨3768384544563222154499009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10049025452168592411997357 3768384544563222154499009)
                    ·
                      refine ⟨2826288408422416615874257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3768384544563222154499009 2826288408422416615874257)
                      ·
                        rfl

theorem cell23_5504177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_5504177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504177 prefixEnd_5504177 := by exact prefixLift 5504177
  have htrace : WordTrace (prefixWord ++ tailWord_5504177) baseStart_5504177 baseEnd_5504177 := by
    simpa [prefixWord, tailWord_5504177, baseEnd_5504177] using wordTrace_append hprefix tailTrace_5504177
  have hstable : (prefixWord ++ tailWord_5504177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504177).length < 2 ^ (prefixWord ++ tailWord_5504177).sum := by decide
  have hdescent : baseEnd_5504177 < baseStart_5504177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504183 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 4, 4]
def baseStart_5504183 : Nat := 118140960795 + 5504183 * 2 ^ 59
def prefixEnd_5504183 : Nat := 4983230072969 + 3 ^ 40 * 5504183 * 2
def baseEnd_5504183 : Nat := 942097163102114530799743

theorem tailTrace_5504183 : CollatzResearch.WordTrace tailWord_5504183 prefixEnd_5504183 942097163102114530799743 := by
  unfold tailWord_5504183
  simp only [CollatzResearch.WordTrace]
  refine ⟨200754046618292505461133203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133836031078861670307422135 200754046618292505461133203)
  ·
    refine ⟨301131069927438758191699805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200754046618292505461133203 301131069927438758191699805)
    ·
      refine ⟨112924151222789534321887427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301131069927438758191699805 112924151222789534321887427)
      ·
        refine ⟨169386226834184301482831141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112924151222789534321887427 169386226834184301482831141)
        ·
          refine ⟨31759917531409556528030839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169386226834184301482831141 31759917531409556528030839)
          ·
            refine ⟨47639876297114334792046259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31759917531409556528030839 47639876297114334792046259)
            ·
              refine ⟨71459814445671502188069389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47639876297114334792046259 71459814445671502188069389)
              ·
                refine ⟨26797430417126813320526021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71459814445671502188069389 26797430417126813320526021)
                ·
                  refine ⟨5024518203211277497598629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26797430417126813320526021 5024518203211277497598629)
                  ·
                    refine ⟨942097163102114530799743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5024518203211277497598629 942097163102114530799743)
                    ·
                      rfl

theorem cell23_5504183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_5504183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504183 prefixEnd_5504183 := by exact prefixLift 5504183
  have htrace : WordTrace (prefixWord ++ tailWord_5504183) baseStart_5504183 baseEnd_5504183 := by
    simpa [prefixWord, tailWord_5504183, baseEnd_5504183] using wordTrace_append hprefix tailTrace_5504183
  have hstable : (prefixWord ++ tailWord_5504183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504183).length < 2 ^ (prefixWord ++ tailWord_5504183).sum := by decide
  have hdescent : baseEnd_5504183 < baseStart_5504183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504210 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_5504210 : Nat := 118140960795 + 5504210 * 2 ^ 59
def prefixEnd_5504210 : Nat := 4983230072969 + 3 ^ 40 * 5504210 * 2
def baseEnd_5504210 : Nat := 2826305353284014986761605

theorem tailTrace_5504210 : CollatzResearch.WordTrace tailWord_5504210 prefixEnd_5504210 2826305353284014986761605 := by
  unfold tailWord_5504210
  simp only [CollatzResearch.WordTrace]
  refine ⟨50188757847298672268091521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133836687592796459381577389 50188757847298672268091521)
  ·
    refine ⟨37641568385474004201068641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50188757847298672268091521 37641568385474004201068641)
    ·
      refine ⟨28231176289105503150801481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37641568385474004201068641 28231176289105503150801481)
      ·
        refine ⟨21173382216829127363101111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28231176289105503150801481 21173382216829127363101111)
        ·
          refine ⟨31760073325243691044651667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21173382216829127363101111 31760073325243691044651667)
          ·
            refine ⟨47640109987865536566977501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31760073325243691044651667 47640109987865536566977501)
            ·
              refine ⟨17865041245449576212616563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47640109987865536566977501 17865041245449576212616563)
              ·
                refine ⟨26797561868174364318924845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17865041245449576212616563 26797561868174364318924845)
                ·
                  refine ⟨10049085700565386619596817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26797561868174364318924845 10049085700565386619596817)
                  ·
                    refine ⟨7536814275424039964697613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10049085700565386619596817 7536814275424039964697613)
                    ·
                      refine ⟨2826305353284014986761605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7536814275424039964697613 2826305353284014986761605)
                      ·
                        rfl

theorem cell23_5504210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_5504210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504210 prefixEnd_5504210 := by exact prefixLift 5504210
  have htrace : WordTrace (prefixWord ++ tailWord_5504210) baseStart_5504210 baseEnd_5504210 := by
    simpa [prefixWord, tailWord_5504210, baseEnd_5504210] using wordTrace_append hprefix tailTrace_5504210
  have hstable : (prefixWord ++ tailWord_5504210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504210).length < 2 ^ (prefixWord ++ tailWord_5504210).sum := by decide
  have hdescent : baseEnd_5504210 < baseStart_5504210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504213 : List Nat := [1, 3, 2, 4, 1, 1, 2, 9]
def baseStart_5504213 : Nat := 118140960795 + 5504213 * 2 ^ 59
def prefixEnd_5504213 : Nat := 4983230072969 + 3 ^ 40 * 5504213 * 2
def baseEnd_5504213 : Nat := 104678033100962165741633

theorem tailTrace_5504213 : CollatzResearch.WordTrace tailWord_5504213 prefixEnd_5504213 104678033100962165741633 := by
  unfold tailWord_5504213
  simp only [CollatzResearch.WordTrace]
  refine ⟨200755140808183820584725293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133836760538789213723150195 200755140808183820584725293)
  ·
    refine ⟨75283177803068932719271985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200755140808183820584725293 75283177803068932719271985)
    ·
      refine ⟨56462383352301699539453989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75283177803068932719271985 56462383352301699539453989)
      ·
        refine ⟨10586696878556568663647623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56462383352301699539453989 10586696878556568663647623)
        ·
          refine ⟨15880045317834852995471435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10586696878556568663647623 15880045317834852995471435)
          ·
            refine ⟨23820067976752279493207153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15880045317834852995471435 23820067976752279493207153)
            ·
              refine ⟨17865050982564209619905365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23820067976752279493207153 17865050982564209619905365)
              ·
                refine ⟨104678033100962165741633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17865050982564209619905365 104678033100962165741633)
                ·
                  rfl

theorem cell23_5504213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 9].length) (baseStart_5504213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504213 prefixEnd_5504213 := by exact prefixLift 5504213
  have htrace : WordTrace (prefixWord ++ tailWord_5504213) baseStart_5504213 baseEnd_5504213 := by
    simpa [prefixWord, tailWord_5504213, baseEnd_5504213] using wordTrace_append hprefix tailTrace_5504213
  have hstable : (prefixWord ++ tailWord_5504213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504213).length < 2 ^ (prefixWord ++ tailWord_5504213).sum := by decide
  have hdescent : baseEnd_5504213 < baseStart_5504213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504223 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 3]
def baseStart_5504223 : Nat := 118140960795 + 5504223 * 2 ^ 59
def prefixEnd_5504223 : Nat := 4983230072969 + 3 ^ 40 * 5504223 * 2
def baseEnd_5504223 : Nat := 2826312028532523435899045

theorem tailTrace_5504223 : CollatzResearch.WordTrace tailWord_5504223 prefixEnd_5504223 2826312028532523435899045 := by
  unfold tailWord_5504223
  simp only [CollatzResearch.WordTrace]
  refine ⟨200755505538147592292589323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133837003692098394861726215 200755505538147592292589323)
  ·
    refine ⟨301133258307221388438883985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200755505538147592292589323 301133258307221388438883985)
    ·
      refine ⟨225849943730416041329162989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301133258307221388438883985 225849943730416041329162989)
      ·
        refine ⟨84693728898906015498436121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225849943730416041329162989 84693728898906015498436121)
        ·
          refine ⟨63520296674179511623827091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84693728898906015498436121 63520296674179511623827091)
          ·
            refine ⟨95280445011269267435740637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63520296674179511623827091 95280445011269267435740637)
            ·
              refine ⟨35730166879225975288402739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95280445011269267435740637 35730166879225975288402739)
              ·
                refine ⟨53595250318838962932604109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35730166879225975288402739 53595250318838962932604109)
                ·
                  refine ⟨20098218869564611099726541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53595250318838962932604109 20098218869564611099726541)
                  ·
                    refine ⟨7536832076086729162397453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20098218869564611099726541 7536832076086729162397453)
                    ·
                      refine ⟨2826312028532523435899045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7536832076086729162397453 2826312028532523435899045)
                      ·
                        rfl

theorem cell23_5504223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_5504223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504223 prefixEnd_5504223 := by exact prefixLift 5504223
  have htrace : WordTrace (prefixWord ++ tailWord_5504223) baseStart_5504223 baseEnd_5504223 := by
    simpa [prefixWord, tailWord_5504223, baseEnd_5504223] using wordTrace_append hprefix tailTrace_5504223
  have hstable : (prefixWord ++ tailWord_5504223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504223).length < 2 ^ (prefixWord ++ tailWord_5504223).sum := by decide
  have hdescent : baseEnd_5504223 < baseStart_5504223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504250 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2]
def baseStart_5504250 : Nat := 118140960795 + 5504250 * 2 ^ 59
def prefixEnd_5504250 : Nat := 4983230072969 + 3 ^ 40 * 5504250 * 2
def baseEnd_5504250 : Nat := 2826325892510194830261421

theorem tailTrace_5504250 : CollatzResearch.WordTrace tailWord_5504250 prefixEnd_5504250 2826325892510194830261421 := by
  unfold tailWord_5504250
  simp only [CollatzResearch.WordTrace]
  refine ⟨50189122577262443975955551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133837660206033183935881469 50189122577262443975955551)
  ·
    refine ⟨75283683865893665963933327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50189122577262443975955551 75283683865893665963933327)
    ·
      refine ⟨112925525798840498945899991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75283683865893665963933327 112925525798840498945899991)
      ·
        refine ⟨169388288698260748418849987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112925525798840498945899991 169388288698260748418849987)
        ·
          refine ⟨254082433047391122628274981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169388288698260748418849987 254082433047391122628274981)
          ·
            refine ⟨47640456196385835492801559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254082433047391122628274981 47640456196385835492801559)
            ·
              refine ⟨71460684294578753239202339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47640456196385835492801559 71460684294578753239202339)
              ·
                refine ⟨107191026441868129858803509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71460684294578753239202339 107191026441868129858803509)
                ·
                  refine ⟨10049158728925137174262829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107191026441868129858803509 10049158728925137174262829)
                  ·
                    refine ⟨3768434523346926440348561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10049158728925137174262829 3768434523346926440348561)
                    ·
                      refine ⟨2826325892510194830261421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3768434523346926440348561 2826325892510194830261421)
                      ·
                        rfl

theorem cell23_5504250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2].length) (baseStart_5504250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504250 prefixEnd_5504250 := by exact prefixLift 5504250
  have htrace : WordTrace (prefixWord ++ tailWord_5504250) baseStart_5504250 baseEnd_5504250 := by
    simpa [prefixWord, tailWord_5504250, baseEnd_5504250] using wordTrace_append hprefix tailTrace_5504250
  have hstable : (prefixWord ++ tailWord_5504250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504250).length < 2 ^ (prefixWord ++ tailWord_5504250).sum := by decide
  have hdescent : baseEnd_5504250 < baseStart_5504250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504257 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_5504257 : Nat := 118140960795 + 5504257 * 2 ^ 59
def prefixEnd_5504257 : Nat := 4983230072969 + 3 ^ 40 * 5504257 * 2
def baseEnd_5504257 : Nat := 2826329486874776302873889

theorem tailTrace_5504257 : CollatzResearch.WordTrace tailWord_5504257 prefixEnd_5504257 2826329486874776302873889 := by
  unfold tailWord_5504257
  simp only [CollatzResearch.WordTrace]
  refine ⟨200756745620024416099327025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133837830413349610732884683 200756745620024416099327025)
  ·
    refine ⟨150567559215018312074495269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200756745620024416099327025 150567559215018312074495269)
    ·
      refine ⟨28231417352815933513967863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150567559215018312074495269 28231417352815933513967863)
      ·
        refine ⟨42347126029223900270951795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28231417352815933513967863 42347126029223900270951795)
        ·
          refine ⟨63520689043835850406427693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42347126029223900270951795 63520689043835850406427693)
          ·
            refine ⟨23820258391438443902410385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63520689043835850406427693 23820258391438443902410385)
            ·
              refine ⟨17865193793578832926807789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23820258391438443902410385 17865193793578832926807789)
              ·
                refine ⟨6699447672592062347552921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17865193793578832926807789 6699447672592062347552921)
                ·
                  refine ⟨5024585754444046760664691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6699447672592062347552921 5024585754444046760664691)
                  ·
                    refine ⟨7536878631666070140997037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5024585754444046760664691 7536878631666070140997037)
                    ·
                      refine ⟨2826329486874776302873889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7536878631666070140997037 2826329486874776302873889)
                      ·
                        rfl

theorem cell23_5504257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_5504257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504257 prefixEnd_5504257 := by exact prefixLift 5504257
  have htrace : WordTrace (prefixWord ++ tailWord_5504257) baseStart_5504257 baseEnd_5504257 := by
    simpa [prefixWord, tailWord_5504257, baseEnd_5504257] using wordTrace_append hprefix tailTrace_5504257
  have hstable : (prefixWord ++ tailWord_5504257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504257).length < 2 ^ (prefixWord ++ tailWord_5504257).sum := by decide
  have hdescent : baseEnd_5504257 < baseStart_5504257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504284 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_5504284 : Nat := 118140960795 + 5504284 * 2 ^ 59
def prefixEnd_5504284 : Nat := 4983230072969 + 3 ^ 40 * 5504284 * 2
def baseEnd_5504284 : Nat := 2826343350852447697236265

theorem tailTrace_5504284 : CollatzResearch.WordTrace tailWord_5504284 prefixEnd_5504284 2826343350852447697236265 := by
  unfold tailWord_5504284
  simp only [CollatzResearch.WordTrace]
  refine ⟨100378865195463299855279953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133838486927284399807039937 100378865195463299855279953)
  ·
    refine ⟨75284148896597474891459965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100378865195463299855279953 75284148896597474891459965)
    ·
      refine ⟨28231555836224053084297487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75284148896597474891459965 28231555836224053084297487)
      ·
        refine ⟨42347333754336079626446231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28231555836224053084297487 42347333754336079626446231)
        ·
          refine ⟨63521000631504119439669347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42347333754336079626446231 63521000631504119439669347)
          ·
            refine ⟨95281500947256179159504021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63521000631504119439669347 95281500947256179159504021)
            ·
              refine ⟨4466320356902633398101751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95281500947256179159504021 4466320356902633398101751)
              ·
                refine ⟨6699480535353950097152627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4466320356902633398101751 6699480535353950097152627)
                ·
                  refine ⟨10049220803030925145728941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6699480535353950097152627 10049220803030925145728941)
                  ·
                    refine ⟨3768457801136596929648353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10049220803030925145728941 3768457801136596929648353)
                    ·
                      refine ⟨2826343350852447697236265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3768457801136596929648353 2826343350852447697236265)
                      ·
                        rfl

theorem cell23_5504284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_5504284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504284 prefixEnd_5504284 := by exact prefixLift 5504284
  have htrace : WordTrace (prefixWord ++ tailWord_5504284) baseStart_5504284 baseEnd_5504284 := by
    simpa [prefixWord, tailWord_5504284, baseEnd_5504284] using wordTrace_append hprefix tailTrace_5504284
  have hstable : (prefixWord ++ tailWord_5504284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504284).length < 2 ^ (prefixWord ++ tailWord_5504284).sum := by decide
  have hdescent : baseEnd_5504284 < baseStart_5504284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504354 : List Nat := [3, 3, 2, 1, 1, 1, 5, 2, 5]
def baseStart_5504354 : Nat := 118140960795 + 5504354 * 2 ^ 59
def prefixEnd_5504354 : Nat := 4983230072969 + 3 ^ 40 * 5504354 * 2
def baseEnd_5504354 : Nat := 314042143833140269262327

theorem tailTrace_5504354 : CollatzResearch.WordTrace tailWord_5504354 prefixEnd_5504354 314042143833140269262327 := by
  unfold tailWord_5504354
  simp only [CollatzResearch.WordTrace]
  refine ⟨50190070875168250416402029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133840189000448667777072077 50190070875168250416402029)
  ·
    refine ⟨18821276578188093906150761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50190070875168250416402029 18821276578188093906150761)
    ·
      refine ⟨14115957433641070429613071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18821276578188093906150761 14115957433641070429613071)
      ·
        refine ⟨21173936150461605644419607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14115957433641070429613071 21173936150461605644419607)
        ·
          refine ⟨31760904225692408466629411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21173936150461605644419607 31760904225692408466629411)
          ·
            refine ⟨47641356338538612699944117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31760904225692408466629411 47641356338538612699944117)
            ·
              refine ⟨4466377156737994940619761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47641356338538612699944117 4466377156737994940619761)
              ·
                refine ⟨3349782867553496205464821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4466377156737994940619761 3349782867553496205464821)
                ·
                  refine ⟨314042143833140269262327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3349782867553496205464821 314042143833140269262327)
                  ·
                    rfl

theorem cell23_5504354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_5504354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504354 prefixEnd_5504354 := by exact prefixLift 5504354
  have htrace : WordTrace (prefixWord ++ tailWord_5504354) baseStart_5504354 baseEnd_5504354 := by
    simpa [prefixWord, tailWord_5504354, baseEnd_5504354] using wordTrace_append hprefix tailTrace_5504354
  have hstable : (prefixWord ++ tailWord_5504354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504354).length < 2 ^ (prefixWord ++ tailWord_5504354).sum := by decide
  have hdescent : baseEnd_5504354 < baseStart_5504354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504370 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_5504370 : Nat := 118140960795 + 5504370 * 2 ^ 59
def prefixEnd_5504370 : Nat := 4983230072969 + 3 ^ 40 * 5504370 * 2
def baseEnd_5504370 : Nat := 2826387510188734360760869

theorem tailTrace_5504370 : CollatzResearch.WordTrace tailWord_5504370 prefixEnd_5504370 2826387510188734360760869 := by
  unfold tailWord_5504370
  simp only [CollatzResearch.WordTrace]
  refine ⟨50190216767153759099547641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133840578045743357598793709 50190216767153759099547641)
  ·
    refine ⟨37642662575365319324660731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50190216767153759099547641 37642662575365319324660731)
    ·
      refine ⟨56463993863047978986991097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37642662575365319324660731 56463993863047978986991097)
      ·
        refine ⟨42347995397285984240243323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56463993863047978986991097 42347995397285984240243323)
        ·
          refine ⟨63521993095928976360364985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42347995397285984240243323 63521993095928976360364985)
          ·
            refine ⟨47641494821946732270273739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63521993095928976360364985 47641494821946732270273739)
            ·
              refine ⟨71462242232920098405410609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47641494821946732270273739 71462242232920098405410609)
              ·
                refine ⟨53596681674690073804057957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71462242232920098405410609 53596681674690073804057957)
                ·
                  refine ⟨10049377814004388838260867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53596681674690073804057957 10049377814004388838260867)
                  ·
                    refine ⟨15074066721006583257391301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10049377814004388838260867 15074066721006583257391301)
                    ·
                      refine ⟨2826387510188734360760869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15074066721006583257391301 2826387510188734360760869)
                      ·
                        rfl

theorem cell23_5504370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_5504370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504370 prefixEnd_5504370 := by exact prefixLift 5504370
  have htrace : WordTrace (prefixWord ++ tailWord_5504370) baseStart_5504370 baseEnd_5504370 := by
    simpa [prefixWord, tailWord_5504370, baseEnd_5504370] using wordTrace_append hprefix tailTrace_5504370
  have hstable : (prefixWord ++ tailWord_5504370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504370).length < 2 ^ (prefixWord ++ tailWord_5504370).sum := by decide
  have hdescent : baseEnd_5504370 < baseStart_5504370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504380 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 5, 4]
def baseStart_5504380 : Nat := 118140960795 + 5504380 * 2 ^ 59
def prefixEnd_5504380 : Nat := 4983230072969 + 3 ^ 40 * 5504380 * 2
def baseEnd_5504380 : Nat := 942130881665093107211941

theorem tailTrace_5504380 : CollatzResearch.WordTrace tailWord_5504380 prefixEnd_5504380 942130881665093107211941 := by
  unfold tailWord_5504380
  simp only [CollatzResearch.WordTrace]
  refine ⟨100380615899289404053027297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133840821199052538737369729 100380615899289404053027297)
  ·
    refine ⟨75285461924467053039770473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100380615899289404053027297 75285461924467053039770473)
    ·
      refine ⟨56464096443350289779827855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75285461924467053039770473 56464096443350289779827855)
      ·
        refine ⟨84696144665025434669741783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56464096443350289779827855 84696144665025434669741783)
        ·
          refine ⟨127044216997538152004612675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84696144665025434669741783 127044216997538152004612675)
          ·
            refine ⟨190566325496307228006919013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127044216997538152004612675 190566325496307228006919013)
            ·
              refine ⟨35731186030557605251297315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190566325496307228006919013 35731186030557605251297315)
              ·
                refine ⟨53596779045836407876945973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35731186030557605251297315 53596779045836407876945973)
                ·
                  refine ⟨5024698035547163238463685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53596779045836407876945973 5024698035547163238463685)
                  ·
                    refine ⟨942130881665093107211941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5024698035547163238463685 942130881665093107211941)
                    ·
                      rfl

theorem cell23_5504380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_5504380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504380 prefixEnd_5504380 := by exact prefixLift 5504380
  have htrace : WordTrace (prefixWord ++ tailWord_5504380) baseStart_5504380 baseEnd_5504380 := by
    simpa [prefixWord, tailWord_5504380, baseEnd_5504380] using wordTrace_append hprefix tailTrace_5504380
  have hstable : (prefixWord ++ tailWord_5504380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504380).length < 2 ^ (prefixWord ++ tailWord_5504380).sum := by decide
  have hdescent : baseEnd_5504380 < baseStart_5504380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504387 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 4]
def baseStart_5504387 : Nat := 118140960795 + 5504387 * 2 ^ 59
def prefixEnd_5504387 : Nat := 4983230072969 + 3 ^ 40 * 5504387 * 2
def baseEnd_5504387 : Nat := 2826396239359860794248291

theorem tailTrace_5504387 : CollatzResearch.WordTrace tailWord_5504387 prefixEnd_5504387 2826396239359860794248291 := by
  unfold tailWord_5504387
  simp only [CollatzResearch.WordTrace]
  refine ⟨200761487109553448301559415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133840991406368965534372943 200761487109553448301559415)
  ·
    refine ⟨301142230664330172452339123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200761487109553448301559415 301142230664330172452339123)
    ·
      refine ⟨451713345996495258678508685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301142230664330172452339123 451713345996495258678508685)
      ·
        refine ⟨169392504748685722004440757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451713345996495258678508685 169392504748685722004440757)
        ·
          refine ⟨15880547320189286437916321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169392504748685722004440757 15880547320189286437916321)
          ·
            refine ⟨11910410490141964828437241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15880547320189286437916321 11910410490141964828437241)
            ·
              refine ⟨8932807867606473621327931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11910410490141964828437241 8932807867606473621327931)
              ·
                refine ⟨13399211801409710431991897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8932807867606473621327931 13399211801409710431991897)
                ·
                  refine ⟨10049408851057282823993923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13399211801409710431991897 10049408851057282823993923)
                  ·
                    refine ⟨15074113276585924235990885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10049408851057282823993923 15074113276585924235990885)
                    ·
                      refine ⟨2826396239359860794248291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15074113276585924235990885 2826396239359860794248291)
                      ·
                        rfl

theorem cell23_5504387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_5504387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504387 prefixEnd_5504387 := by exact prefixLift 5504387
  have htrace : WordTrace (prefixWord ++ tailWord_5504387) baseStart_5504387 baseEnd_5504387 := by
    simpa [prefixWord, tailWord_5504387, baseEnd_5504387] using wordTrace_append hprefix tailTrace_5504387
  have hstable : (prefixWord ++ tailWord_5504387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504387).length < 2 ^ (prefixWord ++ tailWord_5504387).sum := by decide
  have hdescent : baseEnd_5504387 < baseStart_5504387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504420 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_5504420 : Nat := 118140960795 + 5504420 * 2 ^ 59
def prefixEnd_5504420 : Nat := 4983230072969 + 3 ^ 40 * 5504420 * 2
def baseEnd_5504420 : Nat := 2826413184221459165135639

theorem tailTrace_5504420 : CollatzResearch.WordTrace tailWord_5504420 prefixEnd_5504420 2826413184221459165135639 := by
  unfold tailWord_5504420
  simp only [CollatzResearch.WordTrace]
  refine ⟨100381345359216947468755357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133841793812289263291673809 100381345359216947468755357)
  ·
    refine ⟨37643004509706355300783259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100381345359216947468755357 37643004509706355300783259)
    ·
      refine ⟨56464506764559532951174889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37643004509706355300783259 56464506764559532951174889)
      ·
        refine ⟨42348380073419649713381167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56464506764559532951174889 42348380073419649713381167)
        ·
          refine ⟨63522570110129474570071751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42348380073419649713381167 63522570110129474570071751)
          ·
            refine ⟨95283855165194211855107627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63522570110129474570071751 95283855165194211855107627)
            ·
              refine ⟨142925782747791317782661441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95283855165194211855107627 142925782747791317782661441)
              ·
                refine ⟨107194337060843488336996081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142925782747791317782661441 107194337060843488336996081)
                ·
                  refine ⟨80395752795632616252747061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107194337060843488336996081 80395752795632616252747061)
                  ·
                    refine ⟨7537101824590557773695037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80395752795632616252747061 7537101824590557773695037)
                    ·
                      refine ⟨2826413184221459165135639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7537101824590557773695037 2826413184221459165135639)
                      ·
                        rfl

theorem cell23_5504420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_5504420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504420 prefixEnd_5504420 := by exact prefixLift 5504420
  have htrace : WordTrace (prefixWord ++ tailWord_5504420) baseStart_5504420 baseEnd_5504420 := by
    simpa [prefixWord, tailWord_5504420, baseEnd_5504420] using wordTrace_append hprefix tailTrace_5504420
  have hstable : (prefixWord ++ tailWord_5504420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504420).length < 2 ^ (prefixWord ++ tailWord_5504420).sum := by decide
  have hdescent : baseEnd_5504420 < baseStart_5504420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504440 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 3, 5]
def baseStart_5504440 : Nat := 118140960795 + 5504440 * 2 ^ 59
def prefixEnd_5504440 : Nat := 4983230072969 + 3 ^ 40 * 5504440 * 2
def baseEnd_5504440 : Nat := 942141151278183028961849

theorem tailTrace_5504440 : CollatzResearch.WordTrace tailWord_5504440 prefixEnd_5504440 942141151278183028961849 := by
  unfold tailWord_5504440
  simp only [CollatzResearch.WordTrace]
  refine ⟨100381710089180719176619387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133842280118907625568825849 100381710089180719176619387)
  ·
    refine ⟨150572565133771078764929081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100381710089180719176619387 150572565133771078764929081)
    ·
      refine ⟨112929423850328309073696811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150572565133771078764929081 112929423850328309073696811)
      ·
        refine ⟨169394135775492463610545217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112929423850328309073696811 169394135775492463610545217)
        ·
          refine ⟨127045601831619347707908913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169394135775492463610545217 127045601831619347707908913)
          ·
            refine ⟨95284201373714510780931685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127045601831619347707908913 95284201373714510780931685)
            ·
              refine ⟨17865787757571470771424691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95284201373714510780931685 17865787757571470771424691)
              ·
                refine ⟨26798681636357206157137037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17865787757571470771424691 26798681636357206157137037)
                ·
                  refine ⟨10049505613633952308926389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26798681636357206157137037 10049505613633952308926389)
                  ·
                    refine ⟨942141151278183028961849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10049505613633952308926389 942141151278183028961849)
                    ·
                      rfl

theorem cell23_5504440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_5504440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504440 prefixEnd_5504440 := by exact prefixLift 5504440
  have htrace : WordTrace (prefixWord ++ tailWord_5504440) baseStart_5504440 baseEnd_5504440 := by
    simpa [prefixWord, tailWord_5504440, baseEnd_5504440] using wordTrace_append hprefix tailTrace_5504440
  have hstable : (prefixWord ++ tailWord_5504440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504440).length < 2 ^ (prefixWord ++ tailWord_5504440).sum := by decide
  have hdescent : baseEnd_5504440 < baseStart_5504440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504441 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 2, 2, 3]
def baseStart_5504441 : Nat := 118140960795 + 5504441 * 2 ^ 59
def prefixEnd_5504441 : Nat := 4983230072969 + 3 ^ 40 * 5504441 * 2
def baseEnd_5504441 : Nat := 2826423967315203582973043

theorem tailTrace_5504441 : CollatzResearch.WordTrace tailWord_5504441 prefixEnd_5504441 2826423967315203582973043 := by
  unfold tailWord_5504441
  simp only [CollatzResearch.WordTrace]
  refine ⟨200763456651357815524025177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133842304434238543682683451 200763456651357815524025177)
  ·
    refine ⟨150572592488518361643018883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200763456651357815524025177 150572592488518361643018883)
    ·
      refine ⟨225858888732777542464528325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150572592488518361643018883 225858888732777542464528325)
      ·
        refine ⟨42348541637395789212099061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225858888732777542464528325 42348541637395789212099061)
        ·
          refine ⟨3970175778505855238634287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42348541637395789212099061 3970175778505855238634287)
          ·
            refine ⟨5955263667758782857951431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3970175778505855238634287 5955263667758782857951431)
            ·
              refine ⟨8932895501638174286927147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5955263667758782857951431 8932895501638174286927147)
              ·
                refine ⟨13399343252457261430390721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8932895501638174286927147 13399343252457261430390721)
                ·
                  refine ⟨10049507439342946072793041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13399343252457261430390721 10049507439342946072793041)
                  ·
                    refine ⟨7537130579507209554594781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10049507439342946072793041 7537130579507209554594781)
                    ·
                      refine ⟨2826423967315203582973043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7537130579507209554594781 2826423967315203582973043)
                      ·
                        rfl

theorem cell23_5504441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_5504441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504441 prefixEnd_5504441 := by exact prefixLift 5504441
  have htrace : WordTrace (prefixWord ++ tailWord_5504441) baseStart_5504441 baseEnd_5504441 := by
    simpa [prefixWord, tailWord_5504441, baseEnd_5504441] using wordTrace_append hprefix tailTrace_5504441
  have hstable : (prefixWord ++ tailWord_5504441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504441).length < 2 ^ (prefixWord ++ tailWord_5504441).sum := by decide
  have hdescent : baseEnd_5504441 < baseStart_5504441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504480 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 3]
def baseStart_5504480 : Nat := 118140960795 + 5504480 * 2 ^ 59
def prefixEnd_5504480 : Nat := 4983230072969 + 3 ^ 40 * 5504480 * 2
def baseEnd_5504480 : Nat := 2826443993060728930385363

theorem tailTrace_5504480 : CollatzResearch.WordTrace tailWord_5504480 prefixEnd_5504480 2826443993060728930385363 := by
  unfold tailWord_5504480
  simp only [CollatzResearch.WordTrace]
  refine ⟨100382439549108262592347447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133843252732144350123129929 100382439549108262592347447)
  ·
    refine ⟨150573659323662393888521171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100382439549108262592347447 150573659323662393888521171)
    ·
      refine ⟨225860488985493590832781757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150573659323662393888521171 225860488985493590832781757)
      ·
        refine ⟨84697683369560096562293159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225860488985493590832781757 84697683369560096562293159)
        ·
          refine ⟨127046525054340144843439739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84697683369560096562293159 127046525054340144843439739)
          ·
            refine ⟨190569787581510217265159609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127046525054340144843439739 190569787581510217265159609)
            ·
              refine ⟨142927340686132662948869707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190569787581510217265159609 142927340686132662948869707)
              ·
                refine ⟨214391011029198994423304561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142927340686132662948869707 214391011029198994423304561)
                ·
                  refine ⟨160793258271899245817478421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214391011029198994423304561 160793258271899245817478421)
                  ·
                    refine ⟨7537183981495277147694301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 160793258271899245817478421 7537183981495277147694301)
                    ·
                      refine ⟨2826443993060728930385363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7537183981495277147694301 2826443993060728930385363)
                      ·
                        rfl

theorem cell23_5504480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_5504480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504480 prefixEnd_5504480 := by exact prefixLift 5504480
  have htrace : WordTrace (prefixWord ++ tailWord_5504480) baseStart_5504480 baseEnd_5504480 := by
    simpa [prefixWord, tailWord_5504480, baseEnd_5504480] using wordTrace_append hprefix tailTrace_5504480
  have hstable : (prefixWord ++ tailWord_5504480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504480).length < 2 ^ (prefixWord ++ tailWord_5504480).sum := by decide
  have hdescent : baseEnd_5504480 < baseStart_5504480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504487 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 1, 6]
def baseStart_5504487 : Nat := 118140960795 + 5504487 * 2 ^ 59
def prefixEnd_5504487 : Nat := 4983230072969 + 3 ^ 40 * 5504487 * 2
def baseEnd_5504487 : Nat := 942149195808436800999277

theorem tailTrace_5504487 : CollatzResearch.WordTrace tailWord_5504487 prefixEnd_5504487 942149195808436800999277 := by
  unfold tailWord_5504487
  simp only [CollatzResearch.WordTrace]
  refine ⟨200765134409191165380199715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133843422939460776920133143 200765134409191165380199715)
  ·
    refine ⟨301147701613786748070299573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200765134409191165380199715 301147701613786748070299573)
    ·
      refine ⟨28232597026292507631590585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 301147701613786748070299573 28232597026292507631590585)
      ·
        refine ⟨21174447769719380723692939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28232597026292507631590585 21174447769719380723692939)
        ·
          refine ⟨31761671654579071085539409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21174447769719380723692939 31761671654579071085539409)
          ·
            refine ⟨23821253740934303314154557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31761671654579071085539409 23821253740934303314154557)
            ·
              refine ⟨8932970152850363742807959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23821253740934303314154557 8932970152850363742807959)
              ·
                refine ⟨13399455229275545614211939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8932970152850363742807959 13399455229275545614211939)
                ·
                  refine ⟨20099182843913318421317909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13399455229275545614211939 20099182843913318421317909)
                  ·
                    refine ⟨942149195808436800999277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20099182843913318421317909 942149195808436800999277)
                    ·
                      rfl

theorem cell23_5504487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_5504487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504487 prefixEnd_5504487 := by exact prefixLift 5504487
  have htrace : WordTrace (prefixWord ++ tailWord_5504487) baseStart_5504487 baseEnd_5504487 := by
    simpa [prefixWord, tailWord_5504487, baseEnd_5504487] using wordTrace_append hprefix tailTrace_5504487
  have hstable : (prefixWord ++ tailWord_5504487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504487).length < 2 ^ (prefixWord ++ tailWord_5504487).sum := by decide
  have hdescent : baseEnd_5504487 < baseStart_5504487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504494 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_5504494 : Nat := 118140960795 + 5504494 * 2 ^ 59
def prefixEnd_5504494 : Nat := 4983230072969 + 3 ^ 40 * 5504494 * 2
def baseEnd_5504494 : Nat := 2826451181789891875610299

theorem tailTrace_5504494 : CollatzResearch.WordTrace tailWord_5504494 prefixEnd_5504494 2826451181789891875610299 := by
  unfold tailWord_5504494
  simp only [CollatzResearch.WordTrace]
  refine ⟨25095673715020725696963067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133843593146777203717136357 25095673715020725696963067)
  ·
    refine ⟨37643510572531088545444601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25095673715020725696963067 37643510572531088545444601)
    ·
      refine ⟨28232632929398316409083451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37643510572531088545444601 28232632929398316409083451)
      ·
        refine ⟨42348949394097474613625177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28232632929398316409083451 42348949394097474613625177)
        ·
          refine ⟨31761712045573105960218883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42348949394097474613625177 31761712045573105960218883)
          ·
            refine ⟨47642568068359658940328325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31761712045573105960218883 47642568068359658940328325)
            ·
              refine ⟨8932981512817436051311561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47642568068359658940328325 8932981512817436051311561)
              ·
                refine ⟨6699736134613077038483671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8932981512817436051311561 6699736134613077038483671)
                ·
                  refine ⟨10049604201919615557725507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6699736134613077038483671 10049604201919615557725507)
                  ·
                    refine ⟨15074406302879423336588261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10049604201919615557725507 15074406302879423336588261)
                    ·
                      refine ⟨2826451181789891875610299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15074406302879423336588261 2826451181789891875610299)
                      ·
                        rfl

theorem cell23_5504494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_5504494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504494 prefixEnd_5504494 := by exact prefixLift 5504494
  have htrace : WordTrace (prefixWord ++ tailWord_5504494) baseStart_5504494 baseEnd_5504494 := by
    simpa [prefixWord, tailWord_5504494, baseEnd_5504494] using wordTrace_append hprefix tailTrace_5504494
  have hstable : (prefixWord ++ tailWord_5504494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504494).length < 2 ^ (prefixWord ++ tailWord_5504494).sum := by decide
  have hdescent : baseEnd_5504494 < baseStart_5504494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504511 : List Nat := [1, 1, 2, 2, 1, 2, 2, 7, 1, 2, 2]
def baseStart_5504511 : Nat := 118140960795 + 5504511 * 2 ^ 59
def prefixEnd_5504511 : Nat := 4983230072969 + 3 ^ 40 * 5504511 * 2
def baseEnd_5504511 : Nat := 2826459910961018309097721

theorem tailTrace_5504511 : CollatzResearch.WordTrace tailWord_5504511 prefixEnd_5504511 2826459910961018309097721 := by
  unfold tailWord_5504511
  simp only [CollatzResearch.WordTrace]
  refine ⟨200766009761104217479073387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133844006507402811652715591 200766009761104217479073387)
  ·
    refine ⟨301149014641656326218610081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200766009761104217479073387 301149014641656326218610081)
    ·
      refine ⟨225861760981242244663957561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301149014641656326218610081 225861760981242244663957561)
      ·
        refine ⟨169396320735931683497968171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225861760981242244663957561 169396320735931683497968171)
        ·
          refine ⟨254094481103897525246952257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169396320735931683497968171 254094481103897525246952257)
          ·
            refine ⟨190570860827923143935214193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254094481103897525246952257 190570860827923143935214193)
            ·
              refine ⟨142928145620942357951410645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190570860827923143935214193 142928145620942357951410645)
              ·
                refine ⟨3349878412990836514486187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 142928145620942357951410645 3349878412990836514486187)
                ·
                  refine ⟨5024817619486254771729281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3349878412990836514486187 5024817619486254771729281)
                  ·
                    refine ⟨3768613214614691078796961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5024817619486254771729281 3768613214614691078796961)
                    ·
                      refine ⟨2826459910961018309097721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3768613214614691078796961 2826459910961018309097721)
                      ·
                        rfl

theorem cell23_5504511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 1, 2, 2].length) (baseStart_5504511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504511 prefixEnd_5504511 := by exact prefixLift 5504511
  have htrace : WordTrace (prefixWord ++ tailWord_5504511) baseStart_5504511 baseEnd_5504511 := by
    simpa [prefixWord, tailWord_5504511, baseEnd_5504511] using wordTrace_append hprefix tailTrace_5504511
  have hstable : (prefixWord ++ tailWord_5504511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504511).length < 2 ^ (prefixWord ++ tailWord_5504511).sum := by decide
  have hdescent : baseEnd_5504511 < baseStart_5504511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504514 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5504514 : Nat := 118140960795 + 5504514 * 2 ^ 59
def prefixEnd_5504514 : Nat := 4983230072969 + 3 ^ 40 * 5504514 * 2
def baseEnd_5504514 : Nat := 2826461451402981797360207

theorem tailTrace_5504514 : CollatzResearch.WordTrace tailWord_5504514 prefixEnd_5504514 2826461451402981797360207 := by
  unfold tailWord_5504514
  simp only [CollatzResearch.WordTrace]
  refine ⟨50191529795023337247858149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133844079453395565994288397 50191529795023337247858149)
  ·
    refine ⟨9410911836566875733973403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50191529795023337247858149 9410911836566875733973403)
    ·
      refine ⟨14116367754850313600960105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9410911836566875733973403 14116367754850313600960105)
      ·
        refine ⟨10587275816137735200720079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14116367754850313600960105 10587275816137735200720079)
        ·
          refine ⟨15880913724206602801080119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10587275816137735200720079 15880913724206602801080119)
          ·
            refine ⟨23821370586309904201620179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15880913724206602801080119 23821370586309904201620179)
            ·
              refine ⟨35732055879464856302430269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23821370586309904201620179 35732055879464856302430269)
              ·
                refine ⟨13399520954799321113411351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35732055879464856302430269 13399520954799321113411351)
                ·
                  refine ⟨20099281432198981670117027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13399520954799321113411351 20099281432198981670117027)
                  ·
                    refine ⟨30148922148298472505175541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20099281432198981670117027 30148922148298472505175541)
                    ·
                      refine ⟨2826461451402981797360207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30148922148298472505175541 2826461451402981797360207)
                      ·
                        rfl

theorem cell23_5504514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5504514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504514 prefixEnd_5504514 := by exact prefixLift 5504514
  have htrace : WordTrace (prefixWord ++ tailWord_5504514) baseStart_5504514 baseEnd_5504514 := by
    simpa [prefixWord, tailWord_5504514, baseEnd_5504514] using wordTrace_append hprefix tailTrace_5504514
  have hstable : (prefixWord ++ tailWord_5504514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504514).length < 2 ^ (prefixWord ++ tailWord_5504514).sum := by decide
  have hdescent : baseEnd_5504514 < baseStart_5504514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5504527 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 8, 1, 3]
def baseStart_5504527 : Nat := 118140960795 + 5504527 * 2 ^ 59
def prefixEnd_5504527 : Nat := 4983230072969 + 3 ^ 40 * 5504527 * 2
def baseEnd_5504527 : Nat := 2826468126651490246497647

theorem tailTrace_5504527 : CollatzResearch.WordTrace tailWord_5504527 prefixEnd_5504527 2826468126651490246497647 := by
  unfold tailWord_5504527
  simp only [CollatzResearch.WordTrace]
  refine ⟨200766593329046252211655835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133844395552697501474437223 200766593329046252211655835)
  ·
    refine ⟨301149889993569378317483753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200766593329046252211655835 301149889993569378317483753)
    ·
      refine ⟨225862417495177033738112815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301149889993569378317483753 225862417495177033738112815)
      ·
        refine ⟨338793626242765550607169223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225862417495177033738112815 338793626242765550607169223)
        ·
          refine ⟨508190439364148325910753835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338793626242765550607169223 508190439364148325910753835)
          ·
            refine ⟨762285659046222488866130753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508190439364148325910753835 762285659046222488866130753)
            ·
              refine ⟨571714244284666866649598065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762285659046222488866130753 571714244284666866649598065)
              ·
                refine ⟨428785683213500149987198549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 571714244284666866649598065 428785683213500149987198549)
                ·
                  refine ⟨5024832225158204882662483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 428785683213500149987198549 5024832225158204882662483)
                  ·
                    refine ⟨7537248337737307323993725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5024832225158204882662483 7537248337737307323993725)
                    ·
                      refine ⟨2826468126651490246497647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7537248337737307323993725 2826468126651490246497647)
                      ·
                        rfl

theorem cell23_5504527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 1, 3].length) (baseStart_5504527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5504527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5504527 prefixEnd_5504527 := by exact prefixLift 5504527
  have htrace : WordTrace (prefixWord ++ tailWord_5504527) baseStart_5504527 baseEnd_5504527 := by
    simpa [prefixWord, tailWord_5504527, baseEnd_5504527] using wordTrace_append hprefix tailTrace_5504527
  have hstable : (prefixWord ++ tailWord_5504527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5504527).length < 2 ^ (prefixWord ++ tailWord_5504527).sum := by decide
  have hdescent : baseEnd_5504527 < baseStart_5504527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5504527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
