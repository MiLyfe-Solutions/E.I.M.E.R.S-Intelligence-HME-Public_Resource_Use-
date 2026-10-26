import V185TrunkScan21Chunk119

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1459527 : List Nat := [1, 1, 4, 1, 2, 4, 1, 7]
def baseStart_1459527 : Nat := 118140960795 + 1459527 * 2 ^ 59
def prefixEnd_1459527 : Nat := 4983230072969 + 3 ^ 40 * 1459527 * 2
def baseEnd_1459527 : Nat := 111027982105898715200039

theorem tailTrace_1459527 : CollatzResearch.WordTrace tailWord_1459527 prefixEnd_1459527 111027982105898715200039 := by
  unfold tailWord_1459527
  simp only [CollatzResearch.WordTrace]
  refine ⟨53233322983390421211520835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35488881988926947474347223 53233322983390421211520835)
  ·
    refine ⟨79849984475085631817281253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53233322983390421211520835 79849984475085631817281253)
    ·
      refine ⟨14971872089078555965740235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79849984475085631817281253 14971872089078555965740235)
      ·
        refine ⟨22457808133617833948610353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14971872089078555965740235 22457808133617833948610353)
        ·
          refine ⟨16843356100213375461457765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22457808133617833948610353 16843356100213375461457765)
          ·
            refine ⟨3158129268790007899023331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16843356100213375461457765 3158129268790007899023331)
            ·
              refine ⟨4737193903185011848534997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158129268790007899023331 4737193903185011848534997)
              ·
                refine ⟨111027982105898715200039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4737193903185011848534997 111027982105898715200039)
                ·
                  rfl

theorem cell21_1459527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 7].length) (baseStart_1459527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459527 prefixEnd_1459527 := by exact prefixLift 1459527
  have htrace : WordTrace (prefixWord ++ tailWord_1459527) baseStart_1459527 baseEnd_1459527 := by
    simpa [prefixWord, tailWord_1459527, baseEnd_1459527] using wordTrace_append hprefix tailTrace_1459527
  have hstable : (prefixWord ++ tailWord_1459527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459527).length < 2 ^ (prefixWord ++ tailWord_1459527).sum := by decide
  have hdescent : baseEnd_1459527 < baseStart_1459527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459696 : List Nat := [2, 1, 1, 1, 3, 6, 2, 5]
def baseStart_1459696 : Nat := 118140960795 + 1459696 * 2 ^ 59
def prefixEnd_1459696 : Nat := 4983230072969 + 3 ^ 40 * 1459696 * 2
def baseEnd_1459696 : Nat := 111040838140063135761035

theorem tailTrace_1459696 : CollatzResearch.WordTrace tailWord_1459696 prefixEnd_1459696 111040838140063135761035 := by
  unfold tailWord_1459696
  simp only [CollatzResearch.WordTrace]
  refine ⟨26619743459889081537211471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35492991279852108716281961 26619743459889081537211471)
  ·
    refine ⟨39929615189833622305817207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26619743459889081537211471 39929615189833622305817207)
    ·
      refine ⟨59894422784750433458725811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39929615189833622305817207 59894422784750433458725811)
      ·
        refine ⟨89841634177125650188088717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59894422784750433458725811 89841634177125650188088717)
        ·
          refine ⟨33690612816422118820533269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89841634177125650188088717 33690612816422118820533269)
          ·
            refine ⟨1579247475769786819712497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33690612816422118820533269 1579247475769786819712497)
            ·
              refine ⟨1184435606827340114784373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1579247475769786819712497 1184435606827340114784373)
              ·
                refine ⟨111040838140063135761035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1184435606827340114784373 111040838140063135761035)
                ·
                  rfl

theorem cell21_1459696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_1459696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459696 prefixEnd_1459696 := by exact prefixLift 1459696
  have htrace : WordTrace (prefixWord ++ tailWord_1459696) baseStart_1459696 baseEnd_1459696 := by
    simpa [prefixWord, tailWord_1459696, baseEnd_1459696] using wordTrace_append hprefix tailTrace_1459696
  have hstable : (prefixWord ++ tailWord_1459696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459696).length < 2 ^ (prefixWord ++ tailWord_1459696).sum := by decide
  have hdescent : baseEnd_1459696 < baseStart_1459696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459741 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 4]
def baseStart_1459741 : Nat := 118140960795 + 1459741 * 2 ^ 59
def prefixEnd_1459741 : Nat := 4983230072969 + 3 ^ 40 * 1459741 * 2
def baseEnd_1459741 : Nat := 333132784033279329033013

theorem tailTrace_1459741 : CollatzResearch.WordTrace tailWord_1459741 prefixEnd_1459741 333132784033279329033013 := by
  unfold tailWord_1459741
  simp only [CollatzResearch.WordTrace]
  refine ⟨53241128204615135759811077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35494085469743423839874051 53241128204615135759811077)
  ·
    refine ⟨9982711538365337954964577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53241128204615135759811077 9982711538365337954964577)
    ·
      refine ⟨7487033653774003466223433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9982711538365337954964577 7487033653774003466223433)
      ·
        refine ⟨5615275240330502599667575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7487033653774003466223433 5615275240330502599667575)
        ·
          refine ⟨8422912860495753899501363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615275240330502599667575 8422912860495753899501363)
          ·
            refine ⟨12634369290743630849252045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8422912860495753899501363 12634369290743630849252045)
            ·
              refine ⟨4737888484028861568469517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12634369290743630849252045 4737888484028861568469517)
              ·
                refine ⟨1776708181510823088176069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4737888484028861568469517 1776708181510823088176069)
                ·
                  refine ⟨333132784033279329033013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1776708181510823088176069 333132784033279329033013)
                  ·
                    rfl

theorem cell21_1459741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_1459741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459741 prefixEnd_1459741 := by exact prefixLift 1459741
  have htrace : WordTrace (prefixWord ++ tailWord_1459741) baseStart_1459741 baseEnd_1459741 := by
    simpa [prefixWord, tailWord_1459741, baseEnd_1459741] using wordTrace_append hprefix tailTrace_1459741
  have hstable : (prefixWord ++ tailWord_1459741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459741).length < 2 ^ (prefixWord ++ tailWord_1459741).sum := by decide
  have hdescent : baseEnd_1459741 < baseStart_1459741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459789 : List Nat := [1, 6, 1, 1, 3, 2, 1, 6]
def baseStart_1459789 : Nat := 118140960795 + 1459789 * 2 ^ 59
def prefixEnd_1459789 : Nat := 4983230072969 + 3 ^ 40 * 1459789 * 2
def baseEnd_1459789 : Nat := 111047912762413970744305

theorem tailTrace_1459789 : CollatzResearch.WordTrace tailWord_1459789 prefixEnd_1459789 111047912762413970744305 := by
  unfold tailWord_1459789
  simp only [CollatzResearch.WordTrace]
  refine ⟨53242878908441239957558421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35495252605627493305038947 53242878908441239957558421)
  ·
    refine ⟨2495759948833183123010551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53242878908441239957558421 2495759948833183123010551)
    ·
      refine ⟨3743639923249774684515827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2495759948833183123010551 3743639923249774684515827)
      ·
        refine ⟨5615459884874662026773741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3743639923249774684515827 5615459884874662026773741)
        ·
          refine ⟨2105797456827998260040153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5615459884874662026773741 2105797456827998260040153)
          ·
            refine ⟨1579348092620998695030115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2105797456827998260040153 1579348092620998695030115)
            ·
              refine ⟨2369022138931498042545173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579348092620998695030115 2369022138931498042545173)
              ·
                refine ⟨111047912762413970744305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2369022138931498042545173 111047912762413970744305)
                ·
                  rfl

theorem cell21_1459789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 6].length) (baseStart_1459789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459789 prefixEnd_1459789 := by exact prefixLift 1459789
  have htrace : WordTrace (prefixWord ++ tailWord_1459789) baseStart_1459789 baseEnd_1459789 := by
    simpa [prefixWord, tailWord_1459789, baseEnd_1459789] using wordTrace_append hprefix tailTrace_1459789
  have hstable : (prefixWord ++ tailWord_1459789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459789).length < 2 ^ (prefixWord ++ tailWord_1459789).sum := by decide
  have hdescent : baseEnd_1459789 < baseStart_1459789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459859 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 10]
def baseStart_1459859 : Nat := 118140960795 + 1459859 * 2 ^ 59
def prefixEnd_1459859 : Nat := 4983230072969 + 3 ^ 40 * 1459859 * 2
def baseEnd_1459859 : Nat := 333159713240937346066105

theorem tailTrace_1459859 : CollatzResearch.WordTrace tailWord_1459859 prefixEnd_1459859 333159713240937346066105 := by
  unfold tailWord_1459859
  simp only [CollatzResearch.WordTrace]
  refine ⟨53245432018187641912606631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35496954678791761275071087 53245432018187641912606631)
  ·
    refine ⟨79868148027281462868909947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53245432018187641912606631 79868148027281462868909947)
    ·
      refine ⟨119802222040922194303364921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79868148027281462868909947 119802222040922194303364921)
      ·
        refine ⟨89851666530691645727523691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119802222040922194303364921 89851666530691645727523691)
        ·
          refine ⟨134777499796037468591285537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89851666530691645727523691 134777499796037468591285537)
          ·
            refine ⟨101083124847028101443464153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134777499796037468591285537 101083124847028101443464153)
            ·
              refine ⟨75812343635271076082598115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101083124847028101443464153 75812343635271076082598115)
              ·
                refine ⟨113718515452906614123897173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75812343635271076082598115 113718515452906614123897173)
                ·
                  refine ⟨333159713240937346066105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 113718515452906614123897173 333159713240937346066105)
                  ·
                    rfl

theorem cell21_1459859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_1459859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459859 prefixEnd_1459859 := by exact prefixLift 1459859
  have htrace : WordTrace (prefixWord ++ tailWord_1459859) baseStart_1459859 baseEnd_1459859 := by
    simpa [prefixWord, tailWord_1459859, baseEnd_1459859] using wordTrace_append hprefix tailTrace_1459859
  have hstable : (prefixWord ++ tailWord_1459859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459859).length < 2 ^ (prefixWord ++ tailWord_1459859).sum := by decide
  have hdescent : baseEnd_1459859 < baseStart_1459859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459876 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_1459876 : Nat := 118140960795 + 1459876 * 2 ^ 59
def prefixEnd_1459876 : Nat := 4983230072969 + 3 ^ 40 * 1459876 * 2
def baseEnd_1459876 : Nat := 333163592872549094282737

theorem tailTrace_1459876 : CollatzResearch.WordTrace tailWord_1459876 prefixEnd_1459876 333163592872549094282737 := by
  unfold tailWord_1459876
  simp only [CollatzResearch.WordTrace]
  refine ⟨26623026029563026907987741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35497368039417369210650321 26623026029563026907987741)
  ·
    refine ⟨9983634761086135090495403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26623026029563026907987741 9983634761086135090495403)
    ·
      refine ⟨14975452141629202635743105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9983634761086135090495403 14975452141629202635743105)
      ·
        refine ⟨11231589106221901976807329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14975452141629202635743105 11231589106221901976807329)
        ·
          refine ⟨8423691829666426482605497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11231589106221901976807329 8423691829666426482605497)
          ·
            refine ⟨6317768872249819861954123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8423691829666426482605497 6317768872249819861954123)
            ·
              refine ⟨9476653308374729792931185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6317768872249819861954123 9476653308374729792931185)
              ·
                refine ⟨7107489981281047344698389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9476653308374729792931185 7107489981281047344698389)
                ·
                  refine ⟨333163592872549094282737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7107489981281047344698389 333163592872549094282737)
                  ·
                    rfl

theorem cell21_1459876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_1459876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459876 prefixEnd_1459876 := by exact prefixLift 1459876
  have htrace : WordTrace (prefixWord ++ tailWord_1459876) baseStart_1459876 baseEnd_1459876 := by
    simpa [prefixWord, tailWord_1459876, baseEnd_1459876] using wordTrace_append hprefix tailTrace_1459876
  have hstable : (prefixWord ++ tailWord_1459876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459876).length < 2 ^ (prefixWord ++ tailWord_1459876).sum := by decide
  have hdescent : baseEnd_1459876 < baseStart_1459876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459890 : List Nat := [3, 2, 1, 1, 1, 2, 11]
def baseStart_1459890 : Nat := 118140960795 + 1459890 * 2 ^ 59
def prefixEnd_1459890 : Nat := 4983230072969 + 3 ^ 40 * 1459890 * 2
def baseEnd_1459890 : Nat := 37018531984809797894375

theorem tailTrace_1459890 : CollatzResearch.WordTrace tailWord_1459890 prefixEnd_1459890 37018531984809797894375 := by
  unfold tailWord_1459890
  simp only [CollatzResearch.WordTrace]
  refine ⟨13311640670268833551746281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35497708454050222804656749 13311640670268833551746281)
  ·
    refine ⟨9983730502701625163809711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13311640670268833551746281 9983730502701625163809711)
    ·
      refine ⟨14975595754052437745714567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9983730502701625163809711 14975595754052437745714567)
      ·
        refine ⟨22463393631078656618571851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14975595754052437745714567 22463393631078656618571851)
        ·
          refine ⟨33695090446617984927857777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22463393631078656618571851 33695090446617984927857777)
          ·
            refine ⟨25271317834963488695893333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33695090446617984927857777 25271317834963488695893333)
            ·
              refine ⟨37018531984809797894375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25271317834963488695893333 37018531984809797894375)
              ·
                rfl

theorem cell21_1459890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 11].length) (baseStart_1459890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459890 prefixEnd_1459890 := by exact prefixLift 1459890
  have htrace : WordTrace (prefixWord ++ tailWord_1459890) baseStart_1459890 baseEnd_1459890 := by
    simpa [prefixWord, tailWord_1459890, baseEnd_1459890] using wordTrace_append hprefix tailTrace_1459890
  have hstable : (prefixWord ++ tailWord_1459890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459890).length < 2 ^ (prefixWord ++ tailWord_1459890).sum := by decide
  have hdescent : baseEnd_1459890 < baseStart_1459890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459955 : List Nat := [1, 1, 1, 2, 2, 3, 6, 2, 3]
def baseStart_1459955 : Nat := 118140960795 + 1459955 * 2 ^ 59
def prefixEnd_1459955 : Nat := 4983230072969 + 3 ^ 40 * 1459955 * 2
def baseEnd_1459955 : Nat := 333181621748862512465909

theorem tailTrace_1459955 : CollatzResearch.WordTrace tailWord_1459955 prefixEnd_1459955 333181621748862512465909 := by
  unfold tailWord_1459955
  simp only [CollatzResearch.WordTrace]
  refine ⟨53248933425839850308101319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35499288950559900205400879 53248933425839850308101319)
  ·
    refine ⟨79873400138759775462151979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53248933425839850308101319 79873400138759775462151979)
    ·
      refine ⟨119810100208139663193227969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79873400138759775462151979 119810100208139663193227969)
      ·
        refine ⟨89857575156104747394920977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119810100208139663193227969 89857575156104747394920977)
        ·
          refine ⟨67393181367078560546190733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89857575156104747394920977 67393181367078560546190733)
          ·
            refine ⟨25272443012654460204821525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67393181367078560546190733 25272443012654460204821525)
            ·
              refine ⟨1184645766218177822101009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25272443012654460204821525 1184645766218177822101009)
              ·
                refine ⟨888484324663633366575757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1184645766218177822101009 888484324663633366575757)
                ·
                  refine ⟨333181621748862512465909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888484324663633366575757 333181621748862512465909)
                  ·
                    rfl

theorem cell21_1459955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 3].length) (baseStart_1459955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459955 prefixEnd_1459955 := by exact prefixLift 1459955
  have htrace : WordTrace (prefixWord ++ tailWord_1459955) baseStart_1459955 baseEnd_1459955 := by
    simpa [prefixWord, tailWord_1459955, baseEnd_1459955] using wordTrace_append hprefix tailTrace_1459955
  have hstable : (prefixWord ++ tailWord_1459955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459955).length < 2 ^ (prefixWord ++ tailWord_1459955).sum := by decide
  have hdescent : baseEnd_1459955 < baseStart_1459955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460028 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 4]
def baseStart_1460028 : Nat := 118140960795 + 1460028 * 2 ^ 59
def prefixEnd_1460028 : Nat := 4983230072969 + 3 ^ 40 * 1460028 * 2
def baseEnd_1460028 : Nat := 333198281343430607749093

theorem tailTrace_1460028 : CollatzResearch.WordTrace tailWord_1460028 prefixEnd_1460028 333198281343430607749093 := by
  unfold tailWord_1460028
  simp only [CollatzResearch.WordTrace]
  refine ⟨26625797977287691887754369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35501063969716922517005825 26625797977287691887754369)
  ·
    refine ⟨19969348482965768915815777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26625797977287691887754369 19969348482965768915815777)
    ·
      refine ⟨14977011362224326686861833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19969348482965768915815777 14977011362224326686861833)
      ·
        refine ⟨11232758521668245015146375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14977011362224326686861833 11232758521668245015146375)
        ·
          refine ⟨16849137782502367522719563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11232758521668245015146375 16849137782502367522719563)
          ·
            refine ⟨25273706673753551284079345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16849137782502367522719563 25273706673753551284079345)
            ·
              refine ⟨18955280005315163463059509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25273706673753551284079345 18955280005315163463059509)
              ·
                refine ⟨1777057500498296574661829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18955280005315163463059509 1777057500498296574661829)
                ·
                  refine ⟨333198281343430607749093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1777057500498296574661829 333198281343430607749093)
                  ·
                    rfl

theorem cell21_1460028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_1460028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460028 prefixEnd_1460028 := by exact prefixLift 1460028
  have htrace : WordTrace (prefixWord ++ tailWord_1460028) baseStart_1460028 baseEnd_1460028 := by
    simpa [prefixWord, tailWord_1460028, baseEnd_1460028] using wordTrace_append hprefix tailTrace_1460028
  have hstable : (prefixWord ++ tailWord_1460028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460028).length < 2 ^ (prefixWord ++ tailWord_1460028).sum := by decide
  have hdescent : baseEnd_1460028 < baseStart_1460028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460042 : List Nat := [3, 1, 2, 1, 1, 1, 5, 7]
def baseStart_1460042 : Nat := 118140960795 + 1460042 * 2 ^ 59
def prefixEnd_1460042 : Nat := 4983230072969 + 3 ^ 40 * 1460042 * 2
def baseEnd_1460042 : Nat := 111067158778056564838577

theorem tailTrace_1460042 : CollatzResearch.WordTrace tailWord_1460042 prefixEnd_1460042 111067158778056564838577 := by
  unfold tailWord_1460042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13313026644131166041629595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35501404384349776111012253 13313026644131166041629595)
  ·
    refine ⟨19969539966196749062444393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13313026644131166041629595 19969539966196749062444393)
    ·
      refine ⟨14977154974647561796833295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19969539966196749062444393 14977154974647561796833295)
      ·
        refine ⟨22465732461971342695249943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14977154974647561796833295 22465732461971342695249943)
        ·
          refine ⟨33698598692957014042874915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22465732461971342695249943 33698598692957014042874915)
          ·
            refine ⟨50547898039435521064312373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33698598692957014042874915 50547898039435521064312373)
            ·
              refine ⟨4738865441197080099779285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50547898039435521064312373 4738865441197080099779285)
              ·
                refine ⟨111067158778056564838577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4738865441197080099779285 111067158778056564838577)
                ·
                  rfl

theorem cell21_1460042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_1460042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460042 prefixEnd_1460042 := by exact prefixLift 1460042
  have htrace : WordTrace (prefixWord ++ tailWord_1460042) baseStart_1460042 baseEnd_1460042 := by
    simpa [prefixWord, tailWord_1460042, baseEnd_1460042] using wordTrace_append hprefix tailTrace_1460042
  have hstable : (prefixWord ++ tailWord_1460042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460042).length < 2 ^ (prefixWord ++ tailWord_1460042).sum := by decide
  have hdescent : baseEnd_1460042 < baseStart_1460042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460045 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1460045 : Nat := 118140960795 + 1460045 * 2 ^ 59
def prefixEnd_1460045 : Nat := 4983230072969 + 3 ^ 40 * 1460045 * 2
def baseEnd_1460045 : Nat := 333202160975042355965725

theorem tailTrace_1460045 : CollatzResearch.WordTrace tailWord_1460045 prefixEnd_1460045 333202160975042355965725 := by
  unfold tailWord_1460045
  simp only [CollatzResearch.WordTrace]
  refine ⟨53252215995513795678877589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35501477330342530452585059 53252215995513795678877589)
  ·
    refine ⟨2496197624789709172447387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53252215995513795678877589 2496197624789709172447387)
    ·
      refine ⟨3744296437184563758671081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2496197624789709172447387 3744296437184563758671081)
      ·
        refine ⟨2808222327888422819003311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3744296437184563758671081 2808222327888422819003311)
        ·
          refine ⟨4212333491832634228504967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2808222327888422819003311 4212333491832634228504967)
          ·
            refine ⟨6318500237748951342757451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4212333491832634228504967 6318500237748951342757451)
            ·
              refine ⟨9477750356623427014136177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6318500237748951342757451 9477750356623427014136177)
              ·
                refine ⟨7108312767467570260602133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9477750356623427014136177 7108312767467570260602133)
                ·
                  refine ⟨333202160975042355965725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7108312767467570260602133 333202160975042355965725)
                  ·
                    rfl

theorem cell21_1460045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1460045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460045 prefixEnd_1460045 := by exact prefixLift 1460045
  have htrace : WordTrace (prefixWord ++ tailWord_1460045) baseStart_1460045 baseEnd_1460045 := by
    simpa [prefixWord, tailWord_1460045, baseEnd_1460045] using wordTrace_append hprefix tailTrace_1460045
  have hstable : (prefixWord ++ tailWord_1460045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460045).length < 2 ^ (prefixWord ++ tailWord_1460045).sum := by decide
  have hdescent : baseEnd_1460045 < baseStart_1460045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460124 : List Nat := [2, 2, 3, 3, 1, 1, 4, 2, 3]
def baseStart_1460124 : Nat := 118140960795 + 1460124 * 2 ^ 59
def prefixEnd_1460124 : Nat := 4983230072969 + 3 ^ 40 * 1460124 * 2
def baseEnd_1460124 : Nat := 333220189851355774148897

theorem tailTrace_1460124 : CollatzResearch.WordTrace tailWord_1460124 prefixEnd_1460124 333220189851355774148897 := by
  unfold tailWord_1460124
  simp only [CollatzResearch.WordTrace]
  refine ⟨26627548681113796085501713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35503398241485061447335617 26627548681113796085501713)
  ·
    refine ⟨19970661510835347064126285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26627548681113796085501713 19970661510835347064126285)
    ·
      refine ⟨7488998066563255149047357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19970661510835347064126285 7488998066563255149047357)
      ·
        refine ⟨2808374274961220680892759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7488998066563255149047357 2808374274961220680892759)
        ·
          refine ⟨4212561412441831021339139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2808374274961220680892759 4212561412441831021339139)
          ·
            refine ⟨6318842118662746532008709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4212561412441831021339139 6318842118662746532008709)
            ·
              refine ⟨1184782897249264974751633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6318842118662746532008709 1184782897249264974751633)
              ·
                refine ⟨888587172936948731063725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1184782897249264974751633 888587172936948731063725)
                ·
                  refine ⟨333220189851355774148897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888587172936948731063725 333220189851355774148897)
                  ·
                    rfl

theorem cell21_1460124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_1460124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460124 prefixEnd_1460124 := by exact prefixLift 1460124
  have htrace : WordTrace (prefixWord ++ tailWord_1460124) baseStart_1460124 baseEnd_1460124 := by
    simpa [prefixWord, tailWord_1460124, baseEnd_1460124] using wordTrace_append hprefix tailTrace_1460124
  have hstable : (prefixWord ++ tailWord_1460124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460124).length < 2 ^ (prefixWord ++ tailWord_1460124).sum := by decide
  have hdescent : baseEnd_1460124 < baseStart_1460124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460135 : List Nat := [1, 1, 6, 1, 2, 1, 3, 6]
def baseStart_1460135 : Nat := 118140960795 + 1460135 * 2 ^ 59
def prefixEnd_1460135 : Nat := 4983230072969 + 3 ^ 40 * 1460135 * 2
def baseEnd_1460135 : Nat := 111074233400407399821847

theorem tailTrace_1460135 : CollatzResearch.WordTrace tailWord_1460135 prefixEnd_1460135 111074233400407399821847 := by
  unfold tailWord_1460135
  simp only [CollatzResearch.WordTrace]
  refine ⟨53255498565187741049653859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35503665710125160699769239 53255498565187741049653859)
  ·
    refine ⟨79883247847781611574480789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53255498565187741049653859 79883247847781611574480789)
    ·
      refine ⟨3744527242864763042553787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79883247847781611574480789 3744527242864763042553787)
      ·
        refine ⟨5616790864297144563830681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3744527242864763042553787 5616790864297144563830681)
        ·
          refine ⟨4212593148222858422873011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5616790864297144563830681 4212593148222858422873011)
          ·
            refine ⟨6318889722334287634309517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4212593148222858422873011 6318889722334287634309517)
            ·
              refine ⟨2369583645875357862866069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6318889722334287634309517 2369583645875357862866069)
              ·
                refine ⟨111074233400407399821847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2369583645875357862866069 111074233400407399821847)
                ·
                  rfl

theorem cell21_1460135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 6].length) (baseStart_1460135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460135 prefixEnd_1460135 := by exact prefixLift 1460135
  have htrace : WordTrace (prefixWord ++ tailWord_1460135) baseStart_1460135 baseEnd_1460135 := by
    simpa [prefixWord, tailWord_1460135, baseEnd_1460135] using wordTrace_append hprefix tailTrace_1460135
  have hstable : (prefixWord ++ tailWord_1460135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460135).length < 2 ^ (prefixWord ++ tailWord_1460135).sum := by decide
  have hdescent : baseEnd_1460135 < baseStart_1460135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460149 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 7]
def baseStart_1460149 : Nat := 118140960795 + 1460149 * 2 ^ 59
def prefixEnd_1460149 : Nat := 4983230072969 + 3 ^ 40 * 1460149 * 2
def baseEnd_1460149 : Nat := 333225895191961286232179

theorem tailTrace_1460149 : CollatzResearch.WordTrace tailWord_1460149 prefixEnd_1460149 333225895191961286232179 := by
  unfold tailWord_1460149
  simp only [CollatzResearch.WordTrace]
  refine ⟨53256009187137021440663501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35504006124758014293775667 53256009187137021440663501)
  ·
    refine ⟨19971003445176383040248813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53256009187137021440663501 19971003445176383040248813)
    ·
      refine ⟨7489126291941143640093305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19971003445176383040248813 7489126291941143640093305)
      ·
        refine ⟨5616844718955857730069979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7489126291941143640093305 5616844718955857730069979)
        ·
          refine ⟨8425267078433786595104969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5616844718955857730069979 8425267078433786595104969)
          ·
            refine ⟨6318950308825339946328727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8425267078433786595104969 6318950308825339946328727)
            ·
              refine ⟨9478425463238009919493091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6318950308825339946328727 9478425463238009919493091)
              ·
                refine ⟨14217638194857014879239637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9478425463238009919493091 14217638194857014879239637)
                ·
                  refine ⟨333225895191961286232179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14217638194857014879239637 333225895191961286232179)
                  ·
                    rfl

theorem cell21_1460149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_1460149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460149 prefixEnd_1460149 := by exact prefixLift 1460149
  have htrace : WordTrace (prefixWord ++ tailWord_1460149) baseStart_1460149 baseEnd_1460149 := by
    simpa [prefixWord, tailWord_1460149, baseEnd_1460149] using wordTrace_append hprefix tailTrace_1460149
  have hstable : (prefixWord ++ tailWord_1460149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460149).length < 2 ^ (prefixWord ++ tailWord_1460149).sum := by decide
  have hdescent : baseEnd_1460149 < baseStart_1460149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460180 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1460180 : Nat := 118140960795 + 1460180 * 2 ^ 59
def prefixEnd_1460180 : Nat := 4983230072969 + 3 ^ 40 * 1460180 * 2
def baseEnd_1460180 : Nat := 333232969814312121215449

theorem tailTrace_1460180 : CollatzResearch.WordTrace tailWord_1460180 prefixEnd_1460180 333232969814312121215449 := by
  unfold tailWord_1460180
  simp only [CollatzResearch.WordTrace]
  refine ⟨26628569925012356867520997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35504759900016475823361329 26628569925012356867520997)
  ·
    refine ⟨4992856860939816912660187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26628569925012356867520997 4992856860939816912660187)
    ·
      refine ⟨7489285291409725368990281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4992856860939816912660187 7489285291409725368990281)
      ·
        refine ⟨5616963968557294026742711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7489285291409725368990281 5616963968557294026742711)
        ·
          refine ⟨8425445952835941040114067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5616963968557294026742711 8425445952835941040114067)
          ·
            refine ⟨12638168929253911560171101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8425445952835941040114067 12638168929253911560171101)
            ·
              refine ⟨4739313348470216835064163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12638168929253911560171101 4739313348470216835064163)
              ·
                refine ⟨7108970022705325252596245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739313348470216835064163 7108970022705325252596245)
                ·
                  refine ⟨333232969814312121215449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7108970022705325252596245 333232969814312121215449)
                  ·
                    rfl

theorem cell21_1460180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1460180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460180 prefixEnd_1460180 := by exact prefixLift 1460180
  have htrace : WordTrace (prefixWord ++ tailWord_1460180) baseStart_1460180 baseEnd_1460180 := by
    simpa [prefixWord, tailWord_1460180, baseEnd_1460180] using wordTrace_append hprefix tailTrace_1460180
  have hstable : (prefixWord ++ tailWord_1460180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460180).length < 2 ^ (prefixWord ++ tailWord_1460180).sum := by decide
  have hdescent : baseEnd_1460180 < baseStart_1460180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460228 : List Nat := [2, 3, 2, 4, 1, 2, 7]
def baseStart_1460228 : Nat := 118140960795 + 1460228 * 2 ^ 59
def prefixEnd_1460228 : Nat := 4983230072969 + 3 ^ 40 * 1460228 * 2
def baseEnd_1460228 : Nat := 37027102674252744935039

theorem tailTrace_1460228 : CollatzResearch.WordTrace tailWord_1460228 prefixEnd_1460228 37027102674252744935039 := by
  unfold tailWord_1460228
  simp only [CollatzResearch.WordTrace]
  refine ⟨26629445276925408966394669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35505927035900545288526225 26629445276925408966394669)
  ·
    refine ⟨9986041978847028362398001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26629445276925408966394669 9986041978847028362398001)
    ·
      refine ⟨7489531484135271271798501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9986041978847028362398001 7489531484135271271798501)
      ·
        refine ⟨1404287153275363363462219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7489531484135271271798501 1404287153275363363462219)
        ·
          refine ⟨2106430729913045045193329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404287153275363363462219 2106430729913045045193329)
          ·
            refine ⟨1579823047434783783894997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2106430729913045045193329 1579823047434783783894997)
            ·
              refine ⟨37027102674252744935039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1579823047434783783894997 37027102674252744935039)
              ·
                rfl

theorem cell21_1460228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 7].length) (baseStart_1460228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460228 prefixEnd_1460228 := by exact prefixLift 1460228
  have htrace : WordTrace (prefixWord ++ tailWord_1460228) baseStart_1460228 baseEnd_1460228 := by
    simpa [prefixWord, tailWord_1460228, baseEnd_1460228] using wordTrace_append hprefix tailTrace_1460228
  have hstable : (prefixWord ++ tailWord_1460228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460228).length < 2 ^ (prefixWord ++ tailWord_1460228).sum := by decide
  have hdescent : baseEnd_1460228 < baseStart_1460228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460349 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1460349 : Nat := 118140960795 + 1460349 * 2 ^ 59
def prefixEnd_1460349 : Nat := 4983230072969 + 3 ^ 40 * 1460349 * 2
def baseEnd_1460349 : Nat := 333271537916805382898437

theorem tailTrace_1460349 : CollatzResearch.WordTrace tailWord_1460349 prefixEnd_1460349 333271537916805382898437 := by
  unfold tailWord_1460349
  simp only [CollatzResearch.WordTrace]
  refine ⟨53263303786412455597944101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35508869190941637065296067 53263303786412455597944101)
  ·
    refine ⟨9986869459952335424614519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53263303786412455597944101 9986869459952335424614519)
    ·
      refine ⟨14980304189928503136921779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9986869459952335424614519 14980304189928503136921779)
      ·
        refine ⟨22470456284892754705382669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14980304189928503136921779 22470456284892754705382669)
        ·
          refine ⟨8426421106834783014518501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22470456284892754705382669 8426421106834783014518501)
          ·
            refine ⟨1579953957531521815222219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8426421106834783014518501 1579953957531521815222219)
            ·
              refine ⟨2369930936297282722833329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579953957531521815222219 2369930936297282722833329)
              ·
                refine ⟨1777448202222962042124997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2369930936297282722833329 1777448202222962042124997)
                ·
                  refine ⟨333271537916805382898437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1777448202222962042124997 333271537916805382898437)
                  ·
                    rfl

theorem cell21_1460349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1460349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460349 prefixEnd_1460349 := by exact prefixLift 1460349
  have htrace : WordTrace (prefixWord ++ tailWord_1460349) baseStart_1460349 baseEnd_1460349 := by
    simpa [prefixWord, tailWord_1460349, baseEnd_1460349] using wordTrace_append hprefix tailTrace_1460349
  have hstable : (prefixWord ++ tailWord_1460349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460349).length < 2 ^ (prefixWord ++ tailWord_1460349).sum := by decide
  have hdescent : baseEnd_1460349 < baseStart_1460349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460366 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_1460366 : Nat := 118140960795 + 1460366 * 2 ^ 59
def prefixEnd_1460366 : Nat := 4983230072969 + 3 ^ 40 * 1460366 * 2
def baseEnd_1460366 : Nat := 333275417548417131115069

theorem tailTrace_1460366 : CollatzResearch.WordTrace tailWord_1460366 prefixEnd_1460366 333275417548417131115069 := by
  unfold tailWord_1460366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6657990478418858437664119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35509282551567245000875301 6657990478418858437664119)
  ·
    refine ⟨9986985717628287656496179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6657990478418858437664119 9986985717628287656496179)
    ·
      refine ⟨14980478576442431484744269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9986985717628287656496179 14980478576442431484744269)
      ·
        refine ⟨5617679466165911806779101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14980478576442431484744269 5617679466165911806779101)
        ·
          refine ⟨2106629799812216927542163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5617679466165911806779101 2106629799812216927542163)
          ·
            refine ⟨3159944699718325391313245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106629799812216927542163 3159944699718325391313245)
            ·
              refine ⟨1184979262394372021742467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3159944699718325391313245 1184979262394372021742467)
              ·
                refine ⟨1777468893591558032613701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184979262394372021742467 1777468893591558032613701)
                ·
                  refine ⟨333275417548417131115069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1777468893591558032613701 333275417548417131115069)
                  ·
                    rfl

theorem cell21_1460366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_1460366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460366 prefixEnd_1460366 := by exact prefixLift 1460366
  have htrace : WordTrace (prefixWord ++ tailWord_1460366) baseStart_1460366 baseEnd_1460366 := by
    simpa [prefixWord, tailWord_1460366, baseEnd_1460366] using wordTrace_append hprefix tailTrace_1460366
  have hstable : (prefixWord ++ tailWord_1460366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460366).length < 2 ^ (prefixWord ++ tailWord_1460366).sum := by decide
  have hdescent : baseEnd_1460366 < baseStart_1460366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460673 : List Nat := [1, 2, 7, 1, 1, 1, 2, 3, 3]
def baseStart_1460673 : Nat := 118140960795 + 1460673 * 2 ^ 59
def prefixEnd_1460673 : Nat := 4983230072969 + 3 ^ 40 * 1460673 * 2
def baseEnd_1460673 : Nat := 333345479131052819497775

theorem tailTrace_1460673 : CollatzResearch.WordTrace tailWord_1460673 prefixEnd_1460673 333345479131052819497775 := by
  unfold tailWord_1460673
  simp only [CollatzResearch.WordTrace]
  refine ⟨53275121037238658932738673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35516747358159105955159115 53275121037238658932738673)
  ·
    refine ⟨39956340777928994199554005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53275121037238658932738673 39956340777928994199554005)
    ·
      refine ⟨936476736982710801552047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 39956340777928994199554005 936476736982710801552047)
      ·
        refine ⟨1404715105474066202328071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936476736982710801552047 1404715105474066202328071)
        ·
          refine ⟨2107072658211099303492107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404715105474066202328071 2107072658211099303492107)
          ·
            refine ⟨3160608987316648955238161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107072658211099303492107 3160608987316648955238161)
            ·
              refine ⟨2370456740487486716428621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160608987316648955238161 2370456740487486716428621)
              ·
                refine ⟨888921277682807518660733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2370456740487486716428621 888921277682807518660733)
                ·
                  refine ⟨333345479131052819497775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888921277682807518660733 333345479131052819497775)
                  ·
                    rfl

theorem cell21_1460673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 3].length) (baseStart_1460673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460673 prefixEnd_1460673 := by exact prefixLift 1460673
  have htrace : WordTrace (prefixWord ++ tailWord_1460673) baseStart_1460673 baseEnd_1460673 := by
    simpa [prefixWord, tailWord_1460673, baseEnd_1460673] using wordTrace_append hprefix tailTrace_1460673
  have hstable : (prefixWord ++ tailWord_1460673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460673).length < 2 ^ (prefixWord ++ tailWord_1460673).sum := by decide
  have hdescent : baseEnd_1460673 < baseStart_1460673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460681 : List Nat := [1, 2, 1, 1, 2, 1, 5, 5, 3]
def baseStart_1460681 : Nat := 118140960795 + 1460681 * 2 ^ 59
def prefixEnd_1460681 : Nat := 4983230072969 + 3 ^ 40 * 1460681 * 2
def baseEnd_1460681 : Nat := 333347304840046583364425

theorem tailTrace_1460681 : CollatzResearch.WordTrace tailWord_1460681 prefixEnd_1460681 333347304840046583364425 := by
  unfold tailWord_1460681
  simp only [CollatzResearch.WordTrace]
  refine ⟨53275412821209676299029897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35516941880806450866019931 53275412821209676299029897)
  ·
    refine ⟨39956559615907257224272423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53275412821209676299029897 39956559615907257224272423)
    ·
      refine ⟨59934839423860885836408635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39956559615907257224272423 59934839423860885836408635)
      ·
        refine ⟨89902259135791328754612953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59934839423860885836408635 89902259135791328754612953)
        ·
          refine ⟨67426694351843496565959715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89902259135791328754612953 67426694351843496565959715)
          ·
            refine ⟨101140041527765244848939573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67426694351843496565959715 101140041527765244848939573)
            ·
              refine ⟨9481878893227991704588085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101140041527765244848939573 9481878893227991704588085)
              ·
                refine ⟨888926146240124222305133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9481878893227991704588085 888926146240124222305133)
                ·
                  refine ⟨333347304840046583364425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888926146240124222305133 333347304840046583364425)
                  ·
                    rfl

theorem cell21_1460681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 3].length) (baseStart_1460681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460681 prefixEnd_1460681 := by exact prefixLift 1460681
  have htrace : WordTrace (prefixWord ++ tailWord_1460681) baseStart_1460681 baseEnd_1460681 := by
    simpa [prefixWord, tailWord_1460681, baseEnd_1460681] using wordTrace_append hprefix tailTrace_1460681
  have hstable : (prefixWord ++ tailWord_1460681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460681).length < 2 ^ (prefixWord ++ tailWord_1460681).sum := by decide
  have hdescent : baseEnd_1460681 < baseStart_1460681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460726 : List Nat := [5, 1, 1, 1, 2, 1, 3, 7]
def baseStart_1460726 : Nat := 118140960795 + 1460726 * 2 ^ 59
def prefixEnd_1460726 : Nat := 4983230072969 + 3 ^ 40 * 1460726 * 2
def baseEnd_1460726 : Nat := 111119191484378835038111

theorem tailTrace_1460726 : CollatzResearch.WordTrace tailWord_1460726 prefixEnd_1460726 111119191484378835038111 := by
  unfold tailWord_1460726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3329815881627915561526127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35518036070697765989612021 3329815881627915561526127)
  ·
    refine ⟨4994723822441873342289191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3329815881627915561526127 4994723822441873342289191)
    ·
      refine ⟨7492085733662810013433787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4994723822441873342289191 7492085733662810013433787)
      ·
        refine ⟨11238128600494215020150681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7492085733662810013433787 11238128600494215020150681)
        ·
          refine ⟨8428596450370661265113011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11238128600494215020150681 8428596450370661265113011)
          ·
            refine ⟨12642894675555991897669517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8428596450370661265113011 12642894675555991897669517)
            ·
              refine ⟨4741085503333496961626069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12642894675555991897669517 4741085503333496961626069)
              ·
                refine ⟨111119191484378835038111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4741085503333496961626069 111119191484378835038111)
                ·
                  rfl

theorem cell21_1460726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_1460726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460726 prefixEnd_1460726 := by exact prefixLift 1460726
  have htrace : WordTrace (prefixWord ++ tailWord_1460726) baseStart_1460726 baseEnd_1460726 := by
    simpa [prefixWord, tailWord_1460726, baseEnd_1460726] using wordTrace_append hprefix tailTrace_1460726
  have hstable : (prefixWord ++ tailWord_1460726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460726).length < 2 ^ (prefixWord ++ tailWord_1460726).sum := by decide
  have hdescent : baseEnd_1460726 < baseStart_1460726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460743 : List Nat := [1, 1, 4, 3, 4, 1, 7]
def baseStart_1460743 : Nat := 118140960795 + 1460743 * 2 ^ 59
def prefixEnd_1460743 : Nat := 4983230072969 + 3 ^ 40 * 1460743 * 2
def baseEnd_1460743 : Nat := 37040161564972028147885

theorem tailTrace_1460743 : CollatzResearch.WordTrace tailWord_1460743 prefixEnd_1460743 37040161564972028147885 := by
  unfold tailWord_1460743
  simp only [CollatzResearch.WordTrace]
  refine ⟨53277674146985060887786883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35518449431323373925191255 53277674146985060887786883)
  ·
    refine ⟨79916511220477591331680325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53277674146985060887786883 79916511220477591331680325)
    ·
      refine ⟨14984345853839548374690061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79916511220477591331680325 14984345853839548374690061)
      ·
        refine ⟨5619129695189830640508773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14984345853839548374690061 5619129695189830640508773)
        ·
          refine ⟨1053586817848093245095395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5619129695189830640508773 1053586817848093245095395)
          ·
            refine ⟨1580380226772139867643093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053586817848093245095395 1580380226772139867643093)
            ·
              refine ⟨37040161564972028147885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1580380226772139867643093 37040161564972028147885)
              ·
                rfl

theorem cell21_1460743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 7].length) (baseStart_1460743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460743 prefixEnd_1460743 := by exact prefixLift 1460743
  have htrace : WordTrace (prefixWord ++ tailWord_1460743) baseStart_1460743 baseEnd_1460743 := by
    simpa [prefixWord, tailWord_1460743, baseEnd_1460743] using wordTrace_append hprefix tailTrace_1460743
  have hstable : (prefixWord ++ tailWord_1460743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460743).length < 2 ^ (prefixWord ++ tailWord_1460743).sum := by decide
  have hdescent : baseEnd_1460743 < baseStart_1460743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460749 : List Nat := [1, 7, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1460749 : Nat := 118140960795 + 1460749 * 2 ^ 59
def prefixEnd_1460749 : Nat := 4983230072969 + 3 ^ 40 * 1460749 * 2
def baseEnd_1460749 : Nat := 333362823366493576230953

theorem tailTrace_1460749 : CollatzResearch.WordTrace tailWord_1460749 prefixEnd_1460749 333362823366493576230953 := by
  unfold tailWord_1460749
  simp only [CollatzResearch.WordTrace]
  refine ⟨53277892984963323912505301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35518595323308882608336867 53277892984963323912505301)
  ·
    refine ⟨1248700616835077904199343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 53277892984963323912505301 1248700616835077904199343)
    ·
      refine ⟨1873050925252616856299015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1248700616835077904199343 1873050925252616856299015)
      ·
        refine ⟨2809576387878925284448523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1873050925252616856299015 2809576387878925284448523)
        ·
          refine ⟨4214364581818387926672785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809576387878925284448523 4214364581818387926672785)
          ·
            refine ⟨3160773436363790945004589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4214364581818387926672785 3160773436363790945004589)
            ·
              refine ⟨1185290038636421604376721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3160773436363790945004589 1185290038636421604376721)
              ·
                refine ⟨888967528977316203282541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185290038636421604376721 888967528977316203282541)
                ·
                  refine ⟨333362823366493576230953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888967528977316203282541 333362823366493576230953)
                  ·
                    rfl

theorem cell21_1460749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1460749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460749 prefixEnd_1460749 := by exact prefixLift 1460749
  have htrace : WordTrace (prefixWord ++ tailWord_1460749) baseStart_1460749 baseEnd_1460749 := by
    simpa [prefixWord, tailWord_1460749, baseEnd_1460749] using wordTrace_append hprefix tailTrace_1460749
  have hstable : (prefixWord ++ tailWord_1460749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460749).length < 2 ^ (prefixWord ++ tailWord_1460749).sum := by decide
  have hdescent : baseEnd_1460749 < baseStart_1460749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460785 : List Nat := [1, 2, 2, 3, 1, 1, 4, 7]
def baseStart_1460785 : Nat := 118140960795 + 1460785 * 2 ^ 59
def prefixEnd_1460785 : Nat := 4983230072969 + 3 ^ 40 * 1460785 * 2
def baseEnd_1460785 : Nat := 111123679685655171210293

theorem tailTrace_1460785 : CollatzResearch.WordTrace tailWord_1460785 prefixEnd_1460785 111123679685655171210293 := by
  unfold tailWord_1460785
  simp only [CollatzResearch.WordTrace]
  refine ⟨53279206012832902060815809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35519470675221934707210539 53279206012832902060815809)
  ·
    refine ⟨39959404509624676545611857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53279206012832902060815809 39959404509624676545611857)
    ·
      refine ⟨29969553382218507409208893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39959404509624676545611857 29969553382218507409208893)
      ·
        refine ⟨11238582518331940278453335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29969553382218507409208893 11238582518331940278453335)
        ·
          refine ⟨16857873777497910417680003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11238582518331940278453335 16857873777497910417680003)
          ·
            refine ⟨25286810666246865626520005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16857873777497910417680003 25286810666246865626520005)
            ·
              refine ⟨4741276999921287304972501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25286810666246865626520005 4741276999921287304972501)
              ·
                refine ⟨111123679685655171210293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4741276999921287304972501 111123679685655171210293)
                ·
                  rfl

theorem cell21_1460785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 7].length) (baseStart_1460785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460785 prefixEnd_1460785 := by exact prefixLift 1460785
  have htrace : WordTrace (prefixWord ++ tailWord_1460785) baseStart_1460785 baseEnd_1460785 := by
    simpa [prefixWord, tailWord_1460785, baseEnd_1460785] using wordTrace_append hprefix tailTrace_1460785
  have hstable : (prefixWord ++ tailWord_1460785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460785).length < 2 ^ (prefixWord ++ tailWord_1460785).sum := by decide
  have hdescent : baseEnd_1460785 < baseStart_1460785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460864 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 4]
def baseStart_1460864 : Nat := 118140960795 + 1460864 * 2 ^ 59
def prefixEnd_1460864 : Nat := 4983230072969 + 3 ^ 40 * 1460864 * 2
def baseEnd_1460864 : Nat := 333389067933278931814051

theorem tailTrace_1460864 : CollatzResearch.WordTrace tailWord_1460864 prefixEnd_1460864 333389067933278931814051 := by
  unfold tailWord_1460864
  simp only [CollatzResearch.WordTrace]
  refine ⟨26641043689773349276470823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35521391586364465701961097 26641043689773349276470823)
  ·
    refine ⟨39961565534660023914706235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26641043689773349276470823 39961565534660023914706235)
    ·
      refine ⟨59942348301990035872059353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39961565534660023914706235 59942348301990035872059353)
      ·
        refine ⟨44956761226492526904044515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59942348301990035872059353 44956761226492526904044515)
        ·
          refine ⟨67435141839738790356066773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44956761226492526904044515 67435141839738790356066773)
          ·
            refine ⟨1580511136868877898970315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 67435141839738790356066773 1580511136868877898970315)
            ·
              refine ⟨2370766705303316848455473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580511136868877898970315 2370766705303316848455473)
              ·
                refine ⟨1778075028977487636341605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2370766705303316848455473 1778075028977487636341605)
                ·
                  refine ⟨333389067933278931814051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1778075028977487636341605 333389067933278931814051)
                  ·
                    rfl

theorem cell21_1460864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_1460864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460864 prefixEnd_1460864 := by exact prefixLift 1460864
  have htrace : WordTrace (prefixWord ++ tailWord_1460864) baseStart_1460864 baseEnd_1460864 := by
    simpa [prefixWord, tailWord_1460864, baseEnd_1460864] using wordTrace_append hprefix tailTrace_1460864
  have hstable : (prefixWord ++ tailWord_1460864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460864).length < 2 ^ (prefixWord ++ tailWord_1460864).sum := by decide
  have hdescent : baseEnd_1460864 < baseStart_1460864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460940 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 4]
def baseStart_1460940 : Nat := 118140960795 + 1460940 * 2 ^ 59
def prefixEnd_1460940 : Nat := 4983230072969 + 3 ^ 40 * 1460940 * 2
def baseEnd_1460940 : Nat := 333406412168719688547229

theorem tailTrace_1460940 : CollatzResearch.WordTrace tailWord_1460940 prefixEnd_1460940 333406412168719688547229 := by
  unfold tailWord_1460940
  simp only [CollatzResearch.WordTrace]
  refine ⟨26642429663635681766354137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35523239551514242355138849 26642429663635681766354137)
  ·
    refine ⟨19981822247726761324765603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26642429663635681766354137 19981822247726761324765603)
    ·
      refine ⟨29972733371590141987148405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19981822247726761324765603 29972733371590141987148405)
      ·
        refine ⟨2809943753586575811295163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29972733371590141987148405 2809943753586575811295163)
        ·
          refine ⟨4214915630379863716942745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809943753586575811295163 4214915630379863716942745)
          ·
            refine ⟨3161186722784897787707059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4214915630379863716942745 3161186722784897787707059)
            ·
              refine ⟨4741780084177346681560589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161186722784897787707059 4741780084177346681560589)
              ·
                refine ⟨1778167531566505005585221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4741780084177346681560589 1778167531566505005585221)
                ·
                  refine ⟨333406412168719688547229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1778167531566505005585221 333406412168719688547229)
                  ·
                    rfl

theorem cell21_1460940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_1460940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1460940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1460940 prefixEnd_1460940 := by exact prefixLift 1460940
  have htrace : WordTrace (prefixWord ++ tailWord_1460940) baseStart_1460940 baseEnd_1460940 := by
    simpa [prefixWord, tailWord_1460940, baseEnd_1460940] using wordTrace_append hprefix tailTrace_1460940
  have hstable : (prefixWord ++ tailWord_1460940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460940).length < 2 ^ (prefixWord ++ tailWord_1460940).sum := by decide
  have hdescent : baseEnd_1460940 < baseStart_1460940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461027 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 9]
def baseStart_1461027 : Nat := 118140960795 + 1461027 * 2 ^ 59
def prefixEnd_1461027 : Nat := 4983230072969 + 3 ^ 40 * 1461027 * 2
def baseEnd_1461027 : Nat := 333426266754026870597051

theorem tailTrace_1461027 : CollatzResearch.WordTrace tailWord_1461027 prefixEnd_1461027 333426266754026870597051 := by
  unfold tailWord_1461027
  simp only [CollatzResearch.WordTrace]
  refine ⟨53288032477956177391125335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35525354985304118260750223 53288032477956177391125335)
  ·
    refine ⟨79932048716934266086688003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53288032477956177391125335 79932048716934266086688003)
    ·
      refine ⟨119898073075401399130032005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79932048716934266086688003 119898073075401399130032005)
      ·
        refine ⟨22480888701637762336881001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119898073075401399130032005 22480888701637762336881001)
        ·
          refine ⟨16860666526228321752660751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22480888701637762336881001 16860666526228321752660751)
          ·
            refine ⟨25290999789342482628991127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16860666526228321752660751 25290999789342482628991127)
            ·
              refine ⟨37936499684013723943486691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25290999789342482628991127 37936499684013723943486691)
              ·
                refine ⟨56904749526020585915230037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37936499684013723943486691 56904749526020585915230037)
                ·
                  refine ⟨333426266754026870597051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56904749526020585915230037 333426266754026870597051)
                  ·
                    rfl

theorem cell21_1461027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_1461027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461027 prefixEnd_1461027 := by exact prefixLift 1461027
  have htrace : WordTrace (prefixWord ++ tailWord_1461027) baseStart_1461027 baseEnd_1461027 := by
    simpa [prefixWord, tailWord_1461027, baseEnd_1461027] using wordTrace_append hprefix tailTrace_1461027
  have hstable : (prefixWord ++ tailWord_1461027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461027).length < 2 ^ (prefixWord ++ tailWord_1461027).sum := by decide
  have hdescent : baseEnd_1461027 < baseStart_1461027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461109 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 4]
def baseStart_1461109 : Nat := 118140960795 + 1461109 * 2 ^ 59
def prefixEnd_1461109 : Nat := 4983230072969 + 3 ^ 40 * 1461109 * 2
def baseEnd_1461109 : Nat := 333444980271212950230217

theorem tailTrace_1461109 : CollatzResearch.WordTrace tailWord_1461109 prefixEnd_1461109 333444980271212950230217 := by
  unfold tailWord_1461109
  simp only [CollatzResearch.WordTrace]
  refine ⟨53291023263659105395610381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35527348842439403597073587 53291023263659105395610381)
  ·
    refine ⟨19984133723872164523353893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53291023263659105395610381 19984133723872164523353893)
    ·
      refine ⟨3747025073226030848128855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19984133723872164523353893 3747025073226030848128855)
      ·
        refine ⟨5620537609839046272193283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3747025073226030848128855 5620537609839046272193283)
        ·
          refine ⟨8430806414758569408289925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5620537609839046272193283 8430806414758569408289925)
          ·
            refine ⟨1580776202767231764054361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8430806414758569408289925 1580776202767231764054361)
            ·
              refine ⟨1185582152075423823040771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1580776202767231764054361 1185582152075423823040771)
              ·
                refine ⟨1778373228113135734561157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185582152075423823040771 1778373228113135734561157)
                ·
                  refine ⟨333444980271212950230217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1778373228113135734561157 333444980271212950230217)
                  ·
                    rfl

theorem cell21_1461109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_1461109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461109 prefixEnd_1461109 := by exact prefixLift 1461109
  have htrace : WordTrace (prefixWord ++ tailWord_1461109) baseStart_1461109 baseEnd_1461109 := by
    simpa [prefixWord, tailWord_1461109, baseEnd_1461109] using wordTrace_append hprefix tailTrace_1461109
  have hstable : (prefixWord ++ tailWord_1461109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461109).length < 2 ^ (prefixWord ++ tailWord_1461109).sum := by decide
  have hdescent : baseEnd_1461109 < baseStart_1461109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461151 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 4]
def baseStart_1461151 : Nat := 118140960795 + 1461151 * 2 ^ 59
def prefixEnd_1461151 : Nat := 4983230072969 + 3 ^ 40 * 1461151 * 2
def baseEnd_1461151 : Nat := 333454565243430210530131

theorem tailTrace_1461151 : CollatzResearch.WordTrace tailWord_1461151 prefixEnd_1461151 333454565243430210530131 := by
  unfold tailWord_1461151
  simp only [CollatzResearch.WordTrace]
  refine ⟨53292555129506946568639307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35528370086337964379092871 53292555129506946568639307)
  ·
    refine ⟨79938832694260419852958961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53292555129506946568639307 79938832694260419852958961)
    ·
      refine ⟨59954124520695314889719221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79938832694260419852958961 59954124520695314889719221)
      ·
        refine ⟨5620699173815185770911177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59954124520695314889719221 5620699173815185770911177)
        ·
          refine ⟨4215524380361389328183383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5620699173815185770911177 4215524380361389328183383)
          ·
            refine ⟨6323286570542083992275075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4215524380361389328183383 6323286570542083992275075)
            ·
              refine ⟨9484929855813125988412613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6323286570542083992275075 9484929855813125988412613)
              ·
                refine ⟨1778424347964961122827365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9484929855813125988412613 1778424347964961122827365)
                ·
                  refine ⟨333454565243430210530131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1778424347964961122827365 333454565243430210530131)
                  ·
                    rfl

theorem cell21_1461151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 4].length) (baseStart_1461151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461151 prefixEnd_1461151 := by exact prefixLift 1461151
  have htrace : WordTrace (prefixWord ++ tailWord_1461151) baseStart_1461151 baseEnd_1461151 := by
    simpa [prefixWord, tailWord_1461151, baseEnd_1461151] using wordTrace_append hprefix tailTrace_1461151
  have hstable : (prefixWord ++ tailWord_1461151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461151).length < 2 ^ (prefixWord ++ tailWord_1461151).sum := by decide
  have hdescent : baseEnd_1461151 < baseStart_1461151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461154 : List Nat := [3, 3, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1461154 : Nat := 118140960795 + 1461154 * 2 ^ 59
def prefixEnd_1461154 : Nat := 4983230072969 + 3 ^ 40 * 1461154 * 2
def baseEnd_1461154 : Nat := 333455249884302871980125

theorem tailTrace_1461154 : CollatzResearch.WordTrace tailWord_1461154 prefixEnd_1461154 333455249884302871980125 := by
  unfold tailWord_1461154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13323166137124019520249629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35528443032330718720665677 13323166137124019520249629)
  ·
    refine ⟨4996187301421507320093611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13323166137124019520249629 4996187301421507320093611)
    ·
      refine ⟨7494280952132260980140417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4996187301421507320093611 7494280952132260980140417)
      ·
        refine ⟨5620710714099195735105313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7494280952132260980140417 5620710714099195735105313)
        ·
          refine ⟨4215533035574396801328985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5620710714099195735105313 4215533035574396801328985)
          ·
            refine ⟨3161649776680797600996739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4215533035574396801328985 3161649776680797600996739)
            ·
              refine ⟨4742474665021196401495109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161649776680797600996739 4742474665021196401495109)
              ·
                refine ⟨889213999691474325280333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4742474665021196401495109 889213999691474325280333)
                ·
                  refine ⟨333455249884302871980125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889213999691474325280333 333455249884302871980125)
                  ·
                    rfl

theorem cell21_1461154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1461154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461154 prefixEnd_1461154 := by exact prefixLift 1461154
  have htrace : WordTrace (prefixWord ++ tailWord_1461154) baseStart_1461154 baseEnd_1461154 := by
    simpa [prefixWord, tailWord_1461154, baseEnd_1461154] using wordTrace_append hprefix tailTrace_1461154
  have hstable : (prefixWord ++ tailWord_1461154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461154).length < 2 ^ (prefixWord ++ tailWord_1461154).sum := by decide
  have hdescent : baseEnd_1461154 < baseStart_1461154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461182 : List Nat := [4, 2, 1, 1, 1, 2, 5, 5]
def baseStart_1461182 : Nat := 118140960795 + 1461182 * 2 ^ 59
def prefixEnd_1461182 : Nat := 4983230072969 + 3 ^ 40 * 1461182 * 2
def baseEnd_1461182 : Nat := 111153879955260348504467

theorem tailTrace_1461182 : CollatzResearch.WordTrace tailWord_1461182 prefixEnd_1461182 111153879955260348504467 := by
  unfold tailWord_1461182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6661710724049329857877225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35529123861596425908678533 6661710724049329857877225)
  ·
    refine ⟨4996283043036997393407919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6661710724049329857877225 4996283043036997393407919)
    ·
      refine ⟨7494424564555496090111879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4996283043036997393407919 7494424564555496090111879)
      ·
        refine ⟨11241636846833244135167819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7494424564555496090111879 11241636846833244135167819)
        ·
          refine ⟨16862455270249866202751729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11241636846833244135167819 16862455270249866202751729)
          ·
            refine ⟨12646841452687399652063797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16862455270249866202751729 12646841452687399652063797)
            ·
              refine ⟨1185641386189443717380981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12646841452687399652063797 1185641386189443717380981)
              ·
                refine ⟨111153879955260348504467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1185641386189443717380981 111153879955260348504467)
                ·
                  rfl

theorem cell21_1461182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_1461182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461182 prefixEnd_1461182 := by exact prefixLift 1461182
  have htrace : WordTrace (prefixWord ++ tailWord_1461182) baseStart_1461182 baseEnd_1461182 := by
    simpa [prefixWord, tailWord_1461182, baseEnd_1461182] using wordTrace_append hprefix tailTrace_1461182
  have hstable : (prefixWord ++ tailWord_1461182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461182).length < 2 ^ (prefixWord ++ tailWord_1461182).sum := by decide
  have hdescent : baseEnd_1461182 < baseStart_1461182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461213 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1461213 : Nat := 118140960795 + 1461213 * 2 ^ 59
def prefixEnd_1461213 : Nat := 4983230072969 + 3 ^ 40 * 1461213 * 2
def baseEnd_1461213 : Nat := 333468714488131880496671

theorem tailTrace_1461213 : CollatzResearch.WordTrace tailWord_1461213 prefixEnd_1461213 333468714488131880496671 := by
  unfold tailWord_1461213
  simp only [CollatzResearch.WordTrace]
  refine ⟨53294816455282331157396293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35529877636854887438264195 53294816455282331157396293)
  ·
    refine ⟨9992778085365437092011805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53294816455282331157396293 9992778085365437092011805)
    ·
      refine ⟨3747291782012038909504427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9992778085365437092011805 3747291782012038909504427)
      ·
        refine ⟨5620937673018058364256641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3747291782012038909504427 5620937673018058364256641)
        ·
          refine ⟨4215703254763543773192481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5620937673018058364256641 4215703254763543773192481)
          ·
            refine ⟨3161777441072657829894361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4215703254763543773192481 3161777441072657829894361)
            ·
              refine ⟨2371333080804493372420771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3161777441072657829894361 2371333080804493372420771)
              ·
                refine ⟨3556999621206740058631157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371333080804493372420771 3556999621206740058631157)
                ·
                  refine ⟨333468714488131880496671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3556999621206740058631157 333468714488131880496671)
                  ·
                    rfl

theorem cell21_1461213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1461213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461213 prefixEnd_1461213 := by exact prefixLift 1461213
  have htrace : WordTrace (prefixWord ++ tailWord_1461213) baseStart_1461213 baseEnd_1461213 := by
    simpa [prefixWord, tailWord_1461213, baseEnd_1461213] using wordTrace_append hprefix tailTrace_1461213
  have hstable : (prefixWord ++ tailWord_1461213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461213).length < 2 ^ (prefixWord ++ tailWord_1461213).sum := by decide
  have hdescent : baseEnd_1461213 < baseStart_1461213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461272 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 5]
def baseStart_1461272 : Nat := 118140960795 + 1461272 * 2 ^ 59
def prefixEnd_1461272 : Nat := 4983230072969 + 3 ^ 40 * 1461272 * 2
def baseEnd_1461272 : Nat := 333482179091960889013217

theorem tailTrace_1461272 : CollatzResearch.WordTrace tailWord_1461272 prefixEnd_1461272 333482179091960889013217 := by
  unfold tailWord_1461272
  simp only [CollatzResearch.WordTrace]
  refine ⟨26648484181034292116897035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35531312241379056155862713 26648484181034292116897035)
  ·
    refine ⟨39972726271551438175345553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26648484181034292116897035 39972726271551438175345553)
    ·
      refine ⟨29979544703663578631509165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39972726271551438175345553 29979544703663578631509165)
      ·
        refine ⟨11242329263873841986815937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29979544703663578631509165 11242329263873841986815937)
        ·
          refine ⟨8431746947905381490111953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11242329263873841986815937 8431746947905381490111953)
          ·
            refine ⟨6323810210929036117583965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8431746947905381490111953 6323810210929036117583965)
            ·
              refine ⟨2371428829098388544093987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6323810210929036117583965 2371428829098388544093987)
              ·
                refine ⟨3557143243647582816140981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371428829098388544093987 3557143243647582816140981)
                ·
                  refine ⟨333482179091960889013217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3557143243647582816140981 333482179091960889013217)
                  ·
                    rfl

theorem cell21_1461272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_1461272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461272 prefixEnd_1461272 := by exact prefixLift 1461272
  have htrace : WordTrace (prefixWord ++ tailWord_1461272) baseStart_1461272 baseEnd_1461272 := by
    simpa [prefixWord, tailWord_1461272, baseEnd_1461272] using wordTrace_append hprefix tailTrace_1461272
  have hstable : (prefixWord ++ tailWord_1461272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461272).length < 2 ^ (prefixWord ++ tailWord_1461272).sum := by decide
  have hdescent : baseEnd_1461272 < baseStart_1461272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461362 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1461362 : Nat := 118140960795 + 1461362 * 2 ^ 59
def prefixEnd_1461362 : Nat := 4983230072969 + 3 ^ 40 * 1461362 * 2
def baseEnd_1461362 : Nat := 333502718318140732513033

theorem tailTrace_1461362 : CollatzResearch.WordTrace tailWord_1461362 prefixEnd_1461362 333502718318140732513033 := by
  unfold tailWord_1461362
  simp only [CollatzResearch.WordTrace]
  refine ⟨13325062732935632401142585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35533500621161686403046893 13325062732935632401142585)
  ·
    refine ⟨9993797049701724300856939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13325062732935632401142585 9993797049701724300856939)
    ·
      refine ⟨14990695574552586451285409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9993797049701724300856939 14990695574552586451285409)
      ·
        refine ⟨11243021680914439838464057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14990695574552586451285409 11243021680914439838464057)
        ·
          refine ⟨8432266260685829878848043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11243021680914439838464057 8432266260685829878848043)
          ·
            refine ⟨12648399391028744818272065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8432266260685829878848043 12648399391028744818272065)
            ·
              refine ⟨9486299543271558613704049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12648399391028744818272065 9486299543271558613704049)
              ·
                refine ⟨7114724657453668960278037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9486299543271558613704049 7114724657453668960278037)
                ·
                  refine ⟨333502718318140732513033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7114724657453668960278037 333502718318140732513033)
                  ·
                    rfl

theorem cell21_1461362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1461362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461362 prefixEnd_1461362 := by exact prefixLift 1461362
  have htrace : WordTrace (prefixWord ++ tailWord_1461362) baseStart_1461362 baseEnd_1461362 := by
    simpa [prefixWord, tailWord_1461362, baseEnd_1461362] using wordTrace_append hprefix tailTrace_1461362
  have hstable : (prefixWord ++ tailWord_1461362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461362).length < 2 ^ (prefixWord ++ tailWord_1461362).sum := by decide
  have hdescent : baseEnd_1461362 < baseStart_1461362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461410 : List Nat := [3, 3, 1, 3, 2, 1, 1, 7]
def baseStart_1461410 : Nat := 118140960795 + 1461410 * 2 ^ 59
def prefixEnd_1461410 : Nat := 4983230072969 + 3 ^ 40 * 1461410 * 2
def baseEnd_1461410 : Nat := 111171224190701105237645

theorem tailTrace_1461410 : CollatzResearch.WordTrace tailWord_1461410 prefixEnd_1461410 111171224190701105237645 := by
  unfold tailWord_1461410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13325500408892158450579421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35534667757045755868211789 13325500408892158450579421)
  ·
    refine ⟨4997062653334559418967283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13325500408892158450579421 4997062653334559418967283)
    ·
      refine ⟨7495593980001839128450925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4997062653334559418967283 7495593980001839128450925)
      ·
        refine ⟨2810847742500689673169097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7495593980001839128450925 2810847742500689673169097)
        ·
          refine ⟨2108135806875517254876823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2810847742500689673169097 2108135806875517254876823)
          ·
            refine ⟨3162203710313275882315235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108135806875517254876823 3162203710313275882315235)
            ·
              refine ⟨4743305565469913823472853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162203710313275882315235 4743305565469913823472853)
              ·
                refine ⟨111171224190701105237645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4743305565469913823472853 111171224190701105237645)
                ·
                  rfl

theorem cell21_1461410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_1461410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461410 prefixEnd_1461410 := by exact prefixLift 1461410
  have htrace : WordTrace (prefixWord ++ tailWord_1461410) baseStart_1461410 baseEnd_1461410 := by
    simpa [prefixWord, tailWord_1461410, baseEnd_1461410] using wordTrace_append hprefix tailTrace_1461410
  have hstable : (prefixWord ++ tailWord_1461410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461410).length < 2 ^ (prefixWord ++ tailWord_1461410).sum := by decide
  have hdescent : baseEnd_1461410 < baseStart_1461410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461441 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 5]
def baseStart_1461441 : Nat := 118140960795 + 1461441 * 2 ^ 59
def prefixEnd_1461441 : Nat := 4983230072969 + 3 ^ 40 * 1461441 * 2
def baseEnd_1461441 : Nat := 333520747194454150696205

theorem tailTrace_1461441 : CollatzResearch.WordTrace tailWord_1461441 prefixEnd_1461441 333520747194454150696205 := by
  unfold tailWord_1461441
  simp only [CollatzResearch.WordTrace]
  refine ⟨53303132298456326096696177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35535421532304217397797451 53303132298456326096696177)
  ·
    refine ⟨39977349223842244572522133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53303132298456326096696177 39977349223842244572522133)
    ·
      refine ⟨1873938244867605214336975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39977349223842244572522133 1873938244867605214336975)
      ·
        refine ⟨2810907367301407821505463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1873938244867605214336975 2810907367301407821505463)
        ·
          refine ⟨4216361050952111732258195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2810907367301407821505463 4216361050952111732258195)
          ·
            refine ⟨6324541576428167598387293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4216361050952111732258195 6324541576428167598387293)
            ·
              refine ⟨2371703091160562849395235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6324541576428167598387293 2371703091160562849395235)
              ·
                refine ⟨3557554636740844274092853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371703091160562849395235 3557554636740844274092853)
                ·
                  refine ⟨333520747194454150696205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3557554636740844274092853 333520747194454150696205)
                  ·
                    rfl

theorem cell21_1461441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_1461441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461441 prefixEnd_1461441 := by exact prefixLift 1461441
  have htrace : WordTrace (prefixWord ++ tailWord_1461441) baseStart_1461441 baseEnd_1461441 := by
    simpa [prefixWord, tailWord_1461441, baseEnd_1461441] using wordTrace_append hprefix tailTrace_1461441
  have hstable : (prefixWord ++ tailWord_1461441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461441).length < 2 ^ (prefixWord ++ tailWord_1461441).sum := by decide
  have hdescent : baseEnd_1461441 < baseStart_1461441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461492 : List Nat := [2, 6, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1461492 : Nat := 118140960795 + 1461492 * 2 ^ 59
def prefixEnd_1461492 : Nat := 4983230072969 + 3 ^ 40 * 1461492 * 2
def baseEnd_1461492 : Nat := 333532386089289395346101

theorem tailTrace_1461492 : CollatzResearch.WordTrace tailWord_1461492 prefixEnd_1461492 333532386089289395346101 := by
  unfold tailWord_1461492
  simp only [CollatzResearch.WordTrace]
  refine ⟨26652496210635780903401365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35536661614181041204535153 26652496210635780903401365)
  ·
    refine ⟨1249335759873552229846939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26652496210635780903401365 1249335759873552229846939)
    ·
      refine ⟨1874003639810328344770409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1249335759873552229846939 1874003639810328344770409)
      ·
        refine ⟨1405502729857746258577807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1874003639810328344770409 1405502729857746258577807)
        ·
          refine ⟨2108254094786619387866711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405502729857746258577807 2108254094786619387866711)
          ·
            refine ⟨3162381142179929081800067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108254094786619387866711 3162381142179929081800067)
            ·
              refine ⟨4743571713269893622700101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162381142179929081800067 4743571713269893622700101)
              ·
                refine ⟨889419696238105054256269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4743571713269893622700101 889419696238105054256269)
                ·
                  refine ⟨333532386089289395346101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889419696238105054256269 333532386089289395346101)
                  ·
                    rfl

theorem cell21_1461492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1461492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461492 prefixEnd_1461492 := by exact prefixLift 1461492
  have htrace : WordTrace (prefixWord ++ tailWord_1461492) baseStart_1461492 baseEnd_1461492 := by
    simpa [prefixWord, tailWord_1461492, baseEnd_1461492] using wordTrace_append hprefix tailTrace_1461492
  have hstable : (prefixWord ++ tailWord_1461492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461492).length < 2 ^ (prefixWord ++ tailWord_1461492).sum := by decide
  have hdescent : baseEnd_1461492 < baseStart_1461492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461565 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 4]
def baseStart_1461565 : Nat := 118140960795 + 1461565 * 2 ^ 59
def prefixEnd_1461565 : Nat := 4983230072969 + 3 ^ 40 * 1461565 * 2
def baseEnd_1461565 : Nat := 333549045683857490629285

theorem tailTrace_1461565 : CollatzResearch.WordTrace tailWord_1461565 prefixEnd_1461565 333549045683857490629285 := by
  unfold tailWord_1461565
  simp only [CollatzResearch.WordTrace]
  refine ⟨53307654950007095274210149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35538436633338063516140099 53307654950007095274210149)
  ·
    refine ⟨9995185303126330363914403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53307654950007095274210149 9995185303126330363914403)
    ·
      refine ⟨14992777954689495545871605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9995185303126330363914403 14992777954689495545871605)
      ·
        refine ⟨1405572933252140207425463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14992777954689495545871605 1405572933252140207425463)
        ·
          refine ⟨2108359399878210311138195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405572933252140207425463 2108359399878210311138195)
          ·
            refine ⟨3162539099817315466707293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108359399878210311138195 3162539099817315466707293)
            ·
              refine ⟨1185952162431493300015235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3162539099817315466707293 1185952162431493300015235)
              ·
                refine ⟨1778928243647239950022853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185952162431493300015235 1778928243647239950022853)
                ·
                  refine ⟨333549045683857490629285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1778928243647239950022853 333549045683857490629285)
                  ·
                    rfl

theorem cell21_1461565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_1461565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461565 prefixEnd_1461565 := by exact prefixLift 1461565
  have htrace : WordTrace (prefixWord ++ tailWord_1461565) baseStart_1461565 baseEnd_1461565 := by
    simpa [prefixWord, tailWord_1461565, baseEnd_1461565] using wordTrace_append hprefix tailTrace_1461565
  have hstable : (prefixWord ++ tailWord_1461565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461565).length < 2 ^ (prefixWord ++ tailWord_1461565).sum := by decide
  have hdescent : baseEnd_1461565 < baseStart_1461565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461604 : List Nat := [2, 3, 1, 1, 3, 2, 9]
def baseStart_1461604 : Nat := 118140960795 + 1461604 * 2 ^ 59
def prefixEnd_1461604 : Nat := 4983230072969 + 3 ^ 40 * 1461604 * 2
def baseEnd_1461604 : Nat := 37061994001689121053245

theorem tailTrace_1461604 : CollatzResearch.WordTrace tailWord_1461604 prefixEnd_1461604 37061994001689121053245 := by
  unfold tailWord_1461604
  simp only [CollatzResearch.WordTrace]
  refine ⟨26654538698432902467439933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35539384931243869956586577 26654538698432902467439933)
  ·
    refine ⟨9995452011912338425289975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26654538698432902467439933 9995452011912338425289975)
    ·
      refine ⟨14993178017868507637934963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9995452011912338425289975 14993178017868507637934963)
      ·
        refine ⟨22489767026802761456902445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14993178017868507637934963 22489767026802761456902445)
        ·
          refine ⟨8433662635051035546338417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22489767026802761456902445 8433662635051035546338417)
          ·
            refine ⟨6325246976288276659753813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8433662635051035546338417 6325246976288276659753813)
            ·
              refine ⟨37061994001689121053245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6325246976288276659753813 37061994001689121053245)
              ·
                rfl

theorem cell21_1461604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 9].length) (baseStart_1461604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461604 prefixEnd_1461604 := by exact prefixLift 1461604
  have htrace : WordTrace (prefixWord ++ tailWord_1461604) baseStart_1461604 baseEnd_1461604 := by
    simpa [prefixWord, tailWord_1461604, baseEnd_1461604] using wordTrace_append hprefix tailTrace_1461604
  have hstable : (prefixWord ++ tailWord_1461604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461604).length < 2 ^ (prefixWord ++ tailWord_1461604).sum := by decide
  have hdescent : baseEnd_1461604 < baseStart_1461604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461610 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 5]
def baseStart_1461610 : Nat := 118140960795 + 1461610 * 2 ^ 59
def prefixEnd_1461610 : Nat := 4983230072969 + 3 ^ 40 * 1461610 * 2
def baseEnd_1461610 : Nat := 333559315296947412379193

theorem tailTrace_1461610 : CollatzResearch.WordTrace tailWord_1461610 prefixEnd_1461610 333559315296947412379193 := by
  unfold tailWord_1461610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13327324058711016989899571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35539530823229378639732189 13327324058711016989899571)
  ·
    refine ⟨19990986088066525484849357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13327324058711016989899571 19990986088066525484849357)
    ·
      refine ⟨7496619783024947056818509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19990986088066525484849357 7496619783024947056818509)
      ·
        refine ⟨2811232418634355146306941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7496619783024947056818509 2811232418634355146306941)
        ·
          refine ⟨1054212156987883179865103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2811232418634355146306941 1054212156987883179865103)
          ·
            refine ⟨1581318235481824769797655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054212156987883179865103 1581318235481824769797655)
            ·
              refine ⟨2371977353222737154696483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581318235481824769797655 2371977353222737154696483)
              ·
                refine ⟨3557966029834105732044725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371977353222737154696483 3557966029834105732044725)
                ·
                  refine ⟨333559315296947412379193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3557966029834105732044725 333559315296947412379193)
                  ·
                    rfl

theorem cell21_1461610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_1461610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461610 prefixEnd_1461610 := by exact prefixLift 1461610
  have htrace : WordTrace (prefixWord ++ tailWord_1461610) baseStart_1461610 baseEnd_1461610 := by
    simpa [prefixWord, tailWord_1461610, baseEnd_1461610] using wordTrace_append hprefix tailTrace_1461610
  have hstable : (prefixWord ++ tailWord_1461610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461610).length < 2 ^ (prefixWord ++ tailWord_1461610).sum := by decide
  have hdescent : baseEnd_1461610 < baseStart_1461610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461762 : List Nat := [3, 4, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1461762 : Nat := 118140960795 + 1461762 * 2 ^ 59
def prefixEnd_1461762 : Nat := 4983230072969 + 3 ^ 40 * 1461762 * 2
def baseEnd_1461762 : Nat := 333594003767828925845549

theorem tailTrace_1461762 : CollatzResearch.WordTrace tailWord_1461762 prefixEnd_1461762 333594003767828925845549 := by
  unfold tailWord_1461762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13328710032573349479782885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35543226753528931946087693 13328710032573349479782885)
  ·
    refine ⟨2499133131107503027459291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13328710032573349479782885 2499133131107503027459291)
    ·
      refine ⟨3748699696661254541188937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2499133131107503027459291 3748699696661254541188937)
      ·
        refine ⟨2811524772495940905891703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3748699696661254541188937 2811524772495940905891703)
        ·
          refine ⟨4217287158743911358837555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2811524772495940905891703 4217287158743911358837555)
          ·
            refine ⟨6325930738115867038256333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4217287158743911358837555 6325930738115867038256333)
            ·
              refine ⟨2372224026793450139346125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6325930738115867038256333 2372224026793450139346125)
              ·
                refine ⟨889584010047543802254797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2372224026793450139346125 889584010047543802254797)
                ·
                  refine ⟨333594003767828925845549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889584010047543802254797 333594003767828925845549)
                  ·
                    rfl

theorem cell21_1461762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1461762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461762 prefixEnd_1461762 := by exact prefixLift 1461762
  have htrace : WordTrace (prefixWord ++ tailWord_1461762) baseStart_1461762 baseEnd_1461762 := by
    simpa [prefixWord, tailWord_1461762, baseEnd_1461762] using wordTrace_append hprefix tailTrace_1461762
  have hstable : (prefixWord ++ tailWord_1461762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461762).length < 2 ^ (prefixWord ++ tailWord_1461762).sum := by decide
  have hdescent : baseEnd_1461762 < baseStart_1461762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461911 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 4]
def baseStart_1461911 : Nat := 118140960795 + 1461911 * 2 ^ 59
def prefixEnd_1461911 : Nat := 4983230072969 + 3 ^ 40 * 1461911 * 2
def baseEnd_1461911 : Nat := 333628007597837777861911

theorem tailTrace_1461911 : CollatzResearch.WordTrace tailWord_1461911 prefixEnd_1461911 333628007597837777861911 := by
  unfold tailWord_1461911
  simp only [CollatzResearch.WordTrace]
  refine ⟨53320274606753596366305587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35546849737835730910870391 53320274606753596366305587)
  ·
    refine ⟨79980411910130394549458381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53320274606753596366305587 79980411910130394549458381)
    ·
      refine ⟨29992654466298897956046893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79980411910130394549458381 29992654466298897956046893)
      ·
        refine ⟨11247245424862086733517585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29992654466298897956046893 11247245424862086733517585)
        ·
          refine ⟨8435434068646565050138189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11247245424862086733517585 8435434068646565050138189)
          ·
            refine ⟨3163287775742461893801821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8435434068646565050138189 3163287775742461893801821)
            ·
              refine ⟨1186232915903423210175683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3163287775742461893801821 1186232915903423210175683)
              ·
                refine ⟨1779349373855134815263525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186232915903423210175683 1779349373855134815263525)
                ·
                  refine ⟨333628007597837777861911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779349373855134815263525 333628007597837777861911)
                  ·
                    rfl

theorem cell21_1461911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 4].length) (baseStart_1461911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461911 prefixEnd_1461911 := by exact prefixLift 1461911
  have htrace : WordTrace (prefixWord ++ tailWord_1461911) baseStart_1461911 baseEnd_1461911 := by
    simpa [prefixWord, tailWord_1461911, baseEnd_1461911] using wordTrace_append hprefix tailTrace_1461911
  have hstable : (prefixWord ++ tailWord_1461911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461911).length < 2 ^ (prefixWord ++ tailWord_1461911).sum := by decide
  have hdescent : baseEnd_1461911 < baseStart_1461911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461942 : List Nat := [5, 1, 3, 1, 1, 3, 7]
def baseStart_1461942 : Nat := 118140960795 + 1461942 * 2 ^ 59
def prefixEnd_1461942 : Nat := 4983230072969 + 3 ^ 40 * 1461942 * 2
def baseEnd_1461942 : Nat := 37070564691132068093909

theorem tailTrace_1461942 : CollatzResearch.WordTrace tailWord_1461942 prefixEnd_1461942 37070564691132068093909 := by
  unfold tailWord_1461942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3332587829352580541292755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35547603513094192440456053 3332587829352580541292755)
  ·
    refine ⟨4998881744028870811939133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3332587829352580541292755 4998881744028870811939133)
    ·
      refine ⟨1874580654010826554477175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4998881744028870811939133 1874580654010826554477175)
      ·
        refine ⟨2811870981016239831715763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874580654010826554477175 2811870981016239831715763)
        ·
          refine ⟨4217806471524359747573645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2811870981016239831715763 4217806471524359747573645)
          ·
            refine ⟨1581677426821634905340117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4217806471524359747573645 1581677426821634905340117)
            ·
              refine ⟨37070564691132068093909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1581677426821634905340117 37070564691132068093909)
              ·
                rfl

theorem cell21_1461942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 7].length) (baseStart_1461942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1461942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1461942 prefixEnd_1461942 := by exact prefixLift 1461942
  have htrace : WordTrace (prefixWord ++ tailWord_1461942) baseStart_1461942 baseEnd_1461942 := by
    simpa [prefixWord, tailWord_1461942, baseEnd_1461942] using wordTrace_append hprefix tailTrace_1461942
  have hstable : (prefixWord ++ tailWord_1461942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461942).length < 2 ^ (prefixWord ++ tailWord_1461942).sum := by decide
  have hdescent : baseEnd_1461942 < baseStart_1461942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462004 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1462004 : Nat := 118140960795 + 1462004 * 2 ^ 59
def prefixEnd_1462004 : Nat := 4983230072969 + 3 ^ 40 * 1462004 * 2
def baseEnd_1462004 : Nat := 333649231464890282811721

theorem tailTrace_1462004 : CollatzResearch.WordTrace tailWord_1462004 prefixEnd_1462004 333649231464890282811721 := by
  unfold tailWord_1462004
  simp only [CollatzResearch.WordTrace]
  refine ⟨26661833297708336624720533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35549111063611115499627377 26661833297708336624720533)
  ·
    refine ⟨1249773435830078279283775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26661833297708336624720533 1249773435830078279283775)
    ·
      refine ⟨1874660153745117418925663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1249773435830078279283775 1874660153745117418925663)
      ·
        refine ⟨2811990230617676128388495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874660153745117418925663 2811990230617676128388495)
        ·
          refine ⟨4217985345926514192582743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2811990230617676128388495 4217985345926514192582743)
          ·
            refine ⟨6326978018889771288874115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4217985345926514192582743 6326978018889771288874115)
            ·
              refine ⟨9490467028334656933311173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6326978018889771288874115 9490467028334656933311173)
              ·
                refine ⟨1779462567812748174995845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9490467028334656933311173 1779462567812748174995845)
                ·
                  refine ⟨333649231464890282811721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779462567812748174995845 333649231464890282811721)
                  ·
                    rfl

theorem cell21_1462004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1462004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462004 prefixEnd_1462004 := by exact prefixLift 1462004
  have htrace : WordTrace (prefixWord ++ tailWord_1462004) baseStart_1462004 baseEnd_1462004 := by
    simpa [prefixWord, tailWord_1462004, baseEnd_1462004] using wordTrace_append hprefix tailTrace_1462004
  have hstable : (prefixWord ++ tailWord_1462004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462004).length < 2 ^ (prefixWord ++ tailWord_1462004).sum := by decide
  have hdescent : baseEnd_1462004 < baseStart_1462004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462243 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 5]
def baseStart_1462243 : Nat := 118140960795 + 1462243 * 2 ^ 59
def prefixEnd_1462243 : Nat := 4983230072969 + 3 ^ 40 * 1462243 * 2
def baseEnd_1462243 : Nat := 333703774521078978327899

theorem tailTrace_1462243 : CollatzResearch.WordTrace tailWord_1462243 prefixEnd_1462243 333703774521078978327899 := by
  unfold tailWord_1462243
  simp only [CollatzResearch.WordTrace]
  refine ⟨53332383641550817067391383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35554922427700544711594255 53332383641550817067391383)
  ·
    refine ⟨79998575462326225601087075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53332383641550817067391383 79998575462326225601087075)
    ·
      refine ⟨119997863193489338401630613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79998575462326225601087075 119997863193489338401630613)
      ·
        refine ⟨5624899837194812737576435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119997863193489338401630613 5624899837194812737576435)
        ·
          refine ⟨8437349755792219106364653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624899837194812737576435 8437349755792219106364653)
          ·
            refine ⟨3164006158422082164886745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8437349755792219106364653 3164006158422082164886745)
            ·
              refine ⟨2373004618816561623665059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3164006158422082164886745 2373004618816561623665059)
              ·
                refine ⟨3559506928224842435497589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373004618816561623665059 3559506928224842435497589)
                ·
                  refine ⟨333703774521078978327899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3559506928224842435497589 333703774521078978327899)
                  ·
                    rfl

theorem cell21_1462243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 5].length) (baseStart_1462243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462243 prefixEnd_1462243 := by exact prefixLift 1462243
  have htrace : WordTrace (prefixWord ++ tailWord_1462243) baseStart_1462243 baseEnd_1462243 := by
    simpa [prefixWord, tailWord_1462243, baseEnd_1462243] using wordTrace_append hprefix tailTrace_1462243
  have hstable : (prefixWord ++ tailWord_1462243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462243).length < 2 ^ (prefixWord ++ tailWord_1462243).sum := by decide
  have hdescent : baseEnd_1462243 < baseStart_1462243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462308 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1462308 : Nat := 118140960795 + 1462308 * 2 ^ 59
def prefixEnd_1462308 : Nat := 4983230072969 + 3 ^ 40 * 1462308 * 2
def baseEnd_1462308 : Nat := 333718608406653309744433

theorem tailTrace_1462308 : CollatzResearch.WordTrace tailWord_1462308 prefixEnd_1462308 333718608406653309744433 := by
  unfold tailWord_1462308
  simp only [CollatzResearch.WordTrace]
  refine ⟨26667377193157666584253789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35556502924210222112338385 26667377193157666584253789)
  ·
    refine ⟨10000266447434124969095171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26667377193157666584253789 10000266447434124969095171)
    ·
      refine ⟨15000399671151187453642757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10000266447434124969095171 15000399671151187453642757)
      ·
        refine ⟨2812574938340847647558017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15000399671151187453642757 2812574938340847647558017)
        ·
          refine ⟨2109431203755635735668513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2812574938340847647558017 2109431203755635735668513)
          ·
            refine ⟨1582073402816726801751385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2109431203755635735668513 1582073402816726801751385)
            ·
              refine ⟨1186555052112545101313539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1582073402816726801751385 1186555052112545101313539)
              ·
                refine ⟨1779832578168817651970309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186555052112545101313539 1779832578168817651970309)
                ·
                  refine ⟨333718608406653309744433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779832578168817651970309 333718608406653309744433)
                  ·
                    rfl

theorem cell21_1462308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1462308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462308 prefixEnd_1462308 := by exact prefixLift 1462308
  have htrace : WordTrace (prefixWord ++ tailWord_1462308) baseStart_1462308 baseEnd_1462308 := by
    simpa [prefixWord, tailWord_1462308, baseEnd_1462308] using wordTrace_append hprefix tailTrace_1462308
  have hstable : (prefixWord ++ tailWord_1462308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462308).length < 2 ^ (prefixWord ++ tailWord_1462308).sum := by decide
  have hdescent : baseEnd_1462308 < baseStart_1462308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462316 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_1462316 : Nat := 118140960795 + 1462316 * 2 ^ 59
def prefixEnd_1462316 : Nat := 4983230072969 + 3 ^ 40 * 1462316 * 2
def baseEnd_1462316 : Nat := 333720434115647073611083

theorem tailTrace_1462316 : CollatzResearch.WordTrace tailWord_1462316 prefixEnd_1462316 333720434115647073611083 := by
  unfold tailWord_1462316
  simp only [CollatzResearch.WordTrace]
  refine ⟨26667523085143175267399401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35556697446857567023199201 26667523085143175267399401)
  ·
    refine ⟨20000642313857381450549551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26667523085143175267399401 20000642313857381450549551)
    ·
      refine ⟨30000963470786072175824327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20000642313857381450549551 30000963470786072175824327)
      ·
        refine ⟨45001445206179108263736491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30000963470786072175824327 45001445206179108263736491)
        ·
          refine ⟨67502167809268662395604737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45001445206179108263736491 67502167809268662395604737)
          ·
            refine ⟨50626625856951496796703553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67502167809268662395604737 50626625856951496796703553)
            ·
              refine ⟨37969969392713622597527665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50626625856951496796703553 37969969392713622597527665)
              ·
                refine ⟨28477477044535216948145749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37969969392713622597527665 28477477044535216948145749)
                ·
                  refine ⟨333720434115647073611083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28477477044535216948145749 333720434115647073611083)
                  ·
                    rfl

theorem cell21_1462316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_1462316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462316 prefixEnd_1462316 := by exact prefixLift 1462316
  have htrace : WordTrace (prefixWord ++ tailWord_1462316) baseStart_1462316 baseEnd_1462316 := by
    simpa [prefixWord, tailWord_1462316, baseEnd_1462316] using wordTrace_append hprefix tailTrace_1462316
  have hstable : (prefixWord ++ tailWord_1462316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462316).length < 2 ^ (prefixWord ++ tailWord_1462316).sum := by decide
  have hdescent : baseEnd_1462316 < baseStart_1462316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462350 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_1462350 : Nat := 118140960795 + 1462350 * 2 ^ 59
def prefixEnd_1462350 : Nat := 4983230072969 + 3 ^ 40 * 1462350 * 2
def baseEnd_1462350 : Nat := 333728193378870570044347

theorem tailTrace_1462350 : CollatzResearch.WordTrace tailWord_1462350 prefixEnd_1462350 333728193378870570044347 := by
  unfold tailWord_1462350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6667035781520396792692063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35557524168108782894357669 6667035781520396792692063)
  ·
    refine ⟨10000553672280595189038095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6667035781520396792692063 10000553672280595189038095)
    ·
      refine ⟨15000830508420892783557143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10000553672280595189038095 15000830508420892783557143)
      ·
        refine ⟨22501245762631339175335715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15000830508420892783557143 22501245762631339175335715)
        ·
          refine ⟨33751868643947008763003573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22501245762631339175335715 33751868643947008763003573)
          ·
            refine ⟨3164237685370032071531585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33751868643947008763003573 3164237685370032071531585)
            ·
              refine ⟨2373178264027524053648689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3164237685370032071531585 2373178264027524053648689)
              ·
                refine ⟨1779883698020643040236517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2373178264027524053648689 1779883698020643040236517)
                ·
                  refine ⟨333728193378870570044347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779883698020643040236517 333728193378870570044347)
                  ·
                    rfl

theorem cell21_1462350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_1462350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462350 prefixEnd_1462350 := by exact prefixLift 1462350
  have htrace : WordTrace (prefixWord ++ tailWord_1462350) baseStart_1462350 baseEnd_1462350 := by
    simpa [prefixWord, tailWord_1462350, baseEnd_1462350] using wordTrace_append hprefix tailTrace_1462350
  have hstable : (prefixWord ++ tailWord_1462350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462350).length < 2 ^ (prefixWord ++ tailWord_1462350).sum := by decide
  have hdescent : baseEnd_1462350 < baseStart_1462350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462364 : List Nat := [2, 2, 4, 1, 1, 2, 3, 6]
def baseStart_1462364 : Nat := 118140960795 + 1462364 * 2 ^ 59
def prefixEnd_1462364 : Nat := 4983230072969 + 3 ^ 40 * 1462364 * 2
def baseEnd_1462364 : Nat := 111243796123203218936995

theorem tailTrace_1462364 : CollatzResearch.WordTrace tailWord_1462364 prefixEnd_1462364 111243796123203218936995 := by
  unfold tailWord_1462364
  simp only [CollatzResearch.WordTrace]
  refine ⟨26668398437056227366273073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35557864582741636488364097 26668398437056227366273073)
  ·
    refine ⟨20001298827792170524704805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26668398437056227366273073 20001298827792170524704805)
    ·
      refine ⟨3750243530211031973382151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20001298827792170524704805 3750243530211031973382151)
      ·
        refine ⟨5625365295316547960073227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3750243530211031973382151 5625365295316547960073227)
        ·
          refine ⟨8438047942974821940109841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5625365295316547960073227 8438047942974821940109841)
          ·
            refine ⟨6328535957231116455082381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8438047942974821940109841 6328535957231116455082381)
            ·
              refine ⟨2373200983961668670655893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6328535957231116455082381 2373200983961668670655893)
              ·
                refine ⟨111243796123203218936995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2373200983961668670655893 111243796123203218936995)
                ·
                  rfl

theorem cell21_1462364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_1462364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462364 prefixEnd_1462364 := by exact prefixLift 1462364
  have htrace : WordTrace (prefixWord ++ tailWord_1462364) baseStart_1462364 baseEnd_1462364 := by
    simpa [prefixWord, tailWord_1462364, baseEnd_1462364] using wordTrace_append hprefix tailTrace_1462364
  have hstable : (prefixWord ++ tailWord_1462364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462364).length < 2 ^ (prefixWord ++ tailWord_1462364).sum := by decide
  have hdescent : baseEnd_1462364 < baseStart_1462364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462392 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_1462392 : Nat := 118140960795 + 1462392 * 2 ^ 59
def prefixEnd_1462392 : Nat := 4983230072969 + 3 ^ 40 * 1462392 * 2
def baseEnd_1462392 : Nat := 333737778351087830344261

theorem tailTrace_1462392 : CollatzResearch.WordTrace tailWord_1462392 prefixEnd_1462392 333737778351087830344261 := by
  unfold tailWord_1462392
  simp only [CollatzResearch.WordTrace]
  refine ⟨26668909059005507757282715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35558545412007343676376953 26668909059005507757282715)
  ·
    refine ⟨40003363588508261635924073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26668909059005507757282715 40003363588508261635924073)
    ·
      refine ⟨30002522691381196226943055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40003363588508261635924073 30002522691381196226943055)
      ·
        refine ⟨45003784037071794340414583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30002522691381196226943055 45003784037071794340414583)
        ·
          refine ⟨67505676055607691510621875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45003784037071794340414583 67505676055607691510621875)
          ·
            refine ⟨101258514083411537265932813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67505676055607691510621875 101258514083411537265932813)
            ·
              refine ⟨37971942781279326474724805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101258514083411537265932813 37971942781279326474724805)
              ·
                refine ⟨7119739271489873714010901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37971942781279326474724805 7119739271489873714010901)
                ·
                  refine ⟨333737778351087830344261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7119739271489873714010901 333737778351087830344261)
                  ·
                    rfl

theorem cell21_1462392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_1462392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462392 prefixEnd_1462392 := by exact prefixLift 1462392
  have htrace : WordTrace (prefixWord ++ tailWord_1462392) baseStart_1462392 baseEnd_1462392 := by
    simpa [prefixWord, tailWord_1462392, baseEnd_1462392] using wordTrace_append hprefix tailTrace_1462392
  have hstable : (prefixWord ++ tailWord_1462392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462392).length < 2 ^ (prefixWord ++ tailWord_1462392).sum := by decide
  have hdescent : baseEnd_1462392 < baseStart_1462392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462516 : List Nat := [2, 6, 1, 12]
def baseStart_1462516 : Nat := 118140960795 + 1462516 * 2 ^ 59
def prefixEnd_1462516 : Nat := 4983230072969 + 3 ^ 40 * 1462516 * 2
def baseEnd_1462516 : Nat := 1373522949960869013487

theorem tailTrace_1462516 : CollatzResearch.WordTrace tailWord_1462516 prefixEnd_1462516 1373522949960869013487 := by
  unfold tailWord_1462516
  simp only [CollatzResearch.WordTrace]
  refine ⟨26671170384780892346039701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35561560513041189794719601 26671170384780892346039701)
  ·
    refine ⟨1250211111786604328720611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26671170384780892346039701 1250211111786604328720611)
    ·
      refine ⟨1875316667679906493080917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250211111786604328720611 1875316667679906493080917)
      ·
        refine ⟨1373522949960869013487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1875316667679906493080917 1373522949960869013487)
        ·
          rfl

theorem cell21_1462516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 12].length) (baseStart_1462516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462516 prefixEnd_1462516 := by exact prefixLift 1462516
  have htrace : WordTrace (prefixWord ++ tailWord_1462516) baseStart_1462516 baseEnd_1462516 := by
    simpa [prefixWord, tailWord_1462516, baseEnd_1462516] using wordTrace_append hprefix tailTrace_1462516
  have hstable : (prefixWord ++ tailWord_1462516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462516).length < 2 ^ (prefixWord ++ tailWord_1462516).sum := by decide
  have hdescent : baseEnd_1462516 < baseStart_1462516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462564 : List Nat := [2, 3, 1, 3, 1, 3, 2, 3, 3]
def baseStart_1462564 : Nat := 118140960795 + 1462564 * 2 ^ 59
def prefixEnd_1462564 : Nat := 4983230072969 + 3 ^ 40 * 1462564 * 2
def baseEnd_1462564 : Nat := 333777031094453753477243

theorem tailTrace_1462564 : CollatzResearch.WordTrace tailWord_1462564 prefixEnd_1462564 333777031094453753477243 := by
  unfold tailWord_1462564
  simp only [CollatzResearch.WordTrace]
  refine ⟨26672045736693944444913373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35562727648925259259884497 26672045736693944444913373)
  ·
    refine ⟨10002017151260229166842515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26672045736693944444913373 10002017151260229166842515)
    ·
      refine ⟨15003025726890343750263773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10002017151260229166842515 15003025726890343750263773)
      ·
        refine ⟨5626134647583878906348915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15003025726890343750263773 5626134647583878906348915)
        ·
          refine ⟨8439201971375818359523373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626134647583878906348915 8439201971375818359523373)
          ·
            refine ⟨3164700739265931884821265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8439201971375818359523373 3164700739265931884821265)
            ·
              refine ⟨2373525554449448913615949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3164700739265931884821265 2373525554449448913615949)
              ·
                refine ⟨890072082918543342605981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2373525554449448913615949 890072082918543342605981)
                ·
                  refine ⟨333777031094453753477243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890072082918543342605981 333777031094453753477243)
                  ·
                    rfl

theorem cell21_1462564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_1462564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462564 prefixEnd_1462564 := by exact prefixLift 1462564
  have htrace : WordTrace (prefixWord ++ tailWord_1462564) baseStart_1462564 baseEnd_1462564 := by
    simpa [prefixWord, tailWord_1462564, baseEnd_1462564] using wordTrace_append hprefix tailTrace_1462564
  have hstable : (prefixWord ++ tailWord_1462564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462564).length < 2 ^ (prefixWord ++ tailWord_1462564).sum := by decide
  have hdescent : baseEnd_1462564 < baseStart_1462564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462623 : List Nat := [1, 1, 2, 3, 1, 2, 5, 3, 3]
def baseStart_1462623 : Nat := 118140960795 + 1462623 * 2 ^ 59
def prefixEnd_1462623 : Nat := 4983230072969 + 3 ^ 40 * 1462623 * 2
def baseEnd_1462623 : Nat := 333790495698282761993789

theorem tailTrace_1462623 : CollatzResearch.WordTrace tailWord_1462623 prefixEnd_1462623 333790495698282761993789 := by
  unfold tailWord_1462623
  simp only [CollatzResearch.WordTrace]
  refine ⟨53346243380174141966224523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35564162253449427977483015 53346243380174141966224523)
  ·
    refine ⟨80019365070261212949336785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53346243380174141966224523 80019365070261212949336785)
    ·
      refine ⟨60014523802695909712002589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80019365070261212949336785 60014523802695909712002589)
      ·
        refine ⟨22505446426010966142000971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60014523802695909712002589 22505446426010966142000971)
        ·
          refine ⟨33758169639016449213001457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22505446426010966142000971 33758169639016449213001457)
          ·
            refine ⟨25318627229262336909751093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33758169639016449213001457 25318627229262336909751093)
            ·
              refine ⟨2373621302743344085289165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25318627229262336909751093 2373621302743344085289165)
              ·
                refine ⟨890107988528754031983437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2373621302743344085289165 890107988528754031983437)
                ·
                  refine ⟨333790495698282761993789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890107988528754031983437 333790495698282761993789)
                  ·
                    rfl

theorem cell21_1462623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 3].length) (baseStart_1462623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462623 prefixEnd_1462623 := by exact prefixLift 1462623
  have htrace : WordTrace (prefixWord ++ tailWord_1462623) baseStart_1462623 baseEnd_1462623 := by
    simpa [prefixWord, tailWord_1462623, baseEnd_1462623] using wordTrace_append hprefix tailTrace_1462623
  have hstable : (prefixWord ++ tailWord_1462623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462623).length < 2 ^ (prefixWord ++ tailWord_1462623).sum := by decide
  have hdescent : baseEnd_1462623 < baseStart_1462623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462637 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1462637 : Nat := 118140960795 + 1462637 * 2 ^ 59
def prefixEnd_1462637 : Nat := 4983230072969 + 3 ^ 40 * 1462637 * 2
def baseEnd_1462637 : Nat := 333793690689021848760427

theorem tailTrace_1462637 : CollatzResearch.WordTrace tailWord_1462637 prefixEnd_1462637 333793690689021848760427 := by
  unfold tailWord_1462637
  simp only [CollatzResearch.WordTrace]
  refine ⟨53346754002123422357234165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35564502668082281571489443 53346754002123422357234165)
  ·
    refine ⟨5001258187699070845990703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53346754002123422357234165 5001258187699070845990703)
    ·
      refine ⟨7501887281548606268986055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5001258187699070845990703 7501887281548606268986055)
      ·
        refine ⟨11252830922322909403479083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7501887281548606268986055 11252830922322909403479083)
        ·
          refine ⟨16879246383484364105218625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11252830922322909403479083 16879246383484364105218625)
          ·
            refine ⟨12659434787613273078913969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16879246383484364105218625 12659434787613273078913969)
            ·
              refine ⟨9494576090709954809185477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12659434787613273078913969 9494576090709954809185477)
              ·
                refine ⟨1780233017008116526722277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9494576090709954809185477 1780233017008116526722277)
                ·
                  refine ⟨333793690689021848760427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1780233017008116526722277 333793690689021848760427)
                  ·
                    rfl

theorem cell21_1462637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1462637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462637 prefixEnd_1462637 := by exact prefixLift 1462637
  have htrace : WordTrace (prefixWord ++ tailWord_1462637) baseStart_1462637 baseEnd_1462637 := by
    simpa [prefixWord, tailWord_1462637, baseEnd_1462637] using wordTrace_append hprefix tailTrace_1462637
  have hstable : (prefixWord ++ tailWord_1462637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462637).length < 2 ^ (prefixWord ++ tailWord_1462637).sum := by decide
  have hdescent : baseEnd_1462637 < baseStart_1462637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462640 : List Nat := [2, 1, 1, 1, 4, 4, 3, 2, 3]
def baseStart_1462640 : Nat := 118140960795 + 1462640 * 2 ^ 59
def prefixEnd_1462640 : Nat := 4983230072969 + 3 ^ 40 * 1462640 * 2
def baseEnd_1462640 : Nat := 333794375329894510210421

theorem tailTrace_1462640 : CollatzResearch.WordTrace tailWord_1462640 prefixEnd_1462640 333794375329894510210421 := by
  unfold tailWord_1462640
  simp only [CollatzResearch.WordTrace]
  refine ⟨26673431710556276934796687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35564575614075035913062249 26673431710556276934796687)
  ·
    refine ⟨40010147565834415402195031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26673431710556276934796687 40010147565834415402195031)
    ·
      refine ⟨60015221348751623103292547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40010147565834415402195031 60015221348751623103292547)
      ·
        refine ⟨90022832023127434654938821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60015221348751623103292547 90022832023127434654938821)
        ·
          refine ⟨16879281004336393997801029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90022832023127434654938821 16879281004336393997801029)
          ·
            refine ⟨3164865188313073874587693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16879281004336393997801029 3164865188313073874587693)
            ·
              refine ⟨1186824445617402702970385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3164865188313073874587693 1186824445617402702970385)
              ·
                refine ⟨890118334213052027227789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186824445617402702970385 890118334213052027227789)
                ·
                  refine ⟨333794375329894510210421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890118334213052027227789 333794375329894510210421)
                  ·
                    rfl

theorem cell21_1462640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 3].length) (baseStart_1462640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462640 prefixEnd_1462640 := by exact prefixLift 1462640
  have htrace : WordTrace (prefixWord ++ tailWord_1462640) baseStart_1462640 baseEnd_1462640 := by
    simpa [prefixWord, tailWord_1462640, baseEnd_1462640] using wordTrace_append hprefix tailTrace_1462640
  have hstable : (prefixWord ++ tailWord_1462640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462640).length < 2 ^ (prefixWord ++ tailWord_1462640).sum := by decide
  have hdescent : baseEnd_1462640 < baseStart_1462640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462651 : List Nat := [1, 1, 1, 1, 1, 8, 2, 6]
def baseStart_1462651 : Nat := 118140960795 + 1462651 * 2 ^ 59
def prefixEnd_1462651 : Nat := 4983230072969 + 3 ^ 40 * 1462651 * 2
def baseEnd_1462651 : Nat := 111265628559920311842355

theorem tailTrace_1462651 : CollatzResearch.WordTrace tailWord_1462651 prefixEnd_1462651 111265628559920311842355 := by
  unfold tailWord_1462651
  simp only [CollatzResearch.WordTrace]
  refine ⟨53347264624072702748243807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35564843082715135165495871 53347264624072702748243807)
  ·
    refine ⟨80020896936109054122365711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53347264624072702748243807 80020896936109054122365711)
    ·
      refine ⟨120031345404163581183548567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80020896936109054122365711 120031345404163581183548567)
      ·
        refine ⟨180047018106245371775322851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120031345404163581183548567 180047018106245371775322851)
        ·
          refine ⟨270070527159368057662984277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180047018106245371775322851 270070527159368057662984277)
          ·
            refine ⟨3164888990148844425738097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 270070527159368057662984277 3164888990148844425738097)
            ·
              refine ⟨2373666742611633319303573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3164888990148844425738097 2373666742611633319303573)
              ·
                refine ⟨111265628559920311842355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2373666742611633319303573 111265628559920311842355)
                ·
                  rfl

theorem cell21_1462651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 6].length) (baseStart_1462651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462651 prefixEnd_1462651 := by exact prefixLift 1462651
  have htrace : WordTrace (prefixWord ++ tailWord_1462651) baseStart_1462651 baseEnd_1462651 := by
    simpa [prefixWord, tailWord_1462651, baseEnd_1462651] using wordTrace_append hprefix tailTrace_1462651
  have hstable : (prefixWord ++ tailWord_1462651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462651).length < 2 ^ (prefixWord ++ tailWord_1462651).sum := by decide
  have hdescent : baseEnd_1462651 < baseStart_1462651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462713 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 4]
def baseStart_1462713 : Nat := 118140960795 + 1462713 * 2 ^ 59
def prefixEnd_1462713 : Nat := 4983230072969 + 3 ^ 40 * 1462713 * 2
def baseEnd_1462713 : Nat := 333811034924462605493605

theorem tailTrace_1462713 : CollatzResearch.WordTrace tailWord_1462713 prefixEnd_1462713 333811034924462605493605 := by
  unfold tailWord_1462713
  simp only [CollatzResearch.WordTrace]
  refine ⟨53349525949848087337000793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35566350633232058224667195 53349525949848087337000793)
  ·
    refine ⟨40012144462386065502750595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53349525949848087337000793 40012144462386065502750595)
    ·
      refine ⟨60018216693579098254125893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40012144462386065502750595 60018216693579098254125893)
      ·
        refine ⟨11253415630046080922648605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60018216693579098254125893 11253415630046080922648605)
        ·
          refine ⟨4220030861267280345993227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11253415630046080922648605 4220030861267280345993227)
          ·
            refine ⟨6330046291900920518989841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220030861267280345993227 6330046291900920518989841)
            ·
              refine ⟨4747534718925690389242381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6330046291900920518989841 4747534718925690389242381)
              ·
                refine ⟨1780325519597133895965893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4747534718925690389242381 1780325519597133895965893)
                ·
                  refine ⟨333811034924462605493605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1780325519597133895965893 333811034924462605493605)
                  ·
                    rfl

theorem cell21_1462713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_1462713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462713 prefixEnd_1462713 := by exact prefixLift 1462713
  have htrace : WordTrace (prefixWord ++ tailWord_1462713) baseStart_1462713 baseEnd_1462713 := by
    simpa [prefixWord, tailWord_1462713, baseEnd_1462713] using wordTrace_append hprefix tailTrace_1462713
  have hstable : (prefixWord ++ tailWord_1462713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462713).length < 2 ^ (prefixWord ++ tailWord_1462713).sum := by decide
  have hdescent : baseEnd_1462713 < baseStart_1462713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462823 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 4]
def baseStart_1462823 : Nat := 118140960795 + 1462823 * 2 ^ 59
def prefixEnd_1462823 : Nat := 4983230072969 + 3 ^ 40 * 1462823 * 2
def baseEnd_1462823 : Nat := 333836138423126858660047

theorem tailTrace_1462823 : CollatzResearch.WordTrace tailWord_1462823 prefixEnd_1462823 333836138423126858660047 := by
  unfold tailWord_1462823
  simp only [CollatzResearch.WordTrace]
  refine ⟨53353537979449576123505123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35569025319633050749003415 53353537979449576123505123)
  ·
    refine ⟨80030306969174364185257685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53353537979449576123505123 80030306969174364185257685)
    ·
      refine ⟨1875710319590024160591977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 80030306969174364185257685 1875710319590024160591977)
      ·
        refine ⟨1406782739692518120443983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1875710319590024160591977 1406782739692518120443983)
        ·
          refine ⟨2110174109538777180665975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406782739692518120443983 2110174109538777180665975)
          ·
            refine ⟨3165261164308165770998963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110174109538777180665975 3165261164308165770998963)
            ·
              refine ⟨4747891746462248656498445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3165261164308165770998963 4747891746462248656498445)
              ·
                refine ⟨1780459404923343246186917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4747891746462248656498445 1780459404923343246186917)
                ·
                  refine ⟨333836138423126858660047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1780459404923343246186917 333836138423126858660047)
                  ·
                    rfl

theorem cell21_1462823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 4].length) (baseStart_1462823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462823 prefixEnd_1462823 := by exact prefixLift 1462823
  have htrace : WordTrace (prefixWord ++ tailWord_1462823) baseStart_1462823 baseEnd_1462823 := by
    simpa [prefixWord, tailWord_1462823, baseEnd_1462823] using wordTrace_append hprefix tailTrace_1462823
  have hstable : (prefixWord ++ tailWord_1462823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462823).length < 2 ^ (prefixWord ++ tailWord_1462823).sum := by decide
  have hdescent : baseEnd_1462823 < baseStart_1462823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462865 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 4]
def baseStart_1462865 : Nat := 118140960795 + 1462865 * 2 ^ 59
def prefixEnd_1462865 : Nat := 4983230072969 + 3 ^ 40 * 1462865 * 2
def baseEnd_1462865 : Nat := 333845723395344118959961

theorem tailTrace_1462865 : CollatzResearch.WordTrace tailWord_1462865 prefixEnd_1462865 333845723395344118959961 := by
  unfold tailWord_1462865
  simp only [CollatzResearch.WordTrace]
  refine ⟨53355069845297417296534049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35570046563531611531022699 53355069845297417296534049)
  ·
    refine ⟨40016302383973062972400537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53355069845297417296534049 40016302383973062972400537)
    ·
      refine ⟨30012226787979797229300403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40016302383973062972400537 30012226787979797229300403)
      ·
        refine ⟨45018340181969695843950605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30012226787979797229300403 45018340181969695843950605)
        ·
          refine ⟨16881877568238635941481477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45018340181969695843950605 16881877568238635941481477)
          ·
            refine ⟨3165352044044744239027777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16881877568238635941481477 3165352044044744239027777)
            ·
              refine ⟨2374014033033558179270833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3165352044044744239027777 2374014033033558179270833)
              ·
                refine ⟨1780510524775168634453125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2374014033033558179270833 1780510524775168634453125)
                ·
                  refine ⟨333845723395344118959961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1780510524775168634453125 333845723395344118959961)
                  ·
                    rfl

theorem cell21_1462865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_1462865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462865 prefixEnd_1462865 := by exact prefixLift 1462865
  have htrace : WordTrace (prefixWord ++ tailWord_1462865) baseStart_1462865 baseEnd_1462865 := by
    simpa [prefixWord, tailWord_1462865, baseEnd_1462865] using wordTrace_append hprefix tailTrace_1462865
  have hstable : (prefixWord ++ tailWord_1462865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462865).length < 2 ^ (prefixWord ++ tailWord_1462865).sum := by decide
  have hdescent : baseEnd_1462865 < baseStart_1462865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462868 : List Nat := [2, 4, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1462868 : Nat := 118140960795 + 1462868 * 2 ^ 59
def prefixEnd_1462868 : Nat := 4983230072969 + 3 ^ 40 * 1462868 * 2
def baseEnd_1462868 : Nat := 333846408036216780409955

theorem tailTrace_1462868 : CollatzResearch.WordTrace tailWord_1462868 prefixEnd_1462868 333846408036216780409955 := by
  unfold tailWord_1462868
  simp only [CollatzResearch.WordTrace]
  refine ⟨26677589632143274404446629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35570119509524365872595505 26677589632143274404446629)
  ·
    refine ⟨5002048056026863950833743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26677589632143274404446629 5002048056026863950833743)
    ·
      refine ⟨7503072084040295926250615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5002048056026863950833743 7503072084040295926250615)
      ·
        refine ⟨11254608126060443889375923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7503072084040295926250615 11254608126060443889375923)
        ·
          refine ⟨16881912189090665834063885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11254608126060443889375923 16881912189090665834063885)
          ·
            refine ⟨6330717070908999687773957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16881912189090665834063885 6330717070908999687773957)
            ·
              refine ⟨1187009450795437441457617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6330717070908999687773957 1187009450795437441457617)
              ·
                refine ⟨890257088096578081093213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1187009450795437441457617 890257088096578081093213)
                ·
                  refine ⟨333846408036216780409955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890257088096578081093213 333846408036216780409955)
                  ·
                    rfl

theorem cell21_1462868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1462868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462868 prefixEnd_1462868 := by exact prefixLift 1462868
  have htrace : WordTrace (prefixWord ++ tailWord_1462868) baseStart_1462868 baseEnd_1462868 := by
    simpa [prefixWord, tailWord_1462868, baseEnd_1462868] using wordTrace_append hprefix tailTrace_1462868
  have hstable : (prefixWord ++ tailWord_1462868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462868).length < 2 ^ (prefixWord ++ tailWord_1462868).sum := by decide
  have hdescent : baseEnd_1462868 < baseStart_1462868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462896 : List Nat := [2, 1, 1, 1, 7, 1, 3, 5]
def baseStart_1462896 : Nat := 118140960795 + 1462896 * 2 ^ 59
def prefixEnd_1462896 : Nat := 4983230072969 + 3 ^ 40 * 1462896 * 2
def baseEnd_1462896 : Nat := 111284266005898317981077

theorem tailTrace_1462896 : CollatzResearch.WordTrace tailWord_1462896 prefixEnd_1462896 111284266005898317981077 := by
  unfold tailWord_1462896
  simp only [CollatzResearch.WordTrace]
  refine ⟨26678100254092554795456271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35570800338790073060608361 26678100254092554795456271)
  ·
    refine ⟨40017150381138832193184407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26678100254092554795456271 40017150381138832193184407)
    ·
      refine ⟨60025725571708248289776611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40017150381138832193184407 60025725571708248289776611)
      ·
        refine ⟨90038588357562372434664917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60025725571708248289776611 90038588357562372434664917)
        ·
          refine ⟨2110279414630368103937459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 90038588357562372434664917 2110279414630368103937459)
          ·
            refine ⟨3165419121945552155906189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110279414630368103937459 3165419121945552155906189)
            ·
              refine ⟨1187032170729582058464821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3165419121945552155906189 1187032170729582058464821)
              ·
                refine ⟨111284266005898317981077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1187032170729582058464821 111284266005898317981077)
                ·
                  rfl

theorem cell21_1462896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_1462896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462896 prefixEnd_1462896 := by exact prefixLift 1462896
  have htrace : WordTrace (prefixWord ++ tailWord_1462896) baseStart_1462896 baseEnd_1462896 := by
    simpa [prefixWord, tailWord_1462896, baseEnd_1462896] using wordTrace_append hprefix tailTrace_1462896
  have hstable : (prefixWord ++ tailWord_1462896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462896).length < 2 ^ (prefixWord ++ tailWord_1462896).sum := by decide
  have hdescent : baseEnd_1462896 < baseStart_1462896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462924 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 4]
def baseStart_1462924 : Nat := 118140960795 + 1462924 * 2 ^ 59
def prefixEnd_1462924 : Nat := 4983230072969 + 3 ^ 40 * 1462924 * 2
def baseEnd_1462924 : Nat := 333859187999173127476507

theorem tailTrace_1462924 : CollatzResearch.WordTrace tailWord_1462924 prefixEnd_1462924 333859187999173127476507 := by
  unfold tailWord_1462924
  simp only [CollatzResearch.WordTrace]
  refine ⟨26678610876041835186465913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35571481168055780248621217 26678610876041835186465913)
  ·
    refine ⟨20008958157031376389849435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26678610876041835186465913 20008958157031376389849435)
    ·
      refine ⟨30013437235547064584774153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20008958157031376389849435 30013437235547064584774153)
      ·
        refine ⟨22510077926660298438580615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30013437235547064584774153 22510077926660298438580615)
        ·
          refine ⟨33765116889990447657870923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22510077926660298438580615 33765116889990447657870923)
          ·
            refine ⟨50647675334985671486806385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33765116889990447657870923 50647675334985671486806385)
            ·
              refine ⟨37985756501239253615104789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50647675334985671486806385 37985756501239253615104789)
              ·
                refine ⟨1780582335995590013208037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37985756501239253615104789 1780582335995590013208037)
                ·
                  refine ⟨333859187999173127476507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1780582335995590013208037 333859187999173127476507)
                  ·
                    rfl

theorem cell21_1462924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_1462924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462924 prefixEnd_1462924 := by exact prefixLift 1462924
  have htrace : WordTrace (prefixWord ++ tailWord_1462924) baseStart_1462924 baseEnd_1462924 := by
    simpa [prefixWord, tailWord_1462924, baseEnd_1462924] using wordTrace_append hprefix tailTrace_1462924
  have hstable : (prefixWord ++ tailWord_1462924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462924).length < 2 ^ (prefixWord ++ tailWord_1462924).sum := by decide
  have hdescent : baseEnd_1462924 < baseStart_1462924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462961 : List Nat := [1, 2, 2, 6, 1, 2, 1, 3, 3]
def baseStart_1462961 : Nat := 118140960795 + 1462961 * 2 ^ 59
def prefixEnd_1462961 : Nat := 4983230072969 + 3 ^ 40 * 1462961 * 2
def baseEnd_1462961 : Nat := 333867631903269285359765

theorem tailTrace_1462961 : CollatzResearch.WordTrace tailWord_1462961 prefixEnd_1462961 333867631903269285359765 := by
  unfold tailWord_1462961
  simp only [CollatzResearch.WordTrace]
  refine ⟨53358571252949625692028737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35572380835299750461352491 53358571252949625692028737)
  ·
    refine ⟨40018928439712219269021553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53358571252949625692028737 40018928439712219269021553)
    ·
      refine ⟨30014196329784164451766165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40018928439712219269021553 30014196329784164451766165)
      ·
        refine ⟨1406915452958632708676539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30014196329784164451766165 1406915452958632708676539)
        ·
          refine ⟨2110373179437949063014809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406915452958632708676539 2110373179437949063014809)
          ·
            refine ⟨1582779884578461797261107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2110373179437949063014809 1582779884578461797261107)
            ·
              refine ⟨2374169826867692695891661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582779884578461797261107 2374169826867692695891661)
              ·
                refine ⟨890313685075384760959373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2374169826867692695891661 890313685075384760959373)
                ·
                  refine ⟨333867631903269285359765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890313685075384760959373 333867631903269285359765)
                  ·
                    rfl

theorem cell21_1462961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 3].length) (baseStart_1462961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462961 prefixEnd_1462961 := by exact prefixLift 1462961
  have htrace : WordTrace (prefixWord ++ tailWord_1462961) baseStart_1462961 baseEnd_1462961 := by
    simpa [prefixWord, tailWord_1462961, baseEnd_1462961] using wordTrace_append hprefix tailTrace_1462961
  have hstable : (prefixWord ++ tailWord_1462961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462961).length < 2 ^ (prefixWord ++ tailWord_1462961).sum := by decide
  have hdescent : baseEnd_1462961 < baseStart_1462961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462986 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_1462986 : Nat := 118140960795 + 1462986 * 2 ^ 59
def prefixEnd_1462986 : Nat := 4983230072969 + 3 ^ 40 * 1462986 * 2
def baseEnd_1462986 : Nat := 333873337243874797443047

theorem tailTrace_1462986 : CollatzResearch.WordTrace tailWord_1462986 prefixEnd_1462986 333873337243874797443047 := by
  unfold tailWord_1462986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13339870769464763740422203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35572988718572703307792541 13339870769464763740422203)
  ·
    refine ⟨20009806154197145610633305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13339870769464763740422203 20009806154197145610633305)
    ·
      refine ⟨15007354615647859207974979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20009806154197145610633305 15007354615647859207974979)
      ·
        refine ⟨22511031923471788811962469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15007354615647859207974979 22511031923471788811962469)
        ·
          refine ⟨4220818485650960402242963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22511031923471788811962469 4220818485650960402242963)
          ·
            refine ⟨6331227728476440603364445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220818485650960402242963 6331227728476440603364445)
            ·
              refine ⟨2374210398178665226261667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6331227728476440603364445 2374210398178665226261667)
              ·
                refine ⟨3561315597267997839392501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374210398178665226261667 3561315597267997839392501)
                ·
                  refine ⟨333873337243874797443047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3561315597267997839392501 333873337243874797443047)
                  ·
                    rfl

theorem cell21_1462986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_1462986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462986 prefixEnd_1462986 := by exact prefixLift 1462986
  have htrace : WordTrace (prefixWord ++ tailWord_1462986) baseStart_1462986 baseEnd_1462986 := by
    simpa [prefixWord, tailWord_1462986, baseEnd_1462986] using wordTrace_append hprefix tailTrace_1462986
  have hstable : (prefixWord ++ tailWord_1462986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462986).length < 2 ^ (prefixWord ++ tailWord_1462986).sum := by decide
  have hdescent : baseEnd_1462986 < baseStart_1462986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462989 : List Nat := [1, 6, 2, 1, 2, 1, 2, 6]
def baseStart_1462989 : Nat := 118140960795 + 1462989 * 2 ^ 59
def prefixEnd_1462989 : Nat := 4983230072969 + 3 ^ 40 * 1462989 * 2
def baseEnd_1462989 : Nat := 111291340628249152964347

theorem tailTrace_1462989 : CollatzResearch.WordTrace tailWord_1462989 prefixEnd_1462989 111291340628249152964347 := by
  unfold tailWord_1462989
  simp only [CollatzResearch.WordTrace]
  refine ⟨53359592496848186474048021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35573061664565457649365347 53359592496848186474048021)
  ·
    refine ⟨2501230898289758740971001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53359592496848186474048021 2501230898289758740971001)
    ·
      refine ⟨1875923173717319055728251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2501230898289758740971001 1875923173717319055728251)
      ·
        refine ⟨2813884760575978583592377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875923173717319055728251 2813884760575978583592377)
        ·
          refine ⟨2110413570431983937694283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2813884760575978583592377 2110413570431983937694283)
          ·
            refine ⟨3165620355647975906541425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110413570431983937694283 3165620355647975906541425)
            ·
              refine ⟨2374215266735981929906069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3165620355647975906541425 2374215266735981929906069)
              ·
                refine ⟨111291340628249152964347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2374215266735981929906069 111291340628249152964347)
                ·
                  rfl

theorem cell21_1462989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 6].length) (baseStart_1462989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1462989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1462989 prefixEnd_1462989 := by exact prefixLift 1462989
  have htrace : WordTrace (prefixWord ++ tailWord_1462989) baseStart_1462989 baseEnd_1462989 := by
    simpa [prefixWord, tailWord_1462989, baseEnd_1462989] using wordTrace_append hprefix tailTrace_1462989
  have hstable : (prefixWord ++ tailWord_1462989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462989).length < 2 ^ (prefixWord ++ tailWord_1462989).sum := by decide
  have hdescent : baseEnd_1462989 < baseStart_1462989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463090 : List Nat := [3, 2, 1, 1, 3, 1, 10]
def baseStart_1463090 : Nat := 118140960795 + 1463090 * 2 ^ 59
def prefixEnd_1463090 : Nat := 4983230072969 + 3 ^ 40 * 1463090 * 2
def baseEnd_1463090 : Nat := 37099674606754858634389

theorem tailTrace_1463090 : CollatzResearch.WordTrace tailWord_1463090 prefixEnd_1463090 37099674606754858634389 := by
  unfold tailWord_1463090
  simp only [CollatzResearch.WordTrace]
  refine ⟨13340819067370570180868681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35575517512988187148983149 13340819067370570180868681)
  ·
    refine ⟨10005614300527927635651511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13340819067370570180868681 10005614300527927635651511)
    ·
      refine ⟨15008421450791891453477267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10005614300527927635651511 15008421450791891453477267)
      ·
        refine ⟨22512632176187837180215901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15008421450791891453477267 22512632176187837180215901)
        ·
          refine ⟨8442237066070438942580963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22512632176187837180215901 8442237066070438942580963)
          ·
            refine ⟨12663355599105658413871445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8442237066070438942580963 12663355599105658413871445)
            ·
              refine ⟨37099674606754858634389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12663355599105658413871445 37099674606754858634389)
              ·
                rfl

theorem cell21_1463090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 10].length) (baseStart_1463090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463090 prefixEnd_1463090 := by exact prefixLift 1463090
  have htrace : WordTrace (prefixWord ++ tailWord_1463090) baseStart_1463090 baseEnd_1463090 := by
    simpa [prefixWord, tailWord_1463090, baseEnd_1463090] using wordTrace_append hprefix tailTrace_1463090
  have hstable : (prefixWord ++ tailWord_1463090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463090).length < 2 ^ (prefixWord ++ tailWord_1463090).sum := by decide
  have hdescent : baseEnd_1463090 < baseStart_1463090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463093 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 4]
def baseStart_1463093 : Nat := 118140960795 + 1463093 * 2 ^ 59
def prefixEnd_1463093 : Nat := 4983230072969 + 3 ^ 40 * 1463093 * 2
def baseEnd_1463093 : Nat := 333897756101666389159495

theorem tailTrace_1463093 : CollatzResearch.WordTrace tailWord_1463093 prefixEnd_1463093 333897756101666389159495 := by
  unfold tailWord_1463093
  simp only [CollatzResearch.WordTrace]
  refine ⟨53363385688471412235833933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35575590458980941490555955 53363385688471412235833933)
  ·
    refine ⟨20011269633176779588437725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53363385688471412235833933 20011269633176779588437725)
    ·
      refine ⟨7504226112441292345664147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20011269633176779588437725 7504226112441292345664147)
      ·
        refine ⟨11256339168661938518496221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7504226112441292345664147 11256339168661938518496221)
        ·
          refine ⟨4221127188248226944436083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11256339168661938518496221 4221127188248226944436083)
          ·
            refine ⟨6331690782372340416654125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221127188248226944436083 6331690782372340416654125)
            ·
              refine ⟨2374384043389627656245297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6331690782372340416654125 2374384043389627656245297)
              ·
                refine ⟨1780788032542220742183973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2374384043389627656245297 1780788032542220742183973)
                ·
                  refine ⟨333897756101666389159495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1780788032542220742183973 333897756101666389159495)
                  ·
                    rfl

theorem cell21_1463093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_1463093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463093 prefixEnd_1463093 := by exact prefixLift 1463093
  have htrace : WordTrace (prefixWord ++ tailWord_1463093) baseStart_1463093 baseEnd_1463093 := by
    simpa [prefixWord, tailWord_1463093, baseEnd_1463093] using wordTrace_append hprefix tailTrace_1463093
  have hstable : (prefixWord ++ tailWord_1463093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463093).length < 2 ^ (prefixWord ++ tailWord_1463093).sum := by decide
  have hdescent : baseEnd_1463093 < baseStart_1463093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463135 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 8]
def baseStart_1463135 : Nat := 118140960795 + 1463135 * 2 ^ 59
def prefixEnd_1463135 : Nat := 4983230072969 + 3 ^ 40 * 1463135 * 2
def baseEnd_1463135 : Nat := 333907341073883649459409

theorem tailTrace_1463135 : CollatzResearch.WordTrace tailWord_1463135 prefixEnd_1463135 333907341073883649459409 := by
  unfold tailWord_1463135
  simp only [CollatzResearch.WordTrace]
  refine ⟨53364917554319253408862859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35576611702879502272575239 53364917554319253408862859)
  ·
    refine ⟨80047376331478880113294289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53364917554319253408862859 80047376331478880113294289)
    ·
      refine ⟨60035532248609160084970717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80047376331478880113294289 60035532248609160084970717)
      ·
        refine ⟨22513324593228435031864019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60035532248609160084970717 22513324593228435031864019)
        ·
          refine ⟨33769986889842652547796029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22513324593228435031864019 33769986889842652547796029)
          ·
            refine ⟨12663745083690994705423511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33769986889842652547796029 12663745083690994705423511)
            ·
              refine ⟨18995617625536492058135267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12663745083690994705423511 18995617625536492058135267)
              ·
                refine ⟨28493426438304738087202901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18995617625536492058135267 28493426438304738087202901)
                ·
                  refine ⟨333907341073883649459409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28493426438304738087202901 333907341073883649459409)
                  ·
                    rfl

theorem cell21_1463135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_1463135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463135 prefixEnd_1463135 := by exact prefixLift 1463135
  have htrace : WordTrace (prefixWord ++ tailWord_1463135) baseStart_1463135 baseEnd_1463135 := by
    simpa [prefixWord, tailWord_1463135, baseEnd_1463135] using wordTrace_append hprefix tailTrace_1463135
  have hstable : (prefixWord ++ tailWord_1463135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463135).length < 2 ^ (prefixWord ++ tailWord_1463135).sum := by decide
  have hdescent : baseEnd_1463135 < baseStart_1463135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463307 : List Nat := [1, 1, 1, 1, 6, 4, 1, 3, 3]
def baseStart_1463307 : Nat := 118140960795 + 1463307 * 2 ^ 59
def prefixEnd_1463307 : Nat := 4983230072969 + 3 ^ 40 * 1463307 * 2
def baseEnd_1463307 : Nat := 333946593817249572592391

theorem tailTrace_1463307 : CollatzResearch.WordTrace tailWord_1463307 prefixEnd_1463307 333946593817249572592391 := by
  unfold tailWord_1463307
  simp only [CollatzResearch.WordTrace]
  refine ⟨53371190909696126784124175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35580793939797417856082783 53371190909696126784124175)
  ·
    refine ⟨80056786364544190176186263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53371190909696126784124175 80056786364544190176186263)
    ·
      refine ⟨120085179546816285264279395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80056786364544190176186263 120085179546816285264279395)
      ·
        refine ⟨180127769320224427896419093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120085179546816285264279395 180127769320224427896419093)
        ·
          refine ⟨8443489186885520057644645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 180127769320224427896419093 8443489186885520057644645)
          ·
            refine ⟨1583154222541035010808371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8443489186885520057644645 1583154222541035010808371)
            ·
              refine ⟨2374731333811552516212557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583154222541035010808371 2374731333811552516212557)
              ·
                refine ⟨890524250179332193579709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2374731333811552516212557 890524250179332193579709)
                ·
                  refine ⟨333946593817249572592391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890524250179332193579709 333946593817249572592391)
                  ·
                    rfl

theorem cell21_1463307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 3].length) (baseStart_1463307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463307 prefixEnd_1463307 := by exact prefixLift 1463307
  have htrace : WordTrace (prefixWord ++ tailWord_1463307) baseStart_1463307 baseEnd_1463307 := by
    simpa [prefixWord, tailWord_1463307, baseEnd_1463307] using wordTrace_append hprefix tailTrace_1463307
  have hstable : (prefixWord ++ tailWord_1463307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463307).length < 2 ^ (prefixWord ++ tailWord_1463307).sum := by decide
  have hdescent : baseEnd_1463307 < baseStart_1463307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463324 : List Nat := [2, 2, 3, 1, 4, 1, 3, 2, 3]
def baseStart_1463324 : Nat := 118140960795 + 1463324 * 2 ^ 59
def prefixEnd_1463324 : Nat := 4983230072969 + 3 ^ 40 * 1463324 * 2
def baseEnd_1463324 : Nat := 333950473448861320809023

theorem tailTrace_1463324 : CollatzResearch.WordTrace tailWord_1463324 prefixEnd_1463324 333950473448861320809023 := by
  unfold tailWord_1463324
  simp only [CollatzResearch.WordTrace]
  refine ⟨26685905475317269343746513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35581207300423025791662017 26685905475317269343746513)
  ·
    refine ⟨20014429106487952007809885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26685905475317269343746513 20014429106487952007809885)
    ·
      refine ⟨7505410914932982002928707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20014429106487952007809885 7505410914932982002928707)
      ·
        refine ⟨11258116372399473004393061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7505410914932982002928707 11258116372399473004393061)
        ·
          refine ⟨2110896819824901188323699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11258116372399473004393061 2110896819824901188323699)
          ·
            refine ⟨3166345229737351782485549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110896819824901188323699 3166345229737351782485549)
            ·
              refine ⟨1187379461151506918432081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3166345229737351782485549 1187379461151506918432081)
              ·
                refine ⟨890534595863630188824061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1187379461151506918432081 890534595863630188824061)
                ·
                  refine ⟨333950473448861320809023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890534595863630188824061 333950473448861320809023)
                  ·
                    rfl

theorem cell21_1463324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_1463324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463324 prefixEnd_1463324 := by exact prefixLift 1463324
  have htrace : WordTrace (prefixWord ++ tailWord_1463324) baseStart_1463324 baseEnd_1463324 := by
    simpa [prefixWord, tailWord_1463324, baseEnd_1463324] using wordTrace_append hprefix tailTrace_1463324
  have hstable : (prefixWord ++ tailWord_1463324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463324).length < 2 ^ (prefixWord ++ tailWord_1463324).sum := by decide
  have hdescent : baseEnd_1463324 < baseStart_1463324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463335 : List Nat := [1, 1, 7, 1, 1, 1, 1, 8]
def baseStart_1463335 : Nat := 118140960795 + 1463335 * 2 ^ 59
def prefixEnd_1463335 : Nat := 4983230072969 + 3 ^ 40 * 1463335 * 2
def baseEnd_1463335 : Nat := 111317661266242582041889

theorem tailTrace_1463335 : CollatzResearch.WordTrace tailWord_1463335 prefixEnd_1463335 111317661266242582041889 := by
  unfold tailWord_1463335
  simp only [CollatzResearch.WordTrace]
  refine ⟨53372212153594687566143459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35581474769063125044095639 53372212153594687566143459)
  ·
    refine ⟨80058318230392031349215189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53372212153594687566143459 80058318230392031349215189)
    ·
      refine ⟨1876366833524813234747231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 80058318230392031349215189 1876366833524813234747231)
      ·
        refine ⟨2814550250287219852120847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876366833524813234747231 2814550250287219852120847)
        ·
          refine ⟨4221825375430829778181271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2814550250287219852120847 4221825375430829778181271)
          ·
            refine ⟨6332738063146244667271907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221825375430829778181271 6332738063146244667271907)
            ·
              refine ⟨9499107094719367000907861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6332738063146244667271907 9499107094719367000907861)
              ·
                refine ⟨111317661266242582041889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9499107094719367000907861 111317661266242582041889)
                ·
                  rfl

theorem cell21_1463335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 8].length) (baseStart_1463335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463335 prefixEnd_1463335 := by exact prefixLift 1463335
  have htrace : WordTrace (prefixWord ++ tailWord_1463335) baseStart_1463335 baseEnd_1463335 := by
    simpa [prefixWord, tailWord_1463335, baseEnd_1463335] using wordTrace_append hprefix tailTrace_1463335
  have hstable : (prefixWord ++ tailWord_1463335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463335).length < 2 ^ (prefixWord ++ tailWord_1463335).sum := by decide
  have hdescent : baseEnd_1463335 < baseStart_1463335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463380 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1463380 : Nat := 118140960795 + 1463380 * 2 ^ 59
def prefixEnd_1463380 : Nat := 4983230072969 + 3 ^ 40 * 1463380 * 2
def baseEnd_1463380 : Nat := 333963253411817667875575

theorem tailTrace_1463380 : CollatzResearch.WordTrace tailWord_1463380 prefixEnd_1463380 333963253411817667875575 := by
  unfold tailWord_1463380
  simp only [CollatzResearch.WordTrace]
  refine ⟨26686926719215830125765797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35582568958954440167687729 26686926719215830125765797)
  ·
    refine ⟨5003798759852968148581087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26686926719215830125765797 5003798759852968148581087)
    ·
      refine ⟨7505698139779452222871631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5003798759852968148581087 7505698139779452222871631)
      ·
        refine ⟨11258547209669178334307447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7505698139779452222871631 11258547209669178334307447)
        ·
          refine ⟨16887820814503767501461171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11258547209669178334307447 16887820814503767501461171)
          ·
            refine ⟨25331731221755651252191757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16887820814503767501461171 25331731221755651252191757)
            ·
              refine ⟨9499399208158369219571909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25331731221755651252191757 9499399208158369219571909)
              ·
                refine ⟨1781137351529694228669733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9499399208158369219571909 1781137351529694228669733)
                ·
                  refine ⟨333963253411817667875575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781137351529694228669733 333963253411817667875575)
                  ·
                    rfl

theorem cell21_1463380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1463380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463380 prefixEnd_1463380 := by exact prefixLift 1463380
  have htrace : WordTrace (prefixWord ++ tailWord_1463380) baseStart_1463380 baseEnd_1463380 := by
    simpa [prefixWord, tailWord_1463380, baseEnd_1463380] using wordTrace_append hprefix tailTrace_1463380
  have hstable : (prefixWord ++ tailWord_1463380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463380).length < 2 ^ (prefixWord ++ tailWord_1463380).sum := by decide
  have hdescent : baseEnd_1463380 < baseStart_1463380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463442 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1463442 : Nat := 118140960795 + 1463442 * 2 ^ 59
def prefixEnd_1463442 : Nat := 4983230072969 + 3 ^ 40 * 1463442 * 2
def baseEnd_1463442 : Nat := 333977402656519337842115

theorem tailTrace_1463442 : CollatzResearch.WordTrace tailWord_1463442 prefixEnd_1463442 333977402656519337842115 := by
  unfold tailWord_1463442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13344028691051761210072145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35584076509471363226859053 13344028691051761210072145)
  ·
    refine ⟨10008021518288820907554109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13344028691051761210072145 10008021518288820907554109)
    ·
      refine ⟨3753008069358307840332791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10008021518288820907554109 3753008069358307840332791)
      ·
        refine ⟨5629512104037461760499187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3753008069358307840332791 5629512104037461760499187)
        ·
          refine ⟨8444268156056192640748781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5629512104037461760499187 8444268156056192640748781)
          ·
            refine ⟨3166600558521072240280793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8444268156056192640748781 3166600558521072240280793)
            ·
              refine ⟨2374950418890804180210595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3166600558521072240280793 2374950418890804180210595)
              ·
                refine ⟨3562425628336206270315893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374950418890804180210595 3562425628336206270315893)
                ·
                  refine ⟨333977402656519337842115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3562425628336206270315893 333977402656519337842115)
                  ·
                    rfl

theorem cell21_1463442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1463442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463442 prefixEnd_1463442 := by exact prefixLift 1463442
  have htrace : WordTrace (prefixWord ++ tailWord_1463442) baseStart_1463442 baseEnd_1463442 := by
    simpa [prefixWord, tailWord_1463442, baseEnd_1463442] using wordTrace_append hprefix tailTrace_1463442
  have hstable : (prefixWord ++ tailWord_1463442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463442).length < 2 ^ (prefixWord ++ tailWord_1463442).sum := by decide
  have hdescent : baseEnd_1463442 < baseStart_1463442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463639 : List Nat := [1, 1, 3, 2, 3, 4, 2, 5]
def baseStart_1463639 : Nat := 118140960795 + 1463639 * 2 ^ 59
def prefixEnd_1463639 : Nat := 4983230072969 + 3 ^ 40 * 1463639 * 2
def baseEnd_1463639 : Nat := 111340786913496924352793

theorem tailTrace_1463639 : CollatzResearch.WordTrace tailWord_1463639 prefixEnd_1463639 111340786913496924352793 := by
  unfold tailWord_1463639
  simp only [CollatzResearch.WordTrace]
  refine ⟨53383299944493347485209971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35588866629662231656806647 53383299944493347485209971)
  ·
    refine ⟨80074949916740021227814957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53383299944493347485209971 80074949916740021227814957)
    ·
      refine ⟨30028106218777507960430609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80074949916740021227814957 30028106218777507960430609)
      ·
        refine ⟨22521079664083130970322957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30028106218777507960430609 22521079664083130970322957)
        ·
          refine ⟨8445404874031174113871109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22521079664083130970322957 8445404874031174113871109)
          ·
            refine ⟨1583513413880845146350833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8445404874031174113871109 1583513413880845146350833)
            ·
              refine ⟨1187635060410633859763125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1583513413880845146350833 1187635060410633859763125)
              ·
                refine ⟨111340786913496924352793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1187635060410633859763125 111340786913496924352793)
                ·
                  rfl

theorem cell21_1463639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 5].length) (baseStart_1463639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463639 prefixEnd_1463639 := by exact prefixLift 1463639
  have htrace : WordTrace (prefixWord ++ tailWord_1463639) baseStart_1463639 baseEnd_1463639 := by
    simpa [prefixWord, tailWord_1463639, baseEnd_1463639] using wordTrace_append hprefix tailTrace_1463639
  have hstable : (prefixWord ++ tailWord_1463639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463639).length < 2 ^ (prefixWord ++ tailWord_1463639).sum := by decide
  have hdescent : baseEnd_1463639 < baseStart_1463639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463684 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 4]
def baseStart_1463684 : Nat := 118140960795 + 1463684 * 2 ^ 59
def prefixEnd_1463684 : Nat := 4983230072969 + 3 ^ 40 * 1463684 * 2
def baseEnd_1463684 : Nat := 334032630353580694808287

theorem tailTrace_1463684 : CollatzResearch.WordTrace tailWord_1463684 prefixEnd_1463684 334032630353580694808287 := by
  unfold tailWord_1463684
  simp only [CollatzResearch.WordTrace]
  refine ⟨26692470614665160085299053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35589960819553546780398737 26692470614665160085299053)
  ·
    refine ⟨10009676480499435031987145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26692470614665160085299053 10009676480499435031987145)
    ·
      refine ⟨7507257360374576273990359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10009676480499435031987145 7507257360374576273990359)
      ·
        refine ⟨11260886040561864410985539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7507257360374576273990359 11260886040561864410985539)
        ·
          refine ⟨16891329060842796616478309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11260886040561864410985539 16891329060842796616478309)
          ·
            refine ⟨3167124198908024365589683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16891329060842796616478309 3167124198908024365589683)
            ·
              refine ⟨4750686298362036548384525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167124198908024365589683 4750686298362036548384525)
              ·
                refine ⟨1781507361885763705644197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4750686298362036548384525 1781507361885763705644197)
                ·
                  refine ⟨334032630353580694808287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781507361885763705644197 334032630353580694808287)
                  ·
                    rfl

theorem cell21_1463684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_1463684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463684 prefixEnd_1463684 := by exact prefixLift 1463684
  have htrace : WordTrace (prefixWord ++ tailWord_1463684) baseStart_1463684 baseEnd_1463684 := by
    simpa [prefixWord, tailWord_1463684, baseEnd_1463684] using wordTrace_append hprefix tailTrace_1463684
  have hstable : (prefixWord ++ tailWord_1463684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463684).length < 2 ^ (prefixWord ++ tailWord_1463684).sum := by decide
  have hdescent : baseEnd_1463684 < baseStart_1463684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463814 : List Nat := [6, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1463814 : Nat := 118140960795 + 1463814 * 2 ^ 59
def prefixEnd_1463814 : Nat := 4983230072969 + 3 ^ 40 * 1463814 * 2
def baseEnd_1463814 : Nat := 334062298124729357641355

theorem tailTrace_1463814 : CollatzResearch.WordTrace tailWord_1463814 prefixEnd_1463814 334062298124729357641355 := by
  unfold tailWord_1463814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668427584964354761650953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35593121812572901581886997 1668427584964354761650953)
  ·
    refine ⟨1251320688723266071238215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1668427584964354761650953 1251320688723266071238215)
    ·
      refine ⟨1876981033084899106857323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1251320688723266071238215 1876981033084899106857323)
      ·
        refine ⟨2815471549627348660285985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876981033084899106857323 2815471549627348660285985)
        ·
          refine ⟨2111603662220511495214489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2815471549627348660285985 2111603662220511495214489)
          ·
            refine ⟨1583702746665383621410867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2111603662220511495214489 1583702746665383621410867)
            ·
              refine ⟨2375554119998075432116301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583702746665383621410867 2375554119998075432116301)
              ·
                refine ⟨890832794999278287043613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2375554119998075432116301 890832794999278287043613)
                ·
                  refine ⟨334062298124729357641355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890832794999278287043613 334062298124729357641355)
                  ·
                    rfl

theorem cell21_1463814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1463814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463814 prefixEnd_1463814 := by exact prefixLift 1463814
  have htrace : WordTrace (prefixWord ++ tailWord_1463814) baseStart_1463814 baseEnd_1463814 := by
    simpa [prefixWord, tailWord_1463814, baseEnd_1463814] using wordTrace_append hprefix tailTrace_1463814
  have hstable : (prefixWord ++ tailWord_1463814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463814).length < 2 ^ (prefixWord ++ tailWord_1463814).sum := by decide
  have hdescent : baseEnd_1463814 < baseStart_1463814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463850 : List Nat := [3, 1, 4, 1, 1, 1, 4, 6]
def baseStart_1463850 : Nat := 118140960795 + 1463850 * 2 ^ 59
def prefixEnd_1463850 : Nat := 4983230072969 + 3 ^ 40 * 1463850 * 2
def baseEnd_1463850 : Nat := 111356837938400431680427

theorem tailTrace_1463850 : CollatzResearch.WordTrace tailWord_1463850 prefixEnd_1463850 111356837938400431680427 := by
  unfold tailWord_1463850
  simp only [CollatzResearch.WordTrace]
  refine ⟨13347748936682232630285251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35593997164485953680760669 13347748936682232630285251)
  ·
    refine ⟨20021623405023348945427877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13347748936682232630285251 20021623405023348945427877)
    ·
      refine ⟨3754054388441877927267727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20021623405023348945427877 3754054388441877927267727)
      ·
        refine ⟨5631081582662816890901591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3754054388441877927267727 5631081582662816890901591)
        ·
          refine ⟨8446622373994225336352387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631081582662816890901591 8446622373994225336352387)
          ·
            refine ⟨12669933560991338004528581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8446622373994225336352387 12669933560991338004528581)
            ·
              refine ⟨2375612542685875875849109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12669933560991338004528581 2375612542685875875849109)
              ·
                refine ⟨111356837938400431680427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2375612542685875875849109 111356837938400431680427)
                ·
                  rfl

theorem cell21_1463850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_1463850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463850 prefixEnd_1463850 := by exact prefixLift 1463850
  have htrace : WordTrace (prefixWord ++ tailWord_1463850) baseStart_1463850 baseEnd_1463850 := by
    simpa [prefixWord, tailWord_1463850, baseEnd_1463850] using wordTrace_append hprefix tailTrace_1463850
  have hstable : (prefixWord ++ tailWord_1463850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463850).length < 2 ^ (prefixWord ++ tailWord_1463850).sum := by decide
  have hdescent : baseEnd_1463850 < baseStart_1463850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463895 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 4]
def baseStart_1463895 : Nat := 118140960795 + 1463895 * 2 ^ 59
def prefixEnd_1463895 : Nat := 4983230072969 + 3 ^ 40 * 1463895 * 2
def baseEnd_1463895 : Nat := 334080783428291216791189

theorem tailTrace_1463895 : CollatzResearch.WordTrace tailWord_1463895 prefixEnd_1463895 334080783428291216791189 := by
  unfold tailWord_1463895
  simp only [CollatzResearch.WordTrace]
  refine ⟨53392637031565903206529139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35595091354377268804352759 53392637031565903206529139)
  ·
    refine ⟨80088955547348854809793709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53392637031565903206529139 80088955547348854809793709)
    ·
      refine ⟨30033358330255820553672641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80088955547348854809793709 30033358330255820553672641)
      ·
        refine ⟨22525018747691865415254481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30033358330255820553672641 22525018747691865415254481)
        ·
          refine ⟨16893764060768899061440861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22525018747691865415254481 16893764060768899061440861)
          ·
            refine ⟨6335161522788337148040323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16893764060768899061440861 6335161522788337148040323)
            ·
              refine ⟨9502742284182505722060485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6335161522788337148040323 9502742284182505722060485)
              ·
                refine ⟨1781764178284219822886341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9502742284182505722060485 1781764178284219822886341)
                ·
                  refine ⟨334080783428291216791189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781764178284219822886341 334080783428291216791189)
                  ·
                    rfl

theorem cell21_1463895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 4].length) (baseStart_1463895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463895 prefixEnd_1463895 := by exact prefixLift 1463895
  have htrace : WordTrace (prefixWord ++ tailWord_1463895) baseStart_1463895 baseEnd_1463895 := by
    simpa [prefixWord, tailWord_1463895, baseEnd_1463895] using wordTrace_append hprefix tailTrace_1463895
  have hstable : (prefixWord ++ tailWord_1463895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463895).length < 2 ^ (prefixWord ++ tailWord_1463895).sum := by decide
  have hdescent : baseEnd_1463895 < baseStart_1463895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463901 : List Nat := [1, 4, 4, 2, 2, 1, 1, 6]
def baseStart_1463901 : Nat := 118140960795 + 1463901 * 2 ^ 59
def prefixEnd_1463901 : Nat := 4983230072969 + 3 ^ 40 * 1463901 * 2
def baseEnd_1463901 : Nat := 111360717570012179897059

theorem tailTrace_1463901 : CollatzResearch.WordTrace tailWord_1463901 prefixEnd_1463901 111360717570012179897059 := by
  unfold tailWord_1463901
  simp only [CollatzResearch.WordTrace]
  refine ⟨53392855869544166231247557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35595237246362777487498371 53392855869544166231247557)
  ·
    refine ⟨10011160475539531168358917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53392855869544166231247557 10011160475539531168358917)
    ·
      refine ⟨1877092589163662094067297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10011160475539531168358917 1877092589163662094067297)
      ·
        refine ⟨1407819441872746570550473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1877092589163662094067297 1407819441872746570550473)
        ·
          refine ⟨1055864581404559927912855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1407819441872746570550473 1055864581404559927912855)
          ·
            refine ⟨1583796872106839891869283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055864581404559927912855 1583796872106839891869283)
            ·
              refine ⟨2375695308160259837803925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583796872106839891869283 2375695308160259837803925)
              ·
                refine ⟨111360717570012179897059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2375695308160259837803925 111360717570012179897059)
                ·
                  rfl

theorem cell21_1463901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 6].length) (baseStart_1463901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463901 prefixEnd_1463901 := by exact prefixLift 1463901
  have htrace : WordTrace (prefixWord ++ tailWord_1463901) baseStart_1463901 baseEnd_1463901 := by
    simpa [prefixWord, tailWord_1463901, baseEnd_1463901] using wordTrace_append hprefix tailTrace_1463901
  have hstable : (prefixWord ++ tailWord_1463901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463901).length < 2 ^ (prefixWord ++ tailWord_1463901).sum := by decide
  have hdescent : baseEnd_1463901 < baseStart_1463901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463912 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 4]
def baseStart_1463912 : Nat := 118140960795 + 1463912 * 2 ^ 59
def prefixEnd_1463912 : Nat := 4983230072969 + 3 ^ 40 * 1463912 * 2
def baseEnd_1463912 : Nat := 334084663059902965007821

theorem tailTrace_1463912 : CollatzResearch.WordTrace tailWord_1463912 prefixEnd_1463912 334084663059902965007821 := by
  unfold tailWord_1463912
  simp only [CollatzResearch.WordTrace]
  refine ⟨26696628536252157554948995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35595504715002876739931993 26696628536252157554948995)
  ·
    refine ⟨40044942804378236332423493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26696628536252157554948995 40044942804378236332423493)
    ·
      refine ⟨7508426775820919312329405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40044942804378236332423493 7508426775820919312329405)
      ·
        refine ⟨2815660040932844742123527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7508426775820919312329405 2815660040932844742123527)
        ·
          refine ⟨4223490061399267113185291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815660040932844742123527 4223490061399267113185291)
          ·
            refine ⟨6335235092098900669777937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223490061399267113185291 6335235092098900669777937)
            ·
              refine ⟨4751426319074175502333453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6335235092098900669777937 4751426319074175502333453)
              ·
                refine ⟨1781784869652815813375045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4751426319074175502333453 1781784869652815813375045)
                ·
                  refine ⟨334084663059902965007821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781784869652815813375045 334084663059902965007821)
                  ·
                    rfl

theorem cell21_1463912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_1463912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1463912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1463912 prefixEnd_1463912 := by exact prefixLift 1463912
  have htrace : WordTrace (prefixWord ++ tailWord_1463912) baseStart_1463912 baseEnd_1463912 := by
    simpa [prefixWord, tailWord_1463912, baseEnd_1463912] using wordTrace_append hprefix tailTrace_1463912
  have hstable : (prefixWord ++ tailWord_1463912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463912).length < 2 ^ (prefixWord ++ tailWord_1463912).sum := by decide
  have hdescent : baseEnd_1463912 < baseStart_1463912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464022 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1464022 : Nat := 118140960795 + 1464022 * 2 ^ 59
def prefixEnd_1464022 : Nat := 4983230072969 + 3 ^ 40 * 1464022 * 2
def baseEnd_1464022 : Nat := 334109766558567218174263

theorem tailTrace_1464022 : CollatzResearch.WordTrace tailWord_1464022 prefixEnd_1464022 334109766558567218174263 := by
  unfold tailWord_1464022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3337329318881612743525145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35598179401403869264268213 3337329318881612743525145)
  ·
    refine ⟨2502996989161209557643859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3337329318881612743525145 2502996989161209557643859)
    ·
      refine ⟨3754495483741814336465789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2502996989161209557643859 3754495483741814336465789)
      ·
        refine ⟨1407935806403180376174671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3754495483741814336465789 1407935806403180376174671)
        ·
          refine ⟨2111903709604770564262007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407935806403180376174671 2111903709604770564262007)
          ·
            refine ⟨3167855564407155846393011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111903709604770564262007 3167855564407155846393011)
            ·
              refine ⟨4751783346610733769589517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167855564407155846393011 4751783346610733769589517)
              ·
                refine ⟨1781918754979025163596069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4751783346610733769589517 1781918754979025163596069)
                ·
                  refine ⟨334109766558567218174263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781918754979025163596069 334109766558567218174263)
                  ·
                    rfl

theorem cell21_1464022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1464022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464022 prefixEnd_1464022 := by exact prefixLift 1464022
  have htrace : WordTrace (prefixWord ++ tailWord_1464022) baseStart_1464022 baseEnd_1464022 := by
    simpa [prefixWord, tailWord_1464022, baseEnd_1464022] using wordTrace_append hprefix tailTrace_1464022
  have hstable : (prefixWord ++ tailWord_1464022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464022).length < 2 ^ (prefixWord ++ tailWord_1464022).sum := by decide
  have hdescent : baseEnd_1464022 < baseStart_1464022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464092 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_1464092 : Nat := 118140960795 + 1464092 * 2 ^ 59
def prefixEnd_1464092 : Nat := 4983230072969 + 3 ^ 40 * 1464092 * 2
def baseEnd_1464092 : Nat := 334125741512262652007453

theorem tailTrace_1464092 : CollatzResearch.WordTrace tailWord_1464092 prefixEnd_1464092 334125741512262652007453 := by
  unfold tailWord_1464092
  simp only [CollatzResearch.WordTrace]
  refine ⟨26699911105926102925725265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35599881474568137234300353 26699911105926102925725265)
  ·
    refine ⟨20024933329444577194293949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26699911105926102925725265 20024933329444577194293949)
    ·
      refine ⟨7509349998541716447860231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20024933329444577194293949 7509349998541716447860231)
      ·
        refine ⟨11264024997812574671790347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7509349998541716447860231 11264024997812574671790347)
        ·
          refine ⟨16896037496718862007685521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11264024997812574671790347 16896037496718862007685521)
          ·
            refine ⟨12672028122539146505764141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16896037496718862007685521 12672028122539146505764141)
            ·
              refine ⟨4752010545952179939661553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12672028122539146505764141 4752010545952179939661553)
              ·
                refine ⟨3564007909464134954746165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4752010545952179939661553 3564007909464134954746165)
                ·
                  refine ⟨334125741512262652007453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3564007909464134954746165 334125741512262652007453)
                  ·
                    rfl

theorem cell21_1464092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_1464092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464092 prefixEnd_1464092 := by exact prefixLift 1464092
  have htrace : WordTrace (prefixWord ++ tailWord_1464092) baseStart_1464092 baseEnd_1464092 := by
    simpa [prefixWord, tailWord_1464092, baseEnd_1464092] using wordTrace_append hprefix tailTrace_1464092
  have hstable : (prefixWord ++ tailWord_1464092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464092).length < 2 ^ (prefixWord ++ tailWord_1464092).sum := by decide
  have hdescent : baseEnd_1464092 < baseStart_1464092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464126 : List Nat := [4, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_1464126 : Nat := 118140960795 + 1464126 * 2 ^ 59
def prefixEnd_1464126 : Nat := 4983230072969 + 3 ^ 40 * 1464126 * 2
def baseEnd_1464126 : Nat := 334133500775486148440717

theorem tailTrace_1464126 : CollatzResearch.WordTrace tailWord_1464126 prefixEnd_1464126 334133500775486148440717 := by
  unfold tailWord_1464126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6675132786716128707273529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35600708195819353105458821 6675132786716128707273529)
  ·
    refine ⟨5006349590037096530455147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6675132786716128707273529 5006349590037096530455147)
    ·
      refine ⟨7509524385055644795682721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5006349590037096530455147 7509524385055644795682721)
      ·
        refine ⟨5632143288791733596762041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7509524385055644795682721 5632143288791733596762041)
        ·
          refine ⟨4224107466593800197571531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5632143288791733596762041 4224107466593800197571531)
          ·
            refine ⟨6336161199890700296357297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224107466593800197571531 6336161199890700296357297)
            ·
              refine ⟨4752120899918025222267973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6336161199890700296357297 4752120899918025222267973)
              ·
                refine ⟨891022668734629729175245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4752120899918025222267973 891022668734629729175245)
                ·
                  refine ⟨334133500775486148440717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891022668734629729175245 334133500775486148440717)
                  ·
                    rfl

theorem cell21_1464126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_1464126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464126 prefixEnd_1464126 := by exact prefixLift 1464126
  have htrace : WordTrace (prefixWord ++ tailWord_1464126) baseStart_1464126 baseEnd_1464126 := by
    simpa [prefixWord, tailWord_1464126, baseEnd_1464126] using wordTrace_append hprefix tailTrace_1464126
  have hstable : (prefixWord ++ tailWord_1464126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464126).length < 2 ^ (prefixWord ++ tailWord_1464126).sum := by decide
  have hdescent : baseEnd_1464126 < baseStart_1464126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464272 : List Nat := [2, 1, 1, 1, 1, 2, 4, 9]
def baseStart_1464272 : Nat := 118140960795 + 1464272 * 2 ^ 59
def prefixEnd_1464272 : Nat := 4983230072969 + 3 ^ 40 * 1464272 * 2
def baseEnd_1464272 : Nat := 111388939988207446335695

theorem tailTrace_1464272 : CollatzResearch.WordTrace tailWord_1464272 prefixEnd_1464272 111388939988207446335695 := by
  unfold tailWord_1464272
  simp only [CollatzResearch.WordTrace]
  refine ⟨26703193675600048296501535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35604258234133397728668713 26703193675600048296501535)
  ·
    refine ⟨40054790513400072444752303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26703193675600048296501535 40054790513400072444752303)
    ·
      refine ⟨60082185770100108667128455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40054790513400072444752303 60082185770100108667128455)
      ·
        refine ⟨90123278655150163000692683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60082185770100108667128455 90123278655150163000692683)
        ·
          refine ⟨135184917982725244501039025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90123278655150163000692683 135184917982725244501039025)
          ·
            refine ⟨101388688487043933375779269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135184917982725244501039025 101388688487043933375779269)
            ·
              refine ⟨19010379091320737507958613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101388688487043933375779269 19010379091320737507958613)
              ·
                refine ⟨111388939988207446335695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19010379091320737507958613 111388939988207446335695)
                ·
                  rfl

theorem cell21_1464272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_1464272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464272 prefixEnd_1464272 := by exact prefixLift 1464272
  have htrace : WordTrace (prefixWord ++ tailWord_1464272) baseStart_1464272 baseEnd_1464272 := by
    simpa [prefixWord, tailWord_1464272, baseEnd_1464272] using wordTrace_append hprefix tailTrace_1464272
  have hstable : (prefixWord ++ tailWord_1464272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464272).length < 2 ^ (prefixWord ++ tailWord_1464272).sum := by decide
  have hdescent : baseEnd_1464272 < baseStart_1464272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464334 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_1464334 : Nat := 118140960795 + 1464334 * 2 ^ 59
def prefixEnd_1464334 : Nat := 4983230072969 + 3 ^ 40 * 1464334 * 2
def baseEnd_1464334 : Nat := 334180969209324008973625

theorem tailTrace_1464334 : CollatzResearch.WordTrace tailWord_1464334 prefixEnd_1464334 334180969209324008973625 := by
  unfold tailWord_1464334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6676081084621935147720007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35605765784650320787840037 6676081084621935147720007)
  ·
    refine ⟨10014121626932902721580011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6676081084621935147720007 10014121626932902721580011)
    ·
      refine ⟨15021182440399354082370017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10014121626932902721580011 15021182440399354082370017)
      ·
        refine ⟨11265886830299515561777513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15021182440399354082370017 11265886830299515561777513)
        ·
          refine ⟨8449415122724636671333135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11265886830299515561777513 8449415122724636671333135)
          ·
            refine ⟨12674122684086955006999703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8449415122724636671333135 12674122684086955006999703)
            ·
              refine ⟨19011184026130432510499555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12674122684086955006999703 19011184026130432510499555)
              ·
                refine ⟨28516776039195648765749333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19011184026130432510499555 28516776039195648765749333)
                ·
                  refine ⟨334180969209324008973625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28516776039195648765749333 334180969209324008973625)
                  ·
                    rfl

theorem cell21_1464334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1464334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464334 prefixEnd_1464334 := by exact prefixLift 1464334
  have htrace : WordTrace (prefixWord ++ tailWord_1464334) baseStart_1464334 baseEnd_1464334 := by
    simpa [prefixWord, tailWord_1464334, baseEnd_1464334] using wordTrace_append hprefix tailTrace_1464334
  have hstable : (prefixWord ++ tailWord_1464334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464334).length < 2 ^ (prefixWord ++ tailWord_1464334).sum := by decide
  have hdescent : baseEnd_1464334 < baseStart_1464334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464340 : List Nat := [2, 4, 3, 2, 2, 1, 7]
def baseStart_1464340 : Nat := 118140960795 + 1464340 * 2 ^ 59
def prefixEnd_1464340 : Nat := 4983230072969 + 3 ^ 40 * 1464340 * 2
def baseEnd_1464340 : Nat := 37131370943452147985957

theorem tailTrace_1464340 : CollatzResearch.WordTrace tailWord_1464340 prefixEnd_1464340 37131370943452147985957 := by
  unfold tailWord_1464340
  simp only [CollatzResearch.WordTrace]
  refine ⟨26704433757476872103239237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35605911676635829470985649 26704433757476872103239237)
  ·
    refine ⟨5007081329526913519357357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26704433757476872103239237 5007081329526913519357357)
    ·
      refine ⟨1877655498572592569759009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5007081329526913519357357 1877655498572592569759009)
      ·
        refine ⟨1408241623929444427319257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1877655498572592569759009 1408241623929444427319257)
        ·
          refine ⟨1056181217947083320489443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1408241623929444427319257 1056181217947083320489443)
          ·
            refine ⟨1584271826920624980734165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056181217947083320489443 1584271826920624980734165)
            ·
              refine ⟨37131370943452147985957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1584271826920624980734165 37131370943452147985957)
              ·
                rfl

theorem cell21_1464340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 7].length) (baseStart_1464340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464340 prefixEnd_1464340 := by exact prefixLift 1464340
  have htrace : WordTrace (prefixWord ++ tailWord_1464340) baseStart_1464340 baseEnd_1464340 := by
    simpa [prefixWord, tailWord_1464340, baseEnd_1464340] using wordTrace_append hprefix tailTrace_1464340
  have hstable : (prefixWord ++ tailWord_1464340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464340).length < 2 ^ (prefixWord ++ tailWord_1464340).sum := by decide
  have hdescent : baseEnd_1464340 < baseStart_1464340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464354 : List Nat := [3, 3, 1, 1, 1, 2, 5, 2, 3]
def baseStart_1464354 : Nat := 118140960795 + 1464354 * 2 ^ 59
def prefixEnd_1464354 : Nat := 4983230072969 + 3 ^ 40 * 1464354 * 2
def baseEnd_1464354 : Nat := 334185533481808418640251

theorem tailTrace_1464354 : CollatzResearch.WordTrace tailWord_1464354 prefixEnd_1464354 334185533481808418640251 := by
  unfold tailWord_1464354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13352344534225756149372029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35606252091268683064992077 13352344534225756149372029)
  ·
    refine ⟨5007129200334658556014511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13352344534225756149372029 5007129200334658556014511)
    ·
      refine ⟨7510693800501987834021767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5007129200334658556014511 7510693800501987834021767)
      ·
        refine ⟨11266040700752981751032651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7510693800501987834021767 11266040700752981751032651)
        ·
          refine ⟨16899061051129472626548977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11266040700752981751032651 16899061051129472626548977)
          ·
            refine ⟨12674295788347104469911733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16899061051129472626548977 12674295788347104469911733)
            ·
              refine ⟨1188215230157541044054225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12674295788347104469911733 1188215230157541044054225)
              ·
                refine ⟨891161422618155783040669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1188215230157541044054225 891161422618155783040669)
                ·
                  refine ⟨334185533481808418640251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891161422618155783040669 334185533481808418640251)
                  ·
                    rfl

theorem cell21_1464354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_1464354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464354 prefixEnd_1464354 := by exact prefixLift 1464354
  have htrace : WordTrace (prefixWord ++ tailWord_1464354) baseStart_1464354 baseEnd_1464354 := by
    simpa [prefixWord, tailWord_1464354, baseEnd_1464354] using wordTrace_append hprefix tailTrace_1464354
  have hstable : (prefixWord ++ tailWord_1464354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464354).length < 2 ^ (prefixWord ++ tailWord_1464354).sum := by decide
  have hdescent : baseEnd_1464354 < baseStart_1464354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464368 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 4]
def baseStart_1464368 : Nat := 118140960795 + 1464368 * 2 ^ 59
def prefixEnd_1464368 : Nat := 4983230072969 + 3 ^ 40 * 1464368 * 2
def baseEnd_1464368 : Nat := 334188728472547505406889

theorem tailTrace_1464368 : CollatzResearch.WordTrace tailWord_1464368 prefixEnd_1464368 334188728472547505406889 := by
  unfold tailWord_1464368
  simp only [CollatzResearch.WordTrace]
  refine ⟨26704944379426152494248879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35606592505901536658998505 26704944379426152494248879)
  ·
    refine ⟨40057416569139228741373319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26704944379426152494248879 40057416569139228741373319)
    ·
      refine ⟨60086124853708843112059979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40057416569139228741373319 60086124853708843112059979)
      ·
        refine ⟨90129187280563264668089969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60086124853708843112059979 90129187280563264668089969)
        ·
          refine ⟨67596890460422448501067477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90129187280563264668089969 67596890460422448501067477)
          ·
            refine ⟨1584302120166151136743769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 67596890460422448501067477 1584302120166151136743769)
            ·
              refine ⟨1188226590124613352557827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584302120166151136743769 1188226590124613352557827)
              ·
                refine ⟨1782339885186920028836741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188226590124613352557827 1782339885186920028836741)
                ·
                  refine ⟨334188728472547505406889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1782339885186920028836741 334188728472547505406889)
                  ·
                    rfl

theorem cell21_1464368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_1464368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464368 prefixEnd_1464368 := by exact prefixLift 1464368
  have htrace : WordTrace (prefixWord ++ tailWord_1464368) baseStart_1464368 baseEnd_1464368 := by
    simpa [prefixWord, tailWord_1464368, baseEnd_1464368] using wordTrace_append hprefix tailTrace_1464368
  have hstable : (prefixWord ++ tailWord_1464368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464368).length < 2 ^ (prefixWord ++ tailWord_1464368).sum := by decide
  have hdescent : baseEnd_1464368 < baseStart_1464368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464534 : List Nat := [5, 2, 1, 2, 1, 1, 1, 8]
def baseStart_1464534 : Nat := 118140960795 + 1464534 * 2 ^ 59
def prefixEnd_1464534 : Nat := 4983230072969 + 3 ^ 40 * 1464534 * 2
def baseEnd_1464534 : Nat := 111408870644722701879961

theorem tailTrace_1464534 : CollatzResearch.WordTrace tailWord_1464534 prefixEnd_1464534 111408870644722701879961 := by
  unfold tailWord_1464534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3338496454765682208690041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35610628850833943559360437 3338496454765682208690041)
  ·
    refine ⟨2503872341074261656517531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3338496454765682208690041 2503872341074261656517531)
    ·
      refine ⟨3755808511611392484776297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2503872341074261656517531 3755808511611392484776297)
      ·
        refine ⟨2816856383708544363582223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3755808511611392484776297 2816856383708544363582223)
        ·
          refine ⟨4225284575562816545373335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2816856383708544363582223 4225284575562816545373335)
          ·
            refine ⟨6337926863344224818060003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4225284575562816545373335 6337926863344224818060003)
            ·
              refine ⟨9506890295016337227090005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6337926863344224818060003 9506890295016337227090005)
              ·
                refine ⟨111408870644722701879961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9506890295016337227090005 111408870644722701879961)
                ·
                  rfl

theorem cell21_1464534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_1464534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464534 prefixEnd_1464534 := by exact prefixLift 1464534
  have htrace : WordTrace (prefixWord ++ tailWord_1464534) baseStart_1464534 baseEnd_1464534 := by
    simpa [prefixWord, tailWord_1464534, baseEnd_1464534] using wordTrace_append hprefix tailTrace_1464534
  have hstable : (prefixWord ++ tailWord_1464534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464534).length < 2 ^ (prefixWord ++ tailWord_1464534).sum := by decide
  have hdescent : baseEnd_1464534 < baseStart_1464534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464593 : List Nat := [1, 2, 2, 1, 1, 7, 1, 6]
def baseStart_1464593 : Nat := 118140960795 + 1464593 * 2 ^ 59
def prefixEnd_1464593 : Nat := 4983230072969 + 3 ^ 40 * 1464593 * 2
def baseEnd_1464593 : Nat := 111413358845999038052143

theorem tailTrace_1464593 : CollatzResearch.WordTrace tailWord_1464593 prefixEnd_1464593 111413358845999038052143 := by
  unfold tailWord_1464593
  simp only [CollatzResearch.WordTrace]
  refine ⟨53418095183037168415438433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35612063455358112276958955 53418095183037168415438433)
  ·
    refine ⟨40063571387277876311578825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53418095183037168415438433 40063571387277876311578825)
    ·
      refine ⟨30047678540458407233684119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40063571387277876311578825 30047678540458407233684119)
      ·
        refine ⟨45071517810687610850526179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30047678540458407233684119 45071517810687610850526179)
        ·
          refine ⟨67607276716031416275789269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45071517810687610850526179 67607276716031416275789269)
          ·
            refine ⟨1584545548031986318963811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 67607276716031416275789269 1584545548031986318963811)
            ·
              refine ⟨2376818322047979478445717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584545548031986318963811 2376818322047979478445717)
              ·
                refine ⟨111413358845999038052143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2376818322047979478445717 111413358845999038052143)
                ·
                  rfl

theorem cell21_1464593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 6].length) (baseStart_1464593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464593 prefixEnd_1464593 := by exact prefixLift 1464593
  have htrace : WordTrace (prefixWord ++ tailWord_1464593) baseStart_1464593 baseEnd_1464593 := by
    simpa [prefixWord, tailWord_1464593, baseEnd_1464593] using wordTrace_append hprefix tailTrace_1464593
  have hstable : (prefixWord ++ tailWord_1464593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464593).length < 2 ^ (prefixWord ++ tailWord_1464593).sum := by decide
  have hdescent : baseEnd_1464593 < baseStart_1464593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464607 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 7]
def baseStart_1464607 : Nat := 118140960795 + 1464607 * 2 ^ 59
def prefixEnd_1464607 : Nat := 4983230072969 + 3 ^ 40 * 1464607 * 2
def baseEnd_1464607 : Nat := 334243271528736200923067

theorem tailTrace_1464607 : CollatzResearch.WordTrace tailWord_1464607 prefixEnd_1464607 334243271528736200923067 := by
  unfold tailWord_1464607
  simp only [CollatzResearch.WordTrace]
  refine ⟨53418605804986448806448075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35612403869990965870965383 53418605804986448806448075)
  ·
    refine ⟨80127908707479673209672113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53418605804986448806448075 80127908707479673209672113)
    ·
      refine ⟨60095931530609754907254085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80127908707479673209672113 60095931530609754907254085)
      ·
        refine ⟨11267987161989329045110141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60095931530609754907254085 11267987161989329045110141)
        ·
          refine ⟨4225495185745998391916303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11267987161989329045110141 4225495185745998391916303)
          ·
            refine ⟨6338242778618997587874455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4225495185745998391916303 6338242778618997587874455)
            ·
              refine ⟨9507364167928496381811683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6338242778618997587874455 9507364167928496381811683)
              ·
                refine ⟨14261046251892744572717525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9507364167928496381811683 14261046251892744572717525)
                ·
                  refine ⟨334243271528736200923067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14261046251892744572717525 334243271528736200923067)
                  ·
                    rfl

theorem cell21_1464607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_1464607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464607 prefixEnd_1464607 := by exact prefixLift 1464607
  have htrace : WordTrace (prefixWord ++ tailWord_1464607) baseStart_1464607 baseEnd_1464607 := by
    simpa [prefixWord, tailWord_1464607, baseEnd_1464607] using wordTrace_append hprefix tailTrace_1464607
  have hstable : (prefixWord ++ tailWord_1464607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464607).length < 2 ^ (prefixWord ++ tailWord_1464607).sum := by decide
  have hdescent : baseEnd_1464607 < baseStart_1464607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464610 : List Nat := [3, 3, 1, 1, 3, 2, 3, 5]
def baseStart_1464610 : Nat := 118140960795 + 1464610 * 2 ^ 59
def prefixEnd_1464610 : Nat := 4983230072969 + 3 ^ 40 * 1464610 * 2
def baseEnd_1464610 : Nat := 111414652056536287457687

theorem tailTrace_1464610 : CollatzResearch.WordTrace tailWord_1464610 prefixEnd_1464610 111414652056536287457687 := by
  unfold tailWord_1464610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13354678805993895079701821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35612476815983720212538189 13354678805993895079701821)
  ·
    refine ⟨5008004552247710654888183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13354678805993895079701821 5008004552247710654888183)
    ·
      refine ⟨7512006828371565982332275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5008004552247710654888183 7512006828371565982332275)
      ·
        refine ⟨11268010242557348973498413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7512006828371565982332275 11268010242557348973498413)
        ·
          refine ⟨4225503840959005865061905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11268010242557348973498413 4225503840959005865061905)
          ·
            refine ⟨3169127880719254398796429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4225503840959005865061905 3169127880719254398796429)
            ·
              refine ⟨1188422955269720399548661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3169127880719254398796429 1188422955269720399548661)
              ·
                refine ⟨111414652056536287457687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1188422955269720399548661 111414652056536287457687)
                ·
                  rfl

theorem cell21_1464610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_1464610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464610 prefixEnd_1464610 := by exact prefixLift 1464610
  have htrace : WordTrace (prefixWord ++ tailWord_1464610) baseStart_1464610 baseEnd_1464610 := by
    simpa [prefixWord, tailWord_1464610, baseEnd_1464610] using wordTrace_append hprefix tailTrace_1464610
  have hstable : (prefixWord ++ tailWord_1464610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464610).length < 2 ^ (prefixWord ++ tailWord_1464610).sum := by decide
  have hdescent : baseEnd_1464610 < baseStart_1464610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464641 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 5]
def baseStart_1464641 : Nat := 118140960795 + 1464641 * 2 ^ 59
def prefixEnd_1464641 : Nat := 4983230072969 + 3 ^ 40 * 1464641 * 2
def baseEnd_1464641 : Nat := 334251030791959697356331

theorem tailTrace_1464641 : CollatzResearch.WordTrace tailWord_1464641 prefixEnd_1464641 334251030791959697356331 := by
  unfold tailWord_1464641
  simp only [CollatzResearch.WordTrace]
  refine ⟨53419845886863272613185777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35613230591242181742123851 53419845886863272613185777)
  ·
    refine ⟨40064884415147454459889333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53419845886863272613185777 40064884415147454459889333)
    ·
      refine ⟨3756082913920073855614625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40064884415147454459889333 3756082913920073855614625)
      ·
        refine ⟨2817062185440055391710969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3756082913920073855614625 2817062185440055391710969)
        ·
          refine ⟨2112796639080041543783227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2817062185440055391710969 2112796639080041543783227)
          ·
            refine ⟨3169194958620062315674841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112796639080041543783227 3169194958620062315674841)
            ·
              refine ⟨2376896218965046736756131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3169194958620062315674841 2376896218965046736756131)
              ·
                refine ⟨3565344328447570105134197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376896218965046736756131 3565344328447570105134197)
                ·
                  refine ⟨334251030791959697356331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3565344328447570105134197 334251030791959697356331)
                  ·
                    rfl

theorem cell21_1464641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_1464641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464641 prefixEnd_1464641 := by exact prefixLift 1464641
  have htrace : WordTrace (prefixWord ++ tailWord_1464641) baseStart_1464641 baseEnd_1464641 := by
    simpa [prefixWord, tailWord_1464641, baseEnd_1464641] using wordTrace_append hprefix tailTrace_1464641
  have hstable : (prefixWord ++ tailWord_1464641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464641).length < 2 ^ (prefixWord ++ tailWord_1464641).sum := by decide
  have hdescent : baseEnd_1464641 < baseStart_1464641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464652 : List Nat := [2, 2, 1, 3, 2, 1, 2, 8]
def baseStart_1464652 : Nat := 118140960795 + 1464652 * 2 ^ 59
def prefixEnd_1464652 : Nat := 4983230072969 + 3 ^ 40 * 1464652 * 2
def baseEnd_1464652 : Nat := 111417847047275374224325

theorem tailTrace_1464652 : CollatzResearch.WordTrace tailWord_1464652 prefixEnd_1464652 111417847047275374224325 := by
  unfold tailWord_1464652
  simp only [CollatzResearch.WordTrace]
  refine ⟨26710123544911710745918105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35613498059882280994557473 26710123544911710745918105)
  ·
    refine ⟨20032592658683783059438579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26710123544911710745918105 20032592658683783059438579)
    ·
      refine ⟨30048888988025674589157869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20032592658683783059438579 30048888988025674589157869)
      ·
        refine ⟨11268333370509627970934201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30048888988025674589157869 11268333370509627970934201)
        ·
          refine ⟨8451250027882220978200651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11268333370509627970934201 8451250027882220978200651)
          ·
            refine ⟨12676875041823331467300977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8451250027882220978200651 12676875041823331467300977)
            ·
              refine ⟨9507656281367498600475733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12676875041823331467300977 9507656281367498600475733)
              ·
                refine ⟨111417847047275374224325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9507656281367498600475733 111417847047275374224325)
                ·
                  rfl

theorem cell21_1464652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_1464652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464652 prefixEnd_1464652 := by exact prefixLift 1464652
  have htrace : WordTrace (prefixWord ++ tailWord_1464652) baseStart_1464652 baseEnd_1464652 := by
    simpa [prefixWord, tailWord_1464652, baseEnd_1464652] using wordTrace_append hprefix tailTrace_1464652
  have hstable : (prefixWord ++ tailWord_1464652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464652).length < 2 ^ (prefixWord ++ tailWord_1464652).sum := by decide
  have hdescent : baseEnd_1464652 < baseStart_1464652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464706 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1464706 : Nat := 118140960795 + 1464706 * 2 ^ 59
def prefixEnd_1464706 : Nat := 4983230072969 + 3 ^ 40 * 1464706 * 2
def baseEnd_1464706 : Nat := 334265864677534028772865

theorem tailTrace_1464706 : CollatzResearch.WordTrace tailWord_1464706 prefixEnd_1464706 334265864677534028772865 := by
  unfold tailWord_1464706
  simp only [CollatzResearch.WordTrace]
  refine ⟨13355554157906947178575493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35614811087751859142867981 13355554157906947178575493)
  ·
    refine ⟨2504166404607552595982905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13355554157906947178575493 2504166404607552595982905)
    ·
      refine ⟨1878124803455664446987179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2504166404607552595982905 1878124803455664446987179)
      ·
        refine ⟨2817187205183496670480769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1878124803455664446987179 2817187205183496670480769)
        ·
          refine ⟨2112890403887622502860577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2817187205183496670480769 2112890403887622502860577)
          ·
            refine ⟨1584667802915716877145433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2112890403887622502860577 1584667802915716877145433)
            ·
              refine ⟨1188500852186787657859075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584667802915716877145433 1188500852186787657859075)
              ·
                refine ⟨1782751278280181486788613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188500852186787657859075 1782751278280181486788613)
                ·
                  refine ⟨334265864677534028772865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1782751278280181486788613 334265864677534028772865)
                  ·
                    rfl

theorem cell21_1464706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1464706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464706 prefixEnd_1464706 := by exact prefixLift 1464706
  have htrace : WordTrace (prefixWord ++ tailWord_1464706) baseStart_1464706 baseEnd_1464706 := by
    simpa [prefixWord, tailWord_1464706, baseEnd_1464706] using wordTrace_append hprefix tailTrace_1464706
  have hstable : (prefixWord ++ tailWord_1464706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464706).length < 2 ^ (prefixWord ++ tailWord_1464706).sum := by decide
  have hdescent : baseEnd_1464706 < baseStart_1464706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464866 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1464866 : Nat := 118140960795 + 1464866 * 2 ^ 59
def prefixEnd_1464866 : Nat := 4983230072969 + 3 ^ 40 * 1464866 * 2
def baseEnd_1464866 : Nat := 334302378857409306105871

theorem tailTrace_1464866 : CollatzResearch.WordTrace tailWord_1464866 prefixEnd_1464866 334302378857409306105871 := by
  unfold tailWord_1464866
  simp only [CollatzResearch.WordTrace]
  refine ⟨13357013077762034010031613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35618701540698757360084301 13357013077762034010031613)
  ·
    refine ⟨5008879904160762753761855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13357013077762034010031613 5008879904160762753761855)
    ·
      refine ⟨7513319856241144130642783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5008879904160762753761855 7513319856241144130642783)
      ·
        refine ⟨11269979784361716195964175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7513319856241144130642783 11269979784361716195964175)
        ·
          refine ⟨16904969676542574293946263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11269979784361716195964175 16904969676542574293946263)
          ·
            refine ⟨25357454514813861440919395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16904969676542574293946263 25357454514813861440919395)
            ·
              refine ⟨38036181772220792161379093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25357454514813861440919395 38036181772220792161379093)
              ·
                refine ⟨1782946020572849632564645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38036181772220792161379093 1782946020572849632564645)
                ·
                  refine ⟨334302378857409306105871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1782946020572849632564645 334302378857409306105871)
                  ·
                    rfl

theorem cell21_1464866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1464866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464866 prefixEnd_1464866 := by exact prefixLift 1464866
  have htrace : WordTrace (prefixWord ++ tailWord_1464866) baseStart_1464866 baseEnd_1464866 := by
    simpa [prefixWord, tailWord_1464866, baseEnd_1464866] using wordTrace_append hprefix tailTrace_1464866
  have hstable : (prefixWord ++ tailWord_1464866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464866).length < 2 ^ (prefixWord ++ tailWord_1464866).sum := by decide
  have hdescent : baseEnd_1464866 < baseStart_1464866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464939 : List Nat := [1, 1, 1, 1, 2, 2, 1, 12]
def baseStart_1464939 : Nat := 118140960795 + 1464939 * 2 ^ 59
def prefixEnd_1464939 : Nat := 4983230072969 + 3 ^ 40 * 1464939 * 2
def baseEnd_1464939 : Nat := 111439679483992467129685

theorem tailTrace_1464939 : CollatzResearch.WordTrace tailWord_1464939 prefixEnd_1464939 111439679483992467129685 := by
  unfold tailWord_1464939
  simp only [CollatzResearch.WordTrace]
  refine ⟨53430714839783669507533871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35620476559855779671689247 53430714839783669507533871)
  ·
    refine ⟨80146072259675504261300807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53430714839783669507533871 80146072259675504261300807)
    ·
      refine ⟨120219108389513256391951211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80146072259675504261300807 120219108389513256391951211)
      ·
        refine ⟨180328662584269884587926817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120219108389513256391951211 180328662584269884587926817)
        ·
          refine ⟨135246496938202413440945113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180328662584269884587926817 135246496938202413440945113)
          ·
            refine ⟨101434872703651810080708835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135246496938202413440945113 101434872703651810080708835)
            ·
              refine ⟨152152309055477715121063253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101434872703651810080708835 152152309055477715121063253)
              ·
                refine ⟨111439679483992467129685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 152152309055477715121063253 111439679483992467129685)
                ·
                  rfl

theorem cell21_1464939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 12].length) (baseStart_1464939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1464939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1464939 prefixEnd_1464939 := by exact prefixLift 1464939
  have htrace : WordTrace (prefixWord ++ tailWord_1464939) baseStart_1464939 baseEnd_1464939 := by
    simpa [prefixWord, tailWord_1464939, baseEnd_1464939] using wordTrace_append hprefix tailTrace_1464939
  have hstable : (prefixWord ++ tailWord_1464939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464939).length < 2 ^ (prefixWord ++ tailWord_1464939).sum := by decide
  have hdescent : baseEnd_1464939 < baseStart_1464939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465021 : List Nat := [1, 4, 1, 2, 1, 5, 1, 3, 3]
def baseStart_1465021 : Nat := 118140960795 + 1465021 * 2 ^ 59
def prefixEnd_1465021 : Nat := 4983230072969 + 3 ^ 40 * 1465021 * 2
def baseEnd_1465021 : Nat := 334337751969163481022221

theorem tailTrace_1465021 : CollatzResearch.WordTrace tailWord_1465021 prefixEnd_1465021 334337751969163481022221 := by
  unfold tailWord_1465021
  simp only [CollatzResearch.WordTrace]
  refine ⟨53433705625486597512018917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35622470416991065008012611 53433705625486597512018917)
  ·
    refine ⟨10018819804778737033503547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53433705625486597512018917 10018819804778737033503547)
    ·
      refine ⟨15028229707168105550255321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10018819804778737033503547 15028229707168105550255321)
      ·
        refine ⟨11271172280376079162691491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15028229707168105550255321 11271172280376079162691491)
        ·
          refine ⟨16906758420564118744037237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11271172280376079162691491 16906758420564118744037237)
          ·
            refine ⟨1585008601927886132253491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16906758420564118744037237 1585008601927886132253491)
            ·
              refine ⟨2377512902891829198380237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585008601927886132253491 2377512902891829198380237)
              ·
                refine ⟨891567338584435949392589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2377512902891829198380237 891567338584435949392589)
                ·
                  refine ⟨334337751969163481022221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891567338584435949392589 334337751969163481022221)
                  ·
                    rfl

theorem cell21_1465021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_1465021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465021 prefixEnd_1465021 := by exact prefixLift 1465021
  have htrace : WordTrace (prefixWord ++ tailWord_1465021) baseStart_1465021 baseEnd_1465021 := by
    simpa [prefixWord, tailWord_1465021, baseEnd_1465021] using wordTrace_append hprefix tailTrace_1465021
  have hstable : (prefixWord ++ tailWord_1465021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465021).length < 2 ^ (prefixWord ++ tailWord_1465021).sum := by decide
  have hdescent : baseEnd_1465021 < baseStart_1465021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465032 : List Nat := [2, 1, 3, 1, 2, 5, 7]
def baseStart_1465032 : Nat := 118140960795 + 1465032 * 2 ^ 59
def prefixEnd_1465032 : Nat := 4983230072969 + 3 ^ 40 * 1465032 * 2
def baseEnd_1465032 : Nat := 37148918035447767370985

theorem tailTrace_1465032 : CollatzResearch.WordTrace tailWord_1465032 prefixEnd_1465032 37148918035447767370985 := by
  unfold tailWord_1465032
  simp only [CollatzResearch.WordTrace]
  refine ⟨26717053414223373195334675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35622737885631164260446233 26717053414223373195334675)
  ·
    refine ⟨40075580121335059793002013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26717053414223373195334675 40075580121335059793002013)
    ·
      refine ⟨15028342545500647422375755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40075580121335059793002013 15028342545500647422375755)
      ·
        refine ⟨22542513818250971133563633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15028342545500647422375755 22542513818250971133563633)
        ·
          refine ⟨16906885363688228350172725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22542513818250971133563633 16906885363688228350172725)
          ·
            refine ⟨1585020502845771407828693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16906885363688228350172725 1585020502845771407828693)
            ·
              refine ⟨37148918035447767370985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1585020502845771407828693 37148918035447767370985)
              ·
                rfl

theorem cell21_1465032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 7].length) (baseStart_1465032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465032 prefixEnd_1465032 := by exact prefixLift 1465032
  have htrace : WordTrace (prefixWord ++ tailWord_1465032) baseStart_1465032 baseEnd_1465032 := by
    simpa [prefixWord, tailWord_1465032, baseEnd_1465032] using wordTrace_append hprefix tailTrace_1465032
  have hstable : (prefixWord ++ tailWord_1465032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465032).length < 2 ^ (prefixWord ++ tailWord_1465032).sum := by decide
  have hdescent : baseEnd_1465032 < baseStart_1465032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465052 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 4]
def baseStart_1465052 : Nat := 118140960795 + 1465052 * 2 ^ 59
def prefixEnd_1465052 : Nat := 4983230072969 + 3 ^ 40 * 1465052 * 2
def baseEnd_1465052 : Nat := 334344826591514316005491

theorem tailTrace_1465052 : CollatzResearch.WordTrace tailWord_1465052 prefixEnd_1465052 334344826591514316005491 := by
  unfold tailWord_1465052
  simp only [CollatzResearch.WordTrace]
  refine ⟨26717418144187144903198705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35623224192249526537598273 26717418144187144903198705)
  ·
    refine ⟨20038063608140358677399029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26717418144187144903198705 20038063608140358677399029)
    ·
      refine ⟨1878568463263158626006159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20038063608140358677399029 1878568463263158626006159)
      ·
        refine ⟨2817852694894737939009239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1878568463263158626006159 2817852694894737939009239)
        ·
          refine ⟨4226779042342106908513859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2817852694894737939009239 4226779042342106908513859)
          ·
            refine ⟨6340168563513160362770789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4226779042342106908513859 6340168563513160362770789)
            ·
              refine ⟨1188781605658717568019523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6340168563513160362770789 1188781605658717568019523)
              ·
                refine ⟨1783172408488076352029285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188781605658717568019523 1783172408488076352029285)
                ·
                  refine ⟨334344826591514316005491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1783172408488076352029285 334344826591514316005491)
                  ·
                    rfl

theorem cell21_1465052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_1465052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465052 prefixEnd_1465052 := by exact prefixLift 1465052
  have htrace : WordTrace (prefixWord ++ tailWord_1465052) baseStart_1465052 baseEnd_1465052 := by
    simpa [prefixWord, tailWord_1465052, baseEnd_1465052] using wordTrace_append hprefix tailTrace_1465052
  have hstable : (prefixWord ++ tailWord_1465052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465052).length < 2 ^ (prefixWord ++ tailWord_1465052).sum := by decide
  have hdescent : baseEnd_1465052 < baseStart_1465052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465215 : List Nat := [1, 1, 2, 2, 1, 1, 4, 6, 3]
def baseStart_1465215 : Nat := 118140960795 + 1465215 * 2 ^ 59
def prefixEnd_1465215 : Nat := 4983230072969 + 3 ^ 40 * 1465215 * 2
def baseEnd_1465215 : Nat := 334382025412262254788491

theorem tailTrace_1465215 : CollatzResearch.WordTrace tailWord_1465215 prefixEnd_1465215 334382025412262254788491 := by
  unfold tailWord_1465215
  simp only [CollatzResearch.WordTrace]
  refine ⟨53440781386783768644581099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35627187591189179096387399 53440781386783768644581099)
  ·
    refine ⟨80161172080175652966871649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53440781386783768644581099 80161172080175652966871649)
    ·
      refine ⟨60120879060131739725153737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80161172080175652966871649 60120879060131739725153737)
      ·
        refine ⟨45090659295098804793865303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60120879060131739725153737 45090659295098804793865303)
        ·
          refine ⟨67635988942648207190797955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45090659295098804793865303 67635988942648207190797955)
          ·
            refine ⟨101453983413972310786196933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67635988942648207190797955 101453983413972310786196933)
            ·
              refine ⟨19022621890119808272411925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101453983413972310786196933 19022621890119808272411925)
              ·
                refine ⟨891685401099366012769309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19022621890119808272411925 891685401099366012769309)
                ·
                  refine ⟨334382025412262254788491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891685401099366012769309 334382025412262254788491)
                  ·
                    rfl

theorem cell21_1465215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 3].length) (baseStart_1465215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465215 prefixEnd_1465215 := by exact prefixLift 1465215
  have htrace : WordTrace (prefixWord ++ tailWord_1465215) baseStart_1465215 baseEnd_1465215 := by
    simpa [prefixWord, tailWord_1465215, baseEnd_1465215] using wordTrace_append hprefix tailTrace_1465215
  have hstable : (prefixWord ++ tailWord_1465215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465215).length < 2 ^ (prefixWord ++ tailWord_1465215).sum := by decide
  have hdescent : baseEnd_1465215 < baseStart_1465215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465274 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_1465274 : Nat := 118140960795 + 1465274 * 2 ^ 59
def prefixEnd_1465274 : Nat := 4983230072969 + 3 ^ 40 * 1465274 * 2
def baseEnd_1465274 : Nat := 334395490016091263305037

theorem tailTrace_1465274 : CollatzResearch.WordTrace tailWord_1465274 prefixEnd_1465274 334395490016091263305037 := by
  unfold tailWord_1465274
  simp only [CollatzResearch.WordTrace]
  refine ⟨13360733323392505430244719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35628622195713347813985917 13360733323392505430244719)
  ·
    refine ⟨20041099985088758145367079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13360733323392505430244719 20041099985088758145367079)
    ·
      refine ⟨30061649977633137218050619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20041099985088758145367079 30061649977633137218050619)
      ·
        refine ⟨45092474966449705827075929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30061649977633137218050619 45092474966449705827075929)
        ·
          refine ⟨33819356224837279370306947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45092474966449705827075929 33819356224837279370306947)
          ·
            refine ⟨50729034337255919055460421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33819356224837279370306947 50729034337255919055460421)
            ·
              refine ⟨9511693938235484822898829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50729034337255919055460421 9511693938235484822898829)
              ·
                refine ⟨3566885226838306808587061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9511693938235484822898829 3566885226838306808587061)
                ·
                  refine ⟨334395490016091263305037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3566885226838306808587061 334395490016091263305037)
                  ·
                    rfl

theorem cell21_1465274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_1465274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465274 prefixEnd_1465274 := by exact prefixLift 1465274
  have htrace : WordTrace (prefixWord ++ tailWord_1465274) baseStart_1465274 baseEnd_1465274 := by
    simpa [prefixWord, tailWord_1465274, baseEnd_1465274] using wordTrace_append hprefix tailTrace_1465274
  have hstable : (prefixWord ++ tailWord_1465274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465274).length < 2 ^ (prefixWord ++ tailWord_1465274).sum := by decide
  have hdescent : baseEnd_1465274 < baseStart_1465274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465277 : List Nat := [1, 4, 1, 2, 4, 2, 1, 6]
def baseStart_1465277 : Nat := 118140960795 + 1465277 * 2 ^ 59
def prefixEnd_1465277 : Nat := 4983230072969 + 3 ^ 40 * 1465277 * 2
def baseEnd_1465277 : Nat := 111465391552321308251677

theorem tailTrace_1465277 : CollatzResearch.WordTrace tailWord_1465277 prefixEnd_1465277 111465391552321308251677 := by
  unfold tailWord_1465277
  simp only [CollatzResearch.WordTrace]
  refine ⟨53443042712559153233338085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35628695141706102155558723 53443042712559153233338085)
  ·
    refine ⟨10020570508604841231250891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53443042712559153233338085 10020570508604841231250891)
    ·
      refine ⟨15030855762907261846876337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10020570508604841231250891 15030855762907261846876337)
      ·
        refine ⟨11273141822180446385157253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15030855762907261846876337 11273141822180446385157253)
        ·
          refine ⟨2113714091658833697216985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11273141822180446385157253 2113714091658833697216985)
          ·
            refine ⟨1585285568744125272912739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2113714091658833697216985 1585285568744125272912739)
            ·
              refine ⟨2377928353116187909369109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585285568744125272912739 2377928353116187909369109)
              ·
                refine ⟨111465391552321308251677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2377928353116187909369109 111465391552321308251677)
                ·
                  rfl

theorem cell21_1465277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 6].length) (baseStart_1465277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465277 prefixEnd_1465277 := by exact prefixLift 1465277
  have htrace : WordTrace (prefixWord ++ tailWord_1465277) baseStart_1465277 baseEnd_1465277 := by
    simpa [prefixWord, tailWord_1465277, baseEnd_1465277] using wordTrace_append hprefix tailTrace_1465277
  have hstable : (prefixWord ++ tailWord_1465277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465277).length < 2 ^ (prefixWord ++ tailWord_1465277).sum := by decide
  have hdescent : baseEnd_1465277 < baseStart_1465277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465322 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_1465322 : Nat := 118140960795 + 1465322 * 2 ^ 59
def prefixEnd_1465322 : Nat := 4983230072969 + 3 ^ 40 * 1465322 * 2
def baseEnd_1465322 : Nat := 334406444270053846504939

theorem tailTrace_1465322 : CollatzResearch.WordTrace tailWord_1465322 prefixEnd_1465322 334406444270053846504939 := by
  unfold tailWord_1465322
  simp only [CollatzResearch.WordTrace]
  refine ⟨13361170999349031479681555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35629789331597417279150813 13361170999349031479681555)
  ·
    refine ⟨20041756499023547219522333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13361170999349031479681555 20041756499023547219522333)
    ·
      refine ⟨7515658687133830207320875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20041756499023547219522333 7515658687133830207320875)
      ·
        refine ⟨11273488030700745310981313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7515658687133830207320875 11273488030700745310981313)
        ·
          refine ⟨8455116023025558983235985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11273488030700745310981313 8455116023025558983235985)
          ·
            refine ⟨6341337017269169237426989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8455116023025558983235985 6341337017269169237426989)
            ·
              refine ⟨2378001381475938464035121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6341337017269169237426989 2378001381475938464035121)
              ·
                refine ⟨1783501036106953848026341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378001381475938464035121 1783501036106953848026341)
                ·
                  refine ⟨334406444270053846504939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1783501036106953848026341 334406444270053846504939)
                  ·
                    rfl

theorem cell21_1465322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_1465322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465322 prefixEnd_1465322 := by exact prefixLift 1465322
  have htrace : WordTrace (prefixWord ++ tailWord_1465322) baseStart_1465322 baseEnd_1465322 := by
    simpa [prefixWord, tailWord_1465322, baseEnd_1465322] using wordTrace_append hprefix tailTrace_1465322
  have hstable : (prefixWord ++ tailWord_1465322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465322).length < 2 ^ (prefixWord ++ tailWord_1465322).sum := by decide
  have hdescent : baseEnd_1465322 < baseStart_1465322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465381 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 4]
def baseStart_1465381 : Nat := 118140960795 + 1465381 * 2 ^ 59
def prefixEnd_1465381 : Nat := 4983230072969 + 3 ^ 40 * 1465381 * 2
def baseEnd_1465381 : Nat := 334419908873882855021485

theorem tailTrace_1465381 : CollatzResearch.WordTrace tailWord_1465381 prefixEnd_1465381 334419908873882855021485 := by
  unfold tailWord_1465381
  simp only [CollatzResearch.WordTrace]
  refine ⟨53446835904182378995123997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35631223936121585996749331 53446835904182378995123997)
  ·
    refine ⟨20042563464068392123171499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53446835904182378995123997 20042563464068392123171499)
    ·
      refine ⟨30063845196102588184757249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20042563464068392123171499 30063845196102588184757249)
      ·
        refine ⟨22547883897076941138567937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30063845196102588184757249 22547883897076941138567937)
        ·
          refine ⟨16910912922807705853925953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22547883897076941138567937 16910912922807705853925953)
          ·
            refine ⟨12683184692105779390444465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16910912922807705853925953 12683184692105779390444465)
            ·
              refine ⟨9512388519079334542833349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12683184692105779390444465 9512388519079334542833349)
              ·
                refine ⟨1783572847327375226781253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9512388519079334542833349 1783572847327375226781253)
                ·
                  refine ⟨334419908873882855021485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1783572847327375226781253 334419908873882855021485)
                  ·
                    rfl

theorem cell21_1465381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_1465381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465381 prefixEnd_1465381 := by exact prefixLift 1465381
  have htrace : WordTrace (prefixWord ++ tailWord_1465381) baseStart_1465381 baseEnd_1465381 := by
    simpa [prefixWord, tailWord_1465381, baseEnd_1465381] using wordTrace_append hprefix tailTrace_1465381
  have hstable : (prefixWord ++ tailWord_1465381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465381).length < 2 ^ (prefixWord ++ tailWord_1465381).sum := by decide
  have hdescent : baseEnd_1465381 < baseStart_1465381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465609 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 4]
def baseStart_1465609 : Nat := 118140960795 + 1465609 * 2 ^ 59
def prefixEnd_1465609 : Nat := 4983230072969 + 3 ^ 40 * 1465609 * 2
def baseEnd_1465609 : Nat := 334471941580205125221019

theorem tailTrace_1465609 : CollatzResearch.WordTrace tailWord_1465609 prefixEnd_1465609 334471941580205125221019 := by
  unfold tailWord_1465609
  simp only [CollatzResearch.WordTrace]
  refine ⟨53455151747356373934423881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35636767831570915956282587 53455151747356373934423881)
  ·
    refine ⟨40091363810517280450817911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53455151747356373934423881 40091363810517280450817911)
    ·
      refine ⟨60137045715775920676226867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40091363810517280450817911 60137045715775920676226867)
      ·
        refine ⟨90205568573663881014340301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60137045715775920676226867 90205568573663881014340301)
        ·
          refine ⟨33827088215123955380377613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90205568573663881014340301 33827088215123955380377613)
          ·
            refine ⟨12685158080671483267641605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33827088215123955380377613 12685158080671483267641605)
            ·
              refine ⟨2378467140125903112682801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12685158080671483267641605 2378467140125903112682801)
              ·
                refine ⟨1783850355094427334512101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378467140125903112682801 1783850355094427334512101)
                ·
                  refine ⟨334471941580205125221019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1783850355094427334512101 334471941580205125221019)
                  ·
                    rfl

theorem cell21_1465609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_1465609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465609 prefixEnd_1465609 := by exact prefixLift 1465609
  have htrace : WordTrace (prefixWord ++ tailWord_1465609) baseStart_1465609 baseEnd_1465609 := by
    simpa [prefixWord, tailWord_1465609, baseEnd_1465609] using wordTrace_append hprefix tailTrace_1465609
  have hstable : (prefixWord ++ tailWord_1465609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465609).length < 2 ^ (prefixWord ++ tailWord_1465609).sum := by decide
  have hdescent : baseEnd_1465609 < baseStart_1465609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465612 : List Nat := [2, 2, 1, 2, 2, 3, 4, 2, 3]
def baseStart_1465612 : Nat := 118140960795 + 1465612 * 2 ^ 59
def prefixEnd_1465612 : Nat := 4983230072969 + 3 ^ 40 * 1465612 * 2
def baseEnd_1465612 : Nat := 334472626221077786671013

theorem tailTrace_1465612 : CollatzResearch.WordTrace tailWord_1465612 prefixEnd_1465612 334472626221077786671013 := by
  unfold tailWord_1465612
  simp only [CollatzResearch.WordTrace]
  refine ⟨26727630583172752723391545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35636840777563670297855393 26727630583172752723391545)
  ·
    refine ⟨20045722937379564542543659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26727630583172752723391545 20045722937379564542543659)
    ·
      refine ⟨30068584406069346813815489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20045722937379564542543659 30068584406069346813815489)
      ·
        refine ⟨22551438304552010110361617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30068584406069346813815489 22551438304552010110361617)
        ·
          refine ⟨16913578728414007582771213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22551438304552010110361617 16913578728414007582771213)
          ·
            refine ⟨6342592023155252843539205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16913578728414007582771213 6342592023155252843539205)
            ·
              refine ⟨1189236004341609908163601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6342592023155252843539205 1189236004341609908163601)
              ·
                refine ⟨891927003256207431122701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1189236004341609908163601 891927003256207431122701)
                ·
                  refine ⟨334472626221077786671013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891927003256207431122701 334472626221077786671013)
                  ·
                    rfl

theorem cell21_1465612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_1465612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465612 prefixEnd_1465612 := by exact prefixLift 1465612
  have htrace : WordTrace (prefixWord ++ tailWord_1465612) baseStart_1465612 baseEnd_1465612 := by
    simpa [prefixWord, tailWord_1465612, baseEnd_1465612] using wordTrace_append hprefix tailTrace_1465612
  have hstable : (prefixWord ++ tailWord_1465612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465612).length < 2 ^ (prefixWord ++ tailWord_1465612).sum := by decide
  have hdescent : baseEnd_1465612 < baseStart_1465612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465671 : List Nat := [1, 1, 4, 1, 2, 3, 2, 4, 3]
def baseStart_1465671 : Nat := 118140960795 + 1465671 * 2 ^ 59
def prefixEnd_1465671 : Nat := 4983230072969 + 3 ^ 40 * 1465671 * 2
def baseEnd_1465671 : Nat := 334486090824906795187559

theorem tailTrace_1465671 : CollatzResearch.WordTrace tailWord_1465671 prefixEnd_1465671 334486090824906795187559 := by
  unfold tailWord_1465671
  simp only [CollatzResearch.WordTrace]
  refine ⟨53457413073131758523180867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35638275382087839015453911 53457413073131758523180867)
  ·
    refine ⟨80186119609697637784771301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53457413073131758523180867 80186119609697637784771301)
    ·
      refine ⟨15034897426818307084644619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80186119609697637784771301 15034897426818307084644619)
      ·
        refine ⟨22552346140227460626966929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15034897426818307084644619 22552346140227460626966929)
        ·
          refine ⟨16914259605170595470225197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22552346140227460626966929 16914259605170595470225197)
          ·
            refine ⟨6342847351938973301334449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16914259605170595470225197 6342847351938973301334449)
            ·
              refine ⟨4757135513954229976000837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6342847351938973301334449 4757135513954229976000837)
              ·
                refine ⟨891962908866418120500157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4757135513954229976000837 891962908866418120500157)
                ·
                  refine ⟨334486090824906795187559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891962908866418120500157 334486090824906795187559)
                  ·
                    rfl

theorem cell21_1465671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 3].length) (baseStart_1465671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465671 prefixEnd_1465671 := by exact prefixLift 1465671
  have htrace : WordTrace (prefixWord ++ tailWord_1465671) baseStart_1465671 baseEnd_1465671 := by
    simpa [prefixWord, tailWord_1465671, baseEnd_1465671] using wordTrace_append hprefix tailTrace_1465671
  have hstable : (prefixWord ++ tailWord_1465671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465671).length < 2 ^ (prefixWord ++ tailWord_1465671).sum := by decide
  have hdescent : baseEnd_1465671 < baseStart_1465671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465699 : List Nat := [1, 1, 1, 5, 2, 3, 1, 7]
def baseStart_1465699 : Nat := 118140960795 + 1465699 * 2 ^ 59
def prefixEnd_1465699 : Nat := 4983230072969 + 3 ^ 40 * 1465699 * 2
def baseEnd_1465699 : Nat := 111497493602128322906945

theorem tailTrace_1465699 : CollatzResearch.WordTrace tailWord_1465699 prefixEnd_1465699 111497493602128322906945 := by
  unfold tailWord_1465699
  simp only [CollatzResearch.WordTrace]
  refine ⟨53458434317030319305200151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35638956211353546203466767 53458434317030319305200151)
  ·
    refine ⟨80187651475545478957800227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53458434317030319305200151 80187651475545478957800227)
    ·
      refine ⟨120281477213318218436700341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80187651475545478957800227 120281477213318218436700341)
      ·
        refine ⟨11276388488748582978440657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120281477213318218436700341 11276388488748582978440657)
        ·
          refine ⟨8457291366561437233830493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11276388488748582978440657 8457291366561437233830493)
          ·
            refine ⟨3171484262460538962686435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8457291366561437233830493 3171484262460538962686435)
            ·
              refine ⟨4757226393690808444029653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3171484262460538962686435 4757226393690808444029653)
              ·
                refine ⟨111497493602128322906945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4757226393690808444029653 111497493602128322906945)
                ·
                  rfl

theorem cell21_1465699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 7].length) (baseStart_1465699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465699 prefixEnd_1465699 := by exact prefixLift 1465699
  have htrace : WordTrace (prefixWord ++ tailWord_1465699) baseStart_1465699 baseEnd_1465699 := by
    simpa [prefixWord, tailWord_1465699, baseEnd_1465699] using wordTrace_append hprefix tailTrace_1465699
  have hstable : (prefixWord ++ tailWord_1465699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465699).length < 2 ^ (prefixWord ++ tailWord_1465699).sum := by decide
  have hdescent : baseEnd_1465699 < baseStart_1465699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465713 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 7]
def baseStart_1465713 : Nat := 118140960795 + 1465713 * 2 ^ 59
def prefixEnd_1465713 : Nat := 4983230072969 + 3 ^ 40 * 1465713 * 2
def baseEnd_1465713 : Nat := 334495675797124055487473

theorem tailTrace_1465713 : CollatzResearch.WordTrace tailWord_1465713 prefixEnd_1465713 334495675797124055487473 := by
  unfold tailWord_1465713
  simp only [CollatzResearch.WordTrace]
  refine ⟨53458944938979599696209793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35639296625986399797473195 53458944938979599696209793)
  ·
    refine ⟨40094208704234699772157345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53458944938979599696209793 40094208704234699772157345)
    ·
      refine ⟨30070656528176024829118009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40094208704234699772157345 30070656528176024829118009)
      ·
        refine ⟨22552992396132018621838507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30070656528176024829118009 22552992396132018621838507)
        ·
          refine ⟨33829488594198027932757761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22552992396132018621838507 33829488594198027932757761)
          ·
            refine ⟨25372116445648520949568321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33829488594198027932757761 25372116445648520949568321)
            ·
              refine ⟨19029087334236390712176241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25372116445648520949568321 19029087334236390712176241)
              ·
                refine ⟨14271815500677293034132181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19029087334236390712176241 14271815500677293034132181)
                ·
                  refine ⟨334495675797124055487473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14271815500677293034132181 334495675797124055487473)
                  ·
                    rfl

theorem cell21_1465713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_1465713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465713 prefixEnd_1465713 := by exact prefixLift 1465713
  have htrace : WordTrace (prefixWord ++ tailWord_1465713) baseStart_1465713 baseEnd_1465713 := by
    simpa [prefixWord, tailWord_1465713, baseEnd_1465713] using wordTrace_append hprefix tailTrace_1465713
  have hstable : (prefixWord ++ tailWord_1465713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465713).length < 2 ^ (prefixWord ++ tailWord_1465713).sum := by decide
  have hdescent : baseEnd_1465713 < baseStart_1465713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465781 : List Nat := [1, 3, 3, 2, 2, 3, 2, 2, 3]
def baseStart_1465781 : Nat := 118140960795 + 1465781 * 2 ^ 59
def prefixEnd_1465781 : Nat := 4983230072969 + 3 ^ 40 * 1465781 * 2
def baseEnd_1465781 : Nat := 334511194323571048354001

theorem tailTrace_1465781 : CollatzResearch.WordTrace tailWord_1465781 prefixEnd_1465781 334511194323571048354001 := by
  unfold tailWord_1465781
  simp only [CollatzResearch.WordTrace]
  refine ⟨53461425102733247309685197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35640950068488831539790131 53461425102733247309685197)
  ·
    refine ⟨20048034413524967741131949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53461425102733247309685197 20048034413524967741131949)
    ·
      refine ⟨7518012905071862902924481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20048034413524967741131949 7518012905071862902924481)
      ·
        refine ⟨5638509678803897177193361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7518012905071862902924481 5638509678803897177193361)
        ·
          refine ⟨4228882259102922882895021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5638509678803897177193361 4228882259102922882895021)
          ·
            refine ⟨1585830847163596081085633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4228882259102922882895021 1585830847163596081085633)
            ·
              refine ⟨1189373135372697060814225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1585830847163596081085633 1189373135372697060814225)
              ·
                refine ⟨892029851529522795610669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1189373135372697060814225 892029851529522795610669)
                ·
                  refine ⟨334511194323571048354001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892029851529522795610669 334511194323571048354001)
                  ·
                    rfl

theorem cell21_1465781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_1465781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465781 prefixEnd_1465781 := by exact prefixLift 1465781
  have htrace : WordTrace (prefixWord ++ tailWord_1465781) baseStart_1465781 baseEnd_1465781 := by
    simpa [prefixWord, tailWord_1465781, baseEnd_1465781] using wordTrace_append hprefix tailTrace_1465781
  have hstable : (prefixWord ++ tailWord_1465781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465781).length < 2 ^ (prefixWord ++ tailWord_1465781).sum := by decide
  have hdescent : baseEnd_1465781 < baseStart_1465781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465823 : List Nat := [1, 1, 2, 3, 3, 1, 4, 3, 3]
def baseStart_1465823 : Nat := 118140960795 + 1465823 * 2 ^ 59
def prefixEnd_1465823 : Nat := 4983230072969 + 3 ^ 40 * 1465823 * 2
def baseEnd_1465823 : Nat := 334520779295788308653915

theorem tailTrace_1465823 : CollatzResearch.WordTrace tailWord_1465823 prefixEnd_1465823 334520779295788308653915 := by
  unfold tailWord_1465823
  simp only [CollatzResearch.WordTrace]
  refine ⟨53462956968581088482714123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35641971312387392321809415 53462956968581088482714123)
  ·
    refine ⟨80194435452871632724071185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53462956968581088482714123 80194435452871632724071185)
    ·
      refine ⟨60145826589653724543053389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80194435452871632724071185 60145826589653724543053389)
      ·
        refine ⟨22554684971120146703645021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60145826589653724543053389 22554684971120146703645021)
        ·
          refine ⟨8458006864170055013866883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22554684971120146703645021 8458006864170055013866883)
          ·
            refine ⟨12687010296255082520800325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8458006864170055013866883 12687010296255082520800325)
            ·
              refine ⟨2378814430547827972650061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12687010296255082520800325 2378814430547827972650061)
              ·
                refine ⟨892055411455435489743773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2378814430547827972650061 892055411455435489743773)
                ·
                  refine ⟨334520779295788308653915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892055411455435489743773 334520779295788308653915)
                  ·
                    rfl

theorem cell21_1465823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 3].length) (baseStart_1465823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465823 prefixEnd_1465823 := by exact prefixLift 1465823
  have htrace : WordTrace (prefixWord ++ tailWord_1465823) baseStart_1465823 baseEnd_1465823 := by
    simpa [prefixWord, tailWord_1465823, baseEnd_1465823] using wordTrace_append hprefix tailTrace_1465823
  have hstable : (prefixWord ++ tailWord_1465823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465823).length < 2 ^ (prefixWord ++ tailWord_1465823).sum := by decide
  have hdescent : baseEnd_1465823 < baseStart_1465823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465865 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 5]
def baseStart_1465865 : Nat := 118140960795 + 1465865 * 2 ^ 59
def prefixEnd_1465865 : Nat := 4983230072969 + 3 ^ 40 * 1465865 * 2
def baseEnd_1465865 : Nat := 334530364268005568953829

theorem tailTrace_1465865 : CollatzResearch.WordTrace tailWord_1465865 prefixEnd_1465865 334530364268005568953829 := by
  unfold tailWord_1465865
  simp only [CollatzResearch.WordTrace]
  refine ⟨53464488834428929655743049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35642992556285953103828699 53464488834428929655743049)
  ·
    refine ⟨40098366625821697241807287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53464488834428929655743049 40098366625821697241807287)
    ·
      refine ⟨60147549938732545862710931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40098366625821697241807287 60147549938732545862710931)
      ·
        refine ⟨90221324908098818794066397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60147549938732545862710931 90221324908098818794066397)
        ·
          refine ⟨33832996840537057047774899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90221324908098818794066397 33832996840537057047774899)
          ·
            refine ⟨50749495260805585571662349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33832996840537057047774899 50749495260805585571662349)
            ·
              refine ⟨19031060722802094589373381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50749495260805585571662349 19031060722802094589373381)
              ·
                refine ⟨3568323885525392735507509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19031060722802094589373381 3568323885525392735507509)
                ·
                  refine ⟨334530364268005568953829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3568323885525392735507509 334530364268005568953829)
                  ·
                    rfl

theorem cell21_1465865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_1465865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465865 prefixEnd_1465865 := by exact prefixLift 1465865
  have htrace : WordTrace (prefixWord ++ tailWord_1465865) baseStart_1465865 baseEnd_1465865 := by
    simpa [prefixWord, tailWord_1465865, baseEnd_1465865] using wordTrace_append hprefix tailTrace_1465865
  have hstable : (prefixWord ++ tailWord_1465865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465865).length < 2 ^ (prefixWord ++ tailWord_1465865).sum := by decide
  have hdescent : baseEnd_1465865 < baseStart_1465865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465913 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 4]
def baseStart_1465913 : Nat := 118140960795 + 1465913 * 2 ^ 59
def prefixEnd_1465913 : Nat := 4983230072969 + 3 ^ 40 * 1465913 * 2
def baseEnd_1465913 : Nat := 334541318521968152153731

theorem tailTrace_1465913 : CollatzResearch.WordTrace tailWord_1465913 prefixEnd_1465913 334541318521968152153731 := by
  unfold tailWord_1465913
  simp only [CollatzResearch.WordTrace]
  refine ⟨53466239538255033853490393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35644159692170022568993595 53466239538255033853490393)
  ·
    refine ⟨40099679653691275390117795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53466239538255033853490393 40099679653691275390117795)
    ·
      refine ⟨60149519480536913085176693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40099679653691275390117795 60149519480536913085176693)
      ·
        refine ⟨5639017451300335601735315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60149519480536913085176693 5639017451300335601735315)
        ·
          refine ⟨8458526176950503402602973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5639017451300335601735315 8458526176950503402602973)
          ·
            refine ⟨3171947316356438775976115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8458526176950503402602973 3171947316356438775976115)
            ·
              refine ⟨4757920974534658163964173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3171947316356438775976115 4757920974534658163964173)
              ·
                refine ⟨1784220365450496811486565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4757920974534658163964173 1784220365450496811486565)
                ·
                  refine ⟨334541318521968152153731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784220365450496811486565 334541318521968152153731)
                  ·
                    rfl

theorem cell21_1465913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_1465913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1465913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1465913 prefixEnd_1465913 := by exact prefixLift 1465913
  have htrace : WordTrace (prefixWord ++ tailWord_1465913) baseStart_1465913 baseEnd_1465913 := by
    simpa [prefixWord, tailWord_1465913, baseEnd_1465913] using wordTrace_append hprefix tailTrace_1465913
  have hstable : (prefixWord ++ tailWord_1465913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465913).length < 2 ^ (prefixWord ++ tailWord_1465913).sum := by decide
  have hdescent : baseEnd_1465913 < baseStart_1465913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466037 : List Nat := [1, 3, 3, 3, 2, 2, 2, 5]
def baseStart_1466037 : Nat := 118140960795 + 1466037 * 2 ^ 59
def prefixEnd_1466037 : Nat := 4983230072969 + 3 ^ 40 * 1466037 * 2
def baseEnd_1466037 : Nat := 111523205670457164028937

theorem tailTrace_1466037 : CollatzResearch.WordTrace tailWord_1466037 prefixEnd_1466037 111523205670457164028937 := by
  unfold tailWord_1466037
  simp only [CollatzResearch.WordTrace]
  refine ⟨53470762189805803031004365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35647174793203868687336243 53470762189805803031004365)
  ·
    refine ⟨20051535821177176136626637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53470762189805803031004365 20051535821177176136626637)
    ·
      refine ⟨7519325932941441051234989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20051535821177176136626637 7519325932941441051234989)
      ·
        refine ⟨2819747224853040394213121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7519325932941441051234989 2819747224853040394213121)
        ·
          refine ⟨2114810418639780295659841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2819747224853040394213121 2114810418639780295659841)
          ·
            refine ⟨1586107813979835221744881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2114810418639780295659841 1586107813979835221744881)
            ·
              refine ⟨1189580860484876416308661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586107813979835221744881 1189580860484876416308661)
              ·
                refine ⟨111523205670457164028937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1189580860484876416308661 111523205670457164028937)
                ·
                  rfl

theorem cell21_1466037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 5].length) (baseStart_1466037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466037 prefixEnd_1466037 := by exact prefixLift 1466037
  have htrace : WordTrace (prefixWord ++ tailWord_1466037) baseStart_1466037 baseEnd_1466037 := by
    simpa [prefixWord, tailWord_1466037, baseEnd_1466037] using wordTrace_append hprefix tailTrace_1466037
  have hstable : (prefixWord ++ tailWord_1466037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466037).length < 2 ^ (prefixWord ++ tailWord_1466037).sum := by decide
  have hdescent : baseEnd_1466037 < baseStart_1466037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466107 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 6]
def baseStart_1466107 : Nat := 118140960795 + 1466107 * 2 ^ 59
def prefixEnd_1466107 : Nat := 4983230072969 + 3 ^ 40 * 1466107 * 2
def baseEnd_1466107 : Nat := 334585591965066925920001

theorem tailTrace_1466107 : CollatzResearch.WordTrace tailWord_1466107 prefixEnd_1466107 334585591965066925920001 := by
  unfold tailWord_1466107
  simp only [CollatzResearch.WordTrace]
  refine ⟨53473315299552204986052575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35648876866368136657368383 53473315299552204986052575)
  ·
    refine ⟨80209972949328307479078863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53473315299552204986052575 80209972949328307479078863)
    ·
      refine ⟨120314959423992461218618295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80209972949328307479078863 120314959423992461218618295)
      ·
        refine ⟨180472439135988691827927443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120314959423992461218618295 180472439135988691827927443)
        ·
          refine ⟨270708658703983037741891165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180472439135988691827927443 270708658703983037741891165)
          ·
            refine ⟨101515747013993639153209187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270708658703983037741891165 101515747013993639153209187)
            ·
              refine ⟨152273620520990458729813781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101515747013993639153209187 152273620520990458729813781)
              ·
                refine ⟨7137825961921427752960021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 152273620520990458729813781 7137825961921427752960021)
                ·
                  refine ⟨334585591965066925920001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7137825961921427752960021 334585591965066925920001)
                  ·
                    rfl

theorem cell21_1466107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_1466107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466107 prefixEnd_1466107 := by exact prefixLift 1466107
  have htrace : WordTrace (prefixWord ++ tailWord_1466107) baseStart_1466107 baseEnd_1466107 := by
    simpa [prefixWord, tailWord_1466107, baseEnd_1466107] using wordTrace_append hprefix tailTrace_1466107
  have hstable : (prefixWord ++ tailWord_1466107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466107).length < 2 ^ (prefixWord ++ tailWord_1466107).sum := by decide
  have hdescent : baseEnd_1466107 < baseStart_1466107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466124 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 4]
def baseStart_1466124 : Nat := 118140960795 + 1466124 * 2 ^ 59
def prefixEnd_1466124 : Nat := 4983230072969 + 3 ^ 40 * 1466124 * 2
def baseEnd_1466124 : Nat := 334589471596678674136633

theorem tailTrace_1466124 : CollatzResearch.WordTrace tailWord_1466124 prefixEnd_1466124 334589471596678674136633 := by
  unfold tailWord_1466124
  simp only [CollatzResearch.WordTrace]
  refine ⟨26736967670245308444710713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35649290226993744592947617 26736967670245308444710713)
  ·
    refine ⟨20052725752683981333533035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26736967670245308444710713 20052725752683981333533035)
    ·
      refine ⟨30079088629025972000299553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20052725752683981333533035 30079088629025972000299553)
      ·
        refine ⟨22559316471769479000224665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30079088629025972000299553 22559316471769479000224665)
        ·
          refine ⟨16919487353827109250168499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22559316471769479000224665 16919487353827109250168499)
          ·
            refine ⟨25379231030740663875252749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16919487353827109250168499 25379231030740663875252749)
            ·
              refine ⟨9517211636527748953219781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25379231030740663875252749 9517211636527748953219781)
              ·
                refine ⟨1784477181848952928728709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9517211636527748953219781 1784477181848952928728709)
                ·
                  refine ⟨334589471596678674136633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784477181848952928728709 334589471596678674136633)
                  ·
                    rfl

theorem cell21_1466124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_1466124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466124 prefixEnd_1466124 := by exact prefixLift 1466124
  have htrace : WordTrace (prefixWord ++ tailWord_1466124) baseStart_1466124 baseEnd_1466124 := by
    simpa [prefixWord, tailWord_1466124, baseEnd_1466124] using wordTrace_append hprefix tailTrace_1466124
  have hstable : (prefixWord ++ tailWord_1466124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466124).length < 2 ^ (prefixWord ++ tailWord_1466124).sum := by decide
  have hdescent : baseEnd_1466124 < baseStart_1466124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466186 : List Nat := [3, 1, 2, 1, 1, 1, 3, 6, 3]
def baseStart_1466186 : Nat := 118140960795 + 1466186 * 2 ^ 59
def prefixEnd_1466186 : Nat := 4983230072969 + 3 ^ 40 * 1466186 * 2
def baseEnd_1466186 : Nat := 334603620841380344103173

theorem tailTrace_1466186 : CollatzResearch.WordTrace tailWord_1466186 prefixEnd_1466186 334603620841380344103173 := by
  unfold tailWord_1466186
  simp only [CollatzResearch.WordTrace]
  refine ⟨13369049166566500369544603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35650797777510667652118941 13369049166566500369544603)
  ·
    refine ⟨20053573749849750554316905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13369049166566500369544603 20053573749849750554316905)
    ·
      refine ⟨15040180312387312915737679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20053573749849750554316905 15040180312387312915737679)
      ·
        refine ⟨22560270468580969373606519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15040180312387312915737679 22560270468580969373606519)
        ·
          refine ⟨33840405702871454060409779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22560270468580969373606519 33840405702871454060409779)
          ·
            refine ⟨50760608554307181090614669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33840405702871454060409779 50760608554307181090614669)
            ·
              refine ⟨19035228207865192908980501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50760608554307181090614669 19035228207865192908980501)
              ·
                refine ⟨892276322243680917608461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19035228207865192908980501 892276322243680917608461)
                ·
                  refine ⟨334603620841380344103173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892276322243680917608461 334603620841380344103173)
                  ·
                    rfl

theorem cell21_1466186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_1466186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466186 prefixEnd_1466186 := by exact prefixLift 1466186
  have htrace : WordTrace (prefixWord ++ tailWord_1466186) baseStart_1466186 baseEnd_1466186 := by
    simpa [prefixWord, tailWord_1466186, baseEnd_1466186] using wordTrace_append hprefix tailTrace_1466186
  have hstable : (prefixWord ++ tailWord_1466186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466186).length < 2 ^ (prefixWord ++ tailWord_1466186).sum := by decide
  have hdescent : baseEnd_1466186 < baseStart_1466186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466293 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 4]
def baseStart_1466293 : Nat := 118140960795 + 1466293 * 2 ^ 59
def prefixEnd_1466293 : Nat := 4983230072969 + 3 ^ 40 * 1466293 * 2
def baseEnd_1466293 : Nat := 334628039699171935819621

theorem tailTrace_1466293 : CollatzResearch.WordTrace tailWord_1466293 prefixEnd_1466293 334628039699171935819621 := by
  unfold tailWord_1466293
  simp only [CollatzResearch.WordTrace]
  refine ⟨53480099276878358752323533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35653399517918905834882355 53480099276878358752323533)
  ·
    refine ⟨20055037228829384532121325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53480099276878358752323533 20055037228829384532121325)
    ·
      refine ⟨7520638960811019199545497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20055037228829384532121325 7520638960811019199545497)
      ·
        refine ⟨5640479220608264399659123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7520638960811019199545497 5640479220608264399659123)
        ·
          refine ⟨8460718830912396599488685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5640479220608264399659123 8460718830912396599488685)
          ·
            refine ⟨3172769561592148724808257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8460718830912396599488685 3172769561592148724808257)
            ·
              refine ⟨2379577171194111543606193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3172769561592148724808257 2379577171194111543606193)
              ·
                refine ⟨1784682878395583657704645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2379577171194111543606193 1784682878395583657704645)
                ·
                  refine ⟨334628039699171935819621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784682878395583657704645 334628039699171935819621)
                  ·
                    rfl

theorem cell21_1466293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_1466293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466293 prefixEnd_1466293 := by exact prefixLift 1466293
  have htrace : WordTrace (prefixWord ++ tailWord_1466293) baseStart_1466293 baseEnd_1466293 := by
    simpa [prefixWord, tailWord_1466293, baseEnd_1466293] using wordTrace_append hprefix tailTrace_1466293
  have hstable : (prefixWord ++ tailWord_1466293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466293).length < 2 ^ (prefixWord ++ tailWord_1466293).sum := by decide
  have hdescent : baseEnd_1466293 < baseStart_1466293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466352 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 4]
def baseStart_1466352 : Nat := 118140960795 + 1466352 * 2 ^ 59
def prefixEnd_1466352 : Nat := 4983230072969 + 3 ^ 40 * 1466352 * 2
def baseEnd_1466352 : Nat := 334641504303000944336167

theorem tailTrace_1466352 : CollatzResearch.WordTrace tailWord_1466352 prefixEnd_1466352 334641504303000944336167 := by
  unfold tailWord_1466352
  simp only [CollatzResearch.WordTrace]
  refine ⟨26741125591832305914360655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35654834122443074552480873 26741125591832305914360655)
  ·
    refine ⟨40111688387748458871540983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26741125591832305914360655 40111688387748458871540983)
    ·
      refine ⟨60167532581622688307311475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40111688387748458871540983 60167532581622688307311475)
      ·
        refine ⟨90251298872434032460967213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60167532581622688307311475 90251298872434032460967213)
        ·
          refine ⟨33844237077162762172862705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90251298872434032460967213 33844237077162762172862705)
          ·
            refine ⟨25383177807872071629647029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33844237077162762172862705 25383177807872071629647029)
            ·
              refine ⟨2379672919488006715279409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25383177807872071629647029 2379672919488006715279409)
              ·
                refine ⟨1784754689616005036459557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2379672919488006715279409 1784754689616005036459557)
                ·
                  refine ⟨334641504303000944336167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784754689616005036459557 334641504303000944336167)
                  ·
                    rfl

theorem cell21_1466352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_1466352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466352 prefixEnd_1466352 := by exact prefixLift 1466352
  have htrace : WordTrace (prefixWord ++ tailWord_1466352) baseStart_1466352 baseEnd_1466352 := by
    simpa [prefixWord, tailWord_1466352, baseEnd_1466352] using wordTrace_append hprefix tailTrace_1466352
  have hstable : (prefixWord ++ tailWord_1466352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466352).length < 2 ^ (prefixWord ++ tailWord_1466352).sum := by decide
  have hdescent : baseEnd_1466352 < baseStart_1466352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466369 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 4]
def baseStart_1466369 : Nat := 118140960795 + 1466369 * 2 ^ 59
def prefixEnd_1466369 : Nat := 4983230072969 + 3 ^ 40 * 1466369 * 2
def baseEnd_1466369 : Nat := 334645383934612692552799

theorem tailTrace_1466369 : CollatzResearch.WordTrace tailWord_1466369 prefixEnd_1466369 334645383934612692552799 := by
  unfold tailWord_1466369
  simp only [CollatzResearch.WordTrace]
  refine ⟨53482871224603023732090161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35655247483068682488060107 53482871224603023732090161)
  ·
    refine ⟨40112153418452267799067621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53482871224603023732090161 40112153418452267799067621)
    ·
      refine ⟨7521028765959800212325179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40112153418452267799067621 7521028765959800212325179)
      ·
        refine ⟨11281543148939700318487769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7521028765959800212325179 11281543148939700318487769)
        ·
          refine ⟨8461157361704775238865827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11281543148939700318487769 8461157361704775238865827)
          ·
            refine ⟨12691736042557162858298741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8461157361704775238865827 12691736042557162858298741)
            ·
              refine ⟨1189850253989734017965507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12691736042557162858298741 1189850253989734017965507)
              ·
                refine ⟨1784775380984601026948261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189850253989734017965507 1784775380984601026948261)
                ·
                  refine ⟨334645383934612692552799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784775380984601026948261 334645383934612692552799)
                  ·
                    rfl

theorem cell21_1466369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_1466369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466369 prefixEnd_1466369 := by exact prefixLift 1466369
  have htrace : WordTrace (prefixWord ++ tailWord_1466369) baseStart_1466369 baseEnd_1466369 := by
    simpa [prefixWord, tailWord_1466369, baseEnd_1466369] using wordTrace_append hprefix tailTrace_1466369
  have hstable : (prefixWord ++ tailWord_1466369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466369).length < 2 ^ (prefixWord ++ tailWord_1466369).sum := by decide
  have hdescent : baseEnd_1466369 < baseStart_1466369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466414 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_1466414 : Nat := 118140960795 + 1466414 * 2 ^ 59
def prefixEnd_1466414 : Nat := 4983230072969 + 3 ^ 40 * 1466414 * 2
def baseEnd_1466414 : Nat := 334655653547702614302707

theorem tailTrace_1466414 : CollatzResearch.WordTrace tailWord_1466414 prefixEnd_1466414 334655653547702614302707 := by
  unfold tailWord_1466414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6685564063679999552184787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35656341672959997611652197 6685564063679999552184787)
  ·
    refine ⟨10028346095519999328277181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6685564063679999552184787 10028346095519999328277181)
    ·
      refine ⟨3760629785819999748103943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10028346095519999328277181 3760629785819999748103943)
      ·
        refine ⟨5640944678729999622155915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3760629785819999748103943 5640944678729999622155915)
        ·
          refine ⟨8461417018094999433233873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5640944678729999622155915 8461417018094999433233873)
          ·
            refine ⟨6346062763571249574925405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8461417018094999433233873 6346062763571249574925405)
            ·
              refine ⟨2379773536339218590597027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6346062763571249574925405 2379773536339218590597027)
              ·
                refine ⟨3569660304508827885895541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379773536339218590597027 3569660304508827885895541)
                ·
                  refine ⟨334655653547702614302707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3569660304508827885895541 334655653547702614302707)
                  ·
                    rfl

theorem cell21_1466414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_1466414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466414 prefixEnd_1466414 := by exact prefixLift 1466414
  have htrace : WordTrace (prefixWord ++ tailWord_1466414) baseStart_1466414 baseEnd_1466414 := by
    simpa [prefixWord, tailWord_1466414, baseEnd_1466414] using wordTrace_append hprefix tailTrace_1466414
  have hstable : (prefixWord ++ tailWord_1466414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466414).length < 2 ^ (prefixWord ++ tailWord_1466414).sum := by decide
  have hdescent : baseEnd_1466414 < baseStart_1466414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466420 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1466420 : Nat := 118140960795 + 1466420 * 2 ^ 59
def prefixEnd_1466420 : Nat := 4983230072969 + 3 ^ 40 * 1466420 * 2
def baseEnd_1466420 : Nat := 334657022829447937202695

theorem tailTrace_1466420 : CollatzResearch.WordTrace tailWord_1466420 prefixEnd_1466420 334657022829447937202695 := by
  unfold tailWord_1466420
  simp only [CollatzResearch.WordTrace]
  refine ⟨26742365673709129721098357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35656487564945506294797809 26742365673709129721098357)
  ·
    refine ⟨2507096781910230911352971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26742365673709129721098357 2507096781910230911352971)
    ·
      refine ⟨3760645172865346367029457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2507096781910230911352971 3760645172865346367029457)
      ·
        refine ⟨2820483879649009775272093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3760645172865346367029457 2820483879649009775272093)
        ·
          refine ⟨1057681454868378665727035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2820483879649009775272093 1057681454868378665727035)
          ·
            refine ⟨1586522182302567998590553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057681454868378665727035 1586522182302567998590553)
            ·
              refine ⟨1189891636726925998942915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586522182302567998590553 1189891636726925998942915)
              ·
                refine ⟨1784837455090388998414373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189891636726925998942915 1784837455090388998414373)
                ·
                  refine ⟨334657022829447937202695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784837455090388998414373 334657022829447937202695)
                  ·
                    rfl

theorem cell21_1466420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1466420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466420 prefixEnd_1466420 := by exact prefixLift 1466420
  have htrace : WordTrace (prefixWord ++ tailWord_1466420) baseStart_1466420 baseEnd_1466420 := by
    simpa [prefixWord, tailWord_1466420, baseEnd_1466420] using wordTrace_append hprefix tailTrace_1466420
  have hstable : (prefixWord ++ tailWord_1466420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466420).length < 2 ^ (prefixWord ++ tailWord_1466420).sum := by decide
  have hdescent : baseEnd_1466420 < baseStart_1466420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466428 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 4]
def baseStart_1466428 : Nat := 118140960795 + 1466428 * 2 ^ 59
def prefixEnd_1466428 : Nat := 4983230072969 + 3 ^ 40 * 1466428 * 2
def baseEnd_1466428 : Nat := 334658848538441701069345

theorem tailTrace_1466428 : CollatzResearch.WordTrace tailWord_1466428 prefixEnd_1466428 334658848538441701069345 := by
  unfold tailWord_1466428
  simp only [CollatzResearch.WordTrace]
  refine ⟨26742511565694638404243969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35656682087592851205658625 26742511565694638404243969)
  ·
    refine ⟨20056883674270978803182977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26742511565694638404243969 20056883674270978803182977)
    ·
      refine ⟨15042662755703234102387233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20056883674270978803182977 15042662755703234102387233)
      ·
        refine ⟨11281997066777425576790425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15042662755703234102387233 11281997066777425576790425)
        ·
          refine ⟨8461497800083069182592819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11281997066777425576790425 8461497800083069182592819)
          ·
            refine ⟨12692246700124603773889229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8461497800083069182592819 12692246700124603773889229)
            ·
              refine ⟨4759592512546726415208461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12692246700124603773889229 4759592512546726415208461)
              ·
                refine ⟨1784847192205022405703173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4759592512546726415208461 1784847192205022405703173)
                ·
                  refine ⟨334658848538441701069345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784847192205022405703173 334658848538441701069345)
                  ·
                    rfl

theorem cell21_1466428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_1466428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466428 prefixEnd_1466428 := by exact prefixLift 1466428
  have htrace : WordTrace (prefixWord ++ tailWord_1466428) baseStart_1466428 baseEnd_1466428 := by
    simpa [prefixWord, tailWord_1466428, baseEnd_1466428] using wordTrace_append hprefix tailTrace_1466428
  have hstable : (prefixWord ++ tailWord_1466428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466428).length < 2 ^ (prefixWord ++ tailWord_1466428).sum := by decide
  have hdescent : baseEnd_1466428 < baseStart_1466428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466577 : List Nat := [1, 2, 2, 1, 2, 2, 11]
def baseStart_1466577 : Nat := 118140960795 + 1466577 * 2 ^ 59
def prefixEnd_1466577 : Nat := 4983230072969 + 3 ^ 40 * 1466577 * 2
def baseEnd_1466577 : Nat := 37188094707605617009523

theorem tailTrace_1466577 : CollatzResearch.WordTrace tailWord_1466577 prefixEnd_1466577 37188094707605617009523 := by
  unfold tailWord_1466577
  simp only [CollatzResearch.WordTrace]
  refine ⟨53490457607849475255661985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35660305071899650170441323 53490457607849475255661985)
  ·
    refine ⟨40117843205887106441746489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53490457607849475255661985 40117843205887106441746489)
    ·
      refine ⟨30088382404415329831309867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40117843205887106441746489 30088382404415329831309867)
      ·
        refine ⟨45132573606622994746964801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30088382404415329831309867 45132573606622994746964801)
        ·
          refine ⟨33849430204967246060223601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45132573606622994746964801 33849430204967246060223601)
          ·
            refine ⟨25387072653725434545167701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33849430204967246060223601 25387072653725434545167701)
            ·
              refine ⟨37188094707605617009523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25387072653725434545167701 37188094707605617009523)
              ·
                rfl

theorem cell21_1466577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 11].length) (baseStart_1466577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466577 prefixEnd_1466577 := by exact prefixLift 1466577
  have htrace : WordTrace (prefixWord ++ tailWord_1466577) baseStart_1466577 baseEnd_1466577 := by
    simpa [prefixWord, tailWord_1466577, baseEnd_1466577] using wordTrace_append hprefix tailTrace_1466577
  have hstable : (prefixWord ++ tailWord_1466577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466577).length < 2 ^ (prefixWord ++ tailWord_1466577).sum := by decide
  have hdescent : baseEnd_1466577 < baseStart_1466577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466597 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 4]
def baseStart_1466597 : Nat := 118140960795 + 1466597 * 2 ^ 59
def prefixEnd_1466597 : Nat := 4983230072969 + 3 ^ 40 * 1466597 * 2
def baseEnd_1466597 : Nat := 334697416640934962752333

theorem tailTrace_1466597 : CollatzResearch.WordTrace tailWord_1466597 prefixEnd_1466597 334697416640934962752333 := by
  unfold tailWord_1466597
  simp only [CollatzResearch.WordTrace]
  refine ⟨53491187067777018671390045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35660791378518012447593363 53491187067777018671390045)
  ·
    refine ⟨20059195150416382001771267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53491187067777018671390045 20059195150416382001771267)
    ·
      refine ⟨30088792725624573002656901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20059195150416382001771267 30088792725624573002656901)
      ·
        refine ⟨5641648636054607437998169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30088792725624573002656901 5641648636054607437998169)
        ·
          refine ⟨4231236477040955578498627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5641648636054607437998169 4231236477040955578498627)
          ·
            refine ⟨6346854715561433367747941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231236477040955578498627 6346854715561433367747941)
            ·
              refine ⟨1190035259167768756452739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6346854715561433367747941 1190035259167768756452739)
              ·
                refine ⟨1785052888751653134679109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190035259167768756452739 1785052888751653134679109)
                ·
                  refine ⟨334697416640934962752333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785052888751653134679109 334697416640934962752333)
                  ·
                    rfl

theorem cell21_1466597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_1466597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466597 prefixEnd_1466597 := by exact prefixLift 1466597
  have htrace : WordTrace (prefixWord ++ tailWord_1466597) baseStart_1466597 baseEnd_1466597 := by
    simpa [prefixWord, tailWord_1466597, baseEnd_1466597] using wordTrace_append hprefix tailTrace_1466597
  have hstable : (prefixWord ++ tailWord_1466597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466597).length < 2 ^ (prefixWord ++ tailWord_1466597).sum := by decide
  have hdescent : baseEnd_1466597 < baseStart_1466597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466608 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_1466608 : Nat := 118140960795 + 1466608 * 2 ^ 59
def prefixEnd_1466608 : Nat := 4983230072969 + 3 ^ 40 * 1466608 * 2
def baseEnd_1466608 : Nat := 334699926990801388068977

theorem tailTrace_1466608 : CollatzResearch.WordTrace tailWord_1466608 prefixEnd_1466608 334699926990801388068977 := by
  unfold tailWord_1466608
  simp only [CollatzResearch.WordTrace]
  refine ⟨26745794135368583775020239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35661058847158111700026985 26745794135368583775020239)
  ·
    refine ⟨40118691203052875662530359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26745794135368583775020239 40118691203052875662530359)
    ·
      refine ⟨60178036804579313493795539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40118691203052875662530359 60178036804579313493795539)
      ·
        refine ⟨90267055206868970240693309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60178036804579313493795539 90267055206868970240693309)
        ·
          refine ⟨33850145702575863840259991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90267055206868970240693309 33850145702575863840259991)
          ·
            refine ⟨50775218553863795760389987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33850145702575863840259991 50775218553863795760389987)
            ·
              refine ⟨76162827830795693640584981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50775218553863795760389987 76162827830795693640584981)
              ·
                refine ⟨3570132554568548139402421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76162827830795693640584981 3570132554568548139402421)
                ·
                  refine ⟨334699926990801388068977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3570132554568548139402421 334699926990801388068977)
                  ·
                    rfl

theorem cell21_1466608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_1466608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466608 prefixEnd_1466608 := by exact prefixLift 1466608
  have htrace : WordTrace (prefixWord ++ tailWord_1466608) baseStart_1466608 baseEnd_1466608 := by
    simpa [prefixWord, tailWord_1466608, baseEnd_1466608] using wordTrace_append hprefix tailTrace_1466608
  have hstable : (prefixWord ++ tailWord_1466608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466608).length < 2 ^ (prefixWord ++ tailWord_1466608).sum := by decide
  have hdescent : baseEnd_1466608 < baseStart_1466608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466656 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 4]
def baseStart_1466656 : Nat := 118140960795 + 1466656 * 2 ^ 59
def prefixEnd_1466656 : Nat := 4983230072969 + 3 ^ 40 * 1466656 * 2
def baseEnd_1466656 : Nat := 334710881244763971268879

theorem tailTrace_1466656 : CollatzResearch.WordTrace tailWord_1466656 prefixEnd_1466656 334710881244763971268879 := by
  unfold tailWord_1466656
  simp only [CollatzResearch.WordTrace]
  refine ⟨26746669487281635873893911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35662225983042181165191881 26746669487281635873893911)
  ·
    refine ⟨40120004230922453810840867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26746669487281635873893911 40120004230922453810840867)
    ·
      refine ⟨60180006346383680716261301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40120004230922453810840867 60180006346383680716261301)
      ·
        refine ⟨5641875594973470067149497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60180006346383680716261301 5641875594973470067149497)
        ·
          refine ⟨4231406696230102550362123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5641875594973470067149497 4231406696230102550362123)
          ·
            refine ⟨6347110044345153825543185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231406696230102550362123 6347110044345153825543185)
            ·
              refine ⟨4760332533258865369157389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6347110044345153825543185 4760332533258865369157389)
              ·
                refine ⟨1785124699972074513434021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4760332533258865369157389 1785124699972074513434021)
                ·
                  refine ⟨334710881244763971268879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785124699972074513434021 334710881244763971268879)
                  ·
                    rfl

theorem cell21_1466656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_1466656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466656 prefixEnd_1466656 := by exact prefixLift 1466656
  have htrace : WordTrace (prefixWord ++ tailWord_1466656) baseStart_1466656 baseEnd_1466656 := by
    simpa [prefixWord, tailWord_1466656, baseEnd_1466656] using wordTrace_append hprefix tailTrace_1466656
  have hstable : (prefixWord ++ tailWord_1466656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466656).length < 2 ^ (prefixWord ++ tailWord_1466656).sum := by decide
  have hdescent : baseEnd_1466656 < baseStart_1466656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466684 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_1466684 : Nat := 118140960795 + 1466684 * 2 ^ 59
def prefixEnd_1466684 : Nat := 4983230072969 + 3 ^ 40 * 1466684 * 2
def baseEnd_1466684 : Nat := 334717271226242144802155

theorem tailTrace_1466684 : CollatzResearch.WordTrace tailWord_1466684 prefixEnd_1466684 334717271226242144802155 := by
  unfold tailWord_1466684
  simp only [CollatzResearch.WordTrace]
  refine ⟨26747180109230916264903553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35662906812307888353204737 26747180109230916264903553)
  ·
    refine ⟨20060385081923187198677665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26747180109230916264903553 20060385081923187198677665)
    ·
      refine ⟨15045288811442390399008249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20060385081923187198677665 15045288811442390399008249)
      ·
        refine ⟨11283966608581792799256187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15045288811442390399008249 11283966608581792799256187)
        ·
          refine ⟨16925949912872689198884281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11283966608581792799256187 16925949912872689198884281)
          ·
            refine ⟨12694462434654516899163211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16925949912872689198884281 12694462434654516899163211)
            ·
              refine ⟨19041693651981775348744817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12694462434654516899163211 19041693651981775348744817)
              ·
                refine ⟨14281270238986331511558613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19041693651981775348744817 14281270238986331511558613)
                ·
                  refine ⟨334717271226242144802155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14281270238986331511558613 334717271226242144802155)
                  ·
                    rfl

theorem cell21_1466684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_1466684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466684 prefixEnd_1466684 := by exact prefixLift 1466684
  have htrace : WordTrace (prefixWord ++ tailWord_1466684) baseStart_1466684 baseEnd_1466684 := by
    simpa [prefixWord, tailWord_1466684, baseEnd_1466684] using wordTrace_append hprefix tailTrace_1466684
  have hstable : (prefixWord ++ tailWord_1466684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466684).length < 2 ^ (prefixWord ++ tailWord_1466684).sum := by decide
  have hdescent : baseEnd_1466684 < baseStart_1466684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466729 : List Nat := [1, 2, 1, 1, 1, 3, 5, 7]
def baseStart_1466729 : Nat := 118140960795 + 1466729 * 2 ^ 59
def prefixEnd_1466729 : Nat := 4983230072969 + 3 ^ 40 * 1466729 * 2
def baseEnd_1466729 : Nat := 111575846946444022184021

theorem tailTrace_1466729 : CollatzResearch.WordTrace tailWord_1466729 prefixEnd_1466729 111575846946444022184021 := by
  unfold tailWord_1466729
  simp only [CollatzResearch.WordTrace]
  refine ⟨53496001503298805215195241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35664001002199203476796827 53496001503298805215195241)
  ·
    refine ⟨40122001127474103911396431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53496001503298805215195241 40122001127474103911396431)
    ·
      refine ⟨60183001691211155867094647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40122001127474103911396431 60183001691211155867094647)
      ·
        refine ⟨90274502536816733800641971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60183001691211155867094647 90274502536816733800641971)
        ·
          refine ⟨135411753805225100700962957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90274502536816733800641971 135411753805225100700962957)
          ·
            refine ⟨50779407676959412762861109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135411753805225100700962957 50779407676959412762861109)
            ·
              refine ⟨4760569469714944946518229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50779407676959412762861109 4760569469714944946518229)
              ·
                refine ⟨111575846946444022184021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4760569469714944946518229 111575846946444022184021)
                ·
                  rfl

theorem cell21_1466729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 7].length) (baseStart_1466729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466729 prefixEnd_1466729 := by exact prefixLift 1466729
  have htrace : WordTrace (prefixWord ++ tailWord_1466729) baseStart_1466729 baseEnd_1466729 := by
    simpa [prefixWord, tailWord_1466729, baseEnd_1466729] using wordTrace_append hprefix tailTrace_1466729
  have hstable : (prefixWord ++ tailWord_1466729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466729).length < 2 ^ (prefixWord ++ tailWord_1466729).sum := by decide
  have hdescent : baseEnd_1466729 < baseStart_1466729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466766 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1466766 : Nat := 118140960795 + 1466766 * 2 ^ 59
def prefixEnd_1466766 : Nat := 4983230072969 + 3 ^ 40 * 1466766 * 2
def baseEnd_1466766 : Nat := 334735984743428224435321

theorem tailTrace_1466766 : CollatzResearch.WordTrace tailWord_1466766 prefixEnd_1466766 334735984743428224435321 := by
  unfold tailWord_1466766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687168875520595066786519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35664900669443173689528101 6687168875520595066786519)
  ·
    refine ⟨10030753313280892600179779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6687168875520595066786519 10030753313280892600179779)
    ·
      refine ⟨15046129969921338900269669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10030753313280892600179779 15046129969921338900269669)
      ·
        refine ⟨2821149369360251043800563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15046129969921338900269669 2821149369360251043800563)
        ·
          refine ⟨4231724054040376565700845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2821149369360251043800563 4231724054040376565700845)
          ·
            refine ⟨1586896520265141212137817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4231724054040376565700845 1586896520265141212137817)
            ·
              refine ⟨1190172390198855909103363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586896520265141212137817 1190172390198855909103363)
              ·
                refine ⟨1785258585298283863655045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190172390198855909103363 1785258585298283863655045)
                ·
                  refine ⟨334735984743428224435321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785258585298283863655045 334735984743428224435321)
                  ·
                    rfl

theorem cell21_1466766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1466766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466766 prefixEnd_1466766 := by exact prefixLift 1466766
  have htrace : WordTrace (prefixWord ++ tailWord_1466766) baseStart_1466766 baseEnd_1466766 := by
    simpa [prefixWord, tailWord_1466766, baseEnd_1466766] using wordTrace_append hprefix tailTrace_1466766
  have hstable : (prefixWord ++ tailWord_1466766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466766).length < 2 ^ (prefixWord ++ tailWord_1466766).sum := by decide
  have hdescent : baseEnd_1466766 < baseStart_1466766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466805 : List Nat := [1, 3, 3, 2, 12]
def baseStart_1466805 : Nat := 118140960795 + 1466805 * 2 ^ 59
def prefixEnd_1466805 : Nat := 4983230072969 + 3 ^ 40 * 1466805 * 2
def baseEnd_1466805 : Nat := 4132652902157689176361

theorem tailTrace_1466805 : CollatzResearch.WordTrace tailWord_1466805 prefixEnd_1466805 4132652902157689176361 := by
  unfold tailWord_1466805
  simp only [CollatzResearch.WordTrace]
  refine ⟨53498773451023470194961869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35665848967348980129974579 53498773451023470194961869)
  ·
    refine ⟨20062040044133801323110701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53498773451023470194961869 20062040044133801323110701)
    ·
      refine ⟨7523265016550175496166513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20062040044133801323110701 7523265016550175496166513)
      ·
        refine ⟨5642448762412631622124885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7523265016550175496166513 5642448762412631622124885)
        ·
          refine ⟨4132652902157689176361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5642448762412631622124885 4132652902157689176361)
          ·
            rfl

theorem cell21_1466805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 12].length) (baseStart_1466805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466805 prefixEnd_1466805 := by exact prefixLift 1466805
  have htrace : WordTrace (prefixWord ++ tailWord_1466805) baseStart_1466805 baseEnd_1466805 := by
    simpa [prefixWord, tailWord_1466805, baseEnd_1466805] using wordTrace_append hprefix tailTrace_1466805
  have hstable : (prefixWord ++ tailWord_1466805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466805).length < 2 ^ (prefixWord ++ tailWord_1466805).sum := by decide
  have hdescent : baseEnd_1466805 < baseStart_1466805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466870 : List Nat := [5, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1466870 : Nat := 118140960795 + 1466870 * 2 ^ 59
def prefixEnd_1466870 : Nat := 4983230072969 + 3 ^ 40 * 1466870 * 2
def baseEnd_1466870 : Nat := 334759718960347154701775

theorem tailTrace_1466870 : CollatzResearch.WordTrace tailWord_1466870 prefixEnd_1466870 334759718960347154701775 := by
  unfold tailWord_1466870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3343821512236749143504879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35667429463858657530718709 3343821512236749143504879)
  ·
    refine ⟨5015732268355123715257319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3343821512236749143504879 5015732268355123715257319)
    ·
      refine ⟨7523598402532685572885979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5015732268355123715257319 7523598402532685572885979)
      ·
        refine ⟨11285397603799028359328969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7523598402532685572885979 11285397603799028359328969)
        ·
          refine ⟨8464048202849271269496727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11285397603799028359328969 8464048202849271269496727)
          ·
            refine ⟨12696072304273906904245091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8464048202849271269496727 12696072304273906904245091)
            ·
              refine ⟨19044108456410860356367637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12696072304273906904245091 19044108456410860356367637)
              ·
                refine ⟨892692583894259079204733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19044108456410860356367637 892692583894259079204733)
                ·
                  refine ⟨334759718960347154701775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892692583894259079204733 334759718960347154701775)
                  ·
                    rfl

theorem cell21_1466870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1466870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466870 prefixEnd_1466870 := by exact prefixLift 1466870
  have htrace : WordTrace (prefixWord ++ tailWord_1466870) baseStart_1466870 baseEnd_1466870 := by
    simpa [prefixWord, tailWord_1466870, baseEnd_1466870] using wordTrace_append hprefix tailTrace_1466870
  have hstable : (prefixWord ++ tailWord_1466870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466870).length < 2 ^ (prefixWord ++ tailWord_1466870).sum := by decide
  have hdescent : baseEnd_1466870 < baseStart_1466870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466929 : List Nat := [1, 2, 2, 3, 1, 1, 2, 6, 3]
def baseStart_1466929 : Nat := 118140960795 + 1466929 * 2 ^ 59
def prefixEnd_1466929 : Nat := 4983230072969 + 3 ^ 40 * 1466929 * 2
def baseEnd_1466929 : Nat := 334773183564176163218321

theorem tailTrace_1466929 : CollatzResearch.WordTrace tailWord_1466929 prefixEnd_1466929 334773183564176163218321 := by
  unfold tailWord_1466929
  simp only [CollatzResearch.WordTrace]
  refine ⟨53503296102574239372475841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35668864068382826248317227 53503296102574239372475841)
  ·
    refine ⟨40127472076930679529356881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53503296102574239372475841 40127472076930679529356881)
    ·
      refine ⟨30095604057698009647017661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40127472076930679529356881 30095604057698009647017661)
      ·
        refine ⟨11285851521636753617631623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30095604057698009647017661 11285851521636753617631623)
        ·
          refine ⟨16928777282455130426447435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11285851521636753617631623 16928777282455130426447435)
          ·
            refine ⟨25393165923682695639671153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16928777282455130426447435 25393165923682695639671153)
            ·
              refine ⟨19044874442762021729753365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25393165923682695639671153 19044874442762021729753365)
              ·
                refine ⟨892728489504469768582189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19044874442762021729753365 892728489504469768582189)
                ·
                  refine ⟨334773183564176163218321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892728489504469768582189 334773183564176163218321)
                  ·
                    rfl

theorem cell21_1466929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 3].length) (baseStart_1466929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466929 prefixEnd_1466929 := by exact prefixLift 1466929
  have htrace : WordTrace (prefixWord ++ tailWord_1466929) baseStart_1466929 baseEnd_1466929 := by
    simpa [prefixWord, tailWord_1466929, baseEnd_1466929] using wordTrace_append hprefix tailTrace_1466929
  have hstable : (prefixWord ++ tailWord_1466929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466929).length < 2 ^ (prefixWord ++ tailWord_1466929).sum := by decide
  have hdescent : baseEnd_1466929 < baseStart_1466929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466932 : List Nat := [2, 5, 1, 3, 1, 1, 2, 6]
def baseStart_1466932 : Nat := 118140960795 + 1466932 * 2 ^ 59
def prefixEnd_1466932 : Nat := 4983230072969 + 3 ^ 40 * 1466932 * 2
def baseEnd_1466932 : Nat := 111591289401682941556105

theorem tailTrace_1466932 : CollatzResearch.WordTrace tailWord_1466932 prefixEnd_1466932 111591289401682941556105 := by
  unfold tailWord_1466932
  simp only [CollatzResearch.WordTrace]
  refine ⟨26751702760781685442417525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35668937014375580589890033 26751702760781685442417525)
  ·
    refine ⟨2507972133823283010226643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26751702760781685442417525 2507972133823283010226643)
    ·
      refine ⟨3761958200734924515339965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2507972133823283010226643 3761958200734924515339965)
      ·
        refine ⟨1410734325275596693252487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3761958200734924515339965 1410734325275596693252487)
        ·
          refine ⟨2116101487913395039878731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1410734325275596693252487 2116101487913395039878731)
          ·
            refine ⟨3174152231870092559818097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116101487913395039878731 3174152231870092559818097)
            ·
              refine ⟨2380614173902569419863573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3174152231870092559818097 2380614173902569419863573)
              ·
                refine ⟨111591289401682941556105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2380614173902569419863573 111591289401682941556105)
                ·
                  rfl

theorem cell21_1466932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_1466932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466932 prefixEnd_1466932 := by exact prefixLift 1466932
  have htrace : WordTrace (prefixWord ++ tailWord_1466932) baseStart_1466932 baseEnd_1466932 := by
    simpa [prefixWord, tailWord_1466932, baseEnd_1466932] using wordTrace_append hprefix tailTrace_1466932
  have hstable : (prefixWord ++ tailWord_1466932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466932).length < 2 ^ (prefixWord ++ tailWord_1466932).sum := by decide
  have hdescent : baseEnd_1466932 < baseStart_1466932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466943 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 4]
def baseStart_1466943 : Nat := 118140960795 + 1466943 * 2 ^ 59
def prefixEnd_1466943 : Nat := 4983230072969 + 3 ^ 40 * 1466943 * 2
def baseEnd_1466943 : Nat := 334776378554915249984959

theorem tailTrace_1466943 : CollatzResearch.WordTrace tailWord_1466943 prefixEnd_1466943 334776378554915249984959 := by
  unfold tailWord_1466943
  simp only [CollatzResearch.WordTrace]
  refine ⟨53503806724523519763485483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35669204483015679842323655 53503806724523519763485483)
  ·
    refine ⟨80255710086785279645228225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53503806724523519763485483 80255710086785279645228225)
    ·
      refine ⟨60191782565088959733921169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80255710086785279645228225 60191782565088959733921169)
      ·
        refine ⟨45143836923816719800440877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60191782565088959733921169 45143836923816719800440877)
        ·
          refine ⟨16928938846431269925165329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45143836923816719800440877 16928938846431269925165329)
          ·
            refine ⟨12696704134823452443873997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16928938846431269925165329 12696704134823452443873997)
            ·
              refine ⟨4761264050558794666452749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12696704134823452443873997 4761264050558794666452749)
              ·
                refine ⟨1785474018959547999919781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4761264050558794666452749 1785474018959547999919781)
                ·
                  refine ⟨334776378554915249984959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785474018959547999919781 334776378554915249984959)
                  ·
                    rfl

theorem cell21_1466943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 4].length) (baseStart_1466943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1466943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1466943 prefixEnd_1466943 := by exact prefixLift 1466943
  have htrace : WordTrace (prefixWord ++ tailWord_1466943) baseStart_1466943 baseEnd_1466943 := by
    simpa [prefixWord, tailWord_1466943, baseEnd_1466943] using wordTrace_append hprefix tailTrace_1466943
  have hstable : (prefixWord ++ tailWord_1466943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466943).length < 2 ^ (prefixWord ++ tailWord_1466943).sum := by decide
  have hdescent : baseEnd_1466943 < baseStart_1466943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467005 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 5]
def baseStart_1467005 : Nat := 118140960795 + 1467005 * 2 ^ 59
def prefixEnd_1467005 : Nat := 4983230072969 + 3 ^ 40 * 1467005 * 2
def baseEnd_1467005 : Nat := 334790527799616919951499

theorem tailTrace_1467005 : CollatzResearch.WordTrace tailWord_1467005 prefixEnd_1467005 334790527799616919951499 := by
  unfold tailWord_1467005
  simp only [CollatzResearch.WordTrace]
  refine ⟨53506068050298904352242469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35670712033532602901494979 53506068050298904352242469)
  ·
    refine ⟨10032387759431044566045463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53506068050298904352242469 10032387759431044566045463)
    ·
      refine ⟨15048581639146566849068195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10032387759431044566045463 15048581639146566849068195)
      ·
        refine ⟨22572872458719850273602293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15048581639146566849068195 22572872458719850273602293)
        ·
          refine ⟨2116206793004985963150215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22572872458719850273602293 2116206793004985963150215)
          ·
            refine ⟨3174310189507478944725323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116206793004985963150215 3174310189507478944725323)
            ·
              refine ⟨4761465284261218417087985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174310189507478944725323 4761465284261218417087985)
              ·
                refine ⟨3571098963195913812815989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4761465284261218417087985 3571098963195913812815989)
                ·
                  refine ⟨334790527799616919951499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3571098963195913812815989 334790527799616919951499)
                  ·
                    rfl

theorem cell21_1467005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_1467005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467005 prefixEnd_1467005 := by exact prefixLift 1467005
  have htrace : WordTrace (prefixWord ++ tailWord_1467005) baseStart_1467005 baseEnd_1467005 := by
    simpa [prefixWord, tailWord_1467005, baseEnd_1467005] using wordTrace_append hprefix tailTrace_1467005
  have hstable : (prefixWord ++ tailWord_1467005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467005).length < 2 ^ (prefixWord ++ tailWord_1467005).sum := by decide
  have hdescent : baseEnd_1467005 < baseStart_1467005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467022 : List Nat := [4, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_1467022 : Nat := 118140960795 + 1467022 * 2 ^ 59
def prefixEnd_1467022 : Nat := 4983230072969 + 3 ^ 40 * 1467022 * 2
def baseEnd_1467022 : Nat := 334794407431228668168131

theorem tailTrace_1467022 : CollatzResearch.WordTrace tailWord_1467022 prefixEnd_1467022 334794407431228668168131 := by
  unfold tailWord_1467022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6688336011404664531951415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35671125394158210837074213 6688336011404664531951415)
  ·
    refine ⟨10032504017106996797927123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6688336011404664531951415 10032504017106996797927123)
    ·
      refine ⟨15048756025660495196890685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10032504017106996797927123 15048756025660495196890685)
      ·
        refine ⟨5643283509622685698834007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15048756025660495196890685 5643283509622685698834007)
        ·
          refine ⟨8464925264434028548251011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5643283509622685698834007 8464925264434028548251011)
          ·
            refine ⟨12697387896651042822376517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8464925264434028548251011 12697387896651042822376517)
            ·
              refine ⟨2380760230622070529195597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12697387896651042822376517 2380760230622070529195597)
              ·
                refine ⟨892785086483276448448349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2380760230622070529195597 892785086483276448448349)
                ·
                  refine ⟨334794407431228668168131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892785086483276448448349 334794407431228668168131)
                  ·
                    rfl

theorem cell21_1467022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_1467022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467022 prefixEnd_1467022 := by exact prefixLift 1467022
  have htrace : WordTrace (prefixWord ++ tailWord_1467022) baseStart_1467022 baseEnd_1467022 := by
    simpa [prefixWord, tailWord_1467022, baseEnd_1467022] using wordTrace_append hprefix tailTrace_1467022
  have hstable : (prefixWord ++ tailWord_1467022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467022).length < 2 ^ (prefixWord ++ tailWord_1467022).sum := by decide
  have hdescent : baseEnd_1467022 < baseStart_1467022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467036 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 4]
def baseStart_1467036 : Nat := 118140960795 + 1467036 * 2 ^ 59
def prefixEnd_1467036 : Nat := 4983230072969 + 3 ^ 40 * 1467036 * 2
def baseEnd_1467036 : Nat := 334797602421967754934769

theorem tailTrace_1467036 : CollatzResearch.WordTrace tailWord_1467036 prefixEnd_1467036 334797602421967754934769 := by
  unfold tailWord_1467036
  simp only [CollatzResearch.WordTrace]
  refine ⟨26753599356593298323310481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35671465808791064431080641 26753599356593298323310481)
  ·
    refine ⟨20065199517444973742482861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26753599356593298323310481 20065199517444973742482861)
    ·
      refine ⟨7524449819041865153431073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20065199517444973742482861 7524449819041865153431073)
      ·
        refine ⟨5643337364281398865073305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7524449819041865153431073 5643337364281398865073305)
        ·
          refine ⟨4232503023211049148804979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5643337364281398865073305 4232503023211049148804979)
          ·
            refine ⟨6348754534816573723207469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4232503023211049148804979 6348754534816573723207469)
            ·
              refine ⟨2380782950556215146202801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6348754534816573723207469 2380782950556215146202801)
              ·
                refine ⟨1785587212917161359652101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2380782950556215146202801 1785587212917161359652101)
                ·
                  refine ⟨334797602421967754934769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785587212917161359652101 334797602421967754934769)
                  ·
                    rfl

theorem cell21_1467036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_1467036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467036 prefixEnd_1467036 := by exact prefixLift 1467036
  have htrace : WordTrace (prefixWord ++ tailWord_1467036) baseStart_1467036 baseEnd_1467036 := by
    simpa [prefixWord, tailWord_1467036, baseEnd_1467036] using wordTrace_append hprefix tailTrace_1467036
  have hstable : (prefixWord ++ tailWord_1467036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467036).length < 2 ^ (prefixWord ++ tailWord_1467036).sum := by decide
  have hdescent : baseEnd_1467036 < baseStart_1467036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467053 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1467053 : Nat := 118140960795 + 1467053 * 2 ^ 59
def prefixEnd_1467053 : Nat := 4983230072969 + 3 ^ 40 * 1467053 * 2
def baseEnd_1467053 : Nat := 334801482053579503151401

theorem tailTrace_1467053 : CollatzResearch.WordTrace tailWord_1467053 prefixEnd_1467053 334801482053579503151401 := by
  unfold tailWord_1467053
  simp only [CollatzResearch.WordTrace]
  refine ⟨53507818754125008549989813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35671879169416672366659875 53507818754125008549989813)
  ·
    refine ⟨5016358008199219551561545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53507818754125008549989813 5016358008199219551561545)
    ·
      refine ⟨3762268506149414663671159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5016358008199219551561545 3762268506149414663671159)
      ·
        refine ⟨5643402759224121995506739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3762268506149414663671159 5643402759224121995506739)
        ·
          refine ⟨8465104138836182993260109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5643402759224121995506739 8465104138836182993260109)
          ·
            refine ⟨3174414052063568622472541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8465104138836182993260109 3174414052063568622472541)
            ·
              refine ⟨1190405269523838233427203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3174414052063568622472541 1190405269523838233427203)
              ·
                refine ⟨1785607904285757350140805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190405269523838233427203 1785607904285757350140805)
                ·
                  refine ⟨334801482053579503151401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785607904285757350140805 334801482053579503151401)
                  ·
                    rfl

theorem cell21_1467053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1467053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467053 prefixEnd_1467053 := by exact prefixLift 1467053
  have htrace : WordTrace (prefixWord ++ tailWord_1467053) baseStart_1467053 baseEnd_1467053 := by
    simpa [prefixWord, tailWord_1467053, baseEnd_1467053] using wordTrace_append hprefix tailTrace_1467053
  have hstable : (prefixWord ++ tailWord_1467053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467053).length < 2 ^ (prefixWord ++ tailWord_1467053).sum := by decide
  have hdescent : baseEnd_1467053 < baseStart_1467053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467073 : List Nat := [1, 2, 6, 2, 2, 1, 1, 3, 3]
def baseStart_1467073 : Nat := 118140960795 + 1467073 * 2 ^ 59
def prefixEnd_1467073 : Nat := 4983230072969 + 3 ^ 40 * 1467073 * 2
def baseEnd_1467073 : Nat := 334806046326063912818027

theorem tailTrace_1467073 : CollatzResearch.WordTrace tailWord_1467073 prefixEnd_1467073 334806046326063912818027 := by
  unfold tailWord_1467073
  simp only [CollatzResearch.WordTrace]
  refine ⟨53508548214052551965717873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35672365476035034643811915 53508548214052551965717873)
  ·
    refine ⟨40131411160539413974288405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53508548214052551965717873 40131411160539413974288405)
    ·
      refine ⟨1881159898150285030044769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40131411160539413974288405 1881159898150285030044769)
      ·
        refine ⟨1410869923612713772533577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1881159898150285030044769 1410869923612713772533577)
        ·
          refine ⟨1058152442709535329400183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1410869923612713772533577 1058152442709535329400183)
          ·
            refine ⟨1587228664064302994100275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058152442709535329400183 1587228664064302994100275)
            ·
              refine ⟨2380842996096454491150413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587228664064302994100275 2380842996096454491150413)
              ·
                refine ⟨892816123536170434181405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2380842996096454491150413 892816123536170434181405)
                ·
                  refine ⟨334806046326063912818027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892816123536170434181405 334806046326063912818027)
                  ·
                    rfl

theorem cell21_1467073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 3].length) (baseStart_1467073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467073 prefixEnd_1467073 := by exact prefixLift 1467073
  have htrace : WordTrace (prefixWord ++ tailWord_1467073) baseStart_1467073 baseEnd_1467073 := by
    simpa [prefixWord, tailWord_1467073, baseEnd_1467073] using wordTrace_append hprefix tailTrace_1467073
  have hstable : (prefixWord ++ tailWord_1467073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467073).length < 2 ^ (prefixWord ++ tailWord_1467073).sum := by decide
  have hdescent : baseEnd_1467073 < baseStart_1467073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467098 : List Nat := [3, 1, 1, 2, 2, 2, 5, 2, 3]
def baseStart_1467098 : Nat := 118140960795 + 1467098 * 2 ^ 59
def prefixEnd_1467098 : Nat := 4983230072969 + 3 ^ 40 * 1467098 * 2
def baseEnd_1467098 : Nat := 334811751666669424901309

theorem tailTrace_1467098 : CollatzResearch.WordTrace tailWord_1467098 prefixEnd_1467098 334811751666669424901309 := by
  unfold tailWord_1467098
  simp only [CollatzResearch.WordTrace]
  refine ⟨13377365009740495308844487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35672973359307987490251965 13377365009740495308844487)
  ·
    refine ⟨20066047514610742963266731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13377365009740495308844487 20066047514610742963266731)
    ·
      refine ⟨30099071271916114444900097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20066047514610742963266731 30099071271916114444900097)
      ·
        refine ⟨22574303453937085833675073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30099071271916114444900097 22574303453937085833675073)
        ·
          refine ⟨16930727590452814375256305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22574303453937085833675073 16930727590452814375256305)
          ·
            refine ⟨12698045692839610781442229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16930727590452814375256305 12698045692839610781442229)
            ·
              refine ⟨1190441783703713510760209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12698045692839610781442229 1190441783703713510760209)
              ·
                refine ⟨892831337777785133070157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190441783703713510760209 892831337777785133070157)
                ·
                  refine ⟨334811751666669424901309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892831337777785133070157 334811751666669424901309)
                  ·
                    rfl

theorem cell21_1467098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_1467098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467098 prefixEnd_1467098 := by exact prefixLift 1467098
  have htrace : WordTrace (prefixWord ++ tailWord_1467098) baseStart_1467098 baseEnd_1467098 := by
    simpa [prefixWord, tailWord_1467098, baseEnd_1467098] using wordTrace_append hprefix tailTrace_1467098
  have hstable : (prefixWord ++ tailWord_1467098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467098).length < 2 ^ (prefixWord ++ tailWord_1467098).sum := by decide
  have hdescent : baseEnd_1467098 < baseStart_1467098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467109 : List Nat := [1, 3, 1, 4, 1, 2, 1, 8]
def baseStart_1467109 : Nat := 118140960795 + 1467109 * 2 ^ 59
def prefixEnd_1467109 : Nat := 4983230072969 + 3 ^ 40 * 1467109 * 2
def baseEnd_1467109 : Nat := 111604754005511950072651

theorem tailTrace_1467109 : CollatzResearch.WordTrace tailWord_1467109 prefixEnd_1467109 111604754005511950072651 := by
  unfold tailWord_1467109
  simp only [CollatzResearch.WordTrace]
  refine ⟨53509861241922130114028381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35673240827948086742685587 53509861241922130114028381)
  ·
    refine ⟨20066197965720798792760643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53509861241922130114028381 20066197965720798792760643)
    ·
      refine ⟨30099296948581198189140965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20066197965720798792760643 30099296948581198189140965)
      ·
        refine ⟨5643618177858974660463931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30099296948581198189140965 5643618177858974660463931)
        ·
          refine ⟨8465427266788461990695897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5643618177858974660463931 8465427266788461990695897)
          ·
            refine ⟨6349070450091346493021923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8465427266788461990695897 6349070450091346493021923)
            ·
              refine ⟨9523605675137019739532885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6349070450091346493021923 9523605675137019739532885)
              ·
                refine ⟨111604754005511950072651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9523605675137019739532885 111604754005511950072651)
                ·
                  rfl

theorem cell21_1467109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 8].length) (baseStart_1467109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467109 prefixEnd_1467109 := by exact prefixLift 1467109
  have htrace : WordTrace (prefixWord ++ tailWord_1467109) baseStart_1467109 baseEnd_1467109 := by
    simpa [prefixWord, tailWord_1467109, baseEnd_1467109] using wordTrace_append hprefix tailTrace_1467109
  have hstable : (prefixWord ++ tailWord_1467109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467109).length < 2 ^ (prefixWord ++ tailWord_1467109).sum := by decide
  have hdescent : baseEnd_1467109 < baseStart_1467109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467112 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 4]
def baseStart_1467112 : Nat := 118140960795 + 1467112 * 2 ^ 59
def prefixEnd_1467112 : Nat := 4983230072969 + 3 ^ 40 * 1467112 * 2
def baseEnd_1467112 : Nat := 334814946657408511667947

theorem tailTrace_1467112 : CollatzResearch.WordTrace tailWord_1467112 prefixEnd_1467112 334814946657408511667947 := by
  unfold tailWord_1467112
  simp only [CollatzResearch.WordTrace]
  refine ⟨26754985330455630813193795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35673313773940841084258393 26754985330455630813193795)
  ·
    refine ⟨40132477995683446219790693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26754985330455630813193795 40132477995683446219790693)
    ·
      refine ⟨7524839624190646166210755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40132477995683446219790693 7524839624190646166210755)
      ·
        refine ⟨11287259436285969249316133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7524839624190646166210755 11287259436285969249316133)
        ·
          refine ⟨2116361144303619234246775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11287259436285969249316133 2116361144303619234246775)
          ·
            refine ⟨3174541716455428851370163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116361144303619234246775 3174541716455428851370163)
            ·
              refine ⟨4761812574683143277055245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174541716455428851370163 4761812574683143277055245)
              ·
                refine ⟨1785679715506178728895717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4761812574683143277055245 1785679715506178728895717)
                ·
                  refine ⟨334814946657408511667947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785679715506178728895717 334814946657408511667947)
                  ·
                    rfl

theorem cell21_1467112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_1467112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467112 prefixEnd_1467112 := by exact prefixLift 1467112
  have htrace : WordTrace (prefixWord ++ tailWord_1467112) baseStart_1467112 baseEnd_1467112 := by
    simpa [prefixWord, tailWord_1467112, baseEnd_1467112] using wordTrace_append hprefix tailTrace_1467112
  have hstable : (prefixWord ++ tailWord_1467112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467112).length < 2 ^ (prefixWord ++ tailWord_1467112).sum := by decide
  have hdescent : baseEnd_1467112 < baseStart_1467112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467123 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 7]
def baseStart_1467123 : Nat := 118140960795 + 1467123 * 2 ^ 59
def prefixEnd_1467123 : Nat := 4983230072969 + 3 ^ 40 * 1467123 * 2
def baseEnd_1467123 : Nat := 334817457007274936984591

theorem tailTrace_1467123 : CollatzResearch.WordTrace tailWord_1467123 prefixEnd_1467123 334817457007274936984591 := by
  unfold tailWord_1467123
  simp only [CollatzResearch.WordTrace]
  refine ⟨53510371863871410505038023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35673581242580940336692015 53510371863871410505038023)
  ·
    refine ⟨80265557795807115757557035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53510371863871410505038023 80265557795807115757557035)
    ·
      refine ⟨120398336693710673636335553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80265557795807115757557035 120398336693710673636335553)
      ·
        refine ⟨90298752520283005227251665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120398336693710673636335553 90298752520283005227251665)
        ·
          refine ⟨67724064390212253920438749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90298752520283005227251665 67724064390212253920438749)
          ·
            refine ⟨25396524146329595220164531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67724064390212253920438749 25396524146329595220164531)
            ·
              refine ⟨38094786219494392830246797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25396524146329595220164531 38094786219494392830246797)
              ·
                refine ⟨14285544832310397311342549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38094786219494392830246797 14285544832310397311342549)
                ·
                  refine ⟨334817457007274936984591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14285544832310397311342549 334817457007274936984591)
                  ·
                    rfl

theorem cell21_1467123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_1467123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467123 prefixEnd_1467123 := by exact prefixLift 1467123
  have htrace : WordTrace (prefixWord ++ tailWord_1467123) baseStart_1467123 baseEnd_1467123 := by
    simpa [prefixWord, tailWord_1467123, baseEnd_1467123] using wordTrace_append hprefix tailTrace_1467123
  have hstable : (prefixWord ++ tailWord_1467123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467123).length < 2 ^ (prefixWord ++ tailWord_1467123).sum := by decide
  have hdescent : baseEnd_1467123 < baseStart_1467123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467157 : List Nat := [1, 3, 2, 1, 2, 2, 3, 4, 3]
def baseStart_1467157 : Nat := 118140960795 + 1467157 * 2 ^ 59
def prefixEnd_1467157 : Nat := 4983230072969 + 3 ^ 40 * 1467157 * 2
def baseEnd_1467157 : Nat := 334825216270498433417855

theorem tailTrace_1467157 : CollatzResearch.WordTrace tailWord_1467157 prefixEnd_1467157 334825216270498433417855 := by
  unfold tailWord_1467157
  simp only [CollatzResearch.WordTrace]
  refine ⟨53511611945748234311775725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35674407963832156207850483 53511611945748234311775725)
  ·
    refine ⟨20066854479655587866915897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53511611945748234311775725 20066854479655587866915897)
    ·
      refine ⟨15050140859741690900186923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20066854479655587866915897 15050140859741690900186923)
      ·
        refine ⟨22575211289612536350280385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15050140859741690900186923 22575211289612536350280385)
        ·
          refine ⟨16931408467209402262710289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22575211289612536350280385 16931408467209402262710289)
          ·
            refine ⟨12698556350407051697032717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16931408467209402262710289 12698556350407051697032717)
            ·
              refine ⟨4761958631402644386387269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12698556350407051697032717 4761958631402644386387269)
              ·
                refine ⟨892867243387995822447613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4761958631402644386387269 892867243387995822447613)
                ·
                  refine ⟨334825216270498433417855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892867243387995822447613 334825216270498433417855)
                  ·
                    rfl

theorem cell21_1467157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_1467157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467157 prefixEnd_1467157 := by exact prefixLift 1467157
  have htrace : WordTrace (prefixWord ++ tailWord_1467157) baseStart_1467157 baseEnd_1467157 := by
    simpa [prefixWord, tailWord_1467157, baseEnd_1467157] using wordTrace_append hprefix tailTrace_1467157
  have hstable : (prefixWord ++ tailWord_1467157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467157).length < 2 ^ (prefixWord ++ tailWord_1467157).sum := by decide
  have hdescent : baseEnd_1467157 < baseStart_1467157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467318 : List Nat := [5, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_1467318 : Nat := 118140960795 + 1467318 * 2 ^ 59
def prefixEnd_1467318 : Nat := 4983230072969 + 3 ^ 40 * 1467318 * 2
def baseEnd_1467318 : Nat := 334861958663997931234193

theorem tailTrace_1467318 : CollatzResearch.WordTrace tailWord_1467318 prefixEnd_1467318 334861958663997931234193 := by
  unfold tailWord_1467318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3344842756135309925524163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35678322732109972538924405 3344842756135309925524163)
  ·
    refine ⟨5017264134202964888286245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3344842756135309925524163 5017264134202964888286245)
    ·
      refine ⟨940737025163055916553671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5017264134202964888286245 940737025163055916553671)
      ·
        refine ⟨1411105537744583874830507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940737025163055916553671 1411105537744583874830507)
        ·
          refine ⟨2116658306616875812245761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411105537744583874830507 2116658306616875812245761)
          ·
            refine ⟨1587493729962656859184321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2116658306616875812245761 1587493729962656859184321)
            ·
              refine ⟨1190620297471992644388241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587493729962656859184321 1190620297471992644388241)
              ·
                refine ⟨892965223103994483291181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190620297471992644388241 892965223103994483291181)
                ·
                  refine ⟨334861958663997931234193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892965223103994483291181 334861958663997931234193)
                  ·
                    rfl

theorem cell21_1467318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_1467318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467318 prefixEnd_1467318 := by exact prefixLift 1467318
  have htrace : WordTrace (prefixWord ++ tailWord_1467318) baseStart_1467318 baseEnd_1467318 := by
    simpa [prefixWord, tailWord_1467318, baseEnd_1467318] using wordTrace_append hprefix tailTrace_1467318
  have hstable : (prefixWord ++ tailWord_1467318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467318).length < 2 ^ (prefixWord ++ tailWord_1467318).sum := by decide
  have hdescent : baseEnd_1467318 < baseStart_1467318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467320 : List Nat := [2, 1, 2, 1, 2, 13]
def baseStart_1467320 : Nat := 118140960795 + 1467320 * 2 ^ 59
def prefixEnd_1467320 : Nat := 4983230072969 + 3 ^ 40 * 1467320 * 2
def baseEnd_1467320 : Nat := 12402311670046161933365

theorem tailTrace_1467320 : CollatzResearch.WordTrace tailWord_1467320 prefixEnd_1467320 12402311670046161933365 := by
  unfold tailWord_1467320
  simp only [CollatzResearch.WordTrace]
  refine ⟨26758778522078856574979707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35678371362771808766639609 26758778522078856574979707)
  ·
    refine ⟨40138167783118284862469561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26758778522078856574979707 40138167783118284862469561)
    ·
      refine ⟨30103625837338713646852171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40138167783118284862469561 30103625837338713646852171)
      ·
        refine ⟨45155438756008070470278257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30103625837338713646852171 45155438756008070470278257)
        ·
          refine ⟨33866579067006052852708693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45155438756008070470278257 33866579067006052852708693)
          ·
            refine ⟨12402311670046161933365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 33866579067006052852708693 12402311670046161933365)
            ·
              rfl

theorem cell21_1467320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 13].length) (baseStart_1467320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467320 prefixEnd_1467320 := by exact prefixLift 1467320
  have htrace : WordTrace (prefixWord ++ tailWord_1467320) baseStart_1467320 baseEnd_1467320 := by
    simpa [prefixWord, tailWord_1467320, baseEnd_1467320] using wordTrace_append hprefix tailTrace_1467320
  have hstable : (prefixWord ++ tailWord_1467320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467320).length < 2 ^ (prefixWord ++ tailWord_1467320).sum := by decide
  have hdescent : baseEnd_1467320 < baseStart_1467320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467354 : List Nat := [3, 1, 1, 2, 4, 2, 3, 5]
def baseStart_1467354 : Nat := 118140960795 + 1467354 * 2 ^ 59
def prefixEnd_1467354 : Nat := 4983230072969 + 3 ^ 40 * 1467354 * 2
def baseEnd_1467354 : Nat := 111623391451489956211373

theorem tailTrace_1467354 : CollatzResearch.WordTrace tailWord_1467354 prefixEnd_1467354 111623391451489956211373 := by
  unfold tailWord_1467354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13379699281508634239174279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35679198084023024637798077 13379699281508634239174279)
  ·
    refine ⟨20069548922262951358761419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13379699281508634239174279 20069548922262951358761419)
    ·
      refine ⟨30104323383394427038142129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20069548922262951358761419 30104323383394427038142129)
      ·
        refine ⟨22578242537545820278606597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30104323383394427038142129 22578242537545820278606597)
        ·
          refine ⟨4233420475789841302238737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22578242537545820278606597 4233420475789841302238737)
          ·
            refine ⟨3175065356842380976679053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4233420475789841302238737 3175065356842380976679053)
            ·
              refine ⟨1190649508815892866254645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3175065356842380976679053 1190649508815892866254645)
              ·
                refine ⟨111623391451489956211373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1190649508815892866254645 111623391451489956211373)
                ·
                  rfl

theorem cell21_1467354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_1467354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467354 prefixEnd_1467354 := by exact prefixLift 1467354
  have htrace : WordTrace (prefixWord ++ tailWord_1467354) baseStart_1467354 baseEnd_1467354 := by
    simpa [prefixWord, tailWord_1467354, baseEnd_1467354] using wordTrace_append hprefix tailTrace_1467354
  have hstable : (prefixWord ++ tailWord_1467354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467354).length < 2 ^ (prefixWord ++ tailWord_1467354).sum := by decide
  have hdescent : baseEnd_1467354 < baseStart_1467354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467413 : List Nat := [1, 3, 2, 1, 4, 2, 1, 7]
def baseStart_1467413 : Nat := 118140960795 + 1467413 * 2 ^ 59
def prefixEnd_1467413 : Nat := 4983230072969 + 3 ^ 40 * 1467413 * 2
def baseEnd_1467413 : Nat := 111627879652766292383555

theorem tailTrace_1467413 : CollatzResearch.WordTrace tailWord_1467413 prefixEnd_1467413 111627879652766292383555 := by
  unfold tailWord_1467413
  simp only [CollatzResearch.WordTrace]
  refine ⟨53520949032820790033094893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35680632688547193355396595 53520949032820790033094893)
  ·
    refine ⟨20070355887307796262410585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53520949032820790033094893 20070355887307796262410585)
    ·
      refine ⟨15052766915480847196807939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20070355887307796262410585 15052766915480847196807939)
      ·
        refine ⟨22579150373221270795211909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15052766915480847196807939 22579150373221270795211909)
        ·
          refine ⟨4233590694978988274102233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22579150373221270795211909 4233590694978988274102233)
          ·
            refine ⟨3175193021234241205576675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4233590694978988274102233 3175193021234241205576675)
            ·
              refine ⟨4762789531851361808365013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175193021234241205576675 4762789531851361808365013)
              ·
                refine ⟨111627879652766292383555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4762789531851361808365013 111627879652766292383555)
                ·
                  rfl

theorem cell21_1467413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 7].length) (baseStart_1467413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467413 prefixEnd_1467413 := by exact prefixLift 1467413
  have htrace : WordTrace (prefixWord ++ tailWord_1467413) baseStart_1467413 baseEnd_1467413 := by
    simpa [prefixWord, tailWord_1467413, baseEnd_1467413] using wordTrace_append hprefix tailTrace_1467413
  have hstable : (prefixWord ++ tailWord_1467413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467413).length < 2 ^ (prefixWord ++ tailWord_1467413).sum := by decide
  have hdescent : baseEnd_1467413 < baseStart_1467413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467503 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 5]
def baseStart_1467503 : Nat := 118140960795 + 1467503 * 2 ^ 59
def prefixEnd_1467503 : Nat := 4983230072969 + 3 ^ 40 * 1467503 * 2
def baseEnd_1467503 : Nat := 334904178184478720650481

theorem tailTrace_1467503 : CollatzResearch.WordTrace tailWord_1467503 prefixEnd_1467503 334904178184478720650481 := by
  unfold tailWord_1467503
  simp only [CollatzResearch.WordTrace]
  refine ⟨53524231602494735403871163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35682821068329823602580775 53524231602494735403871163)
  ·
    refine ⟨80286347403742103105806745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53524231602494735403871163 80286347403742103105806745)
    ·
      refine ⟨60214760552806577329355059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80286347403742103105806745 60214760552806577329355059)
      ·
        refine ⟨90322140829209865994032589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60214760552806577329355059 90322140829209865994032589)
        ·
          refine ⟨33870802810953699747762221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90322140829209865994032589 33870802810953699747762221)
          ·
            refine ⟨12701551054107637405410833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33870802810953699747762221 12701551054107637405410833)
            ·
              refine ⟨9526163290580728054058125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12701551054107637405410833 9526163290580728054058125)
              ·
                refine ⟨3572311233967773020271797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9526163290580728054058125 3572311233967773020271797)
                ·
                  refine ⟨334904178184478720650481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3572311233967773020271797 334904178184478720650481)
                  ·
                    rfl

theorem cell21_1467503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_1467503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467503 prefixEnd_1467503 := by exact prefixLift 1467503
  have htrace : WordTrace (prefixWord ++ tailWord_1467503) baseStart_1467503 baseEnd_1467503 := by
    simpa [prefixWord, tailWord_1467503, baseEnd_1467503] using wordTrace_append hprefix tailTrace_1467503
  have hstable : (prefixWord ++ tailWord_1467503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467503).length < 2 ^ (prefixWord ++ tailWord_1467503).sum := by decide
  have hdescent : baseEnd_1467503 < baseStart_1467503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467551 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 6]
def baseStart_1467551 : Nat := 118140960795 + 1467551 * 2 ^ 59
def prefixEnd_1467551 : Nat := 4983230072969 + 3 ^ 40 * 1467551 * 2
def baseEnd_1467551 : Nat := 334915132438441303850383

theorem tailTrace_1467551 : CollatzResearch.WordTrace tailWord_1467551 prefixEnd_1467551 334915132438441303850383 := by
  unfold tailWord_1467551
  simp only [CollatzResearch.WordTrace]
  refine ⟨53525982306320839601618507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35683988204213893067745671 53525982306320839601618507)
  ·
    refine ⟨80288973459481259402427761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53525982306320839601618507 80288973459481259402427761)
    ·
      refine ⟨60216730094610944551820821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80288973459481259402427761 60216730094610944551820821)
      ·
        refine ⟨2822659223184888025866601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60216730094610944551820821 2822659223184888025866601)
        ·
          refine ⟨2116994417388666019399951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2822659223184888025866601 2116994417388666019399951)
          ·
            refine ⟨3175491626082999029099927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116994417388666019399951 3175491626082999029099927)
            ·
              refine ⟨4763237439124498543649891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175491626082999029099927 4763237439124498543649891)
              ·
                refine ⟨7144856158686747815474837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763237439124498543649891 7144856158686747815474837)
                ·
                  refine ⟨334915132438441303850383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7144856158686747815474837 334915132438441303850383)
                  ·
                    rfl

theorem cell21_1467551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 6].length) (baseStart_1467551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467551 prefixEnd_1467551 := by exact prefixLift 1467551
  have htrace : WordTrace (prefixWord ++ tailWord_1467551) baseStart_1467551 baseEnd_1467551 := by
    simpa [prefixWord, tailWord_1467551, baseEnd_1467551] using wordTrace_append hprefix tailTrace_1467551
  have hstable : (prefixWord ++ tailWord_1467551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467551).length < 2 ^ (prefixWord ++ tailWord_1467551).sum := by decide
  have hdescent : baseEnd_1467551 < baseStart_1467551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467582 : List Nat := [4, 2, 1, 1, 3, 1, 4, 5]
def baseStart_1467582 : Nat := 118140960795 + 1467582 * 2 ^ 59
def prefixEnd_1467582 : Nat := 4983230072969 + 3 ^ 40 * 1467582 * 2
def baseEnd_1467582 : Nat := 111640735686930712944551

theorem tailTrace_1467582 : CollatzResearch.WordTrace tailWord_1467582 prefixEnd_1467582 111640735686930712944551 := by
  unfold tailWord_1467582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6690889121151066486999625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35684741979472354597331333 6690889121151066486999625)
  ·
    refine ⟨5018166840863299865249719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6690889121151066486999625 5018166840863299865249719)
    ·
      refine ⟨7527250261294949797874579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5018166840863299865249719 7527250261294949797874579)
      ·
        refine ⟨11290875391942424696811869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7527250261294949797874579 11290875391942424696811869)
        ·
          refine ⟨4234078271978409261304451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11290875391942424696811869 4234078271978409261304451)
          ·
            refine ⟨6351117407967613891956677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4234078271978409261304451 6351117407967613891956677)
            ·
              refine ⟨1190834513993927604741877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6351117407967613891956677 1190834513993927604741877)
              ·
                refine ⟨111640735686930712944551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1190834513993927604741877 111640735686930712944551)
                ·
                  rfl

theorem cell21_1467582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_1467582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467582 prefixEnd_1467582 := by exact prefixLift 1467582
  have htrace : WordTrace (prefixWord ++ tailWord_1467582) baseStart_1467582 baseEnd_1467582 := by
    simpa [prefixWord, tailWord_1467582, baseEnd_1467582] using wordTrace_append hprefix tailTrace_1467582
  have hstable : (prefixWord ++ tailWord_1467582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467582).length < 2 ^ (prefixWord ++ tailWord_1467582).sum := by decide
  have hdescent : baseEnd_1467582 < baseStart_1467582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467610 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_1467610 : Nat := 118140960795 + 1467610 * 2 ^ 59
def prefixEnd_1467610 : Nat := 4983230072969 + 3 ^ 40 * 1467610 * 2
def baseEnd_1467610 : Nat := 334928597042270312366929

theorem tailTrace_1467610 : CollatzResearch.WordTrace tailWord_1467610 prefixEnd_1467610 334928597042270312366929 := by
  unfold tailWord_1467610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13382033553276773169504071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35685422808738061785344189 13382033553276773169504071)
  ·
    refine ⟨20073050329915159754256107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13382033553276773169504071 20073050329915159754256107)
    ·
      refine ⟨30109575494872739631384161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20073050329915159754256107 30109575494872739631384161)
      ·
        refine ⟨22582181621154554723538121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30109575494872739631384161 22582181621154554723538121)
        ·
          refine ⟨16936636215865916042653591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22582181621154554723538121 16936636215865916042653591)
          ·
            refine ⟨25404954323798874063980387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16936636215865916042653591 25404954323798874063980387)
            ·
              refine ⟨38107431485698311095970581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25404954323798874063980387 38107431485698311095970581)
              ·
                refine ⟨1786285850892108332623621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38107431485698311095970581 1786285850892108332623621)
                ·
                  refine ⟨334928597042270312366929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786285850892108332623621 334928597042270312366929)
                  ·
                    rfl

theorem cell21_1467610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_1467610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467610 prefixEnd_1467610 := by exact prefixLift 1467610
  have htrace : WordTrace (prefixWord ++ tailWord_1467610) baseStart_1467610 baseEnd_1467610 := by
    simpa [prefixWord, tailWord_1467610, baseEnd_1467610] using wordTrace_append hprefix tailTrace_1467610
  have hstable : (prefixWord ++ tailWord_1467610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467610).length < 2 ^ (prefixWord ++ tailWord_1467610).sum := by decide
  have hdescent : baseEnd_1467610 < baseStart_1467610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467627 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 4]
def baseStart_1467627 : Nat := 118140960795 + 1467627 * 2 ^ 59
def prefixEnd_1467627 : Nat := 4983230072969 + 3 ^ 40 * 1467627 * 2
def baseEnd_1467627 : Nat := 334932476673882060583561

theorem tailTrace_1467627 : CollatzResearch.WordTrace tailWord_1467627 prefixEnd_1467627 334932476673882060583561 := by
  unfold tailWord_1467627
  simp only [CollatzResearch.WordTrace]
  refine ⟨53528754254045504581385135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35685836169363669720923423 53528754254045504581385135)
  ·
    refine ⟨80293131381068256872077703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53528754254045504581385135 80293131381068256872077703)
    ·
      refine ⟨120439697071602385308116555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80293131381068256872077703 120439697071602385308116555)
      ·
        refine ⟨180659545607403577962174833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120439697071602385308116555 180659545607403577962174833)
        ·
          refine ⟨135494659205552683471631125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180659545607403577962174833 135494659205552683471631125)
          ·
            refine ⟨6351312150260282037732709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135494659205552683471631125 6351312150260282037732709)
            ·
              refine ⟨1190871028173802882074883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6351312150260282037732709 1190871028173802882074883)
              ·
                refine ⟨1786306542260704323112325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190871028173802882074883 1786306542260704323112325)
                ·
                  refine ⟨334932476673882060583561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786306542260704323112325 334932476673882060583561)
                  ·
                    rfl

theorem cell21_1467627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 4].length) (baseStart_1467627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467627 prefixEnd_1467627 := by exact prefixLift 1467627
  have htrace : WordTrace (prefixWord ++ tailWord_1467627) baseStart_1467627 baseEnd_1467627 := by
    simpa [prefixWord, tailWord_1467627, baseEnd_1467627] using wordTrace_append hprefix tailTrace_1467627
  have hstable : (prefixWord ++ tailWord_1467627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467627).length < 2 ^ (prefixWord ++ tailWord_1467627).sum := by decide
  have hdescent : baseEnd_1467627 < baseStart_1467627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467731 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 5]
def baseStart_1467731 : Nat := 118140960795 + 1467731 * 2 ^ 59
def prefixEnd_1467731 : Nat := 4983230072969 + 3 ^ 40 * 1467731 * 2
def baseEnd_1467731 : Nat := 334956210890800990850015

theorem tailTrace_1467731 : CollatzResearch.WordTrace tailWord_1467731 prefixEnd_1467731 334956210890800990850015 := by
  unfold tailWord_1467731
  simp only [CollatzResearch.WordTrace]
  refine ⟨53532547445668730343171047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35688364963779153562114031 53532547445668730343171047)
  ·
    refine ⟨80298821168503095514756571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53532547445668730343171047 80298821168503095514756571)
    ·
      refine ⟨120448231752754643272134857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80298821168503095514756571 120448231752754643272134857)
      ·
        refine ⟨90336173814565982454101143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120448231752754643272134857 90336173814565982454101143)
        ·
          refine ⟨135504260721848973681151715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90336173814565982454101143 135504260721848973681151715)
          ·
            refine ⟨203256391082773460521727573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135504260721848973681151715 203256391082773460521727573)
            ·
              refine ⟨2381910833001251490488995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 203256391082773460521727573 2381910833001251490488995)
              ·
                refine ⟨3572866249501877235733493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381910833001251490488995 3572866249501877235733493)
                ·
                  refine ⟨334956210890800990850015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3572866249501877235733493 334956210890800990850015)
                  ·
                    rfl

theorem cell21_1467731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 5].length) (baseStart_1467731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467731 prefixEnd_1467731 := by exact prefixLift 1467731
  have htrace : WordTrace (prefixWord ++ tailWord_1467731) baseStart_1467731 baseEnd_1467731 := by
    simpa [prefixWord, tailWord_1467731, baseEnd_1467731] using wordTrace_append hprefix tailTrace_1467731
  have hstable : (prefixWord ++ tailWord_1467731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467731).length < 2 ^ (prefixWord ++ tailWord_1467731).sum := by decide
  have hdescent : baseEnd_1467731 < baseStart_1467731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467751 : List Nat := [1, 1, 5, 1, 5, 1, 2, 5]
def baseStart_1467751 : Nat := 118140960795 + 1467751 * 2 ^ 59
def prefixEnd_1467751 : Nat := 4983230072969 + 3 ^ 40 * 1467751 * 2
def baseEnd_1467751 : Nat := 111653591721095133505547

theorem tailTrace_1467751 : CollatzResearch.WordTrace tailWord_1467751 prefixEnd_1467751 111653591721095133505547 := by
  unfold tailWord_1467751
  simp only [CollatzResearch.WordTrace]
  refine ⟨53533276905596273758899107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35688851270397515839266071 53533276905596273758899107)
  ·
    refine ⟨80299915358394410638348661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53533276905596273758899107 80299915358394410638348661)
    ·
      refine ⟨7528117064849475997345187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80299915358394410638348661 7528117064849475997345187)
      ·
        refine ⟨11292175597274213996017781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7528117064849475997345187 11292175597274213996017781)
        ·
          refine ⟨1058641462244457562126667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11292175597274213996017781 1058641462244457562126667)
          ·
            refine ⟨1587962193366686343190001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058641462244457562126667 1587962193366686343190001)
            ·
              refine ⟨1190971645025014757392501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587962193366686343190001 1190971645025014757392501)
              ·
                refine ⟨111653591721095133505547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1190971645025014757392501 111653591721095133505547)
                ·
                  rfl

theorem cell21_1467751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 5].length) (baseStart_1467751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467751 prefixEnd_1467751 := by exact prefixLift 1467751
  have htrace : WordTrace (prefixWord ++ tailWord_1467751) baseStart_1467751 baseEnd_1467751 := by
    simpa [prefixWord, tailWord_1467751, baseEnd_1467751] using wordTrace_append hprefix tailTrace_1467751
  have hstable : (prefixWord ++ tailWord_1467751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467751).length < 2 ^ (prefixWord ++ tailWord_1467751).sum := by decide
  have hdescent : baseEnd_1467751 < baseStart_1467751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467796 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1467796 : Nat := 118140960795 + 1467796 * 2 ^ 59
def prefixEnd_1467796 : Nat := 4983230072969 + 3 ^ 40 * 1467796 * 2
def baseEnd_1467796 : Nat := 334971044776375322266549

theorem tailTrace_1467796 : CollatzResearch.WordTrace tailWord_1467796 prefixEnd_1467796 334971044776375322266549 := by
  unfold tailWord_1467796
  simp only [CollatzResearch.WordTrace]
  refine ⟨26767459095216623222143621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35689945460288830962858161 26767459095216623222143621)
  ·
    refine ⟨5018898580353116854151929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26767459095216623222143621 5018898580353116854151929)
    ·
      refine ⟨3764173935264837640613947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5018898580353116854151929 3764173935264837640613947)
      ·
        refine ⟨5646260902897256460920921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3764173935264837640613947 5646260902897256460920921)
        ·
          refine ⟨4234695677172942345690691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5646260902897256460920921 4234695677172942345690691)
          ·
            refine ⟨6352043515759413518536037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4234695677172942345690691 6352043515759413518536037)
            ·
              refine ⟨1191008159204890034725507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6352043515759413518536037 1191008159204890034725507)
              ·
                refine ⟨1786512238807335052088261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191008159204890034725507 1786512238807335052088261)
                ·
                  refine ⟨334971044776375322266549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786512238807335052088261 334971044776375322266549)
                  ·
                    rfl

theorem cell21_1467796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1467796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467796 prefixEnd_1467796 := by exact prefixLift 1467796
  have htrace : WordTrace (prefixWord ++ tailWord_1467796) baseStart_1467796 baseEnd_1467796 := by
    simpa [prefixWord, tailWord_1467796, baseEnd_1467796] using wordTrace_append hprefix tailTrace_1467796
  have hstable : (prefixWord ++ tailWord_1467796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467796).length < 2 ^ (prefixWord ++ tailWord_1467796).sum := by decide
  have hdescent : baseEnd_1467796 < baseStart_1467796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467900 : List Nat := [2, 2, 2, 1, 2, 1, 4, 4, 3]
def baseStart_1467900 : Nat := 118140960795 + 1467900 * 2 ^ 59
def prefixEnd_1467900 : Nat := 4983230072969 + 3 ^ 40 * 1467900 * 2
def baseEnd_1467900 : Nat := 334994778993294252533003

theorem tailTrace_1467900 : CollatzResearch.WordTrace tailWord_1467900 prefixEnd_1467900 334994778993294252533003 := by
  unfold tailWord_1467900
  simp only [CollatzResearch.WordTrace]
  refine ⟨26769355691028236103036577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35692474254704314804048769 26769355691028236103036577)
  ·
    refine ⟨20077016768271177077277433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26769355691028236103036577 20077016768271177077277433)
    ·
      refine ⟨15057762576203382807958075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20077016768271177077277433 15057762576203382807958075)
      ·
        refine ⟨22586643864305074211937113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15057762576203382807958075 22586643864305074211937113)
        ·
          refine ⟨16939982898228805658952835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22586643864305074211937113 16939982898228805658952835)
          ·
            refine ⟨25409974347343208488429253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16939982898228805658952835 25409974347343208488429253)
            ·
              refine ⟨4764370190126851591580485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25409974347343208488429253 4764370190126851591580485)
              ·
                refine ⟨893319410648784673421341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4764370190126851591580485 893319410648784673421341)
                ·
                  refine ⟨334994778993294252533003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893319410648784673421341 334994778993294252533003)
                  ·
                    rfl

theorem cell21_1467900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_1467900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467900 prefixEnd_1467900 := by exact prefixLift 1467900
  have htrace : WordTrace (prefixWord ++ tailWord_1467900) baseStart_1467900 baseEnd_1467900 := by
    simpa [prefixWord, tailWord_1467900, baseEnd_1467900] using wordTrace_append hprefix tailTrace_1467900
  have hstable : (prefixWord ++ tailWord_1467900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467900).length < 2 ^ (prefixWord ++ tailWord_1467900).sum := by decide
  have hdescent : baseEnd_1467900 < baseStart_1467900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467959 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 5]
def baseStart_1467959 : Nat := 118140960795 + 1467959 * 2 ^ 59
def prefixEnd_1467959 : Nat := 4983230072969 + 3 ^ 40 * 1467959 * 2
def baseEnd_1467959 : Nat := 335008243597123261049549

theorem tailTrace_1467959 : CollatzResearch.WordTrace tailWord_1467959 prefixEnd_1467959 335008243597123261049549 := by
  unfold tailWord_1467959
  simp only [CollatzResearch.WordTrace]
  refine ⟨53540863288842725282470931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35693908859228483521647287 53540863288842725282470931)
  ·
    refine ⟨80311294933264087923706397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53540863288842725282470931 80311294933264087923706397)
    ·
      refine ⟨30116735599974032971389899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80311294933264087923706397 30116735599974032971389899)
      ·
        refine ⟨45175103399961049457084849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30116735599974032971389899 45175103399961049457084849)
        ·
          refine ⟨33881327549970787092813637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45175103399961049457084849 33881327549970787092813637)
          ·
            refine ⟨6352748915619522579902557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33881327549970787092813637 6352748915619522579902557)
            ·
              refine ⟨2382280843357320967463459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6352748915619522579902557 2382280843357320967463459)
              ·
                refine ⟨3573421265035981451195189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382280843357320967463459 3573421265035981451195189)
                ·
                  refine ⟨335008243597123261049549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3573421265035981451195189 335008243597123261049549)
                  ·
                    rfl

theorem cell21_1467959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 5].length) (baseStart_1467959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467959 prefixEnd_1467959 := by exact prefixLift 1467959
  have htrace : WordTrace (prefixWord ++ tailWord_1467959) baseStart_1467959 baseEnd_1467959 := by
    simpa [prefixWord, tailWord_1467959, baseEnd_1467959] using wordTrace_append hprefix tailTrace_1467959
  have hstable : (prefixWord ++ tailWord_1467959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467959).length < 2 ^ (prefixWord ++ tailWord_1467959).sum := by decide
  have hdescent : baseEnd_1467959 < baseStart_1467959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467965 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 4]
def baseStart_1467965 : Nat := 118140960795 + 1467965 * 2 ^ 59
def prefixEnd_1467965 : Nat := 4983230072969 + 3 ^ 40 * 1467965 * 2
def baseEnd_1467965 : Nat := 335009612878868583949537

theorem tailTrace_1467965 : CollatzResearch.WordTrace tailWord_1467965 prefixEnd_1467965 335009612878868583949537 := by
  unfold tailWord_1467965
  simp only [CollatzResearch.WordTrace]
  refine ⟨53541082126820988307189349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35694054751213992204792899 53541082126820988307189349)
  ·
    refine ⟨10038952898778935307598003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53541082126820988307189349 10038952898778935307598003)
    ·
      refine ⟨15058429348168402961397005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10038952898778935307598003 15058429348168402961397005)
      ·
        refine ⟨5646911005563151110523877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15058429348168402961397005 5646911005563151110523877)
        ·
          refine ⟨1058795813543090833223227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5646911005563151110523877 1058795813543090833223227)
          ·
            refine ⟨1588193720314636249834841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058795813543090833223227 1588193720314636249834841)
            ·
              refine ⟨1191145290235977187376131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1588193720314636249834841 1191145290235977187376131)
              ·
                refine ⟨1786717935353965781064197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191145290235977187376131 1786717935353965781064197)
                ·
                  refine ⟨335009612878868583949537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786717935353965781064197 335009612878868583949537)
                  ·
                    rfl

theorem cell21_1467965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_1467965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1467965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1467965 prefixEnd_1467965 := by exact prefixLift 1467965
  have htrace : WordTrace (prefixWord ++ tailWord_1467965) baseStart_1467965 baseEnd_1467965 := by
    simpa [prefixWord, tailWord_1467965, baseEnd_1467965] using wordTrace_append hprefix tailTrace_1467965
  have hstable : (prefixWord ++ tailWord_1467965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467965).length < 2 ^ (prefixWord ++ tailWord_1467965).sum := by decide
  have hdescent : baseEnd_1467965 < baseStart_1467965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468010 : List Nat := [3, 1, 3, 2, 1, 4, 2, 2, 3]
def baseStart_1468010 : Nat := 118140960795 + 1468010 * 2 ^ 59
def prefixEnd_1468010 : Nat := 4983230072969 + 3 ^ 40 * 1468010 * 2
def baseEnd_1468010 : Nat := 335019882491958505699445

theorem tailTrace_1468010 : CollatzResearch.WordTrace tailWord_1468010 prefixEnd_1468010 335019882491958505699445 := by
  unfold tailWord_1468010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13385680852914490248144371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35695148941105307328384989 13385680852914490248144371)
  ·
    refine ⟨20078521279371735372216557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13385680852914490248144371 20078521279371735372216557)
    ·
      refine ⟨7529445479764400764581209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20078521279371735372216557 7529445479764400764581209)
      ·
        refine ⟨5647084109823300573435907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7529445479764400764581209 5647084109823300573435907)
        ·
          refine ⟨8470626164734950860153861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5647084109823300573435907 8470626164734950860153861)
          ·
            refine ⟨1588242405887803286278849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8470626164734950860153861 1588242405887803286278849)
            ·
              refine ⟨1191181804415852464709137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1588242405887803286278849 1191181804415852464709137)
              ·
                refine ⟨893386353311889348531853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191181804415852464709137 893386353311889348531853)
                ·
                  refine ⟨335019882491958505699445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893386353311889348531853 335019882491958505699445)
                  ·
                    rfl

theorem cell21_1468010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_1468010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468010 prefixEnd_1468010 := by exact prefixLift 1468010
  have htrace : WordTrace (prefixWord ++ tailWord_1468010) baseStart_1468010 baseEnd_1468010 := by
    simpa [prefixWord, tailWord_1468010, baseEnd_1468010] using wordTrace_append hprefix tailTrace_1468010
  have hstable : (prefixWord ++ tailWord_1468010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468010).length < 2 ^ (prefixWord ++ tailWord_1468010).sum := by decide
  have hdescent : baseEnd_1468010 < baseStart_1468010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468021 : List Nat := [1, 3, 4, 2, 1, 1, 3, 6]
def baseStart_1468021 : Nat := 118140960795 + 1468021 * 2 ^ 59
def prefixEnd_1468021 : Nat := 4983230072969 + 3 ^ 40 * 1468021 * 2
def baseEnd_1468021 : Nat := 111674130947274977005363

theorem tailTrace_1468021 : CollatzResearch.WordTrace tailWord_1468021 prefixEnd_1468021 111674130947274977005363 := by
  unfold tailWord_1468021
  simp only [CollatzResearch.WordTrace]
  refine ⟨53543124614618109871227917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35695416409745406580818611 53543124614618109871227917)
  ·
    refine ⟨20078671730481791201710469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53543124614618109871227917 20078671730481791201710469)
    ·
      refine ⟨3764750949465335850320713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20078671730481791201710469 3764750949465335850320713)
      ·
        refine ⟨2823563212099001887740535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3764750949465335850320713 2823563212099001887740535)
        ·
          refine ⟨4235344818148502831610803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2823563212099001887740535 4235344818148502831610803)
          ·
            refine ⟨6353017227222754247416205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4235344818148502831610803 6353017227222754247416205)
            ·
              refine ⟨2382381460208532842781077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6353017227222754247416205 2382381460208532842781077)
              ·
                refine ⟨111674130947274977005363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2382381460208532842781077 111674130947274977005363)
                ·
                  rfl

theorem cell21_1468021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 6].length) (baseStart_1468021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468021 prefixEnd_1468021 := by exact prefixLift 1468021
  have htrace : WordTrace (prefixWord ++ tailWord_1468021) baseStart_1468021 baseEnd_1468021 := by
    simpa [prefixWord, tailWord_1468021, baseEnd_1468021] using wordTrace_append hprefix tailTrace_1468021
  have hstable : (prefixWord ++ tailWord_1468021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468021).length < 2 ^ (prefixWord ++ tailWord_1468021).sum := by decide
  have hdescent : baseEnd_1468021 < baseStart_1468021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468139 : List Nat := [1, 1, 1, 1, 2, 4, 3, 8]
def baseStart_1468139 : Nat := 118140960795 + 1468139 * 2 ^ 59
def prefixEnd_1468139 : Nat := 4983230072969 + 3 ^ 40 * 1468139 * 2
def baseEnd_1468139 : Nat := 111683107349827649349727

theorem tailTrace_1468139 : CollatzResearch.WordTrace tailWord_1468139 prefixEnd_1468139 111683107349827649349727 := by
  unfold tailWord_1468139
  simp only [CollatzResearch.WordTrace]
  refine ⟨53547428428190616024023471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35698285618793744016015647 53547428428190616024023471)
  ·
    refine ⟨80321142642285924036035207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53547428428190616024023471 80321142642285924036035207)
    ·
      refine ⟨120481713963428886054052811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80321142642285924036035207 120481713963428886054052811)
      ·
        refine ⟨180722570945143329081079217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120481713963428886054052811 180722570945143329081079217)
        ·
          refine ⟨135541928208857496810809413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180722570945143329081079217 135541928208857496810809413)
          ·
            refine ⟨25414111539160780652026765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135541928208857496810809413 25414111539160780652026765)
            ·
              refine ⟨9530291827185292744510037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25414111539160780652026765 9530291827185292744510037)
              ·
                refine ⟨111683107349827649349727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9530291827185292744510037 111683107349827649349727)
                ·
                  rfl

theorem cell21_1468139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 8].length) (baseStart_1468139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468139 prefixEnd_1468139 := by exact prefixLift 1468139
  have htrace : WordTrace (prefixWord ++ tailWord_1468139) baseStart_1468139 baseEnd_1468139 := by
    simpa [prefixWord, tailWord_1468139, baseEnd_1468139] using wordTrace_append hprefix tailTrace_1468139
  have hstable : (prefixWord ++ tailWord_1468139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468139).length < 2 ^ (prefixWord ++ tailWord_1468139).sum := by decide
  have hdescent : baseEnd_1468139 < baseStart_1468139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468142 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_1468142 : Nat := 118140960795 + 1468142 * 2 ^ 59
def prefixEnd_1468142 : Nat := 4983230072969 + 3 ^ 40 * 1468142 * 2
def baseEnd_1468142 : Nat := 335050006690355609499175

theorem tailTrace_1468142 : CollatzResearch.WordTrace tailWord_1468142 prefixEnd_1468142 335050006690355609499175 := by
  unfold tailWord_1468142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6693442230897468442047835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35698358564786498357588453 6693442230897468442047835)
  ·
    refine ⟨10040163346346202663071753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6693442230897468442047835 10040163346346202663071753)
    ·
      refine ⟨7530122509759651997303815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10040163346346202663071753 7530122509759651997303815)
      ·
        refine ⟨11295183764639477995955723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7530122509759651997303815 11295183764639477995955723)
        ·
          refine ⟨16942775646959216993933585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11295183764639477995955723 16942775646959216993933585)
          ·
            refine ⟨12707081735219412745450189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16942775646959216993933585 12707081735219412745450189)
            ·
              refine ⟨4765155650707279779543821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12707081735219412745450189 4765155650707279779543821)
              ·
                refine ⟨1786933369015229917328933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4765155650707279779543821 1786933369015229917328933)
                ·
                  refine ⟨335050006690355609499175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786933369015229917328933 335050006690355609499175)
                  ·
                    rfl

theorem cell21_1468142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_1468142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468142 prefixEnd_1468142 := by exact prefixLift 1468142
  have htrace : WordTrace (prefixWord ++ tailWord_1468142) baseStart_1468142 baseEnd_1468142 := by
    simpa [prefixWord, tailWord_1468142, baseEnd_1468142] using wordTrace_append hprefix tailTrace_1468142
  have hstable : (prefixWord ++ tailWord_1468142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468142).length < 2 ^ (prefixWord ++ tailWord_1468142).sum := by decide
  have hdescent : baseEnd_1468142 < baseStart_1468142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468187 : List Nat := [1, 1, 1, 1, 1, 1, 4, 8, 3]
def baseStart_1468187 : Nat := 118140960795 + 1468187 * 2 ^ 59
def prefixEnd_1468187 : Nat := 4983230072969 + 3 ^ 40 * 1468187 * 2
def baseEnd_1468187 : Nat := 335060276303445531249083

theorem tailTrace_1468187 : CollatzResearch.WordTrace tailWord_1468187 prefixEnd_1468187 335060276303445531249083 := by
  unfold tailWord_1468187
  simp only [CollatzResearch.WordTrace]
  refine ⟨53549179132016720221770815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35699452754677813481180543 53549179132016720221770815)
  ·
    refine ⟨80323768698025080332656223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53549179132016720221770815 80323768698025080332656223)
    ·
      refine ⟨120485653047037620498984335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80323768698025080332656223 120485653047037620498984335)
      ·
        refine ⟨180728479570556430748476503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120485653047037620498984335 180728479570556430748476503)
        ·
          refine ⟨271092719355834646122714755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180728479570556430748476503 271092719355834646122714755)
          ·
            refine ⟨406639079033751969184072133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271092719355834646122714755 406639079033751969184072133)
            ·
              refine ⟨76244827318828494222013525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406639079033751969184072133 76244827318828494222013525)
              ·
                refine ⟨893494070142521416664221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 76244827318828494222013525 893494070142521416664221)
                ·
                  refine ⟨335060276303445531249083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893494070142521416664221 335060276303445531249083)
                  ·
                    rfl

theorem cell21_1468187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 3].length) (baseStart_1468187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468187 prefixEnd_1468187 := by exact prefixLift 1468187
  have htrace : WordTrace (prefixWord ++ tailWord_1468187) baseStart_1468187 baseEnd_1468187 := by
    simpa [prefixWord, tailWord_1468187, baseEnd_1468187] using wordTrace_append hprefix tailTrace_1468187
  have hstable : (prefixWord ++ tailWord_1468187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468187).length < 2 ^ (prefixWord ++ tailWord_1468187).sum := by decide
  have hdescent : baseEnd_1468187 < baseStart_1468187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468221 : List Nat := [1, 4, 1, 4, 1, 2, 2, 3, 3]
def baseStart_1468221 : Nat := 118140960795 + 1468221 * 2 ^ 59
def prefixEnd_1468221 : Nat := 4983230072969 + 3 ^ 40 * 1468221 * 2
def baseEnd_1468221 : Nat := 335068035566669027682347

theorem tailTrace_1468221 : CollatzResearch.WordTrace tailWord_1468221 prefixEnd_1468221 335068035566669027682347 := by
  unfold tailWord_1468221
  simp only [CollatzResearch.WordTrace]
  refine ⟨53550419213893544028508517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35700279475929029352339011 53550419213893544028508517)
  ·
    refine ⟨10040703602605039505345347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53550419213893544028508517 10040703602605039505345347)
    ·
      refine ⟨15061055403907559258018021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10040703602605039505345347 15061055403907559258018021)
      ·
        refine ⟨2823947888232667360878379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15061055403907559258018021 2823947888232667360878379)
        ·
          refine ⟨4235921832349001041317569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2823947888232667360878379 4235921832349001041317569)
          ·
            refine ⟨3176941374261750780988177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4235921832349001041317569 3176941374261750780988177)
            ·
              refine ⟨2382706030696313085741133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3176941374261750780988177 2382706030696313085741133)
              ·
                refine ⟨893514761511117407152925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2382706030696313085741133 893514761511117407152925)
                ·
                  refine ⟨335068035566669027682347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893514761511117407152925 335068035566669027682347)
                  ·
                    rfl

theorem cell21_1468221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_1468221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468221 prefixEnd_1468221 := by exact prefixLift 1468221
  have htrace : WordTrace (prefixWord ++ tailWord_1468221) baseStart_1468221 baseEnd_1468221 := by
    simpa [prefixWord, tailWord_1468221, baseEnd_1468221] using wordTrace_append hprefix tailTrace_1468221
  have hstable : (prefixWord ++ tailWord_1468221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468221).length < 2 ^ (prefixWord ++ tailWord_1468221).sum := by decide
  have hdescent : baseEnd_1468221 < baseStart_1468221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468252 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 4]
def baseStart_1468252 : Nat := 118140960795 + 1468252 * 2 ^ 59
def prefixEnd_1468252 : Nat := 4983230072969 + 3 ^ 40 * 1468252 * 2
def baseEnd_1468252 : Nat := 335075110189019862665617

theorem tailTrace_1468252 : CollatzResearch.WordTrace tailWord_1468252 prefixEnd_1468252 335075110189019862665617 := by
  unfold tailWord_1468252
  simp only [CollatzResearch.WordTrace]
  refine ⟨26775774938390618161443505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35701033251187490881924673 26775774938390618161443505)
  ·
    refine ⟨20081831203792963621082629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26775774938390618161443505 20081831203792963621082629)
    ·
      refine ⟨3765343350711180678952993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20081831203792963621082629 3765343350711180678952993)
      ·
        refine ⟨2824007513033385509214745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3765343350711180678952993 2824007513033385509214745)
        ·
          refine ⟨2118005634775039131911059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2824007513033385509214745 2118005634775039131911059)
          ·
            refine ⟨3177008452162558697866589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118005634775039131911059 3177008452162558697866589)
            ·
              refine ⟨1191378169560959511699971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3177008452162558697866589 1191378169560959511699971)
              ·
                refine ⟨1787067254341439267549957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191378169560959511699971 1787067254341439267549957)
                ·
                  refine ⟨335075110189019862665617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1787067254341439267549957 335075110189019862665617)
                  ·
                    rfl

theorem cell21_1468252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_1468252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468252 prefixEnd_1468252 := by exact prefixLift 1468252
  have htrace : WordTrace (prefixWord ++ tailWord_1468252) baseStart_1468252 baseEnd_1468252 := by
    simpa [prefixWord, tailWord_1468252, baseEnd_1468252] using wordTrace_append hprefix tailTrace_1468252
  have hstable : (prefixWord ++ tailWord_1468252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468252).length < 2 ^ (prefixWord ++ tailWord_1468252).sum := by decide
  have hdescent : baseEnd_1468252 < baseStart_1468252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468277 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 8]
def baseStart_1468277 : Nat := 118140960795 + 1468277 * 2 ^ 59
def prefixEnd_1468277 : Nat := 4983230072969 + 3 ^ 40 * 1468277 * 2
def baseEnd_1468277 : Nat := 335080815529625374748899

theorem tailTrace_1468277 : CollatzResearch.WordTrace tailWord_1468277 prefixEnd_1468277 335080815529625374748899 := by
  unfold tailWord_1468277
  simp only [CollatzResearch.WordTrace]
  refine ⟨53552461701690665592547085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35701641134460443728364723 53552461701690665592547085)
  ·
    refine ⟨20082173138133999597205157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53552461701690665592547085 20082173138133999597205157)
    ·
      refine ⟨3765407463400124924475967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20082173138133999597205157 3765407463400124924475967)
      ·
        refine ⟨5648111195100187386713951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3765407463400124924475967 5648111195100187386713951)
        ·
          refine ⟨8472166792650281080070927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5648111195100187386713951 8472166792650281080070927)
          ·
            refine ⟨12708250188975421620106391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8472166792650281080070927 12708250188975421620106391)
            ·
              refine ⟨19062375283463132430159587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12708250188975421620106391 19062375283463132430159587)
              ·
                refine ⟨28593562925194698645239381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19062375283463132430159587 28593562925194698645239381)
                ·
                  refine ⟨335080815529625374748899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28593562925194698645239381 335080815529625374748899)
                  ·
                    rfl

theorem cell21_1468277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_1468277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468277 prefixEnd_1468277 := by exact prefixLift 1468277
  have htrace : WordTrace (prefixWord ++ tailWord_1468277) baseStart_1468277 baseEnd_1468277 := by
    simpa [prefixWord, tailWord_1468277, baseEnd_1468277] using wordTrace_append hprefix tailTrace_1468277
  have hstable : (prefixWord ++ tailWord_1468277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468277).length < 2 ^ (prefixWord ++ tailWord_1468277).sum := by decide
  have hdescent : baseEnd_1468277 < baseStart_1468277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468291 : List Nat := [1, 1, 1, 3, 4, 2, 9]
def baseStart_1468291 : Nat := 118140960795 + 1468291 * 2 ^ 59
def prefixEnd_1468291 : Nat := 4983230072969 + 3 ^ 40 * 1468291 * 2
def baseEnd_1468291 : Nat := 37231556724484940168393

theorem tailTrace_1468291 : CollatzResearch.WordTrace tailWord_1468291 prefixEnd_1468291 37231556724484940168393 := by
  unfold tailWord_1468291
  simp only [CollatzResearch.WordTrace]
  refine ⟨53552972323639945983556727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35701981549093297322371151 53552972323639945983556727)
  ·
    refine ⟨80329458485459918975335091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53552972323639945983556727 80329458485459918975335091)
    ·
      refine ⟨120494187728189878463002637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80329458485459918975335091 120494187728189878463002637)
      ·
        refine ⟨45185320398071204423625989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120494187728189878463002637 45185320398071204423625989)
        ·
          refine ⟨8472247574638350829429873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45185320398071204423625989 8472247574638350829429873)
          ·
            refine ⟨6354185680978763122072405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8472247574638350829429873 6354185680978763122072405)
            ·
              refine ⟨37231556724484940168393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6354185680978763122072405 37231556724484940168393)
              ·
                rfl

theorem cell21_1468291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 9].length) (baseStart_1468291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468291 prefixEnd_1468291 := by exact prefixLift 1468291
  have htrace : WordTrace (prefixWord ++ tailWord_1468291) baseStart_1468291 baseEnd_1468291 := by
    simpa [prefixWord, tailWord_1468291, baseEnd_1468291] using wordTrace_append hprefix tailTrace_1468291
  have hstable : (prefixWord ++ tailWord_1468291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468291).length < 2 ^ (prefixWord ++ tailWord_1468291).sum := by decide
  have hdescent : baseEnd_1468291 < baseStart_1468291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468308 : List Nat := [2, 4, 2, 1, 1, 2, 1, 8]
def baseStart_1468308 : Nat := 118140960795 + 1468308 * 2 ^ 59
def prefixEnd_1468308 : Nat := 4983230072969 + 3 ^ 40 * 1468308 * 2
def baseEnd_1468308 : Nat := 111695963383992069910723

theorem tailTrace_1468308 : CollatzResearch.WordTrace tailWord_1468308 prefixEnd_1468308 111695963383992069910723 := by
  unfold tailWord_1468308
  simp only [CollatzResearch.WordTrace]
  refine ⟨26776796182289178943462789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35702394909718905257950385 26776796182289178943462789)
  ·
    refine ⟨5020649284179221051899273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26776796182289178943462789 5020649284179221051899273)
    ·
      refine ⟨3765486963134415788924455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5020649284179221051899273 3765486963134415788924455)
      ·
        refine ⟨5648230444701623683386683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3765486963134415788924455 5648230444701623683386683)
        ·
          refine ⟨8472345667052435525080025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5648230444701623683386683 8472345667052435525080025)
          ·
            refine ⟨6354259250289326643810019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8472345667052435525080025 6354259250289326643810019)
            ·
              refine ⟨9531388875433989965715029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6354259250289326643810019 9531388875433989965715029)
              ·
                refine ⟨111695963383992069910723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9531388875433989965715029 111695963383992069910723)
                ·
                  rfl

theorem cell21_1468308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_1468308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468308 prefixEnd_1468308 := by exact prefixLift 1468308
  have htrace : WordTrace (prefixWord ++ tailWord_1468308) baseStart_1468308 baseEnd_1468308 := by
    simpa [prefixWord, tailWord_1468308, baseEnd_1468308] using wordTrace_append hprefix tailTrace_1468308
  have hstable : (prefixWord ++ tailWord_1468308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468308).length < 2 ^ (prefixWord ++ tailWord_1468308).sum := by decide
  have hdescent : baseEnd_1468308 < baseStart_1468308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468311 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 4]
def baseStart_1468311 : Nat := 118140960795 + 1468311 * 2 ^ 59
def prefixEnd_1468311 : Nat := 4983230072969 + 3 ^ 40 * 1468311 * 2
def baseEnd_1468311 : Nat := 335088574792848871182163

theorem tailTrace_1468311 : CollatzResearch.WordTrace tailWord_1468311 prefixEnd_1468311 335088574792848871182163 := by
  unfold tailWord_1468311
  simp only [CollatzResearch.WordTrace]
  refine ⟨53553701783567489399284787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35702467855711659599523191 53553701783567489399284787)
  ·
    refine ⟨80330552675351234098927181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53553701783567489399284787 80330552675351234098927181)
    ·
      refine ⟨30123957253256712787097693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80330552675351234098927181 30123957253256712787097693)
      ·
        refine ⟨11296483969971267295161635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30123957253256712787097693 11296483969971267295161635)
        ·
          refine ⟨16944725954956900942742453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11296483969971267295161635 16944725954956900942742453)
          ·
            refine ⟨1588568058277209463382105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16944725954956900942742453 1588568058277209463382105)
            ·
              refine ⟨1191426043707907097536579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1588568058277209463382105 1191426043707907097536579)
              ·
                refine ⟨1787139065561860646304869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191426043707907097536579 1787139065561860646304869)
                ·
                  refine ⟨335088574792848871182163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1787139065561860646304869 335088574792848871182163)
                  ·
                    rfl

theorem cell21_1468311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 4].length) (baseStart_1468311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468311 prefixEnd_1468311 := by exact prefixLift 1468311
  have htrace : WordTrace (prefixWord ++ tailWord_1468311) baseStart_1468311 baseEnd_1468311 := by
    simpa [prefixWord, tailWord_1468311, baseEnd_1468311] using wordTrace_append hprefix tailTrace_1468311
  have hstable : (prefixWord ++ tailWord_1468311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468311).length < 2 ^ (prefixWord ++ tailWord_1468311).sum := by decide
  have hdescent : baseEnd_1468311 < baseStart_1468311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468339 : List Nat := [1, 1, 1, 2, 3, 1, 4, 5, 3]
def baseStart_1468339 : Nat := 118140960795 + 1468339 * 2 ^ 59
def prefixEnd_1468339 : Nat := 4983230072969 + 3 ^ 40 * 1468339 * 2
def baseEnd_1468339 : Nat := 335094964774327044715439

theorem tailTrace_1468339 : CollatzResearch.WordTrace tailWord_1468339 prefixEnd_1468339 335094964774327044715439 := by
  unfold tailWord_1468339
  simp only [CollatzResearch.WordTrace]
  refine ⟨53554723027466050181304071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35703148684977366787536047 53554723027466050181304071)
  ·
    refine ⟨80332084541199075271956107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53554723027466050181304071 80332084541199075271956107)
    ·
      refine ⟨120498126811798612907934161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80332084541199075271956107 120498126811798612907934161)
      ·
        refine ⟨90373595108848959680950621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120498126811798612907934161 90373595108848959680950621)
        ·
          refine ⟨33890098165818359880356483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90373595108848959680950621 33890098165818359880356483)
          ·
            refine ⟨50835147248727539820534725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33890098165818359880356483 50835147248727539820534725)
            ·
              refine ⟨9531590109136413716350261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50835147248727539820534725 9531590109136413716350261)
              ·
                refine ⟨893586572731538785907837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9531590109136413716350261 893586572731538785907837)
                ·
                  refine ⟨335094964774327044715439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893586572731538785907837 335094964774327044715439)
                  ·
                    rfl

theorem cell21_1468339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 3].length) (baseStart_1468339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468339 prefixEnd_1468339 := by exact prefixLift 1468339
  have htrace : WordTrace (prefixWord ++ tailWord_1468339) baseStart_1468339 baseEnd_1468339 := by
    simpa [prefixWord, tailWord_1468339, baseEnd_1468339] using wordTrace_append hprefix tailTrace_1468339
  have hstable : (prefixWord ++ tailWord_1468339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468339).length < 2 ^ (prefixWord ++ tailWord_1468339).sum := by decide
  have hdescent : baseEnd_1468339 < baseStart_1468339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468449 : List Nat := [1, 2, 3, 2, 4, 2, 1, 3, 3]
def baseStart_1468449 : Nat := 118140960795 + 1468449 * 2 ^ 59
def prefixEnd_1468449 : Nat := 4983230072969 + 3 ^ 40 * 1468449 * 2
def baseEnd_1468449 : Nat := 335120068272991297881881

theorem tailTrace_1468449 : CollatzResearch.WordTrace tailWord_1468449 prefixEnd_1468449 335120068272991297881881 := by
  unfold tailWord_1468449
  simp only [CollatzResearch.WordTrace]
  refine ⟨53558735057067538967808401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35705823371378359311872267 53558735057067538967808401)
  ·
    refine ⟨40169051292800654225856301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53558735057067538967808401 40169051292800654225856301)
    ·
      refine ⟨15063394234800245334696113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40169051292800654225856301 15063394234800245334696113)
      ·
        refine ⟨11297545676100184001022085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15063394234800245334696113 11297545676100184001022085)
        ·
          refine ⟨2118289814268784500191641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11297545676100184001022085 2118289814268784500191641)
          ·
            refine ⟨1588717360701588375143731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2118289814268784500191641 1588717360701588375143731)
            ·
              refine ⟨2383076041052382562715597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588717360701588375143731 2383076041052382562715597)
              ·
                refine ⟨893653515394643461018349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2383076041052382562715597 893653515394643461018349)
                ·
                  refine ⟨335120068272991297881881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893653515394643461018349 335120068272991297881881)
                  ·
                    rfl

theorem cell21_1468449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 3].length) (baseStart_1468449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468449 prefixEnd_1468449 := by exact prefixLift 1468449
  have htrace : WordTrace (prefixWord ++ tailWord_1468449) baseStart_1468449 baseEnd_1468449 := by
    simpa [prefixWord, tailWord_1468449, baseEnd_1468449] using wordTrace_append hprefix tailTrace_1468449
  have hstable : (prefixWord ++ tailWord_1468449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468449).length < 2 ^ (prefixWord ++ tailWord_1468449).sum := by decide
  have hdescent : baseEnd_1468449 < baseStart_1468449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468488 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_1468488 : Nat := 118140960795 + 1468488 * 2 ^ 59
def prefixEnd_1468488 : Nat := 4983230072969 + 3 ^ 40 * 1468488 * 2
def baseEnd_1468488 : Nat := 335128968604335896731801

theorem tailTrace_1468488 : CollatzResearch.WordTrace tailWord_1468488 prefixEnd_1468488 335128968604335896731801 := by
  unfold tailWord_1468488
  simp only [CollatzResearch.WordTrace]
  refine ⟨26780078751963124314239059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35706771669284165752318745 26780078751963124314239059)
  ·
    refine ⟨40170118127944686471358589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26780078751963124314239059 40170118127944686471358589)
    ·
      refine ⟨15063794297979257426759471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40170118127944686471358589 15063794297979257426759471)
      ·
        refine ⟨22595691446968886140139207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15063794297979257426759471 22595691446968886140139207)
        ·
          refine ⟨33893537170453329210208811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22595691446968886140139207 33893537170453329210208811)
          ·
            refine ⟨50840305755679993815313217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33893537170453329210208811 50840305755679993815313217)
            ·
              refine ⟨38130229316759995361484913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50840305755679993815313217 38130229316759995361484913)
              ·
                refine ⟨28597671987569996521113685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38130229316759995361484913 28597671987569996521113685)
                ·
                  refine ⟨335128968604335896731801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28597671987569996521113685 335128968604335896731801)
                  ·
                    rfl

theorem cell21_1468488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_1468488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468488 prefixEnd_1468488 := by exact prefixLift 1468488
  have htrace : WordTrace (prefixWord ++ tailWord_1468488) baseStart_1468488 baseEnd_1468488 := by
    simpa [prefixWord, tailWord_1468488, baseEnd_1468488] using wordTrace_append hprefix tailTrace_1468488
  have hstable : (prefixWord ++ tailWord_1468488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468488).length < 2 ^ (prefixWord ++ tailWord_1468488).sum := by decide
  have hdescent : baseEnd_1468488 < baseStart_1468488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468612 : List Nat := [2, 3, 3, 1, 2, 2, 1, 7]
def baseStart_1468612 : Nat := 118140960795 + 1468612 * 2 ^ 59
def prefixEnd_1468612 : Nat := 4983230072969 + 3 ^ 40 * 1468612 * 2
def baseEnd_1468612 : Nat := 111719089031246412221627

theorem tailTrace_1468612 : CollatzResearch.WordTrace tailWord_1468612 prefixEnd_1468612 111719089031246412221627 := by
  unfold tailWord_1468612
  simp only [CollatzResearch.WordTrace]
  refine ⟨26782340077738508902996045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35709786770318011870661393 26782340077738508902996045)
  ·
    refine ⟨10043377529151940838623517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26782340077738508902996045 10043377529151940838623517)
    ·
      refine ⟨3766266573431977814483819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10043377529151940838623517 3766266573431977814483819)
      ·
        refine ⟨5649399860147966721725729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3766266573431977814483819 5649399860147966721725729)
        ·
          refine ⟨4237049895110975041294297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5649399860147966721725729 4237049895110975041294297)
          ·
            refine ⟨3177787421333231280970723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4237049895110975041294297 3177787421333231280970723)
            ·
              refine ⟨4766681131999846921456085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177787421333231280970723 4766681131999846921456085)
              ·
                refine ⟨111719089031246412221627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4766681131999846921456085 111719089031246412221627)
                ·
                  rfl

theorem cell21_1468612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_1468612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468612 prefixEnd_1468612 := by exact prefixLift 1468612
  have htrace : WordTrace (prefixWord ++ tailWord_1468612) baseStart_1468612 baseEnd_1468612 := by
    simpa [prefixWord, tailWord_1468612, baseEnd_1468612] using wordTrace_append hprefix tailTrace_1468612
  have hstable : (prefixWord ++ tailWord_1468612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468612).length < 2 ^ (prefixWord ++ tailWord_1468612).sum := by decide
  have hdescent : baseEnd_1468612 < baseStart_1468612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468629 : List Nat := [1, 3, 2, 4, 3, 1, 7]
def baseStart_1468629 : Nat := 118140960795 + 1468629 * 2 ^ 59
def prefixEnd_1468629 : Nat := 4983230072969 + 3 ^ 40 * 1468629 * 2
def baseEnd_1468629 : Nat := 37240127413927887209057

theorem tailTrace_1468629 : CollatzResearch.WordTrace tailWord_1468629 prefixEnd_1468629 37240127413927887209057 := by
  unfold tailWord_1468629
  simp only [CollatzResearch.WordTrace]
  refine ⟨53565300196415429709360941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35710200130943619806240627 53565300196415429709360941)
  ·
    refine ⟨20086987573655786141010353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53565300196415429709360941 20086987573655786141010353)
    ·
      refine ⟨15065240680241839605757765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20086987573655786141010353 15065240680241839605757765)
      ·
        refine ⟨2824732627545344926079581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15065240680241839605757765 2824732627545344926079581)
        ·
          refine ⟨1059274735329504347279843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2824732627545344926079581 1059274735329504347279843)
          ·
            refine ⟨1588912102994256520919765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059274735329504347279843 1588912102994256520919765)
            ·
              refine ⟨37240127413927887209057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1588912102994256520919765 37240127413927887209057)
              ·
                rfl

theorem cell21_1468629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 7].length) (baseStart_1468629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468629 prefixEnd_1468629 := by exact prefixLift 1468629
  have htrace : WordTrace (prefixWord ++ tailWord_1468629) baseStart_1468629 baseEnd_1468629 := by
    simpa [prefixWord, tailWord_1468629, baseEnd_1468629] using wordTrace_append hprefix tailTrace_1468629
  have hstable : (prefixWord ++ tailWord_1468629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468629).length < 2 ^ (prefixWord ++ tailWord_1468629).sum := by decide
  have hdescent : baseEnd_1468629 < baseStart_1468629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468640 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_1468640 : Nat := 118140960795 + 1468640 * 2 ^ 59
def prefixEnd_1468640 : Nat := 4983230072969 + 3 ^ 40 * 1468640 * 2
def baseEnd_1468640 : Nat := 335163657075217410198157

theorem tailTrace_1468640 : CollatzResearch.WordTrace tailWord_1468640 prefixEnd_1468640 335163657075217410198157 := by
  unfold tailWord_1468640
  simp only [CollatzResearch.WordTrace]
  refine ⟨26782850699687789294005687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35710467599583719058674249 26782850699687789294005687)
  ·
    refine ⟨40174276049531683941008531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26782850699687789294005687 40174276049531683941008531)
    ·
      refine ⟨60261414074297525911512797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40174276049531683941008531 60261414074297525911512797)
      ·
        refine ⟨22598030277861572216817299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60261414074297525911512797 22598030277861572216817299)
        ·
          refine ⟨33897045416792358325225949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22598030277861572216817299 33897045416792358325225949)
          ·
            refine ⟨12711392031297134371959731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33897045416792358325225949 12711392031297134371959731)
            ·
              refine ⟨19067088046945701557939597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12711392031297134371959731 19067088046945701557939597)
              ·
                refine ⟨7150158017604638084227349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19067088046945701557939597 7150158017604638084227349)
                ·
                  refine ⟨335163657075217410198157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7150158017604638084227349 335163657075217410198157)
                  ·
                    rfl

theorem cell21_1468640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_1468640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468640 prefixEnd_1468640 := by exact prefixLift 1468640
  have htrace : WordTrace (prefixWord ++ tailWord_1468640) baseStart_1468640 baseEnd_1468640 := by
    simpa [prefixWord, tailWord_1468640, baseEnd_1468640] using wordTrace_append hprefix tailTrace_1468640
  have hstable : (prefixWord ++ tailWord_1468640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468640).length < 2 ^ (prefixWord ++ tailWord_1468640).sum := by decide
  have hdescent : baseEnd_1468640 < baseStart_1468640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468795 : List Nat := [1, 1, 1, 1, 1, 7, 3, 3, 3]
def baseStart_1468795 : Nat := 118140960795 + 1468795 * 2 ^ 59
def prefixEnd_1468795 : Nat := 4983230072969 + 3 ^ 40 * 1468795 * 2
def baseEnd_1468795 : Nat := 335199030186971585114507

theorem tailTrace_1468795 : CollatzResearch.WordTrace tailWord_1468795 prefixEnd_1468795 335199030186971585114507 := by
  unfold tailWord_1468795
  simp only [CollatzResearch.WordTrace]
  refine ⟨53571354713814040059903839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35714236475876026706602559 53571354713814040059903839)
  ·
    refine ⟨80357032070721060089855759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53571354713814040059903839 80357032070721060089855759)
    ·
      refine ⟨120535548106081590134783639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80357032070721060089855759 120535548106081590134783639)
      ·
        refine ⟨180803322159122385202175459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120535548106081590134783639 180803322159122385202175459)
        ·
          refine ⟨271204983238683577803263189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180803322159122385202175459 271204983238683577803263189)
          ·
            refine ⟨6356366794656646354763981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 271204983238683577803263189 6356366794656646354763981)
            ·
              refine ⟨2383637547996242383036493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6356366794656646354763981 2383637547996242383036493)
              ·
                refine ⟨893864080498590893638685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2383637547996242383036493 893864080498590893638685)
                ·
                  refine ⟨335199030186971585114507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893864080498590893638685 335199030186971585114507)
                  ·
                    rfl

theorem cell21_1468795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 3].length) (baseStart_1468795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468795 prefixEnd_1468795 := by exact prefixLift 1468795
  have htrace : WordTrace (prefixWord ++ tailWord_1468795) baseStart_1468795 baseEnd_1468795 := by
    simpa [prefixWord, tailWord_1468795, baseEnd_1468795] using wordTrace_append hprefix tailTrace_1468795
  have hstable : (prefixWord ++ tailWord_1468795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468795).length < 2 ^ (prefixWord ++ tailWord_1468795).sum := by decide
  have hdescent : baseEnd_1468795 < baseStart_1468795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468812 : List Nat := [2, 2, 1, 2, 1, 5, 3, 2, 3]
def baseStart_1468812 : Nat := 118140960795 + 1468812 * 2 ^ 59
def prefixEnd_1468812 : Nat := 4983230072969 + 3 ^ 40 * 1468812 * 2
def baseEnd_1468812 : Nat := 335202909818583333331139

theorem tailTrace_1468812 : CollatzResearch.WordTrace tailWord_1468812 prefixEnd_1468812 335202909818583333331139 := by
  unfold tailWord_1468812
  simp only [CollatzResearch.WordTrace]
  refine ⟨26785987377376225981636345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35714649836501634642181793 26785987377376225981636345)
  ·
    refine ⟨20089490533032169486227259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26785987377376225981636345 20089490533032169486227259)
    ·
      refine ⟨30134235799548254229340889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20089490533032169486227259 30134235799548254229340889)
      ·
        refine ⟨22600676849661190672005667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30134235799548254229340889 22600676849661190672005667)
        ·
          refine ⟨33901015274491786008008501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22600676849661190672005667 33901015274491786008008501)
          ·
            refine ⟨3178220181983604938250797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33901015274491786008008501 3178220181983604938250797)
            ·
              refine ⟨1191832568243851851844049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3178220181983604938250797 1191832568243851851844049)
              ·
                refine ⟨893874426182888888883037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191832568243851851844049 893874426182888888883037)
                ·
                  refine ⟨335202909818583333331139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893874426182888888883037 335202909818583333331139)
                  ·
                    rfl

theorem cell21_1468812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_1468812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468812 prefixEnd_1468812 := by exact prefixLift 1468812
  have htrace : WordTrace (prefixWord ++ tailWord_1468812) baseStart_1468812 baseEnd_1468812 := by
    simpa [prefixWord, tailWord_1468812, baseEnd_1468812] using wordTrace_append hprefix tailTrace_1468812
  have hstable : (prefixWord ++ tailWord_1468812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468812).length < 2 ^ (prefixWord ++ tailWord_1468812).sum := by decide
  have hdescent : baseEnd_1468812 < baseStart_1468812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468826 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_1468826 : Nat := 118140960795 + 1468826 * 2 ^ 59
def prefixEnd_1468826 : Nat := 4983230072969 + 3 ^ 40 * 1468826 * 2
def baseEnd_1468826 : Nat := 335206104809322420097777

theorem tailTrace_1468826 : CollatzResearch.WordTrace tailWord_1468826 prefixEnd_1468826 335206104809322420097777 := by
  unfold tailWord_1468826
  simp only [CollatzResearch.WordTrace]
  refine ⟨13393121344175433088570583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35714990251134488236188221 13393121344175433088570583)
  ·
    refine ⟨20089682016263149632855875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13393121344175433088570583 20089682016263149632855875)
    ·
      refine ⟨30134523024394724449283813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20089682016263149632855875 30134523024394724449283813)
      ·
        refine ⟨5650223067074010834240715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30134523024394724449283813 5650223067074010834240715)
        ·
          refine ⟨8475334600611016251361073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5650223067074010834240715 8475334600611016251361073)
          ·
            refine ⟨6356500950458262188520805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8475334600611016251361073 6356500950458262188520805)
            ·
              refine ⟨1191843928210924160347651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6356500950458262188520805 1191843928210924160347651)
              ·
                refine ⟨1787765892316386240521477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191843928210924160347651 1787765892316386240521477)
                ·
                  refine ⟨335206104809322420097777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1787765892316386240521477 335206104809322420097777)
                  ·
                    rfl

theorem cell21_1468826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_1468826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468826 prefixEnd_1468826 := by exact prefixLift 1468826
  have htrace : WordTrace (prefixWord ++ tailWord_1468826) baseStart_1468826 baseEnd_1468826 := by
    simpa [prefixWord, tailWord_1468826, baseEnd_1468826] using wordTrace_append hprefix tailTrace_1468826
  have hstable : (prefixWord ++ tailWord_1468826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468826).length < 2 ^ (prefixWord ++ tailWord_1468826).sum := by decide
  have hdescent : baseEnd_1468826 < baseStart_1468826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468837 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 7]
def baseStart_1468837 : Nat := 118140960795 + 1468837 * 2 ^ 59
def prefixEnd_1468837 : Nat := 4983230072969 + 3 ^ 40 * 1468837 * 2
def baseEnd_1468837 : Nat := 335208615159188845414421

theorem tailTrace_1468837 : CollatzResearch.WordTrace tailWord_1468837 prefixEnd_1468837 335208615159188845414421 := by
  unfold tailWord_1468837
  simp only [CollatzResearch.WordTrace]
  refine ⟨53572886579661881232932765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35715257719774587488621843 53572886579661881232932765)
  ·
    refine ⟨20089832467373205462349787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53572886579661881232932765 20089832467373205462349787)
    ·
      refine ⟨30134748701059808193524681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20089832467373205462349787 30134748701059808193524681)
      ·
        refine ⟨22601061525794856145143511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30134748701059808193524681 22601061525794856145143511)
        ·
          refine ⟨33901592288692284217715267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22601061525794856145143511 33901592288692284217715267)
          ·
            refine ⟨50852388433038426326572901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33901592288692284217715267 50852388433038426326572901)
            ·
              refine ⟨9534822831194704936232419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50852388433038426326572901 9534822831194704936232419)
              ·
                refine ⟨14302234246792057404348629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9534822831194704936232419 14302234246792057404348629)
                ·
                  refine ⟨335208615159188845414421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14302234246792057404348629 335208615159188845414421)
                  ·
                    rfl

theorem cell21_1468837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_1468837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468837 prefixEnd_1468837 := by exact prefixLift 1468837
  have htrace : WordTrace (prefixWord ++ tailWord_1468837) baseStart_1468837 baseEnd_1468837 := by
    simpa [prefixWord, tailWord_1468837, baseEnd_1468837] using wordTrace_append hprefix tailTrace_1468837
  have hstable : (prefixWord ++ tailWord_1468837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468837).length < 2 ^ (prefixWord ++ tailWord_1468837).sum := by decide
  have hdescent : baseEnd_1468837 < baseStart_1468837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468840 : List Nat := [2, 1, 6, 1, 1, 1, 2, 7]
def baseStart_1468840 : Nat := 118140960795 + 1468840 * 2 ^ 59
def prefixEnd_1468840 : Nat := 4983230072969 + 3 ^ 40 * 1468840 * 2
def baseEnd_1468840 : Nat := 111736433266687168954805

theorem tailTrace_1468840 : CollatzResearch.WordTrace tailWord_1468840 prefixEnd_1468840 111736433266687168954805 := by
  unfold tailWord_1468840
  simp only [CollatzResearch.WordTrace]
  refine ⟨26786497999325506372645987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35715330665767341830194649 26786497999325506372645987)
  ·
    refine ⟨40179746998988259558968981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26786497999325506372645987 40179746998988259558968981)
    ·
      refine ⟨1883425640577574666826671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40179746998988259558968981 1883425640577574666826671)
      ·
        refine ⟨2825138460866362000240007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1883425640577574666826671 2825138460866362000240007)
        ·
          refine ⟨4237707691299543000360011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2825138460866362000240007 4237707691299543000360011)
          ·
            refine ⟨6356561536949314500540017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237707691299543000360011 6356561536949314500540017)
            ·
              refine ⟨4767421152711985875405013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6356561536949314500540017 4767421152711985875405013)
              ·
                refine ⟨111736433266687168954805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4767421152711985875405013 111736433266687168954805)
                ·
                  rfl

theorem cell21_1468840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_1468840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468840 prefixEnd_1468840 := by exact prefixLift 1468840
  have htrace : WordTrace (prefixWord ++ tailWord_1468840) baseStart_1468840 baseEnd_1468840 := by
    simpa [prefixWord, tailWord_1468840, baseEnd_1468840] using wordTrace_append hprefix tailTrace_1468840
  have hstable : (prefixWord ++ tailWord_1468840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468840).length < 2 ^ (prefixWord ++ tailWord_1468840).sum := by decide
  have hdescent : baseEnd_1468840 < baseStart_1468840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468871 : List Nat := [1, 1, 4, 1, 1, 5, 1, 4, 3]
def baseStart_1468871 : Nat := 118140960795 + 1468871 * 2 ^ 59
def prefixEnd_1468871 : Nat := 4983230072969 + 3 ^ 40 * 1468871 * 2
def baseEnd_1468871 : Nat := 335216374422412341847685

theorem tailTrace_1468871 : CollatzResearch.WordTrace tailWord_1468871 prefixEnd_1468871 335216374422412341847685 := by
  unfold tailWord_1468871
  simp only [CollatzResearch.WordTrace]
  refine ⟨53574126661538705039670467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35716084441025803359780311 53574126661538705039670467)
  ·
    refine ⟨80361189992308057559505701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53574126661538705039670467 80361189992308057559505701)
    ·
      refine ⟨15067723123557760792407319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80361189992308057559505701 15067723123557760792407319)
      ·
        refine ⟨22601584685336641188610979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15067723123557760792407319 22601584685336641188610979)
        ·
          refine ⟨33902377028004961782916469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22601584685336641188610979 33902377028004961782916469)
          ·
            refine ⟨3178347846375465167148419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33902377028004961782916469 3178347846375465167148419)
            ·
              refine ⟨4767521769563197750722629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178347846375465167148419 4767521769563197750722629)
              ·
                refine ⟨893910331793099578260493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4767521769563197750722629 893910331793099578260493)
                ·
                  refine ⟨335216374422412341847685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893910331793099578260493 335216374422412341847685)
                  ·
                    rfl

theorem cell21_1468871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 3].length) (baseStart_1468871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468871 prefixEnd_1468871 := by exact prefixLift 1468871
  have htrace : WordTrace (prefixWord ++ tailWord_1468871) baseStart_1468871 baseEnd_1468871 := by
    simpa [prefixWord, tailWord_1468871, baseEnd_1468871] using wordTrace_append hprefix tailTrace_1468871
  have hstable : (prefixWord ++ tailWord_1468871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468871).length < 2 ^ (prefixWord ++ tailWord_1468871).sum := by decide
  have hdescent : baseEnd_1468871 < baseStart_1468871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468885 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 4]
def baseStart_1468885 : Nat := 118140960795 + 1468885 * 2 ^ 59
def prefixEnd_1468885 : Nat := 4983230072969 + 3 ^ 40 * 1468885 * 2
def baseEnd_1468885 : Nat := 335219569413151428614323

theorem tailTrace_1468885 : CollatzResearch.WordTrace tailWord_1468885 prefixEnd_1468885 335219569413151428614323 := by
  unfold tailWord_1468885
  simp only [CollatzResearch.WordTrace]
  refine ⟨53574637283487985430680109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35716424855658656953786739 53574637283487985430680109)
  ·
    refine ⟨20090488981307994536505041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53574637283487985430680109 20090488981307994536505041)
    ·
      refine ⟨15067866735980995902378781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20090488981307994536505041 15067866735980995902378781)
      ·
        refine ⟨5650450025992873463392043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15067866735980995902378781 5650450025992873463392043)
        ·
          refine ⟨8475675038989310195088065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5650450025992873463392043 8475675038989310195088065)
          ·
            refine ⟨6356756279241982646316049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8475675038989310195088065 6356756279241982646316049)
            ·
              refine ⟨4767567209431486984737037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6356756279241982646316049 4767567209431486984737037)
              ·
                refine ⟨1787837703536807619276389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4767567209431486984737037 1787837703536807619276389)
                ·
                  refine ⟨335219569413151428614323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1787837703536807619276389 335219569413151428614323)
                  ·
                    rfl

theorem cell21_1468885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_1468885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468885 prefixEnd_1468885 := by exact prefixLift 1468885
  have htrace : WordTrace (prefixWord ++ tailWord_1468885) baseStart_1468885 baseEnd_1468885 := by
    simpa [prefixWord, tailWord_1468885, baseEnd_1468885] using wordTrace_append hprefix tailTrace_1468885
  have hstable : (prefixWord ++ tailWord_1468885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468885).length < 2 ^ (prefixWord ++ tailWord_1468885).sum := by decide
  have hdescent : baseEnd_1468885 < baseStart_1468885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468913 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 7]
def baseStart_1468913 : Nat := 118140960795 + 1468913 * 2 ^ 59
def prefixEnd_1468913 : Nat := 4983230072969 + 3 ^ 40 * 1468913 * 2
def baseEnd_1468913 : Nat := 335225959394629602147599

theorem tailTrace_1468913 : CollatzResearch.WordTrace tailWord_1468913 prefixEnd_1468913 335225959394629602147599 := by
  unfold tailWord_1468913
  simp only [CollatzResearch.WordTrace]
  refine ⟨53575658527386546212699393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35717105684924364141799595 53575658527386546212699393)
  ·
    refine ⟨40181743895539909659524545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53575658527386546212699393 40181743895539909659524545)
    ·
      refine ⟨30136307921654932244643409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40181743895539909659524545 30136307921654932244643409)
      ·
        refine ⟨22602230941241199183482557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30136307921654932244643409 22602230941241199183482557)
        ·
          refine ⟨8475836602965449693805959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22602230941241199183482557 8475836602965449693805959)
          ·
            refine ⟨12713754904448174540708939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8475836602965449693805959 12713754904448174540708939)
            ·
              refine ⟨19070632356672261811063409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12713754904448174540708939 19070632356672261811063409)
              ·
                refine ⟨14302974267504196358297557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19070632356672261811063409 14302974267504196358297557)
                ·
                  refine ⟨335225959394629602147599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14302974267504196358297557 335225959394629602147599)
                  ·
                    rfl

theorem cell21_1468913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_1468913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1468913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1468913 prefixEnd_1468913 := by exact prefixLift 1468913
  have htrace : WordTrace (prefixWord ++ tailWord_1468913) baseStart_1468913 baseEnd_1468913 := by
    simpa [prefixWord, tailWord_1468913, baseEnd_1468913] using wordTrace_append hprefix tailTrace_1468913
  have hstable : (prefixWord ++ tailWord_1468913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468913).length < 2 ^ (prefixWord ++ tailWord_1468913).sum := by decide
  have hdescent : baseEnd_1468913 < baseStart_1468913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469037 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1469037 : Nat := 118140960795 + 1469037 * 2 ^ 59
def prefixEnd_1469037 : Nat := 4983230072969 + 3 ^ 40 * 1469037 * 2
def baseEnd_1469037 : Nat := 335254257884032942080679

theorem tailTrace_1469037 : CollatzResearch.WordTrace tailWord_1469037 prefixEnd_1469037 335254257884032942080679 := by
  unfold tailWord_1469037
  simp only [CollatzResearch.WordTrace]
  refine ⟨53580181178937315390213365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35720120785958210260142243 53580181178937315390213365)
  ·
    refine ⟨5023141985525373317832503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53580181178937315390213365 5023141985525373317832503)
    ·
      refine ⟨7534712978288059976748755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5023141985525373317832503 7534712978288059976748755)
      ·
        refine ⟨11302069467432089965123133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7534712978288059976748755 11302069467432089965123133)
        ·
          refine ⟨4238276050287033736921175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11302069467432089965123133 4238276050287033736921175)
          ·
            refine ⟨6357414075430550605381763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4238276050287033736921175 6357414075430550605381763)
            ·
              refine ⟨9536121113145825908072645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6357414075430550605381763 9536121113145825908072645)
              ·
                refine ⟨1788022708714842357763621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9536121113145825908072645 1788022708714842357763621)
                ·
                  refine ⟨335254257884032942080679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1788022708714842357763621 335254257884032942080679)
                  ·
                    rfl

theorem cell21_1469037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1469037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469037 prefixEnd_1469037 := by exact prefixLift 1469037
  have htrace : WordTrace (prefixWord ++ tailWord_1469037) baseStart_1469037 baseEnd_1469037 := by
    simpa [prefixWord, tailWord_1469037, baseEnd_1469037] using wordTrace_append hprefix tailTrace_1469037
  have hstable : (prefixWord ++ tailWord_1469037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469037).length < 2 ^ (prefixWord ++ tailWord_1469037).sum := by decide
  have hdescent : baseEnd_1469037 < baseStart_1469037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469217 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 5]
def baseStart_1469217 : Nat := 118140960795 + 1469217 * 2 ^ 59
def prefixEnd_1469217 : Nat := 4983230072969 + 3 ^ 40 * 1469217 * 2
def baseEnd_1469217 : Nat := 335295336336392629080311

theorem tailTrace_1469217 : CollatzResearch.WordTrace tailWord_1469217 prefixEnd_1469217 335295336336392629080311 := by
  unfold tailWord_1469217
  simp only [CollatzResearch.WordTrace]
  refine ⟨53586746318285206131765905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35724497545523470754510603 53586746318285206131765905)
  ·
    refine ⟨40190059738713904598824429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53586746318285206131765905 40190059738713904598824429)
    ·
      refine ⟨15071272402017714224559161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40190059738713904598824429 15071272402017714224559161)
      ·
        refine ⟨11303454301513285668419371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15071272402017714224559161 11303454301513285668419371)
        ·
          refine ⟨16955181452269928502629057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11303454301513285668419371 16955181452269928502629057)
          ·
            refine ⟨12716386089202446376971793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16955181452269928502629057 12716386089202446376971793)
            ·
              refine ⟨9537289566901834782728845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12716386089202446376971793 9537289566901834782728845)
              ·
                refine ⟨3576483587588188043523317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9537289566901834782728845 3576483587588188043523317)
                ·
                  refine ⟨335295336336392629080311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3576483587588188043523317 335295336336392629080311)
                  ·
                    rfl

theorem cell21_1469217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_1469217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469217 prefixEnd_1469217 := by exact prefixLift 1469217
  have htrace : WordTrace (prefixWord ++ tailWord_1469217) baseStart_1469217 baseEnd_1469217 := by
    simpa [prefixWord, tailWord_1469217, baseEnd_1469217] using wordTrace_append hprefix tailTrace_1469217
  have hstable : (prefixWord ++ tailWord_1469217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469217).length < 2 ^ (prefixWord ++ tailWord_1469217).sum := by decide
  have hdescent : baseEnd_1469217 < baseStart_1469217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469220 : List Nat := [2, 3, 1, 3, 3, 2, 1, 6]
def baseStart_1469220 : Nat := 118140960795 + 1469220 * 2 ^ 59
def prefixEnd_1469220 : Nat := 4983230072969 + 3 ^ 40 * 1469220 * 2
def baseEnd_1469220 : Nat := 111765340325755096843435

theorem tailTrace_1469220 : CollatzResearch.WordTrace tailWord_1469220 prefixEnd_1469220 111765340325755096843435 := by
  unfold tailWord_1469220
  simp only [CollatzResearch.WordTrace]
  refine ⟨26793427868637168822062557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35724570491516225096083409 26793427868637168822062557)
  ·
    refine ⟨10047535450738938308273459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26793427868637168822062557 10047535450738938308273459)
    ·
      refine ⟨15071303176108407462410189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10047535450738938308273459 15071303176108407462410189)
      ·
        refine ⟨5651738691040652798403821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15071303176108407462410189 5651738691040652798403821)
        ·
          refine ⟨2119402009140244799401433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5651738691040652798403821 2119402009140244799401433)
          ·
            refine ⟨1589551506855183599551075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2119402009140244799401433 1589551506855183599551075)
            ·
              refine ⟨2384327260282775399326613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589551506855183599551075 2384327260282775399326613)
              ·
                refine ⟨111765340325755096843435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2384327260282775399326613 111765340325755096843435)
                ·
                  rfl

theorem cell21_1469220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_1469220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469220 prefixEnd_1469220 := by exact prefixLift 1469220
  have htrace : WordTrace (prefixWord ++ tailWord_1469220) baseStart_1469220 baseEnd_1469220 := by
    simpa [prefixWord, tailWord_1469220, baseEnd_1469220] using wordTrace_append hprefix tailTrace_1469220
  have hstable : (prefixWord ++ tailWord_1469220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469220).length < 2 ^ (prefixWord ++ tailWord_1469220).sum := by decide
  have hdescent : baseEnd_1469220 < baseStart_1469220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469307 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 6]
def baseStart_1469307 : Nat := 118140960795 + 1469307 * 2 ^ 59
def prefixEnd_1469307 : Nat := 4983230072969 + 3 ^ 40 * 1469307 * 2
def baseEnd_1469307 : Nat := 335315875562572472580127

theorem tailTrace_1469307 : CollatzResearch.WordTrace tailWord_1469307 prefixEnd_1469307 335315875562572472580127 := by
  unfold tailWord_1469307
  simp only [CollatzResearch.WordTrace]
  refine ⟨53590028887959151502542175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35726685925306101001694783 53590028887959151502542175)
  ·
    refine ⟨80385043331938727253813263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53590028887959151502542175 80385043331938727253813263)
    ·
      refine ⟨120577564997908090880719895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80385043331938727253813263 120577564997908090880719895)
      ·
        refine ⟨180866347496862136321079843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120577564997908090880719895 180866347496862136321079843)
        ·
          refine ⟨271299521245293204481619765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180866347496862136321079843 271299521245293204481619765)
          ·
            refine ⟨25434330116746237920151853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 271299521245293204481619765 25434330116746237920151853)
            ·
              refine ⟨9537873793779839220056945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25434330116746237920151853 9537873793779839220056945)
              ·
                refine ⟨7153405345334879415042709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9537873793779839220056945 7153405345334879415042709)
                ·
                  refine ⟨335315875562572472580127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7153405345334879415042709 335315875562572472580127)
                  ·
                    rfl

theorem cell21_1469307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_1469307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469307 prefixEnd_1469307 := by exact prefixLift 1469307
  have htrace : WordTrace (prefixWord ++ tailWord_1469307) baseStart_1469307 baseEnd_1469307 := by
    simpa [prefixWord, tailWord_1469307, baseEnd_1469307] using wordTrace_append hprefix tailTrace_1469307
  have hstable : (prefixWord ++ tailWord_1469307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469307).length < 2 ^ (prefixWord ++ tailWord_1469307).sum := by decide
  have hdescent : baseEnd_1469307 < baseStart_1469307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469383 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 6]
def baseStart_1469383 : Nat := 118140960795 + 1469383 * 2 ^ 59
def prefixEnd_1469383 : Nat := 4983230072969 + 3 ^ 40 * 1469383 * 2
def baseEnd_1469383 : Nat := 335333219798013229313305

theorem tailTrace_1469383 : CollatzResearch.WordTrace tailWord_1469383 prefixEnd_1469383 335333219798013229313305 := by
  unfold tailWord_1469383
  simp only [CollatzResearch.WordTrace]
  refine ⟨53592800835683816482308803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35728533890455877654872535 53592800835683816482308803)
  ·
    refine ⟨80389201253525724723463205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53592800835683816482308803 80389201253525724723463205)
    ·
      refine ⟨15072975235036073385649351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80389201253525724723463205 15072975235036073385649351)
      ·
        refine ⟨22609462852554110078474027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15072975235036073385649351 22609462852554110078474027)
        ·
          refine ⟨33914194278831165117711041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22609462852554110078474027 33914194278831165117711041)
          ·
            refine ⟨25435645709123373838283281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33914194278831165117711041 25435645709123373838283281)
            ·
              refine ⟨19076734281842530378712461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25435645709123373838283281 19076734281842530378712461)
              ·
                refine ⟨7153775355690948892017173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19076734281842530378712461 7153775355690948892017173)
                ·
                  refine ⟨335333219798013229313305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7153775355690948892017173 335333219798013229313305)
                  ·
                    rfl

theorem cell21_1469383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_1469383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469383 prefixEnd_1469383 := by exact prefixLift 1469383
  have htrace : WordTrace (prefixWord ++ tailWord_1469383) baseStart_1469383 baseEnd_1469383 := by
    simpa [prefixWord, tailWord_1469383, baseEnd_1469383] using wordTrace_append hprefix tailTrace_1469383
  have hstable : (prefixWord ++ tailWord_1469383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469383).length < 2 ^ (prefixWord ++ tailWord_1469383).sum := by decide
  have hdescent : baseEnd_1469383 < baseStart_1469383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469400 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 4]
def baseStart_1469400 : Nat := 118140960795 + 1469400 * 2 ^ 59
def prefixEnd_1469400 : Nat := 4983230072969 + 3 ^ 40 * 1469400 * 2
def baseEnd_1469400 : Nat := 335337099429624977529937

theorem tailTrace_1469400 : CollatzResearch.WordTrace tailWord_1469400 prefixEnd_1469400 335337099429624977529937 := by
  unfold tailWord_1469400
  simp only [CollatzResearch.WordTrace]
  refine ⟨26796710438311114192838827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35728947251081485590451769 26796710438311114192838827)
  ·
    refine ⟨40195065657466671289258241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26796710438311114192838827 40195065657466671289258241)
    ·
      refine ⟨30146299243100003466943681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40195065657466671289258241 30146299243100003466943681)
      ·
        refine ⟨22609724432325002600207761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30146299243100003466943681 22609724432325002600207761)
        ·
          refine ⟨16957293324243751950155821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22609724432325002600207761 16957293324243751950155821)
          ·
            refine ⟨6358984996591406981308433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16957293324243751950155821 6358984996591406981308433)
            ·
              refine ⟨4769238747443555235981325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6358984996591406981308433 4769238747443555235981325)
              ·
                refine ⟨1788464530291333213492997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4769238747443555235981325 1788464530291333213492997)
                ·
                  refine ⟨335337099429624977529937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1788464530291333213492997 335337099429624977529937)
                  ·
                    rfl

theorem cell21_1469400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_1469400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469400 prefixEnd_1469400 := by exact prefixLift 1469400
  have htrace : WordTrace (prefixWord ++ tailWord_1469400) baseStart_1469400 baseEnd_1469400 := by
    simpa [prefixWord, tailWord_1469400, baseEnd_1469400] using wordTrace_append hprefix tailTrace_1469400
  have hstable : (prefixWord ++ tailWord_1469400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469400).length < 2 ^ (prefixWord ++ tailWord_1469400).sum := by decide
  have hdescent : baseEnd_1469400 < baseStart_1469400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469445 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 5]
def baseStart_1469445 : Nat := 118140960795 + 1469445 * 2 ^ 59
def prefixEnd_1469445 : Nat := 4983230072969 + 3 ^ 40 * 1469445 * 2
def baseEnd_1469445 : Nat := 335347369042714899279845

theorem tailTrace_1469445 : CollatzResearch.WordTrace tailWord_1469445 prefixEnd_1469445 335347369042714899279845 := by
  unfold tailWord_1469445
  simp only [CollatzResearch.WordTrace]
  refine ⟨53595062161459201071065789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35730041440972800714043859 53595062161459201071065789)
  ·
    refine ⟨20098148310547200401649671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53595062161459201071065789 20098148310547200401649671)
    ·
      refine ⟨30147222465820800602474507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20098148310547200401649671 30147222465820800602474507)
      ·
        refine ⟨45220833698731200903711761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30147222465820800602474507 45220833698731200903711761)
        ·
          refine ⟨33915625274048400677783821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45220833698731200903711761 33915625274048400677783821)
          ·
            refine ⟨12718359477768150254168933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33915625274048400677783821 12718359477768150254168933)
            ·
              refine ⟨2384692402081528172656675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12718359477768150254168933 2384692402081528172656675)
              ·
                refine ⟨3577038603122292258985013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384692402081528172656675 3577038603122292258985013)
                ·
                  refine ⟨335347369042714899279845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3577038603122292258985013 335347369042714899279845)
                  ·
                    rfl

theorem cell21_1469445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_1469445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469445 prefixEnd_1469445 := by exact prefixLift 1469445
  have htrace : WordTrace (prefixWord ++ tailWord_1469445) baseStart_1469445 baseEnd_1469445 := by
    simpa [prefixWord, tailWord_1469445, baseEnd_1469445] using wordTrace_append hprefix tailTrace_1469445
  have hstable : (prefixWord ++ tailWord_1469445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469445).length < 2 ^ (prefixWord ++ tailWord_1469445).sum := by decide
  have hdescent : baseEnd_1469445 < baseStart_1469445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469476 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 6]
def baseStart_1469476 : Nat := 118140960795 + 1469476 * 2 ^ 59
def prefixEnd_1469476 : Nat := 4983230072969 + 3 ^ 40 * 1469476 * 2
def baseEnd_1469476 : Nat := 335354443665065734263115

theorem tailTrace_1469476 : CollatzResearch.WordTrace tailWord_1469476 prefixEnd_1469476 335354443665065734263115 := by
  unfold tailWord_1469476
  simp only [CollatzResearch.WordTrace]
  refine ⟨26798096412173446682722141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35730795216231262243629521 26798096412173446682722141)
  ·
    refine ⟨10049286154565042506020803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26798096412173446682722141 10049286154565042506020803)
    ·
      refine ⟨15073929231847563759031205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10049286154565042506020803 15073929231847563759031205)
      ·
        refine ⟨2826361730971418204818351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15073929231847563759031205 2826361730971418204818351)
        ·
          refine ⟨4239542596457127307227527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826361730971418204818351 4239542596457127307227527)
          ·
            refine ⟨6359313894685690960841291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239542596457127307227527 6359313894685690960841291)
            ·
              refine ⟨9538970842028536441261937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6359313894685690960841291 9538970842028536441261937)
              ·
                refine ⟨7154228131521402330946453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9538970842028536441261937 7154228131521402330946453)
                ·
                  refine ⟨335354443665065734263115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7154228131521402330946453 335354443665065734263115)
                  ·
                    rfl

theorem cell21_1469476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_1469476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469476 prefixEnd_1469476 := by exact prefixLift 1469476
  have htrace : WordTrace (prefixWord ++ tailWord_1469476) baseStart_1469476 baseEnd_1469476 := by
    simpa [prefixWord, tailWord_1469476, baseEnd_1469476] using wordTrace_append hprefix tailTrace_1469476
  have hstable : (prefixWord ++ tailWord_1469476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469476).length < 2 ^ (prefixWord ++ tailWord_1469476).sum := by decide
  have hdescent : baseEnd_1469476 < baseStart_1469476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469510 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1469510 : Nat := 118140960795 + 1469510 * 2 ^ 59
def prefixEnd_1469510 : Nat := 4983230072969 + 3 ^ 40 * 1469510 * 2
def baseEnd_1469510 : Nat := 335362202928289230696379

theorem tailTrace_1469510 : CollatzResearch.WordTrace tailWord_1469510 prefixEnd_1469510 335362202928289230696379 := by
  unfold tailWord_1469510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1674919778319491161630687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35731621937482478114787989 1674919778319491161630687)
  ·
    refine ⟨2512379667479236742446031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1674919778319491161630687 2512379667479236742446031)
    ·
      refine ⟨3768569501218855113669047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2512379667479236742446031 3768569501218855113669047)
      ·
        refine ⟨5652854251828282670503571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3768569501218855113669047 5652854251828282670503571)
        ·
          refine ⟨8479281377742424005755357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5652854251828282670503571 8479281377742424005755357)
          ·
            refine ⟨3179730516653409002158259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8479281377742424005755357 3179730516653409002158259)
            ·
              refine ⟨4769595774980113503237389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179730516653409002158259 4769595774980113503237389)
              ·
                refine ⟨1788598415617542563714021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4769595774980113503237389 1788598415617542563714021)
                ·
                  refine ⟨335362202928289230696379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1788598415617542563714021 335362202928289230696379)
                  ·
                    rfl

theorem cell21_1469510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1469510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469510 prefixEnd_1469510 := by exact prefixLift 1469510
  have htrace : WordTrace (prefixWord ++ tailWord_1469510) baseStart_1469510 baseEnd_1469510 := by
    simpa [prefixWord, tailWord_1469510, baseEnd_1469510] using wordTrace_append hprefix tailTrace_1469510
  have hstable : (prefixWord ++ tailWord_1469510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469510).length < 2 ^ (prefixWord ++ tailWord_1469510).sum := by decide
  have hdescent : baseEnd_1469510 < baseStart_1469510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469552 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 4]
def baseStart_1469552 : Nat := 118140960795 + 1469552 * 2 ^ 59
def prefixEnd_1469552 : Nat := 4983230072969 + 3 ^ 40 * 1469552 * 2
def baseEnd_1469552 : Nat := 335371787900506490996293

theorem tailTrace_1469552 : CollatzResearch.WordTrace tailWord_1469552 prefixEnd_1469552 335371787900506490996293 := by
  unfold tailWord_1469552
  simp only [CollatzResearch.WordTrace]
  refine ⟨26799482386035779172605455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35732643181381038896807273 26799482386035779172605455)
  ·
    refine ⟨40199223579053668758908183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26799482386035779172605455 40199223579053668758908183)
    ·
      refine ⟨60298835368580503138362275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40199223579053668758908183 60298835368580503138362275)
      ·
        refine ⟨90448253052870754707543413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60298835368580503138362275 90448253052870754707543413)
        ·
          refine ⟨8479523723706633253832195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90448253052870754707543413 8479523723706633253832195)
          ·
            refine ⟨12719285585559949880748293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8479523723706633253832195 12719285585559949880748293)
            ·
              refine ⟨2384866047292490602640305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12719285585559949880748293 2384866047292490602640305)
              ·
                refine ⟨1788649535469367951980229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2384866047292490602640305 1788649535469367951980229)
                ·
                  refine ⟨335371787900506490996293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1788649535469367951980229 335371787900506490996293)
                  ·
                    rfl

theorem cell21_1469552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_1469552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469552 prefixEnd_1469552 := by exact prefixLift 1469552
  have htrace : WordTrace (prefixWord ++ tailWord_1469552) baseStart_1469552 baseEnd_1469552 := by
    simpa [prefixWord, tailWord_1469552, baseEnd_1469552] using wordTrace_append hprefix tailTrace_1469552
  have hstable : (prefixWord ++ tailWord_1469552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469552).length < 2 ^ (prefixWord ++ tailWord_1469552).sum := by decide
  have hdescent : baseEnd_1469552 < baseStart_1469552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469634 : List Nat := [3, 5, 1, 1, 2, 2, 2, 5]
def baseStart_1469634 : Nat := 118140960795 + 1469634 * 2 ^ 59
def prefixEnd_1469634 : Nat := 4983230072969 + 3 ^ 40 * 1469634 * 2
def baseEnd_1469634 : Nat := 111796833805897523543153

theorem tailTrace_1469634 : CollatzResearch.WordTrace tailWord_1469634 prefixEnd_1469634 111796833805897523543153 := by
  unfold tailWord_1469634
  simp only [CollatzResearch.WordTrace]
  refine ⟨13400488889443621587423989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35734637038516324233130637 13400488889443621587423989)
  ·
    refine ⟨1256295833385339523820999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13400488889443621587423989 1256295833385339523820999)
    ·
      refine ⟨1884443750078009285731499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256295833385339523820999 1884443750078009285731499)
      ·
        refine ⟨2826665625117013928597249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884443750078009285731499 2826665625117013928597249)
        ·
          refine ⟨2119999218837760446447937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2826665625117013928597249 2119999218837760446447937)
          ·
            refine ⟨1589999414128320334835953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2119999218837760446447937 1589999414128320334835953)
            ·
              refine ⟨1192499560596240251126965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1589999414128320334835953 1192499560596240251126965)
              ·
                refine ⟨111796833805897523543153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1192499560596240251126965 111796833805897523543153)
                ·
                  rfl

theorem cell21_1469634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_1469634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469634 prefixEnd_1469634 := by exact prefixLift 1469634
  have htrace : WordTrace (prefixWord ++ tailWord_1469634) baseStart_1469634 baseEnd_1469634 := by
    simpa [prefixWord, tailWord_1469634, baseEnd_1469634] using wordTrace_append hprefix tailTrace_1469634
  have hstable : (prefixWord ++ tailWord_1469634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469634).length < 2 ^ (prefixWord ++ tailWord_1469634).sum := by decide
  have hdescent : baseEnd_1469634 < baseStart_1469634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469642 : List Nat := [3, 1, 2, 1, 3, 3, 1, 7]
def baseStart_1469642 : Nat := 118140960795 + 1469642 * 2 ^ 59
def prefixEnd_1469642 : Nat := 4983230072969 + 3 ^ 40 * 1469642 * 2
def baseEnd_1469642 : Nat := 111797442375562111498703

theorem tailTrace_1469642 : CollatzResearch.WordTrace tailWord_1469642 prefixEnd_1469642 111797442375562111498703 := by
  unfold tailWord_1469642
  simp only [CollatzResearch.WordTrace]
  refine ⟨13400561835436375928996795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35734831561163669143991453 13400561835436375928996795)
  ·
    refine ⟨20100842753154563893495193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13400561835436375928996795 20100842753154563893495193)
    ·
      refine ⟨15075632064865922920121395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20100842753154563893495193 15075632064865922920121395)
      ·
        refine ⟨22613448097298884380182093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15075632064865922920121395 22613448097298884380182093)
        ·
          refine ⟨8480043036487081642568285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22613448097298884380182093 8480043036487081642568285)
          ·
            refine ⟨3180016138682655615963107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8480043036487081642568285 3180016138682655615963107)
            ·
              refine ⟨4770024208023983423944661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180016138682655615963107 4770024208023983423944661)
              ·
                refine ⟨111797442375562111498703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4770024208023983423944661 111797442375562111498703)
                ·
                  rfl

theorem cell21_1469642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_1469642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469642 prefixEnd_1469642 := by exact prefixLift 1469642
  have htrace : WordTrace (prefixWord ++ tailWord_1469642) baseStart_1469642 baseEnd_1469642 := by
    simpa [prefixWord, tailWord_1469642, baseEnd_1469642] using wordTrace_append hprefix tailTrace_1469642
  have hstable : (prefixWord ++ tailWord_1469642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469642).length < 2 ^ (prefixWord ++ tailWord_1469642).sum := by decide
  have hdescent : baseEnd_1469642 < baseStart_1469642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469687 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 4]
def baseStart_1469687 : Nat := 118140960795 + 1469687 * 2 ^ 59
def prefixEnd_1469687 : Nat := 4983230072969 + 3 ^ 40 * 1469687 * 2
def baseEnd_1469687 : Nat := 335402596739776256246017

theorem tailTrace_1469687 : CollatzResearch.WordTrace tailWord_1469687 prefixEnd_1469687 335402596739776256246017 := by
  unfold tailWord_1469687
  simp only [CollatzResearch.WordTrace]
  refine ⟨53603888626582476401375315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35735925751054984267583543 53603888626582476401375315)
  ·
    refine ⟨80405832939873714602062973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53603888626582476401375315 80405832939873714602062973)
    ·
      refine ⟨30152187352452642975773615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80405832939873714602062973 30152187352452642975773615)
      ·
        refine ⟨45228281028678964463660423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30152187352452642975773615 45228281028678964463660423)
        ·
          refine ⟨67842421543018446695490635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45228281028678964463660423 67842421543018446695490635)
          ·
            refine ⟨101763632314527670043235953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67842421543018446695490635 101763632314527670043235953)
            ·
              refine ⟨76322724235895752532426965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101763632314527670043235953 76322724235895752532426965)
              ·
                refine ⟨1788813849278806699978757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76322724235895752532426965 1788813849278806699978757)
                ·
                  refine ⟨335402596739776256246017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1788813849278806699978757 335402596739776256246017)
                  ·
                    rfl

theorem cell21_1469687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 4].length) (baseStart_1469687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469687 prefixEnd_1469687 := by exact prefixLift 1469687
  have htrace : WordTrace (prefixWord ++ tailWord_1469687) baseStart_1469687 baseEnd_1469687 := by
    simpa [prefixWord, tailWord_1469687, baseEnd_1469687] using wordTrace_append hprefix tailTrace_1469687
  have hstable : (prefixWord ++ tailWord_1469687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469687).length < 2 ^ (prefixWord ++ tailWord_1469687).sum := by decide
  have hdescent : baseEnd_1469687 < baseStart_1469687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469701 : List Nat := [1, 3, 1, 1, 2, 1, 3, 9]
def baseStart_1469701 : Nat := 118140960795 + 1469701 * 2 ^ 59
def prefixEnd_1469701 : Nat := 4983230072969 + 3 ^ 40 * 1469701 * 2
def baseEnd_1469701 : Nat := 111801930576838447670885

theorem tailTrace_1469701 : CollatzResearch.WordTrace tailWord_1469701 prefixEnd_1469701 111801930576838447670885 := by
  unfold tailWord_1469701
  simp only [CollatzResearch.WordTrace]
  refine ⟨53604399248531756792384957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35736266165687837861589971 53604399248531756792384957)
  ·
    refine ⟨20101649718199408797144359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53604399248531756792384957 20101649718199408797144359)
    ·
      refine ⟨30152474577299113195716539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20101649718199408797144359 30152474577299113195716539)
      ·
        refine ⟨45228711865948669793574809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30152474577299113195716539 45228711865948669793574809)
        ·
          refine ⟨33921533899461502345181107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45228711865948669793574809 33921533899461502345181107)
          ·
            refine ⟨50882300849192253517771661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33921533899461502345181107 50882300849192253517771661)
            ·
              refine ⟨19080862818447095069164373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50882300849192253517771661 19080862818447095069164373)
              ·
                refine ⟨111801930576838447670885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19080862818447095069164373 111801930576838447670885)
                ·
                  rfl

theorem cell21_1469701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 9].length) (baseStart_1469701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469701 prefixEnd_1469701 := by exact prefixLift 1469701
  have htrace : WordTrace (prefixWord ++ tailWord_1469701) baseStart_1469701 baseEnd_1469701 := by
    simpa [prefixWord, tailWord_1469701, baseEnd_1469701] using wordTrace_append hprefix tailTrace_1469701
  have hstable : (prefixWord ++ tailWord_1469701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469701).length < 2 ^ (prefixWord ++ tailWord_1469701).sum := by decide
  have hdescent : baseEnd_1469701 < baseStart_1469701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469749 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 5]
def baseStart_1469749 : Nat := 118140960795 + 1469749 * 2 ^ 59
def prefixEnd_1469749 : Nat := 4983230072969 + 3 ^ 40 * 1469749 * 2
def baseEnd_1469749 : Nat := 335416745984477926212557

theorem tailTrace_1469749 : CollatzResearch.WordTrace tailWord_1469749 prefixEnd_1469749 335416745984477926212557 := by
  unfold tailWord_1469749
  simp only [CollatzResearch.WordTrace]
  refine ⟨53606149952357860990132301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35737433301571907326754867 53606149952357860990132301)
  ·
    refine ⟨20102306232134197871299613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53606149952357860990132301 20102306232134197871299613)
    ·
      refine ⟨7538364837050324201737355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20102306232134197871299613 7538364837050324201737355)
      ·
        refine ⟨11307547255575486302606033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7538364837050324201737355 11307547255575486302606033)
        ·
          refine ⟨8480660441681614726954525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11307547255575486302606033 8480660441681614726954525)
          ·
            refine ⟨3180247665630605522607947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8480660441681614726954525 3180247665630605522607947)
            ·
              refine ⟨4770371498445908283911921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180247665630605522607947 4770371498445908283911921)
              ·
                refine ⟨3577778623834431212933941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4770371498445908283911921 3577778623834431212933941)
                ·
                  refine ⟨335416745984477926212557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3577778623834431212933941 335416745984477926212557)
                  ·
                    rfl

theorem cell21_1469749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_1469749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469749 prefixEnd_1469749 := by exact prefixLift 1469749
  have htrace : WordTrace (prefixWord ++ tailWord_1469749) baseStart_1469749 baseEnd_1469749 := by
    simpa [prefixWord, tailWord_1469749, baseEnd_1469749] using wordTrace_append hprefix tailTrace_1469749
  have hstable : (prefixWord ++ tailWord_1469749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469749).length < 2 ^ (prefixWord ++ tailWord_1469749).sum := by decide
  have hdescent : baseEnd_1469749 < baseStart_1469749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469777 : List Nat := [1, 2, 2, 1, 4, 1, 10]
def baseStart_1469777 : Nat := 118140960795 + 1469777 * 2 ^ 59
def prefixEnd_1469777 : Nat := 4983230072969 + 3 ^ 40 * 1469777 * 2
def baseEnd_1469777 : Nat := 37269237329550677749537

theorem tailTrace_1469777 : CollatzResearch.WordTrace tailWord_1469777 prefixEnd_1469777 37269237329550677749537 := by
  unfold tailWord_1469777
  simp only [CollatzResearch.WordTrace]
  refine ⟨53607171196256421772151585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35738114130837614514767723 53607171196256421772151585)
  ·
    refine ⟨40205378397192316329113689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53607171196256421772151585 40205378397192316329113689)
    ·
      refine ⟨30154033797894237246835267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40205378397192316329113689 30154033797894237246835267)
      ·
        refine ⟨45231050696841355870252901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30154033797894237246835267 45231050696841355870252901)
        ·
          refine ⟨8480822005657754225672419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45231050696841355870252901 8480822005657754225672419)
          ·
            refine ⟨12721233008486631338508629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8480822005657754225672419 12721233008486631338508629)
            ·
              refine ⟨37269237329550677749537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12721233008486631338508629 37269237329550677749537)
              ·
                rfl

theorem cell21_1469777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 10].length) (baseStart_1469777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469777 prefixEnd_1469777 := by exact prefixLift 1469777
  have htrace : WordTrace (prefixWord ++ tailWord_1469777) baseStart_1469777 baseEnd_1469777 := by
    simpa [prefixWord, tailWord_1469777, baseEnd_1469777] using wordTrace_append hprefix tailTrace_1469777
  have hstable : (prefixWord ++ tailWord_1469777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469777).length < 2 ^ (prefixWord ++ tailWord_1469777).sum := by decide
  have hdescent : baseEnd_1469777 < baseStart_1469777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469794 : List Nat := [3, 3, 2, 1, 1, 1, 2, 8]
def baseStart_1469794 : Nat := 118140960795 + 1469794 * 2 ^ 59
def prefixEnd_1469794 : Nat := 4983230072969 + 3 ^ 40 * 1469794 * 2
def baseEnd_1469794 : Nat := 111809005199189282654155

theorem tailTrace_1469794 : CollatzResearch.WordTrace tailWord_1469794 prefixEnd_1469794 111809005199189282654155 := by
  unfold tailWord_1469794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13401947809298708418880109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35738527491463222450346957 13401947809298708418880109)
  ·
    refine ⟨5025730428487015657080041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13401947809298708418880109 5025730428487015657080041)
    ·
      refine ⟨3769297821365261742810031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5025730428487015657080041 3769297821365261742810031)
      ·
        refine ⟨5653946732047892614215047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3769297821365261742810031 5653946732047892614215047)
        ·
          refine ⟨8480920098071838921322571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5653946732047892614215047 8480920098071838921322571)
          ·
            refine ⟨12721380147107758381983857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8480920098071838921322571 12721380147107758381983857)
            ·
              refine ⟨9541035110330818786487893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12721380147107758381983857 9541035110330818786487893)
              ·
                refine ⟨111809005199189282654155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9541035110330818786487893 111809005199189282654155)
                ·
                  rfl

theorem cell21_1469794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_1469794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469794 prefixEnd_1469794 := by exact prefixLift 1469794
  have htrace : WordTrace (prefixWord ++ tailWord_1469794) baseStart_1469794 baseEnd_1469794 := by
    simpa [prefixWord, tailWord_1469794, baseEnd_1469794] using wordTrace_append hprefix tailTrace_1469794
  have hstable : (prefixWord ++ tailWord_1469794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469794).length < 2 ^ (prefixWord ++ tailWord_1469794).sum := by decide
  have hdescent : baseEnd_1469794 < baseStart_1469794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469808 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_1469808 : Nat := 118140960795 + 1469808 * 2 ^ 59
def prefixEnd_1469808 : Nat := 4983230072969 + 3 ^ 40 * 1469808 * 2
def baseEnd_1469808 : Nat := 335430210588306934729103

theorem tailTrace_1469808 : CollatzResearch.WordTrace tailWord_1469808 prefixEnd_1469808 335430210588306934729103 := by
  unfold tailWord_1469808
  simp only [CollatzResearch.WordTrace]
  refine ⟨26804150929572057033265039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35738867906096076044353385 26804150929572057033265039)
  ·
    refine ⟨40206226394358085549897559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26804150929572057033265039 40206226394358085549897559)
    ·
      refine ⟨60309339591537128324846339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40206226394358085549897559 60309339591537128324846339)
      ·
        refine ⟨90464009387305692487269509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60309339591537128324846339 90464009387305692487269509)
        ·
          refine ⟨16962001760119817341363033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90464009387305692487269509 16962001760119817341363033)
          ·
            refine ⟨12721501320089863006022275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16962001760119817341363033 12721501320089863006022275)
            ·
              refine ⟨19082251980134794509033413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12721501320089863006022275 19082251980134794509033413)
              ·
                refine ⟨3577922246275273970443765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19082251980134794509033413 3577922246275273970443765)
                ·
                  refine ⟨335430210588306934729103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3577922246275273970443765 335430210588306934729103)
                  ·
                    rfl

theorem cell21_1469808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_1469808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469808 prefixEnd_1469808 := by exact prefixLift 1469808
  have htrace : WordTrace (prefixWord ++ tailWord_1469808) baseStart_1469808 baseEnd_1469808 := by
    simpa [prefixWord, tailWord_1469808, baseEnd_1469808] using wordTrace_append hprefix tailTrace_1469808
  have hstable : (prefixWord ++ tailWord_1469808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469808).length < 2 ^ (prefixWord ++ tailWord_1469808).sum := by decide
  have hdescent : baseEnd_1469808 < baseStart_1469808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469960 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_1469960 : Nat := 118140960795 + 1469960 * 2 ^ 59
def prefixEnd_1469960 : Nat := 4983230072969 + 3 ^ 40 * 1469960 * 2
def baseEnd_1469960 : Nat := 335464899059188448195459

theorem tailTrace_1469960 : CollatzResearch.WordTrace tailWord_1469960 prefixEnd_1469960 335464899059188448195459 := by
  unfold tailWord_1469960
  simp only [CollatzResearch.WordTrace]
  refine ⟨26806922877296722013031667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35742563836395629350708889 26806922877296722013031667)
  ·
    refine ⟨40210384315945083019547501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26806922877296722013031667 40210384315945083019547501)
    ·
      refine ⟨15078894118479406132330313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40210384315945083019547501 15078894118479406132330313)
      ·
        refine ⟨11309170588859554599247735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15078894118479406132330313 11309170588859554599247735)
        ·
          refine ⟨16963755883289331898871603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11309170588859554599247735 16963755883289331898871603)
          ·
            refine ⟨25445633824933997848307405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16963755883289331898871603 25445633824933997848307405)
            ·
              refine ⟨9542112684350249193115277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25445633824933997848307405 9542112684350249193115277)
              ·
                refine ⟨3578292256631343447418229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9542112684350249193115277 3578292256631343447418229)
                ·
                  refine ⟨335464899059188448195459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3578292256631343447418229 335464899059188448195459)
                  ·
                    rfl

theorem cell21_1469960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_1469960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1469960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1469960 prefixEnd_1469960 := by exact prefixLift 1469960
  have htrace : WordTrace (prefixWord ++ tailWord_1469960) baseStart_1469960 baseEnd_1469960 := by
    simpa [prefixWord, tailWord_1469960, baseEnd_1469960] using wordTrace_append hprefix tailTrace_1469960
  have hstable : (prefixWord ++ tailWord_1469960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469960).length < 2 ^ (prefixWord ++ tailWord_1469960).sum := by decide
  have hdescent : baseEnd_1469960 < baseStart_1469960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470005 : List Nat := [1, 3, 3, 1, 1, 3, 9]
def baseStart_1470005 : Nat := 118140960795 + 1470005 * 2 ^ 59
def prefixEnd_1470005 : Nat := 4983230072969 + 3 ^ 40 * 1470005 * 2
def baseEnd_1470005 : Nat := 37275018741364263327263

theorem tailTrace_1470005 : CollatzResearch.WordTrace tailWord_1470005 prefixEnd_1470005 37275018741364263327263 := by
  unfold tailWord_1470005
  simp only [CollatzResearch.WordTrace]
  refine ⟨53615487039430416711451469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35743658026286944474300979 53615487039430416711451469)
  ·
    refine ⟨20105807639786406266794301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53615487039430416711451469 20105807639786406266794301)
    ·
      refine ⟨7539677864919902350047863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20105807639786406266794301 7539677864919902350047863)
      ·
        refine ⟨11309516797379853525071795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7539677864919902350047863 11309516797379853525071795)
        ·
          refine ⟨16964275196069780287607693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11309516797379853525071795 16964275196069780287607693)
          ·
            refine ⟨6361603198526167607852885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16964275196069780287607693 6361603198526167607852885)
            ·
              refine ⟨37275018741364263327263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6361603198526167607852885 37275018741364263327263)
              ·
                rfl

theorem cell21_1470005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 9].length) (baseStart_1470005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470005 prefixEnd_1470005 := by exact prefixLift 1470005
  have htrace : WordTrace (prefixWord ++ tailWord_1470005) baseStart_1470005 baseEnd_1470005 := by
    simpa [prefixWord, tailWord_1470005, baseEnd_1470005] using wordTrace_append hprefix tailTrace_1470005
  have hstable : (prefixWord ++ tailWord_1470005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470005).length < 2 ^ (prefixWord ++ tailWord_1470005).sum := by decide
  have hdescent : baseEnd_1470005 < baseStart_1470005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470036 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1470036 : Nat := 118140960795 + 1470036 * 2 ^ 59
def prefixEnd_1470036 : Nat := 4983230072969 + 3 ^ 40 * 1470036 * 2
def baseEnd_1470036 : Nat := 335482243294629204928637

theorem tailTrace_1470036 : CollatzResearch.WordTrace tailWord_1470036 prefixEnd_1470036 335482243294629204928637 := by
  unfold tailWord_1470036
  simp only [CollatzResearch.WordTrace]
  refine ⟨26808308851159054502914981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35744411801545406003886641 26808308851159054502914981)
  ·
    refine ⟨5026557909592322719296559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26808308851159054502914981 5026557909592322719296559)
    ·
      refine ⟨7539836864388484078944839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5026557909592322719296559 7539836864388484078944839)
      ·
        refine ⟨11309755296582726118417259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7539836864388484078944839 11309755296582726118417259)
        ·
          refine ⟨16964632944874089177625889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11309755296582726118417259 16964632944874089177625889)
          ·
            refine ⟨12723474708655566883219417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16964632944874089177625889 12723474708655566883219417)
            ·
              refine ⟨9542606031491675162414563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12723474708655566883219417 9542606031491675162414563)
              ·
                refine ⟨14313909047237512743621845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9542606031491675162414563 14313909047237512743621845)
                ·
                  refine ⟨335482243294629204928637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14313909047237512743621845 335482243294629204928637)
                  ·
                    rfl

theorem cell21_1470036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1470036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470036 prefixEnd_1470036 := by exact prefixLift 1470036
  have htrace : WordTrace (prefixWord ++ tailWord_1470036) baseStart_1470036 baseEnd_1470036 := by
    simpa [prefixWord, tailWord_1470036, baseEnd_1470036] using wordTrace_append hprefix tailTrace_1470036
  have hstable : (prefixWord ++ tailWord_1470036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470036).length < 2 ^ (prefixWord ++ tailWord_1470036).sum := by decide
  have hdescent : baseEnd_1470036 < baseStart_1470036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470188 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 5]
def baseStart_1470188 : Nat := 118140960795 + 1470188 * 2 ^ 59
def prefixEnd_1470188 : Nat := 4983230072969 + 3 ^ 40 * 1470188 * 2
def baseEnd_1470188 : Nat := 335516931765510718394993

theorem tailTrace_1470188 : CollatzResearch.WordTrace tailWord_1470188 prefixEnd_1470188 335516931765510718394993 := by
  unfold tailWord_1470188
  simp only [CollatzResearch.WordTrace]
  refine ⟨26811080798883719482681609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35748107731844959310242145 26811080798883719482681609)
  ·
    refine ⟨20108310599162789612011207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26811080798883719482681609 20108310599162789612011207)
    ·
      refine ⟨30162465898744184418016811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20108310599162789612011207 30162465898744184418016811)
      ·
        refine ⟨45243698848116276627025217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30162465898744184418016811 45243698848116276627025217)
        ·
          refine ⟨33932774136087207470268913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45243698848116276627025217 33932774136087207470268913)
          ·
            refine ⟨25449580602065405602701685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33932774136087207470268913 25449580602065405602701685)
            ·
              refine ⟨2385898181443631775253283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25449580602065405602701685 2385898181443631775253283)
              ·
                refine ⟨3578847272165447662879925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385898181443631775253283 3578847272165447662879925)
                ·
                  refine ⟨335516931765510718394993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3578847272165447662879925 335516931765510718394993)
                  ·
                    rfl

theorem cell21_1470188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_1470188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470188 prefixEnd_1470188 := by exact prefixLift 1470188
  have htrace : WordTrace (prefixWord ++ tailWord_1470188) baseStart_1470188 baseEnd_1470188 := by
    simpa [prefixWord, tailWord_1470188, baseEnd_1470188] using wordTrace_append hprefix tailTrace_1470188
  have hstable : (prefixWord ++ tailWord_1470188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470188).length < 2 ^ (prefixWord ++ tailWord_1470188).sum := by decide
  have hdescent : baseEnd_1470188 < baseStart_1470188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470264 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 5]
def baseStart_1470264 : Nat := 118140960795 + 1470264 * 2 ^ 59
def prefixEnd_1470264 : Nat := 4983230072969 + 3 ^ 40 * 1470264 * 2
def baseEnd_1470264 : Nat := 335534276000951475128171

theorem tailTrace_1470264 : CollatzResearch.WordTrace tailWord_1470264 prefixEnd_1470264 335534276000951475128171 := by
  unfold tailWord_1470264
  simp only [CollatzResearch.WordTrace]
  refine ⟨26812466772746051972564923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35749955696994735963419897 26812466772746051972564923)
  ·
    refine ⟨40218700159119077958847385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26812466772746051972564923 40218700159119077958847385)
    ·
      refine ⟨30164025119339308469135539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40218700159119077958847385 30164025119339308469135539)
      ·
        refine ⟨45246037679008962703703309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30164025119339308469135539 45246037679008962703703309)
        ·
          refine ⟨16967264129628361013888741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45246037679008962703703309 16967264129628361013888741)
          ·
            refine ⟨3181362024305317690104139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16967264129628361013888741 3181362024305317690104139)
            ·
              refine ⟨4772043036457976535156209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181362024305317690104139 4772043036457976535156209)
              ·
                refine ⟨3579032277343482401367157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4772043036457976535156209 3579032277343482401367157)
                ·
                  refine ⟨335534276000951475128171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3579032277343482401367157 335534276000951475128171)
                  ·
                    rfl

theorem cell21_1470264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_1470264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470264 prefixEnd_1470264 := by exact prefixLift 1470264
  have htrace : WordTrace (prefixWord ++ tailWord_1470264) baseStart_1470264 baseEnd_1470264 := by
    simpa [prefixWord, tailWord_1470264, baseEnd_1470264] using wordTrace_append hprefix tailTrace_1470264
  have hstable : (prefixWord ++ tailWord_1470264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470264).length < 2 ^ (prefixWord ++ tailWord_1470264).sum := by decide
  have hdescent : baseEnd_1470264 < baseStart_1470264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470281 : List Nat := [1, 2, 1, 1, 2, 4, 4, 3, 3]
def baseStart_1470281 : Nat := 118140960795 + 1470281 * 2 ^ 59
def prefixEnd_1470281 : Nat := 4983230072969 + 3 ^ 40 * 1470281 * 2
def baseEnd_1470281 : Nat := 335538155632563223344803

theorem tailTrace_1470281 : CollatzResearch.WordTrace tailWord_1470281 prefixEnd_1470281 335538155632563223344803 := by
  unfold tailWord_1470281
  simp only [CollatzResearch.WordTrace]
  refine ⟨53625553586430515848498697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35750369057620343898999131 53625553586430515848498697)
  ·
    refine ⟨40219165189822886886374023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53625553586430515848498697 40219165189822886886374023)
    ·
      refine ⟨60328747784734330329561035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40219165189822886886374023 60328747784734330329561035)
      ·
        refine ⟨90493121677101495494341553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60328747784734330329561035 90493121677101495494341553)
        ·
          refine ⟨67869841257826121620756165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90493121677101495494341553 67869841257826121620756165)
          ·
            refine ⟨12725595235842397803891781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67869841257826121620756165 12725595235842397803891781)
            ·
              refine ⟨2386049106720449588229709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12725595235842397803891781 2386049106720449588229709)
              ·
                refine ⟨894768415020168595586141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2386049106720449588229709 894768415020168595586141)
                ·
                  refine ⟨335538155632563223344803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894768415020168595586141 335538155632563223344803)
                  ·
                    rfl

theorem cell21_1470281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 3].length) (baseStart_1470281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470281 prefixEnd_1470281 := by exact prefixLift 1470281
  have htrace : WordTrace (prefixWord ++ tailWord_1470281) baseStart_1470281 baseEnd_1470281 := by
    simpa [prefixWord, tailWord_1470281, baseEnd_1470281] using wordTrace_append hprefix tailTrace_1470281
  have hstable : (prefixWord ++ tailWord_1470281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470281).length < 2 ^ (prefixWord ++ tailWord_1470281).sum := by decide
  have hdescent : baseEnd_1470281 < baseStart_1470281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470295 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 6]
def baseStart_1470295 : Nat := 118140960795 + 1470295 * 2 ^ 59
def prefixEnd_1470295 : Nat := 4983230072969 + 3 ^ 40 * 1470295 * 2
def baseEnd_1470295 : Nat := 335541350623302310111441

theorem tailTrace_1470295 : CollatzResearch.WordTrace tailWord_1470295 prefixEnd_1470295 335541350623302310111441 := by
  unfold tailWord_1470295
  simp only [CollatzResearch.WordTrace]
  refine ⟨53626064208379796239508339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35750709472253197493005559 53626064208379796239508339)
  ·
    refine ⟨80439096312569694359262509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53626064208379796239508339 80439096312569694359262509)
    ·
      refine ⟨30164661117213635384723441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80439096312569694359262509 30164661117213635384723441)
      ·
        refine ⟨22623495837910226538542581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30164661117213635384723441 22623495837910226538542581)
        ·
          refine ⟨2120952734804083737988367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22623495837910226538542581 2120952734804083737988367)
          ·
            refine ⟨3181429102206125606982551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120952734804083737988367 3181429102206125606982551)
            ·
              refine ⟨4772143653309188410473827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181429102206125606982551 4772143653309188410473827)
              ·
                refine ⟨7158215479963782615710741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4772143653309188410473827 7158215479963782615710741)
                ·
                  refine ⟨335541350623302310111441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7158215479963782615710741 335541350623302310111441)
                  ·
                    rfl

theorem cell21_1470295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 6].length) (baseStart_1470295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470295 prefixEnd_1470295 := by exact prefixLift 1470295
  have htrace : WordTrace (prefixWord ++ tailWord_1470295) baseStart_1470295 baseEnd_1470295 := by
    simpa [prefixWord, tailWord_1470295, baseEnd_1470295] using wordTrace_append hprefix tailTrace_1470295
  have hstable : (prefixWord ++ tailWord_1470295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470295).length < 2 ^ (prefixWord ++ tailWord_1470295).sum := by decide
  have hdescent : baseEnd_1470295 < baseStart_1470295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470312 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 4]
def baseStart_1470312 : Nat := 118140960795 + 1470312 * 2 ^ 59
def prefixEnd_1470312 : Nat := 4983230072969 + 3 ^ 40 * 1470312 * 2
def baseEnd_1470312 : Nat := 335545230254914058328073

theorem tailTrace_1470312 : CollatzResearch.WordTrace tailWord_1470312 prefixEnd_1470312 335545230254914058328073 := by
  unfold tailWord_1470312
  simp only [CollatzResearch.WordTrace]
  refine ⟨26813342124659104071438595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35751122832878805428584793 26813342124659104071438595)
  ·
    refine ⟨40220013186988656107157893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26813342124659104071438595 40220013186988656107157893)
    ·
      refine ⟨7541252472560373020092105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40220013186988656107157893 7541252472560373020092105)
      ·
        refine ⟨5655939354420279765069079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7541252472560373020092105 5655939354420279765069079)
        ·
          refine ⟨8483909031630419647603619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5655939354420279765069079 8483909031630419647603619)
          ·
            refine ⟨12725863547445629471405429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8483909031630419647603619 12725863547445629471405429)
            ·
              refine ⟨1193049707573027762944259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12725863547445629471405429 1193049707573027762944259)
              ·
                refine ⟨1789574561359541644416389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193049707573027762944259 1789574561359541644416389)
                ·
                  refine ⟨335545230254914058328073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1789574561359541644416389 335545230254914058328073)
                  ·
                    rfl

theorem cell21_1470312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_1470312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470312 prefixEnd_1470312 := by exact prefixLift 1470312
  have htrace : WordTrace (prefixWord ++ tailWord_1470312) baseStart_1470312 baseEnd_1470312 := by
    simpa [prefixWord, tailWord_1470312, baseEnd_1470312] using wordTrace_append hprefix tailTrace_1470312
  have hstable : (prefixWord ++ tailWord_1470312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470312).length < 2 ^ (prefixWord ++ tailWord_1470312).sum := by decide
  have hdescent : baseEnd_1470312 < baseStart_1470312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470385 : List Nat := [1, 2, 2, 4, 2, 1, 2, 7]
def baseStart_1470385 : Nat := 118140960795 + 1470385 * 2 ^ 59
def prefixEnd_1470385 : Nat := 4983230072969 + 3 ^ 40 * 1470385 * 2
def baseEnd_1470385 : Nat := 111853963283160717870419

theorem tailTrace_1470385 : CollatzResearch.WordTrace tailWord_1470385 prefixEnd_1470385 111853963283160717870419 := by
  unfold tailWord_1470385
  simp only [CollatzResearch.WordTrace]
  refine ⟨53629346778053741610284609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35752897852035827740189739 53629346778053741610284609)
  ·
    refine ⟨40222010083540306207713457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53629346778053741610284609 40222010083540306207713457)
    ·
      refine ⟨30166507562655229655785093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40222010083540306207713457 30166507562655229655785093)
      ·
        refine ⟨5656220167997855560459705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30166507562655229655785093 5656220167997855560459705)
        ·
          refine ⟨4242165125998391670344779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5656220167997855560459705 4242165125998391670344779)
          ·
            refine ⟨6363247688997587505517169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242165125998391670344779 6363247688997587505517169)
            ·
              refine ⟨4772435766748190629137877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6363247688997587505517169 4772435766748190629137877)
              ·
                refine ⟨111853963283160717870419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4772435766748190629137877 111853963283160717870419)
                ·
                  rfl

theorem cell21_1470385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 7].length) (baseStart_1470385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470385 prefixEnd_1470385 := by exact prefixLift 1470385
  have htrace : WordTrace (prefixWord ++ tailWord_1470385) baseStart_1470385 baseEnd_1470385 := by
    simpa [prefixWord, tailWord_1470385, baseEnd_1470385] using wordTrace_append hprefix tailTrace_1470385
  have hstable : (prefixWord ++ tailWord_1470385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470385).length < 2 ^ (prefixWord ++ tailWord_1470385).sum := by decide
  have hdescent : baseEnd_1470385 < baseStart_1470385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470444 : List Nat := [2, 2, 1, 1, 2, 1, 1, 11]
def baseStart_1470444 : Nat := 118140960795 + 1470444 * 2 ^ 59
def prefixEnd_1470444 : Nat := 4983230072969 + 3 ^ 40 * 1470444 * 2
def baseEnd_1470444 : Nat := 111858451484437054042601

theorem tailTrace_1470444 : CollatzResearch.WordTrace tailWord_1470444 prefixEnd_1470444 111858451484437054042601 := by
  unfold tailWord_1470444
  simp only [CollatzResearch.WordTrace]
  refine ⟨26815749342419997343341193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35754332456559996457788257 26815749342419997343341193)
  ·
    refine ⟨20111812006814998007505895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26815749342419997343341193 20111812006814998007505895)
    ·
      refine ⟨30167718010222497011258843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20111812006814998007505895 30167718010222497011258843)
      ·
        refine ⟨45251577015333745516888265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30167718010222497011258843 45251577015333745516888265)
        ·
          refine ⟨33938682761500309137666199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45251577015333745516888265 33938682761500309137666199)
          ·
            refine ⟨50908024142250463706499299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33938682761500309137666199 50908024142250463706499299)
            ·
              refine ⟨76362036213375695559748949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50908024142250463706499299 76362036213375695559748949)
              ·
                refine ⟨111858451484437054042601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 76362036213375695559748949 111858451484437054042601)
                ·
                  rfl

theorem cell21_1470444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_1470444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470444 prefixEnd_1470444 := by exact prefixLift 1470444
  have htrace : WordTrace (prefixWord ++ tailWord_1470444) baseStart_1470444 baseEnd_1470444 := by
    simpa [prefixWord, tailWord_1470444, baseEnd_1470444] using wordTrace_append hprefix tailTrace_1470444
  have hstable : (prefixWord ++ tailWord_1470444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470444).length < 2 ^ (prefixWord ++ tailWord_1470444).sum := by decide
  have hdescent : baseEnd_1470444 < baseStart_1470444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470492 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_1470492 : Nat := 118140960795 + 1470492 * 2 ^ 59
def prefixEnd_1470492 : Nat := 4983230072969 + 3 ^ 40 * 1470492 * 2
def baseEnd_1470492 : Nat := 335586308707273745327705

theorem tailTrace_1470492 : CollatzResearch.WordTrace tailWord_1470492 prefixEnd_1470492 335586308707273745327705 := by
  unfold tailWord_1470492
  simp only [CollatzResearch.WordTrace]
  refine ⟨26816624694333049442214865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35755499592444065922953153 26816624694333049442214865)
  ·
    refine ⟨20112468520749787081661149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26816624694333049442214865 20112468520749787081661149)
    ·
      refine ⟨7542175695281170155622931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20112468520749787081661149 7542175695281170155622931)
      ·
        refine ⟨11313263542921755233434397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7542175695281170155622931 11313263542921755233434397)
        ·
          refine ⟨4242473828595658212537899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11313263542921755233434397 4242473828595658212537899)
          ·
            refine ⟨6363710742893487318806849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242473828595658212537899 6363710742893487318806849)
            ·
              refine ⟨4772783057170115489105137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6363710742893487318806849 4772783057170115489105137)
              ·
                refine ⟨3579587292877586616828853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4772783057170115489105137 3579587292877586616828853)
                ·
                  refine ⟨335586308707273745327705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3579587292877586616828853 335586308707273745327705)
                  ·
                    rfl

theorem cell21_1470492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_1470492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470492 prefixEnd_1470492 := by exact prefixLift 1470492
  have htrace : WordTrace (prefixWord ++ tailWord_1470492) baseStart_1470492 baseEnd_1470492 := by
    simpa [prefixWord, tailWord_1470492, baseEnd_1470492] using wordTrace_append hprefix tailTrace_1470492
  have hstable : (prefixWord ++ tailWord_1470492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470492).length < 2 ^ (prefixWord ++ tailWord_1470492).sum := by decide
  have hdescent : baseEnd_1470492 < baseStart_1470492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470526 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_1470526 : Nat := 118140960795 + 1470526 * 2 ^ 59
def prefixEnd_1470526 : Nat := 4983230072969 + 3 ^ 40 * 1470526 * 2
def baseEnd_1470526 : Nat := 335594067970497241760969

theorem tailTrace_1470526 : CollatzResearch.WordTrace tailWord_1470526 prefixEnd_1470526 335594067970497241760969 := by
  unfold tailWord_1470526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704311183817865336395929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35756326313695281794111621 6704311183817865336395929)
  ·
    refine ⟨5028233387863399002296947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6704311183817865336395929 5028233387863399002296947)
    ·
      refine ⟨7542350081795098503445421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5028233387863399002296947 7542350081795098503445421)
      ·
        refine ⟨2828381280673161938792033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7542350081795098503445421 2828381280673161938792033)
        ·
          refine ⟨2121285960504871454094025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2828381280673161938792033 2121285960504871454094025)
          ·
            refine ⟨1590964470378653590570519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2121285960504871454094025 1590964470378653590570519)
            ·
              refine ⟨2386446705567980385855779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1590964470378653590570519 2386446705567980385855779)
              ·
                refine ⟨3579670058351970578783669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386446705567980385855779 3579670058351970578783669)
                ·
                  refine ⟨335594067970497241760969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3579670058351970578783669 335594067970497241760969)
                  ·
                    rfl

theorem cell21_1470526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_1470526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470526 prefixEnd_1470526 := by exact prefixLift 1470526
  have htrace : WordTrace (prefixWord ++ tailWord_1470526) baseStart_1470526 baseEnd_1470526 := by
    simpa [prefixWord, tailWord_1470526, baseEnd_1470526] using wordTrace_append hprefix tailTrace_1470526
  have hstable : (prefixWord ++ tailWord_1470526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470526).length < 2 ^ (prefixWord ++ tailWord_1470526).sum := by decide
  have hdescent : baseEnd_1470526 < baseStart_1470526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470551 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 5]
def baseStart_1470551 : Nat := 118140960795 + 1470551 * 2 ^ 59
def prefixEnd_1470551 : Nat := 4983230072969 + 3 ^ 40 * 1470551 * 2
def baseEnd_1470551 : Nat := 335599773311102753844251

theorem tailTrace_1470551 : CollatzResearch.WordTrace tailWord_1470551 prefixEnd_1470551 335599773311102753844251 := by
  unfold tailWord_1470551
  simp only [CollatzResearch.WordTrace]
  refine ⟨53635401295452351960827507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35756934196968234640551671 53635401295452351960827507)
  ·
    refine ⟨80453101943178527941241261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53635401295452351960827507 80453101943178527941241261)
    ·
      refine ⟨30169913228691947977965473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80453101943178527941241261 30169913228691947977965473)
      ·
        refine ⟨22627434921518960983474105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30169913228691947977965473 22627434921518960983474105)
        ·
          refine ⟨16970576191139220737605579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22627434921518960983474105 16970576191139220737605579)
          ·
            refine ⟨25455864286708831106408369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16970576191139220737605579 25455864286708831106408369)
            ·
              refine ⟨19091898215031623329806277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25455864286708831106408369 19091898215031623329806277)
              ·
                refine ⟨3579730915318429374338677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19091898215031623329806277 3579730915318429374338677)
                ·
                  refine ⟨335599773311102753844251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3579730915318429374338677 335599773311102753844251)
                  ·
                    rfl

theorem cell21_1470551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_1470551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470551 prefixEnd_1470551 := by exact prefixLift 1470551
  have htrace : WordTrace (prefixWord ++ tailWord_1470551) baseStart_1470551 baseEnd_1470551 := by
    simpa [prefixWord, tailWord_1470551, baseEnd_1470551] using wordTrace_append hprefix tailTrace_1470551
  have hstable : (prefixWord ++ tailWord_1470551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470551).length < 2 ^ (prefixWord ++ tailWord_1470551).sum := by decide
  have hdescent : baseEnd_1470551 < baseStart_1470551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470585 : List Nat := [1, 2, 1, 3, 4, 2, 1, 4, 3]
def baseStart_1470585 : Nat := 118140960795 + 1470585 * 2 ^ 59
def prefixEnd_1470585 : Nat := 4983230072969 + 3 ^ 40 * 1470585 * 2
def baseEnd_1470585 : Nat := 335607532574326250277515

theorem tailTrace_1470585 : CollatzResearch.WordTrace tailWord_1470585 prefixEnd_1470585 335607532574326250277515 := by
  unfold tailWord_1470585
  simp only [CollatzResearch.WordTrace]
  refine ⟨53636641377329175767565209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35757760918219450511710139 53636641377329175767565209)
  ·
    refine ⟨40227481032996881825673907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53636641377329175767565209 40227481032996881825673907)
    ·
      refine ⟨60341221549495322738510861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40227481032996881825673907 60341221549495322738510861)
      ·
        refine ⟨22627958081060746026941573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60341221549495322738510861 22627958081060746026941573)
        ·
          refine ⟨4242742140198889880051545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22627958081060746026941573 4242742140198889880051545)
          ·
            refine ⟨3182056605149167410038659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4242742140198889880051545 3182056605149167410038659)
            ·
              refine ⟨4773084907723751115057989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182056605149167410038659 4773084907723751115057989)
              ·
                refine ⟨894953420198203334073373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4773084907723751115057989 894953420198203334073373)
                ·
                  refine ⟨335607532574326250277515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894953420198203334073373 335607532574326250277515)
                  ·
                    rfl

theorem cell21_1470585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 3].length) (baseStart_1470585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470585 prefixEnd_1470585 := by exact prefixLift 1470585
  have htrace : WordTrace (prefixWord ++ tailWord_1470585) baseStart_1470585 baseEnd_1470585 := by
    simpa [prefixWord, tailWord_1470585, baseEnd_1470585] using wordTrace_append hprefix tailTrace_1470585
  have hstable : (prefixWord ++ tailWord_1470585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470585).length < 2 ^ (prefixWord ++ tailWord_1470585).sum := by decide
  have hdescent : baseEnd_1470585 < baseStart_1470585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470613 : List Nat := [1, 3, 2, 1, 1, 1, 7, 5]
def baseStart_1470613 : Nat := 118140960795 + 1470613 * 2 ^ 59
def prefixEnd_1470613 : Nat := 4983230072969 + 3 ^ 40 * 1470613 * 2
def baseEnd_1470613 : Nat := 111871307518601474603597

theorem tailTrace_1470613 : CollatzResearch.WordTrace tailWord_1470613 prefixEnd_1470613 111871307518601474603597 := by
  unfold tailWord_1470613
  simp only [CollatzResearch.WordTrace]
  refine ⟨53637662621227736549584493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35758441747485157699722995 53637662621227736549584493)
  ·
    refine ⟨20114123482960401206094185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53637662621227736549584493 20114123482960401206094185)
    ·
      refine ⟨15085592612220300904570639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20114123482960401206094185 15085592612220300904570639)
      ·
        refine ⟨22628388918330451356855959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15085592612220300904570639 22628388918330451356855959)
        ·
          refine ⟨33942583377495677035283939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22628388918330451356855959 33942583377495677035283939)
          ·
            refine ⟨50913875066243515552925909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33942583377495677035283939 50913875066243515552925909)
            ·
              refine ⟨1193293946865082395771701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 50913875066243515552925909 1193293946865082395771701)
              ·
                refine ⟨111871307518601474603597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1193293946865082395771701 111871307518601474603597)
                ·
                  rfl

theorem cell21_1470613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 5].length) (baseStart_1470613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470613 prefixEnd_1470613 := by exact prefixLift 1470613
  have htrace : WordTrace (prefixWord ++ tailWord_1470613) baseStart_1470613 baseEnd_1470613 := by
    simpa [prefixWord, tailWord_1470613, baseEnd_1470613] using wordTrace_append hprefix tailTrace_1470613
  have hstable : (prefixWord ++ tailWord_1470613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470613).length < 2 ^ (prefixWord ++ tailWord_1470613).sum := by decide
  have hdescent : baseEnd_1470613 < baseStart_1470613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470751 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 4]
def baseStart_1470751 : Nat := 118140960795 + 1470751 * 2 ^ 59
def prefixEnd_1470751 : Nat := 4983230072969 + 3 ^ 40 * 1470751 * 2
def baseEnd_1470751 : Nat := 335645416035946850510509

theorem tailTrace_1470751 : CollatzResearch.WordTrace tailWord_1470751 prefixEnd_1470751 335645416035946850510509 := by
  unfold tailWord_1470751
  simp only [CollatzResearch.WordTrace]
  refine ⟨53642695894727786118108107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35761797263151857412072071 53642695894727786118108107)
  ·
    refine ⟨80464043842091679177162161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53642695894727786118108107 80464043842091679177162161)
    ·
      refine ⟨60348032881568759382871621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80464043842091679177162161 60348032881568759382871621)
      ·
        refine ⟨11315256165294142384288429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60348032881568759382871621 11315256165294142384288429)
        ·
          refine ⟨4243221061985303394108161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11315256165294142384288429 4243221061985303394108161)
          ·
            refine ⟨3182415796488977545581121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4243221061985303394108161 3182415796488977545581121)
            ·
              refine ⟨2386811847366733159185841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3182415796488977545581121 2386811847366733159185841)
              ·
                refine ⟨1790108885525049869389381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386811847366733159185841 1790108885525049869389381)
                ·
                  refine ⟨335645416035946850510509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1790108885525049869389381 335645416035946850510509)
                  ·
                    rfl

theorem cell21_1470751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 4].length) (baseStart_1470751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470751 prefixEnd_1470751 := by exact prefixLift 1470751
  have htrace : WordTrace (prefixWord ++ tailWord_1470751) baseStart_1470751 baseEnd_1470751 := by
    simpa [prefixWord, tailWord_1470751, baseEnd_1470751] using wordTrace_append hprefix tailTrace_1470751
  have hstable : (prefixWord ++ tailWord_1470751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470751).length < 2 ^ (prefixWord ++ tailWord_1470751).sum := by decide
  have hdescent : baseEnd_1470751 < baseStart_1470751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470754 : List Nat := [3, 3, 1, 1, 3, 1, 4, 2, 3]
def baseStart_1470754 : Nat := 118140960795 + 1470754 * 2 ^ 59
def prefixEnd_1470754 : Nat := 4983230072969 + 3 ^ 40 * 1470754 * 2
def baseEnd_1470754 : Nat := 335646100676819511960503

theorem tailTrace_1470754 : CollatzResearch.WordTrace tailWord_1470754 prefixEnd_1470754 335646100676819511960503 := by
  unfold tailWord_1470754
  simp only [CollatzResearch.WordTrace]
  refine ⟨13410701328429229407616829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35761870209144611753644877 13410701328429229407616829)
  ·
    refine ⟨5029012998160961027856311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13410701328429229407616829 5029012998160961027856311)
    ·
      refine ⟨7543519497241441541784467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5029012998160961027856311 7543519497241441541784467)
      ·
        refine ⟨11315279245862162312676701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7543519497241441541784467 11315279245862162312676701)
        ·
          refine ⟨4243229717198310867253763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11315279245862162312676701 4243229717198310867253763)
          ·
            refine ⟨6364844575797466300880645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243229717198310867253763 6364844575797466300880645)
            ·
              refine ⟨1193408357962024931415121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6364844575797466300880645 1193408357962024931415121)
              ·
                refine ⟨895056268471518698561341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193408357962024931415121 895056268471518698561341)
                ·
                  refine ⟨335646100676819511960503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895056268471518698561341 335646100676819511960503)
                  ·
                    rfl

theorem cell21_1470754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_1470754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470754 prefixEnd_1470754 := by exact prefixLift 1470754
  have htrace : WordTrace (prefixWord ++ tailWord_1470754) baseStart_1470754 baseEnd_1470754 := by
    simpa [prefixWord, tailWord_1470754, baseEnd_1470754] using wordTrace_append hprefix tailTrace_1470754
  have hstable : (prefixWord ++ tailWord_1470754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470754).length < 2 ^ (prefixWord ++ tailWord_1470754).sum := by decide
  have hdescent : baseEnd_1470754 < baseStart_1470754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470782 : List Nat := [4, 2, 1, 2, 1, 3, 3, 5]
def baseStart_1470782 : Nat := 118140960795 + 1470782 * 2 ^ 59
def prefixEnd_1470782 : Nat := 4983230072969 + 3 ^ 40 * 1470782 * 2
def baseEnd_1470782 : Nat := 111884163552765895164593

theorem tailTrace_1470782 : CollatzResearch.WordTrace tailWord_1470782 prefixEnd_1470782 111884163552765895164593 := by
  unfold tailWord_1470782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6705478319701934801560825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35762551038410318941657733 6705478319701934801560825)
  ·
    refine ⟨5029108739776451101170619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6705478319701934801560825 5029108739776451101170619)
    ·
      refine ⟨7543663109664676651755929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5029108739776451101170619 7543663109664676651755929)
      ·
        refine ⟨5657747332248507488816947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7543663109664676651755929 5657747332248507488816947)
        ·
          refine ⟨8486620998372761233225421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5657747332248507488816947 8486620998372761233225421)
          ·
            refine ⟨3182482874389785462459533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8486620998372761233225421 3182482874389785462459533)
            ·
              refine ⟨1193431077896169548422325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3182482874389785462459533 1193431077896169548422325)
              ·
                refine ⟨111884163552765895164593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1193431077896169548422325 111884163552765895164593)
                ·
                  rfl

theorem cell21_1470782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_1470782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470782 prefixEnd_1470782 := by exact prefixLift 1470782
  have htrace : WordTrace (prefixWord ++ tailWord_1470782) baseStart_1470782 baseEnd_1470782 := by
    simpa [prefixWord, tailWord_1470782, baseEnd_1470782] using wordTrace_append hprefix tailTrace_1470782
  have hstable : (prefixWord ++ tailWord_1470782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470782).length < 2 ^ (prefixWord ++ tailWord_1470782).sum := by decide
  have hdescent : baseEnd_1470782 < baseStart_1470782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470793 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 6]
def baseStart_1470793 : Nat := 118140960795 + 1470793 * 2 ^ 59
def prefixEnd_1470793 : Nat := 4983230072969 + 3 ^ 40 * 1470793 * 2
def baseEnd_1470793 : Nat := 335655001008164110810423

theorem tailTrace_1470793 : CollatzResearch.WordTrace tailWord_1470793 prefixEnd_1470793 335655001008164110810423 := by
  unfold tailWord_1470793
  simp only [CollatzResearch.WordTrace]
  refine ⟨53644227760575627291137033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35762818507050418194091355 53644227760575627291137033)
  ·
    refine ⟨40233170820431720468352775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53644227760575627291137033 40233170820431720468352775)
    ·
      refine ⟨60349756230647580702529163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40233170820431720468352775 60349756230647580702529163)
      ·
        refine ⟨90524634345971371053793745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60349756230647580702529163 90524634345971371053793745)
        ·
          refine ⟨67893475759478528290345309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90524634345971371053793745 67893475759478528290345309)
          ·
            refine ⟨25460053409804448108879491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67893475759478528290345309 25460053409804448108879491)
            ·
              refine ⟨38190080114706672163319237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25460053409804448108879491 38190080114706672163319237)
              ·
                refine ⟨7160640021507501030622357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38190080114706672163319237 7160640021507501030622357)
                ·
                  refine ⟨335655001008164110810423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7160640021507501030622357 335655001008164110810423)
                  ·
                    rfl

theorem cell21_1470793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_1470793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470793 prefixEnd_1470793 := by exact prefixLift 1470793
  have htrace : WordTrace (prefixWord ++ tailWord_1470793) baseStart_1470793 baseEnd_1470793 := by
    simpa [prefixWord, tailWord_1470793, baseEnd_1470793] using wordTrace_append hprefix tailTrace_1470793
  have hstable : (prefixWord ++ tailWord_1470793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470793).length < 2 ^ (prefixWord ++ tailWord_1470793).sum := by decide
  have hdescent : baseEnd_1470793 < baseStart_1470793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470858 : List Nat := [3, 1, 2, 5, 1, 2, 7]
def baseStart_1470858 : Nat := 118140960795 + 1470858 * 2 ^ 59
def prefixEnd_1470858 : Nat := 4983230072969 + 3 ^ 40 * 1470858 * 2
def baseEnd_1470858 : Nat := 37296648321526493580773

theorem tailTrace_1470858 : CollatzResearch.WordTrace tailWord_1470858 prefixEnd_1470858 37296648321526493580773 := by
  unfold tailWord_1470858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13411649626335035848063307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35764399003560095594835485 13411649626335035848063307)
  ·
    refine ⟨20117474439502553772094961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13411649626335035848063307 20117474439502553772094961)
    ·
      refine ⟨15088105829626915329071221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20117474439502553772094961 15088105829626915329071221)
      ·
        refine ⟨1414509921527523312100427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15088105829626915329071221 1414509921527523312100427)
        ·
          refine ⟨2121764882291284968150641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1414509921527523312100427 2121764882291284968150641)
          ·
            refine ⟨1591323661718463726112981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2121764882291284968150641 1591323661718463726112981)
            ·
              refine ⟨37296648321526493580773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1591323661718463726112981 37296648321526493580773)
              ·
                rfl

theorem cell21_1470858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 7].length) (baseStart_1470858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470858 prefixEnd_1470858 := by exact prefixLift 1470858
  have htrace : WordTrace (prefixWord ++ tailWord_1470858) baseStart_1470858 baseEnd_1470858 := by
    simpa [prefixWord, tailWord_1470858, baseEnd_1470858] using wordTrace_append hprefix tailTrace_1470858
  have hstable : (prefixWord ++ tailWord_1470858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470858).length < 2 ^ (prefixWord ++ tailWord_1470858).sum := by decide
  have hdescent : baseEnd_1470858 < baseStart_1470858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470872 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 5]
def baseStart_1470872 : Nat := 118140960795 + 1470872 * 2 ^ 59
def prefixEnd_1470872 : Nat := 4983230072969 + 3 ^ 40 * 1470872 * 2
def baseEnd_1470872 : Nat := 335673029884477528993595

theorem tailTrace_1470872 : CollatzResearch.WordTrace tailWord_1470872 prefixEnd_1470872 335673029884477528993595 := by
  unfold tailWord_1470872
  simp only [CollatzResearch.WordTrace]
  refine ⟨26823554563644711891631435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35764739418192949188841913 26823554563644711891631435)
  ·
    refine ⟨40235331845467067837447153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26823554563644711891631435 40235331845467067837447153)
    ·
      refine ⟨30176498884100300878085365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40235331845467067837447153 30176498884100300878085365)
      ·
        refine ⟨2829046770384403207320503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30176498884100300878085365 2829046770384403207320503)
        ·
          refine ⟨4243570155576604810980755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829046770384403207320503 4243570155576604810980755)
          ·
            refine ⟨6365355233364907216471133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243570155576604810980755 6365355233364907216471133)
            ·
              refine ⟨2387008212511840206176675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6365355233364907216471133 2387008212511840206176675)
              ·
                refine ⟨3580512318767760309265013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387008212511840206176675 3580512318767760309265013)
                ·
                  refine ⟨335673029884477528993595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3580512318767760309265013 335673029884477528993595)
                  ·
                    rfl

theorem cell21_1470872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_1470872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470872 prefixEnd_1470872 := by exact prefixLift 1470872
  have htrace : WordTrace (prefixWord ++ tailWord_1470872) baseStart_1470872 baseEnd_1470872 := by
    simpa [prefixWord, tailWord_1470872, baseEnd_1470872] using wordTrace_append hprefix tailTrace_1470872
  have hstable : (prefixWord ++ tailWord_1470872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470872).length < 2 ^ (prefixWord ++ tailWord_1470872).sum := by decide
  have hdescent : baseEnd_1470872 < baseStart_1470872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470982 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1470982 : Nat := 118140960795 + 1470982 * 2 ^ 59
def prefixEnd_1470982 : Nat := 4983230072969 + 3 ^ 40 * 1470982 * 2
def baseEnd_1470982 : Nat := 335698133383141782160037

theorem tailTrace_1470982 : CollatzResearch.WordTrace tailWord_1470982 prefixEnd_1470982 335698133383141782160037 := by
  unfold tailWord_1470982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676597536152841017805225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35767414104593941713178133 1676597536152841017805225)
  ·
    refine ⟨1257448152114630763353919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1676597536152841017805225 1257448152114630763353919)
    ·
      refine ⟨1886172228171946145030879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1257448152114630763353919 1886172228171946145030879)
      ·
        refine ⟨2829258342257919217546319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886172228171946145030879 2829258342257919217546319)
        ·
          refine ⟨4243887513386878826319479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829258342257919217546319 4243887513386878826319479)
          ·
            refine ⟨6365831270080318239479219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243887513386878826319479 6365831270080318239479219)
            ·
              refine ⟨9548746905120477359218829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6365831270080318239479219 9548746905120477359218829)
              ·
                refine ⟨3580780089420179009707061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9548746905120477359218829 3580780089420179009707061)
                ·
                  refine ⟨335698133383141782160037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3580780089420179009707061 335698133383141782160037)
                  ·
                    rfl

theorem cell21_1470982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1470982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1470982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1470982 prefixEnd_1470982 := by exact prefixLift 1470982
  have htrace : WordTrace (prefixWord ++ tailWord_1470982) baseStart_1470982 baseEnd_1470982 := by
    simpa [prefixWord, tailWord_1470982, baseEnd_1470982] using wordTrace_append hprefix tailTrace_1470982
  have hstable : (prefixWord ++ tailWord_1470982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470982).length < 2 ^ (prefixWord ++ tailWord_1470982).sum := by decide
  have hdescent : baseEnd_1470982 < baseStart_1470982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471024 : List Nat := [2, 1, 1, 1, 2, 3, 5, 3, 3]
def baseStart_1471024 : Nat := 118140960795 + 1471024 * 2 ^ 59
def prefixEnd_1471024 : Nat := 4983230072969 + 3 ^ 40 * 1471024 * 2
def baseEnd_1471024 : Nat := 335707718355359042459951

theorem tailTrace_1471024 : CollatzResearch.WordTrace tailWord_1471024 prefixEnd_1471024 335707718355359042459951 := by
  unfold tailWord_1471024
  simp only [CollatzResearch.WordTrace]
  refine ⟨26826326511369376871398063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35768435348492502495197417 26826326511369376871398063)
  ·
    refine ⟨40239489767054065307097095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26826326511369376871398063 40239489767054065307097095)
    ·
      refine ⟨60359234650581097960645643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40239489767054065307097095 60359234650581097960645643)
      ·
        refine ⟨90538851975871646940968465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60359234650581097960645643 90538851975871646940968465)
        ·
          refine ⟨67904138981903735205726349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90538851975871646940968465 67904138981903735205726349)
          ·
            refine ⟨25464052118213900702147381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67904138981903735205726349 25464052118213900702147381)
            ·
              refine ⟨2387254886082553190826317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25464052118213900702147381 2387254886082553190826317)
              ·
                refine ⟨895220582280957446559869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2387254886082553190826317 895220582280957446559869)
                ·
                  refine ⟨335707718355359042459951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895220582280957446559869 335707718355359042459951)
                  ·
                    rfl

theorem cell21_1471024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 3].length) (baseStart_1471024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471024 prefixEnd_1471024 := by exact prefixLift 1471024
  have htrace : WordTrace (prefixWord ++ tailWord_1471024) baseStart_1471024 baseEnd_1471024 := by
    simpa [prefixWord, tailWord_1471024, baseEnd_1471024] using wordTrace_append hprefix tailTrace_1471024
  have hstable : (prefixWord ++ tailWord_1471024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471024).length < 2 ^ (prefixWord ++ tailWord_1471024).sum := by decide
  have hdescent : baseEnd_1471024 < baseStart_1471024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471052 : List Nat := [2, 2, 1, 3, 1, 2, 4, 6]
def baseStart_1471052 : Nat := 118140960795 + 1471052 * 2 ^ 59
def prefixEnd_1471052 : Nat := 4983230072969 + 3 ^ 40 * 1471052 * 2
def baseEnd_1471052 : Nat := 111904702778945738664409

theorem tailTrace_1471052 : CollatzResearch.WordTrace tailWord_1471052 prefixEnd_1471052 111904702778945738664409 := by
  unfold tailWord_1471052
  simp only [CollatzResearch.WordTrace]
  refine ⟨26826837133318657262407705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35769116177758209683210273 26826837133318657262407705)
  ·
    refine ⟨20120127849988992946805779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26826837133318657262407705 20120127849988992946805779)
    ·
      refine ⟨30180191774983489420208669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20120127849988992946805779 30180191774983489420208669)
      ·
        refine ⟨11317571915618808532578251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30180191774983489420208669 11317571915618808532578251)
        ·
          refine ⟨16976357873428212798867377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11317571915618808532578251 16976357873428212798867377)
          ·
            refine ⟨12732268405071159599150533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16976357873428212798867377 12732268405071159599150533)
            ·
              refine ⟨2387300325950842424840725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12732268405071159599150533 2387300325950842424840725)
              ·
                refine ⟨111904702778945738664409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2387300325950842424840725 111904702778945738664409)
                ·
                  rfl

theorem cell21_1471052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_1471052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471052 prefixEnd_1471052 := by exact prefixLift 1471052
  have htrace : WordTrace (prefixWord ++ tailWord_1471052) baseStart_1471052 baseEnd_1471052 := by
    simpa [prefixWord, tailWord_1471052, baseEnd_1471052] using wordTrace_append hprefix tailTrace_1471052
  have hstable : (prefixWord ++ tailWord_1471052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471052).length < 2 ^ (prefixWord ++ tailWord_1471052).sum := by decide
  have hdescent : baseEnd_1471052 < baseStart_1471052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471204 : List Nat := [2, 3, 1, 1, 1, 6, 7]
def baseStart_1471204 : Nat := 118140960795 + 1471204 * 2 ^ 59
def prefixEnd_1471204 : Nat := 4983230072969 + 3 ^ 40 * 1471204 * 2
def baseEnd_1471204 : Nat := 37305421867524303273287

theorem tailTrace_1471204 : CollatzResearch.WordTrace tailWord_1471204 prefixEnd_1471204 37305421867524303273287 := by
  unfold tailWord_1471204
  simp only [CollatzResearch.WordTrace]
  refine ⟨26829609081043322242174333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35772812108057762989565777 26829609081043322242174333)
  ·
    refine ⟨10061103405391245840815375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26829609081043322242174333 10061103405391245840815375)
    ·
      refine ⟨15091655108086868761223063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10061103405391245840815375 15091655108086868761223063)
      ·
        refine ⟨22637482662130303141834595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15091655108086868761223063 22637482662130303141834595)
        ·
          refine ⟨33956223993195454712751893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22637482662130303141834595 33956223993195454712751893)
          ·
            refine ⟨1591697999681036939660245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33956223993195454712751893 1591697999681036939660245)
            ·
              refine ⟨37305421867524303273287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1591697999681036939660245 37305421867524303273287)
              ·
                rfl

theorem cell21_1471204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 7].length) (baseStart_1471204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471204 prefixEnd_1471204 := by exact prefixLift 1471204
  have htrace : WordTrace (prefixWord ++ tailWord_1471204) baseStart_1471204 baseEnd_1471204 := by
    simpa [prefixWord, tailWord_1471204, baseEnd_1471204] using wordTrace_append hprefix tailTrace_1471204
  have hstable : (prefixWord ++ tailWord_1471204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471204).length < 2 ^ (prefixWord ++ tailWord_1471204).sum := by decide
  have hdescent : baseEnd_1471204 < baseStart_1471204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471263 : List Nat := [1, 1, 2, 4, 2, 11]
def baseStart_1471263 : Nat := 118140960795 + 1471263 * 2 ^ 59
def prefixEnd_1471263 : Nat := 4983230072969 + 3 ^ 40 * 1471263 * 2
def baseEnd_1471263 : Nat := 12435639311538805110227

theorem tailTrace_1471263 : CollatzResearch.WordTrace tailWord_1471263 prefixEnd_1471263 12435639311538805110227 := by
  unfold tailWord_1471263
  simp only [CollatzResearch.WordTrace]
  refine ⟨53661370068872897560746443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35774246712581931707164295 53661370068872897560746443)
  ·
    refine ⟨80492055103309346341119665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53661370068872897560746443 80492055103309346341119665)
    ·
      refine ⟨60369041327482009755839749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80492055103309346341119665 60369041327482009755839749)
      ·
        refine ⟨11319195248902876829219953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60369041327482009755839749 11319195248902876829219953)
        ·
          refine ⟨8489396436677157621914965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11319195248902876829219953 8489396436677157621914965)
          ·
            refine ⟨12435639311538805110227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8489396436677157621914965 12435639311538805110227)
            ·
              rfl

theorem cell21_1471263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 11].length) (baseStart_1471263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471263 prefixEnd_1471263 := by exact prefixLift 1471263
  have htrace : WordTrace (prefixWord ++ tailWord_1471263) baseStart_1471263 baseEnd_1471263 := by
    simpa [prefixWord, tailWord_1471263, baseEnd_1471263] using wordTrace_append hprefix tailTrace_1471263
  have hstable : (prefixWord ++ tailWord_1471263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471263).length < 2 ^ (prefixWord ++ tailWord_1471263).sum := by decide
  have hdescent : baseEnd_1471263 < baseStart_1471263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471266 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1471266 : Nat := 118140960795 + 1471266 * 2 ^ 59
def prefixEnd_1471266 : Nat := 4983230072969 + 3 ^ 40 * 1471266 * 2
def baseEnd_1471266 : Nat := 335762946052420399426123

theorem tailTrace_1471266 : CollatzResearch.WordTrace tailWord_1471266 prefixEnd_1471266 335762946052420399426123 := by
  unfold tailWord_1471266
  simp only [CollatzResearch.WordTrace]
  refine ⟨13415369871965507268276413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35774319658574686048737101 13415369871965507268276413)
  ·
    refine ⟨5030763701987065225603655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13415369871965507268276413 5030763701987065225603655)
    ·
      refine ⟨7546145552980597838405483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5030763701987065225603655 7546145552980597838405483)
      ·
        refine ⟨11319218329470896757608225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7546145552980597838405483 11319218329470896757608225)
        ·
          refine ⟨8489413747103172568206169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11319218329470896757608225 8489413747103172568206169)
          ·
            refine ⟨6367060310327379426154627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8489413747103172568206169 6367060310327379426154627)
            ·
              refine ⟨9550590465491069139231941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6367060310327379426154627 9550590465491069139231941)
              ·
                refine ⟨1790735712279575463605989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9550590465491069139231941 1790735712279575463605989)
                ·
                  refine ⟨335762946052420399426123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1790735712279575463605989 335762946052420399426123)
                  ·
                    rfl

theorem cell21_1471266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1471266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471266 prefixEnd_1471266 := by exact prefixLift 1471266
  have htrace : WordTrace (prefixWord ++ tailWord_1471266) baseStart_1471266 baseEnd_1471266 := by
    simpa [prefixWord, tailWord_1471266, baseEnd_1471266] using wordTrace_append hprefix tailTrace_1471266
  have hstable : (prefixWord ++ tailWord_1471266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471266).length < 2 ^ (prefixWord ++ tailWord_1471266).sum := by decide
  have hdescent : baseEnd_1471266 < baseStart_1471266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471401 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 4]
def baseStart_1471401 : Nat := 118140960795 + 1471401 * 2 ^ 59
def prefixEnd_1471401 : Nat := 4983230072969 + 3 ^ 40 * 1471401 * 2
def baseEnd_1471401 : Nat := 335793754891690164675847

theorem tailTrace_1471401 : CollatzResearch.WordTrace tailWord_1471401 prefixEnd_1471401 335793754891690164675847 := by
  unfold tailWord_1471401
  simp only [CollatzResearch.WordTrace]
  refine ⟨53666403342372947129270057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35777602228248631419513371 53666403342372947129270057)
  ·
    refine ⟨40249802506779710346952543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53666403342372947129270057 40249802506779710346952543)
    ·
      refine ⟨60374703760169565520428815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40249802506779710346952543 60374703760169565520428815)
      ·
        refine ⟨90562055640254348280643223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60374703760169565520428815 90562055640254348280643223)
        ·
          refine ⟨135843083460381522420964835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90562055640254348280643223 135843083460381522420964835)
          ·
            refine ⟨203764625190572283631447253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135843083460381522420964835 203764625190572283631447253)
            ·
              refine ⟨4775733402904037897612045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 203764625190572283631447253 4775733402904037897612045)
              ·
                refine ⟨1790900026089014211604517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4775733402904037897612045 1790900026089014211604517)
                ·
                  refine ⟨335793754891690164675847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1790900026089014211604517 335793754891690164675847)
                  ·
                    rfl

theorem cell21_1471401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_1471401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471401 prefixEnd_1471401 := by exact prefixLift 1471401
  have htrace : WordTrace (prefixWord ++ tailWord_1471401) baseStart_1471401 baseEnd_1471401 := by
    simpa [prefixWord, tailWord_1471401, baseEnd_1471401] using wordTrace_append hprefix tailTrace_1471401
  have hstable : (prefixWord ++ tailWord_1471401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471401).length < 2 ^ (prefixWord ++ tailWord_1471401).sum := by decide
  have hdescent : baseEnd_1471401 < baseStart_1471401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471415 : List Nat := [1, 1, 3, 1, 3, 1, 4, 7]
def baseStart_1471415 : Nat := 118140960795 + 1471415 * 2 ^ 59
def prefixEnd_1471415 : Nat := 4983230072969 + 3 ^ 40 * 1471415 * 2
def baseEnd_1471415 : Nat := 111932316627476417147495

theorem tailTrace_1471415 : CollatzResearch.WordTrace tailWord_1471415 prefixEnd_1471415 111932316627476417147495 := by
  unfold tailWord_1471415
  simp only [CollatzResearch.WordTrace]
  refine ⟨53666913964322227520279699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35777942642881485013519799 53666913964322227520279699)
  ·
    refine ⟨80500370946483341280419549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53666913964322227520279699 80500370946483341280419549)
    ·
      refine ⟨30187639104931252980157331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80500370946483341280419549 30187639104931252980157331)
      ·
        refine ⟨45281458657396879470235997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30187639104931252980157331 45281458657396879470235997)
        ·
          refine ⟨16980546996523829801338499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45281458657396879470235997 16980546996523829801338499)
          ·
            refine ⟨25470820494785744702007749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16980546996523829801338499 25470820494785744702007749)
            ·
              refine ⟨4775778842772327131626453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25470820494785744702007749 4775778842772327131626453)
              ·
                refine ⟨111932316627476417147495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4775778842772327131626453 111932316627476417147495)
                ·
                  rfl

theorem cell21_1471415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 7].length) (baseStart_1471415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471415 prefixEnd_1471415 := by exact prefixLift 1471415
  have htrace : WordTrace (prefixWord ++ tailWord_1471415) baseStart_1471415 baseEnd_1471415 := by
    simpa [prefixWord, tailWord_1471415, baseEnd_1471415] using wordTrace_append hprefix tailTrace_1471415
  have hstable : (prefixWord ++ tailWord_1471415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471415).length < 2 ^ (prefixWord ++ tailWord_1471415).sum := by decide
  have hdescent : baseEnd_1471415 < baseStart_1471415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471430 : List Nat := [6, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1471430 : Nat := 118140960795 + 1471430 * 2 ^ 59
def prefixEnd_1471430 : Nat := 4983230072969 + 3 ^ 40 * 1471430 * 2
def baseEnd_1471430 : Nat := 335800373086792558692455

theorem tailTrace_1471430 : CollatzResearch.WordTrace tailWord_1471430 prefixEnd_1471430 335800373086792558692455 := by
  unfold tailWord_1471430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677108158102121408814867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35778307372845256721383829 1677108158102121408814867)
  ·
    refine ⟨2515662237153182113222301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1677108158102121408814867 2515662237153182113222301)
    ·
      refine ⟨943373338932443292458363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2515662237153182113222301 943373338932443292458363)
      ·
        refine ⟨1415060008398664938687545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 943373338932443292458363 1415060008398664938687545)
        ·
          refine ⟨1061295006298998704015659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1415060008398664938687545 1061295006298998704015659)
          ·
            refine ⟨1591942509448498056023489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061295006298998704015659 1591942509448498056023489)
            ·
              refine ⟨1193956882086373542017617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591942509448498056023489 1193956882086373542017617)
              ·
                refine ⟨895467661564780156513213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193956882086373542017617 895467661564780156513213)
                ·
                  refine ⟨335800373086792558692455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895467661564780156513213 335800373086792558692455)
                  ·
                    rfl

theorem cell21_1471430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1471430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471430 prefixEnd_1471430 := by exact prefixLift 1471430
  have htrace : WordTrace (prefixWord ++ tailWord_1471430) baseStart_1471430 baseEnd_1471430 := by
    simpa [prefixWord, tailWord_1471430, baseEnd_1471430] using wordTrace_append hprefix tailTrace_1471430
  have hstable : (prefixWord ++ tailWord_1471430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471430).length < 2 ^ (prefixWord ++ tailWord_1471430).sum := by decide
  have hdescent : baseEnd_1471430 < baseStart_1471430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471432 : List Nat := [2, 1, 3, 1, 6, 8]
def baseStart_1471432 : Nat := 118140960795 + 1471432 * 2 ^ 59
def prefixEnd_1471432 : Nat := 4983230072969 + 3 ^ 40 * 1471432 * 2
def baseEnd_1471432 : Nat := 12437067759779296283671

theorem tailTrace_1471432 : CollatzResearch.WordTrace tailWord_1471432 prefixEnd_1471432 12437067759779296283671 := by
  unfold tailWord_1471432
  simp only [CollatzResearch.WordTrace]
  refine ⟨26833767002630319711824275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35778356003507092949099033 26833767002630319711824275)
  ·
    refine ⟨40250650503945479567736413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26833767002630319711824275 40250650503945479567736413)
    ·
      refine ⟨15093993938979554837901155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40250650503945479567736413 15093993938979554837901155)
      ·
        refine ⟨22640990908469332256851733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15093993938979554837901155 22640990908469332256851733)
        ·
          refine ⟨1061296448834499949539925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22640990908469332256851733 1061296448834499949539925)
          ·
            refine ⟨12437067759779296283671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1061296448834499949539925 12437067759779296283671)
            ·
              rfl

theorem cell21_1471432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 8].length) (baseStart_1471432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471432 prefixEnd_1471432 := by exact prefixLift 1471432
  have htrace : WordTrace (prefixWord ++ tailWord_1471432) baseStart_1471432 baseEnd_1471432 := by
    simpa [prefixWord, tailWord_1471432, baseEnd_1471432] using wordTrace_append hprefix tailTrace_1471432
  have hstable : (prefixWord ++ tailWord_1471432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471432).length < 2 ^ (prefixWord ++ tailWord_1471432).sum := by decide
  have hdescent : baseEnd_1471432 < baseStart_1471432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471463 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 5]
def baseStart_1471463 : Nat := 118140960795 + 1471463 * 2 ^ 59
def prefixEnd_1471463 : Nat := 4983230072969 + 3 ^ 40 * 1471463 * 2
def baseEnd_1471463 : Nat := 335807904136391834642387

theorem tailTrace_1471463 : CollatzResearch.WordTrace tailWord_1471463 prefixEnd_1471463 335807904136391834642387 := by
  unfold tailWord_1471463
  simp only [CollatzResearch.WordTrace]
  refine ⟨53668664668148331718027043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35779109778765554478684695 53668664668148331718027043)
  ·
    refine ⟨80502997002222497577040565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53668664668148331718027043 80502997002222497577040565)
    ·
      refine ⟨7547155968958359147847553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80502997002222497577040565 7547155968958359147847553)
      ·
        refine ⟨5660366976718769360885665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7547155968958359147847553 5660366976718769360885665)
        ·
          refine ⟨4245275232539077020664249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5660366976718769360885665 4245275232539077020664249)
          ·
            refine ⟨3183956424404307765498187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4245275232539077020664249 3183956424404307765498187)
            ·
              refine ⟨4775934636606461648247281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183956424404307765498187 4775934636606461648247281)
              ·
                refine ⟨3581950977454846236185461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4775934636606461648247281 3581950977454846236185461)
                ·
                  refine ⟨335807904136391834642387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3581950977454846236185461 335807904136391834642387)
                  ·
                    rfl

theorem cell21_1471463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 5].length) (baseStart_1471463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471463 prefixEnd_1471463 := by exact prefixLift 1471463
  have htrace : WordTrace (prefixWord ++ tailWord_1471463) baseStart_1471463 baseEnd_1471463 := by
    simpa [prefixWord, tailWord_1471463, baseEnd_1471463] using wordTrace_append hprefix tailTrace_1471463
  have hstable : (prefixWord ++ tailWord_1471463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471463).length < 2 ^ (prefixWord ++ tailWord_1471463).sum := by decide
  have hdescent : baseEnd_1471463 < baseStart_1471463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471511 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 4]
def baseStart_1471511 : Nat := 118140960795 + 1471511 * 2 ^ 59
def prefixEnd_1471511 : Nat := 4983230072969 + 3 ^ 40 * 1471511 * 2
def baseEnd_1471511 : Nat := 335818858390354417842289

theorem tailTrace_1471511 : CollatzResearch.WordTrace tailWord_1471511 prefixEnd_1471511 335818858390354417842289 := by
  unfold tailWord_1471511
  simp only [CollatzResearch.WordTrace]
  refine ⟨53670415371974435915774387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35780276914649623943849591 53670415371974435915774387)
  ·
    refine ⟨80505623057961653873661581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53670415371974435915774387 80505623057961653873661581)
    ·
      refine ⟨30189608646735620202623093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80505623057961653873661581 30189608646735620202623093)
      ·
        refine ⟨2830275810631464393995915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30189608646735620202623093 2830275810631464393995915)
        ·
          refine ⟨4245413715947196590993873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830275810631464393995915 4245413715947196590993873)
          ·
            refine ⟨3184060286960397443245405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4245413715947196590993873 3184060286960397443245405)
            ·
              refine ⟨1194022607610149041217027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3184060286960397443245405 1194022607610149041217027)
              ·
                refine ⟨1791033911415223561825541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194022607610149041217027 1791033911415223561825541)
                ·
                  refine ⟨335818858390354417842289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1791033911415223561825541 335818858390354417842289)
                  ·
                    rfl

theorem cell21_1471511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 4].length) (baseStart_1471511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471511 prefixEnd_1471511 := by exact prefixLift 1471511
  have htrace : WordTrace (prefixWord ++ tailWord_1471511) baseStart_1471511 baseEnd_1471511 := by
    simpa [prefixWord, tailWord_1471511, baseEnd_1471511] using wordTrace_append hprefix tailTrace_1471511
  have hstable : (prefixWord ++ tailWord_1471511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471511).length < 2 ^ (prefixWord ++ tailWord_1471511).sum := by decide
  have hdescent : baseEnd_1471511 < baseStart_1471511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471536 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_1471536 : Nat := 118140960795 + 1471536 * 2 ^ 59
def prefixEnd_1471536 : Nat := 4983230072969 + 3 ^ 40 * 1471536 * 2
def baseEnd_1471536 : Nat := 335824563730959929925571

theorem tailTrace_1471536 : CollatzResearch.WordTrace tailWord_1471536 prefixEnd_1471536 335824563730959929925571 := by
  unfold tailWord_1471536
  simp only [CollatzResearch.WordTrace]
  refine ⟨26835663598441932592717231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35780884797922576790289641 26835663598441932592717231)
  ·
    refine ⟨40253495397662898889075847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26835663598441932592717231 40253495397662898889075847)
    ·
      refine ⟨60380243096494348333613771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40253495397662898889075847 60380243096494348333613771)
      ·
        refine ⟨90570364644741522500420657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60380243096494348333613771 90570364644741522500420657)
        ·
          refine ⟨67927773483556141875315493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90570364644741522500420657 67927773483556141875315493)
          ·
            refine ⟨12736457528166776601621655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67927773483556141875315493 12736457528166776601621655)
            ·
              refine ⟨19104686292250164902432483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12736457528166776601621655 19104686292250164902432483)
              ·
                refine ⟨28657029438375247353648725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19104686292250164902432483 28657029438375247353648725)
                ·
                  refine ⟨335824563730959929925571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28657029438375247353648725 335824563730959929925571)
                  ·
                    rfl

theorem cell21_1471536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_1471536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471536 prefixEnd_1471536 := by exact prefixLift 1471536
  have htrace : WordTrace (prefixWord ++ tailWord_1471536) baseStart_1471536 baseEnd_1471536 := by
    simpa [prefixWord, tailWord_1471536, baseEnd_1471536] using wordTrace_append hprefix tailTrace_1471536
  have hstable : (prefixWord ++ tailWord_1471536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471536).length < 2 ^ (prefixWord ++ tailWord_1471536).sum := by decide
  have hdescent : baseEnd_1471536 < baseStart_1471536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471570 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_1471570 : Nat := 118140960795 + 1471570 * 2 ^ 59
def prefixEnd_1471570 : Nat := 4983230072969 + 3 ^ 40 * 1471570 * 2
def baseEnd_1471570 : Nat := 335832322994183426358835

theorem tailTrace_1471570 : CollatzResearch.WordTrace tailWord_1471570 prefixEnd_1471570 335832322994183426358835 := by
  unfold tailWord_1471570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13418141819690172248043041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35781711519173792661448109 13418141819690172248043041)
  ·
    refine ⟨10063606364767629186032281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13418141819690172248043041 10063606364767629186032281)
    ·
      refine ⟨7547704773575721889524211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10063606364767629186032281 7547704773575721889524211)
      ·
        refine ⟨11321557160363582834286317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7547704773575721889524211 11321557160363582834286317)
        ·
          refine ⟨4245583935136343562857369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11321557160363582834286317 4245583935136343562857369)
          ·
            refine ⟨3184187951352257672143027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4245583935136343562857369 3184187951352257672143027)
            ·
              refine ⟨4776281927028386508214541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3184187951352257672143027 4776281927028386508214541)
              ·
                refine ⟨1791105722635644940580453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4776281927028386508214541 1791105722635644940580453)
                ·
                  refine ⟨335832322994183426358835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1791105722635644940580453 335832322994183426358835)
                  ·
                    rfl

theorem cell21_1471570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_1471570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471570 prefixEnd_1471570 := by exact prefixLift 1471570
  have htrace : WordTrace (prefixWord ++ tailWord_1471570) baseStart_1471570 baseEnd_1471570 := by
    simpa [prefixWord, tailWord_1471570, baseEnd_1471570] using wordTrace_append hprefix tailTrace_1471570
  have hstable : (prefixWord ++ tailWord_1471570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471570).length < 2 ^ (prefixWord ++ tailWord_1471570).sum := by decide
  have hdescent : baseEnd_1471570 < baseStart_1471570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471694 : List Nat := [4, 1, 1, 1, 6, 1, 2, 5]
def baseStart_1471694 : Nat := 118140960795 + 1471694 * 2 ^ 59
def prefixEnd_1471694 : Nat := 4983230072969 + 3 ^ 40 * 1471694 * 2
def baseEnd_1471694 : Nat := 111953540494528922097305

theorem tailTrace_1471694 : CollatzResearch.WordTrace tailWord_1471694 prefixEnd_1471694 111953540494528922097305 := by
  unfold tailWord_1471694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6709636241288932271210767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35784726620207638779790757 6709636241288932271210767)
  ·
    refine ⟨10064454361933398406816151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6709636241288932271210767 10064454361933398406816151)
    ·
      refine ⟨15096681542900097610224227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10064454361933398406816151 15096681542900097610224227)
      ·
        refine ⟨22645022314350146415336341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15096681542900097610224227 22645022314350146415336341)
        ·
          refine ⟨1061485420985163113218891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22645022314350146415336341 1061485420985163113218891)
          ·
            refine ⟨1592228131477744669828337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061485420985163113218891 1592228131477744669828337)
            ·
              refine ⟨1194171098608308502371253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592228131477744669828337 1194171098608308502371253)
              ·
                refine ⟨111953540494528922097305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1194171098608308502371253 111953540494528922097305)
                ·
                  rfl

theorem cell21_1471694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_1471694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471694 prefixEnd_1471694 := by exact prefixLift 1471694
  have htrace : WordTrace (prefixWord ++ tailWord_1471694) baseStart_1471694 baseEnd_1471694 := by
    simpa [prefixWord, tailWord_1471694, baseEnd_1471694] using wordTrace_append hprefix tailTrace_1471694
  have hstable : (prefixWord ++ tailWord_1471694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471694).length < 2 ^ (prefixWord ++ tailWord_1471694).sum := by decide
  have hdescent : baseEnd_1471694 < baseStart_1471694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471725 : List Nat := [1, 5, 1, 2, 2, 2, 3, 2, 3]
def baseStart_1471725 : Nat := 118140960795 + 1471725 * 2 ^ 59
def prefixEnd_1471725 : Nat := 4983230072969 + 3 ^ 40 * 1471725 * 2
def baseEnd_1471725 : Nat := 335867696105937601275185

theorem tailTrace_1471725 : CollatzResearch.WordTrace tailWord_1471725 prefixEnd_1471725 335867696105937601275185 := by
  unfold tailWord_1471725
  simp only [CollatzResearch.WordTrace]
  refine ⟨53678220593199150464064629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35785480395466100309376419 53678220593199150464064629)
  ·
    refine ⟨5032333180612420356006059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53678220593199150464064629 5032333180612420356006059)
    ·
      refine ⟨7548499770918630534009089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5032333180612420356006059 7548499770918630534009089)
      ·
        refine ⟨5661374828188972900506817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7548499770918630534009089 5661374828188972900506817)
        ·
          refine ⟨4246031121141729675380113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5661374828188972900506817 4246031121141729675380113)
          ·
            refine ⟨3184523340856297256535085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4246031121141729675380113 3184523340856297256535085)
            ·
              refine ⟨1194196252821111471200657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3184523340856297256535085 1194196252821111471200657)
              ·
                refine ⟨895647189615833603400493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194196252821111471200657 895647189615833603400493)
                ·
                  refine ⟨335867696105937601275185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895647189615833603400493 335867696105937601275185)
                  ·
                    rfl

theorem cell21_1471725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_1471725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471725 prefixEnd_1471725 := by exact prefixLift 1471725
  have htrace : WordTrace (prefixWord ++ tailWord_1471725) baseStart_1471725 baseEnd_1471725 := by
    simpa [prefixWord, tailWord_1471725, baseEnd_1471725] using wordTrace_append hprefix tailTrace_1471725
  have hstable : (prefixWord ++ tailWord_1471725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471725).length < 2 ^ (prefixWord ++ tailWord_1471725).sum := by decide
  have hdescent : baseEnd_1471725 < baseStart_1471725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471767 : List Nat := [1, 1, 3, 4, 1, 1, 2, 5, 3]
def baseStart_1471767 : Nat := 118140960795 + 1471767 * 2 ^ 59
def prefixEnd_1471767 : Nat := 4983230072969 + 3 ^ 40 * 1471767 * 2
def baseEnd_1471767 : Nat := 335877281078154861575099

theorem tailTrace_1471767 : CollatzResearch.WordTrace tailWord_1471767 prefixEnd_1471767 335877281078154861575099 := by
  unfold tailWord_1471767
  simp only [CollatzResearch.WordTrace]
  refine ⟨53679752459046991637093555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35786501639364661091395703 53679752459046991637093555)
  ·
    refine ⟨80519628688570487455640333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53679752459046991637093555 80519628688570487455640333)
    ·
      refine ⟨30194860758213932795865125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80519628688570487455640333 30194860758213932795865125)
      ·
        refine ⟨5661536392165112399224711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30194860758213932795865125 5661536392165112399224711)
        ·
          refine ⟨8492304588247668598837067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5661536392165112399224711 8492304588247668598837067)
          ·
            refine ⟨12738456882371502898255601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8492304588247668598837067 12738456882371502898255601)
            ·
              refine ⟨9553842661778627173691701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12738456882371502898255601 9553842661778627173691701)
              ·
                refine ⟨895672749541746297533597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9553842661778627173691701 895672749541746297533597)
                ·
                  refine ⟨335877281078154861575099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895672749541746297533597 335877281078154861575099)
                  ·
                    rfl

theorem cell21_1471767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 3].length) (baseStart_1471767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471767 prefixEnd_1471767 := by exact prefixLift 1471767
  have htrace : WordTrace (prefixWord ++ tailWord_1471767) baseStart_1471767 baseEnd_1471767 := by
    simpa [prefixWord, tailWord_1471767, baseEnd_1471767] using wordTrace_append hprefix tailTrace_1471767
  have hstable : (prefixWord ++ tailWord_1471767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471767).length < 2 ^ (prefixWord ++ tailWord_1471767).sum := by decide
  have hdescent : baseEnd_1471767 < baseStart_1471767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471781 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 4]
def baseStart_1471781 : Nat := 118140960795 + 1471781 * 2 ^ 59
def prefixEnd_1471781 : Nat := 4983230072969 + 3 ^ 40 * 1471781 * 2
def baseEnd_1471781 : Nat := 335880476068893948341737

theorem tailTrace_1471781 : CollatzResearch.WordTrace tailWord_1471781 prefixEnd_1471781 335880476068893948341737 := by
  unfold tailWord_1471781
  simp only [CollatzResearch.WordTrace]
  refine ⟨53680263080996272028103197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35786842053997514685402131 53680263080996272028103197)
  ·
    refine ⟨20130098655373602010538699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53680263080996272028103197 20130098655373602010538699)
    ·
      refine ⟨30195147983060403015808049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20130098655373602010538699 30195147983060403015808049)
      ·
        refine ⟨22646360987295302261856037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30195147983060403015808049 22646360987295302261856037)
        ·
          refine ⟨4246192685117869174098007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22646360987295302261856037 4246192685117869174098007)
          ·
            refine ⟨6369289027676803761147011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246192685117869174098007 6369289027676803761147011)
            ·
              refine ⟨9553933541515205641720517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6369289027676803761147011 9553933541515205641720517)
              ·
                refine ⟨1791362539034101057822597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9553933541515205641720517 1791362539034101057822597)
                ·
                  refine ⟨335880476068893948341737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1791362539034101057822597 335880476068893948341737)
                  ·
                    rfl

theorem cell21_1471781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_1471781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471781 prefixEnd_1471781 := by exact prefixLift 1471781
  have htrace : WordTrace (prefixWord ++ tailWord_1471781) baseStart_1471781 baseEnd_1471781 := by
    simpa [prefixWord, tailWord_1471781, baseEnd_1471781] using wordTrace_append hprefix tailTrace_1471781
  have hstable : (prefixWord ++ tailWord_1471781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471781).length < 2 ^ (prefixWord ++ tailWord_1471781).sum := by decide
  have hdescent : baseEnd_1471781 < baseStart_1471781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471784 : List Nat := [2, 1, 5, 1, 2, 2, 1, 4, 3]
def baseStart_1471784 : Nat := 118140960795 + 1471784 * 2 ^ 59
def prefixEnd_1471784 : Nat := 4983230072969 + 3 ^ 40 * 1471784 * 2
def baseEnd_1471784 : Nat := 335881160709766609791731

theorem tailTrace_1471784 : CollatzResearch.WordTrace tailWord_1471784 prefixEnd_1471784 335881160709766609791731 := by
  unfold tailWord_1471784
  simp only [CollatzResearch.WordTrace]
  refine ⟨26840186249992701770231203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35786914999990269026974937 26840186249992701770231203)
  ·
    refine ⟨40260279374989052655346805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26840186249992701770231203 40260279374989052655346805)
    ·
      refine ⟨3774401191405223686438763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40260279374989052655346805 3774401191405223686438763)
      ·
        refine ⟨5661601787107835529658145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3774401191405223686438763 5661601787107835529658145)
        ·
          refine ⟨4246201340330876647243609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5661601787107835529658145 4246201340330876647243609)
          ·
            refine ⟨3184651005248157485432707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4246201340330876647243609 3184651005248157485432707)
            ·
              refine ⟨4776976507872236228149061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3184651005248157485432707 4776976507872236228149061)
              ·
                refine ⟨895683095226044292777949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4776976507872236228149061 895683095226044292777949)
                ·
                  refine ⟨335881160709766609791731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895683095226044292777949 335881160709766609791731)
                  ·
                    rfl

theorem cell21_1471784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 3].length) (baseStart_1471784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471784 prefixEnd_1471784 := by exact prefixLift 1471784
  have htrace : WordTrace (prefixWord ++ tailWord_1471784) baseStart_1471784 baseEnd_1471784 := by
    simpa [prefixWord, tailWord_1471784, baseEnd_1471784] using wordTrace_append hprefix tailTrace_1471784
  have hstable : (prefixWord ++ tailWord_1471784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471784).length < 2 ^ (prefixWord ++ tailWord_1471784).sum := by decide
  have hdescent : baseEnd_1471784 < baseStart_1471784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471795 : List Nat := [1, 1, 1, 2, 5, 2, 3, 6]
def baseStart_1471795 : Nat := 118140960795 + 1471795 * 2 ^ 59
def prefixEnd_1471795 : Nat := 4983230072969 + 3 ^ 40 * 1471795 * 2
def baseEnd_1471795 : Nat := 111961223686544345036125

theorem tailTrace_1471795 : CollatzResearch.WordTrace tailWord_1471795 prefixEnd_1471795 111961223686544345036125 := by
  unfold tailWord_1471795
  simp only [CollatzResearch.WordTrace]
  refine ⟨53680773702945552419112839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35787182468630368279408559 53680773702945552419112839)
  ·
    refine ⟨80521160554418328628669259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53680773702945552419112839 80521160554418328628669259)
    ·
      refine ⟨120781740831627492943003889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80521160554418328628669259 120781740831627492943003889)
      ·
        refine ⟨90586305623720619707252917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120781740831627492943003889 90586305623720619707252917)
        ·
          refine ⟨8492466152223808097554961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90586305623720619707252917 8492466152223808097554961)
          ·
            refine ⟨6369349614167856073166221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8492466152223808097554961 6369349614167856073166221)
            ·
              refine ⟨2388506105312946027437333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6369349614167856073166221 2388506105312946027437333)
              ·
                refine ⟨111961223686544345036125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2388506105312946027437333 111961223686544345036125)
                ·
                  rfl

theorem cell21_1471795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 6].length) (baseStart_1471795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471795 prefixEnd_1471795 := by exact prefixLift 1471795
  have htrace : WordTrace (prefixWord ++ tailWord_1471795) baseStart_1471795 baseEnd_1471795 := by
    simpa [prefixWord, tailWord_1471795, baseEnd_1471795] using wordTrace_append hprefix tailTrace_1471795
  have hstable : (prefixWord ++ tailWord_1471795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471795).length < 2 ^ (prefixWord ++ tailWord_1471795).sum := by decide
  have hdescent : baseEnd_1471795 < baseStart_1471795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471843 : List Nat := [1, 1, 1, 5, 2, 2, 2, 4, 3]
def baseStart_1471843 : Nat := 118140960795 + 1471843 * 2 ^ 59
def prefixEnd_1471843 : Nat := 4983230072969 + 3 ^ 40 * 1471843 * 2
def baseEnd_1471843 : Nat := 335894625313595618308277

theorem tailTrace_1471843 : CollatzResearch.WordTrace tailWord_1471843 prefixEnd_1471843 335894625313595618308277 := by
  unfold tailWord_1471843
  simp only [CollatzResearch.WordTrace]
  refine ⟨53682524406771656616860183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35788349604514437744573455 53682524406771656616860183)
  ·
    refine ⟨80523786610157484925290275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53682524406771656616860183 80523786610157484925290275)
    ·
      refine ⟨120785679915236227387935413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80523786610157484925290275 120785679915236227387935413)
      ·
        refine ⟨11323657492053396317618945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120785679915236227387935413 11323657492053396317618945)
        ·
          refine ⟨8492743119040047238214209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11323657492053396317618945 8492743119040047238214209)
          ·
            refine ⟨6369557339280035428660657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8492743119040047238214209 6369557339280035428660657)
            ·
              refine ⟨4777168004460026571495493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6369557339280035428660657 4777168004460026571495493)
              ·
                refine ⟨895719000836254982155405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4777168004460026571495493 895719000836254982155405)
                ·
                  refine ⟨335894625313595618308277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895719000836254982155405 335894625313595618308277)
                  ·
                    rfl

theorem cell21_1471843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 3].length) (baseStart_1471843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471843 prefixEnd_1471843 := by exact prefixLift 1471843
  have htrace : WordTrace (prefixWord ++ tailWord_1471843) baseStart_1471843 baseEnd_1471843 := by
    simpa [prefixWord, tailWord_1471843, baseEnd_1471843] using wordTrace_append hprefix tailTrace_1471843
  have hstable : (prefixWord ++ tailWord_1471843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471843).length < 2 ^ (prefixWord ++ tailWord_1471843).sum := by decide
  have hdescent : baseEnd_1471843 < baseStart_1471843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471874 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1471874 : Nat := 118140960795 + 1471874 * 2 ^ 59
def prefixEnd_1471874 : Nat := 4983230072969 + 3 ^ 40 * 1471874 * 2
def baseEnd_1471874 : Nat := 335901699935946453291547

theorem tailTrace_1471874 : CollatzResearch.WordTrace tailWord_1471874 prefixEnd_1471874 335901699935946453291547 := by
  unfold tailWord_1471874
  simp only [CollatzResearch.WordTrace]
  refine ⟨13420913767414837227809669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35789103379772899274159117 13420913767414837227809669)
  ·
    refine ⟨2516421331390281980214313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13420913767414837227809669 2516421331390281980214313)
    ·
      refine ⟨1887315998542711485160735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2516421331390281980214313 1887315998542711485160735)
      ·
        refine ⟨2830973997814067227741103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887315998542711485160735 2830973997814067227741103)
        ·
          refine ⟨4246460996721100841611655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830973997814067227741103 4246460996721100841611655)
          ·
            refine ⟨6369691495081651262417483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246460996721100841611655 6369691495081651262417483)
            ·
              refine ⟨9554537242622476893626225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6369691495081651262417483 9554537242622476893626225)
              ·
                refine ⟨7165902931966857670219669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9554537242622476893626225 7165902931966857670219669)
                ·
                  refine ⟨335901699935946453291547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7165902931966857670219669 335901699935946453291547)
                  ·
                    rfl

theorem cell21_1471874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1471874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471874 prefixEnd_1471874 := by exact prefixLift 1471874
  have htrace : WordTrace (prefixWord ++ tailWord_1471874) baseStart_1471874 baseEnd_1471874 := by
    simpa [prefixWord, tailWord_1471874, baseEnd_1471874] using wordTrace_append hprefix tailTrace_1471874
  have hstable : (prefixWord ++ tailWord_1471874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471874).length < 2 ^ (prefixWord ++ tailWord_1471874).sum := by decide
  have hdescent : baseEnd_1471874 < baseStart_1471874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471981 : List Nat := [1, 5, 1, 3, 2, 1, 3, 5]
def baseStart_1471981 : Nat := 118140960795 + 1471981 * 2 ^ 59
def prefixEnd_1471981 : Nat := 4983230072969 + 3 ^ 40 * 1471981 * 2
def baseEnd_1471981 : Nat := 111975372931246015002665

theorem tailTrace_1471981 : CollatzResearch.WordTrace tailWord_1471981 prefixEnd_1471981 111975372931246015002665 := by
  unfold tailWord_1471981
  simp only [CollatzResearch.WordTrace]
  refine ⟨53687557680271706185383797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35791705120181137456922531 53687557680271706185383797)
  ·
    refine ⟨5033208532525472454879731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53687557680271706185383797 5033208532525472454879731)
    ·
      refine ⟨7549812798788208682319597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5033208532525472454879731 7549812798788208682319597)
      ·
        refine ⟨2831179799545578255869849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7549812798788208682319597 2831179799545578255869849)
        ·
          refine ⟨2123384849659183691902387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2831179799545578255869849 2123384849659183691902387)
          ·
            refine ⟨3185077274488775537853581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123384849659183691902387 3185077274488775537853581)
            ·
              refine ⟨1194403977933290826695093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3185077274488775537853581 1194403977933290826695093)
              ·
                refine ⟨111975372931246015002665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1194403977933290826695093 111975372931246015002665)
                ·
                  rfl

theorem cell21_1471981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 5].length) (baseStart_1471981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1471981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1471981 prefixEnd_1471981 := by exact prefixLift 1471981
  have htrace : WordTrace (prefixWord ++ tailWord_1471981) baseStart_1471981 baseEnd_1471981 := by
    simpa [prefixWord, tailWord_1471981, baseEnd_1471981] using wordTrace_append hprefix tailTrace_1471981
  have hstable : (prefixWord ++ tailWord_1471981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471981).length < 2 ^ (prefixWord ++ tailWord_1471981).sum := by decide
  have hdescent : baseEnd_1471981 < baseStart_1471981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472040 : List Nat := [2, 1, 5, 2, 2, 1, 1, 7]
def baseStart_1472040 : Nat := 118140960795 + 1472040 * 2 ^ 59
def prefixEnd_1472040 : Nat := 4983230072969 + 3 ^ 40 * 1472040 * 2
def baseEnd_1472040 : Nat := 111979861132522351174847

theorem tailTrace_1472040 : CollatzResearch.WordTrace tailWord_1472040 prefixEnd_1472040 111979861132522351174847 := by
  unfold tailWord_1472040
  simp only [CollatzResearch.WordTrace]
  refine ⟨26844854793528979630890787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35793139724705306174521049 26844854793528979630890787)
  ·
    refine ⟨40267282190293469446336181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26844854793528979630890787 40267282190293469446336181)
    ·
      refine ⟨3775057705340012760594017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40267282190293469446336181 3775057705340012760594017)
      ·
        refine ⟨2831293279005009570445513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3775057705340012760594017 2831293279005009570445513)
        ·
          refine ⟨2123469959253757177834135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2831293279005009570445513 2123469959253757177834135)
          ·
            refine ⟨3185204938880635766751203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123469959253757177834135 3185204938880635766751203)
            ·
              refine ⟨4777807408320953650126805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3185204938880635766751203 4777807408320953650126805)
              ·
                refine ⟨111979861132522351174847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4777807408320953650126805 111979861132522351174847)
                ·
                  rfl

theorem cell21_1472040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_1472040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472040 prefixEnd_1472040 := by exact prefixLift 1472040
  have htrace : WordTrace (prefixWord ++ tailWord_1472040) baseStart_1472040 baseEnd_1472040 := by
    simpa [prefixWord, tailWord_1472040, baseEnd_1472040] using wordTrace_append hprefix tailTrace_1472040
  have hstable : (prefixWord ++ tailWord_1472040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472040).length < 2 ^ (prefixWord ++ tailWord_1472040).sum := by decide
  have hdescent : baseEnd_1472040 < baseStart_1472040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472071 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 5]
def baseStart_1472071 : Nat := 118140960795 + 1472071 * 2 ^ 59
def prefixEnd_1472071 : Nat := 4983230072969 + 3 ^ 40 * 1472071 * 2
def baseEnd_1472071 : Nat := 335946658019917888507811

theorem tailTrace_1472071 : CollatzResearch.WordTrace tailWord_1472071 prefixEnd_1472071 335946658019917888507811 := by
  unfold tailWord_1472071
  simp only [CollatzResearch.WordTrace]
  refine ⟨53690840249945651556160067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35793893499963767704106711 53690840249945651556160067)
  ·
    refine ⟨80536260374918477334240101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53690840249945651556160067 80536260374918477334240101)
    ·
      refine ⟨15100548820297214500170019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80536260374918477334240101 15100548820297214500170019)
      ·
        refine ⟨22650823230445821750255029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15100548820297214500170019 22650823230445821750255029)
        ·
          refine ⟨2123514677854295789086409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22650823230445821750255029 2123514677854295789086409)
          ·
            refine ⟨1592636008390721841814807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2123514677854295789086409 1592636008390721841814807)
            ·
              refine ⟨2388954012586082762722211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592636008390721841814807 2388954012586082762722211)
              ·
                refine ⟨3583431018879124144083317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388954012586082762722211 3583431018879124144083317)
                ·
                  refine ⟨335946658019917888507811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3583431018879124144083317 335946658019917888507811)
                  ·
                    rfl

theorem cell21_1472071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 5].length) (baseStart_1472071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472071 prefixEnd_1472071 := by exact prefixLift 1472071
  have htrace : WordTrace (prefixWord ++ tailWord_1472071) baseStart_1472071 baseEnd_1472071 := by
    simpa [prefixWord, tailWord_1472071, baseEnd_1472071] using wordTrace_append hprefix tailTrace_1472071
  have hstable : (prefixWord ++ tailWord_1472071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472071).length < 2 ^ (prefixWord ++ tailWord_1472071).sum := by decide
  have hdescent : baseEnd_1472071 < baseStart_1472071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472127 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 10]
def baseStart_1472127 : Nat := 118140960795 + 1472127 * 2 ^ 59
def prefixEnd_1472127 : Nat := 4983230072969 + 3 ^ 40 * 1472127 * 2
def baseEnd_1472127 : Nat := 335959437982874235574363

theorem tailTrace_1472127 : CollatzResearch.WordTrace tailWord_1472127 prefixEnd_1472127 335959437982874235574363 := by
  unfold tailWord_1472127
  simp only [CollatzResearch.WordTrace]
  refine ⟨53692882737742773120198635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35795255158495182080132423 53692882737742773120198635)
  ·
    refine ⟨80539324106614159680297953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53692882737742773120198635 80539324106614159680297953)
    ·
      refine ⟨60404493079960619760223465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80539324106614159680297953 60404493079960619760223465)
      ·
        refine ⟨45303369809970464820167599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60404493079960619760223465 45303369809970464820167599)
        ·
          refine ⟨67955054714955697230251399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45303369809970464820167599 67955054714955697230251399)
          ·
            refine ⟨101932582072433545845377099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67955054714955697230251399 101932582072433545845377099)
            ·
              refine ⟨152898873108650318768065649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101932582072433545845377099 152898873108650318768065649)
              ·
                refine ⟨114674154831487739076049237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152898873108650318768065649 114674154831487739076049237)
                ·
                  refine ⟨335959437982874235574363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 114674154831487739076049237 335959437982874235574363)
                  ·
                    rfl

theorem cell21_1472127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_1472127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472127 prefixEnd_1472127 := by exact prefixLift 1472127
  have htrace : WordTrace (prefixWord ++ tailWord_1472127) baseStart_1472127 baseEnd_1472127 := by
    simpa [prefixWord, tailWord_1472127, baseEnd_1472127] using wordTrace_append hprefix tailTrace_1472127
  have hstable : (prefixWord ++ tailWord_1472127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472127).length < 2 ^ (prefixWord ++ tailWord_1472127).sum := by decide
  have hdescent : baseEnd_1472127 < baseStart_1472127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472234 : List Nat := [3, 1, 3, 1, 1, 1, 11]
def baseStart_1472234 : Nat := 118140960795 + 1472234 * 2 ^ 59
def prefixEnd_1472234 : Nat := 4983230072969 + 3 ^ 40 * 1472234 * 2
def baseEnd_1472234 : Nat := 37331539648962869698979

theorem tailTrace_1472234 : CollatzResearch.WordTrace tailWord_1472234 prefixEnd_1472234 37331539648962869698979 := by
  unfold tailWord_1472234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13424196337088782598585939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35797856898903420262895837 13424196337088782598585939)
  ·
    refine ⟨20136294505633173897878909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13424196337088782598585939 20136294505633173897878909)
    ·
      refine ⟨7551110439612440211704591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20136294505633173897878909 7551110439612440211704591)
      ·
        refine ⟨11326665659418660317556887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7551110439612440211704591 11326665659418660317556887)
        ·
          refine ⟨16989998489127990476335331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11326665659418660317556887 16989998489127990476335331)
          ·
            refine ⟨25484997733691985714502997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16989998489127990476335331 25484997733691985714502997)
            ·
              refine ⟨37331539648962869698979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25484997733691985714502997 37331539648962869698979)
              ·
                rfl

theorem cell21_1472234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 11].length) (baseStart_1472234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472234 prefixEnd_1472234 := by exact prefixLift 1472234
  have htrace : WordTrace (prefixWord ++ tailWord_1472234) baseStart_1472234 baseEnd_1472234 := by
    simpa [prefixWord, tailWord_1472234, baseEnd_1472234] using wordTrace_append hprefix tailTrace_1472234
  have hstable : (prefixWord ++ tailWord_1472234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472234).length < 2 ^ (prefixWord ++ tailWord_1472234).sum := by decide
  have hdescent : baseEnd_1472234 < baseStart_1472234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472254 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_1472254 : Nat := 118140960795 + 1472254 * 2 ^ 59
def prefixEnd_1472254 : Nat := 4983230072969 + 3 ^ 40 * 1472254 * 2
def baseEnd_1472254 : Nat := 335988421113150236957437

theorem tailTrace_1472254 : CollatzResearch.WordTrace tailWord_1472254 prefixEnd_1472254 335988421113150236957437 := by
  unfold tailWord_1472254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712189351035334226258977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35798343205521782540047877 6712189351035334226258977)
  ·
    refine ⟨5034142013276500669694233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6712189351035334226258977 5034142013276500669694233)
    ·
      refine ⟨3775606509957375502270675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5034142013276500669694233 3775606509957375502270675)
      ·
        refine ⟨5663409764936063253406013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3775606509957375502270675 5663409764936063253406013)
        ·
          refine ⟨2123778661851023720027255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5663409764936063253406013 2123778661851023720027255)
          ·
            refine ⟨3185667992776535580040883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123778661851023720027255 3185667992776535580040883)
            ·
              refine ⟨4778501989164803370061325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3185667992776535580040883 4778501989164803370061325)
              ·
                refine ⟨1791938245936801263772997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4778501989164803370061325 1791938245936801263772997)
                ·
                  refine ⟨335988421113150236957437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1791938245936801263772997 335988421113150236957437)
                  ·
                    rfl

theorem cell21_1472254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_1472254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472254 prefixEnd_1472254 := by exact prefixLift 1472254
  have htrace : WordTrace (prefixWord ++ tailWord_1472254) baseStart_1472254 baseEnd_1472254 := by
    simpa [prefixWord, tailWord_1472254, baseEnd_1472254] using wordTrace_append hprefix tailTrace_1472254
  have hstable : (prefixWord ++ tailWord_1472254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472254).length < 2 ^ (prefixWord ++ tailWord_1472254).sum := by decide
  have hdescent : baseEnd_1472254 < baseStart_1472254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472392 : List Nat := [2, 1, 3, 3, 3, 2, 1, 3, 3]
def baseStart_1472392 : Nat := 118140960795 + 1472392 * 2 ^ 59
def prefixEnd_1472392 : Nat := 4983230072969 + 3 ^ 40 * 1472392 * 2
def baseEnd_1472392 : Nat := 336019914593292663657155

theorem tailTrace_1472392 : CollatzResearch.WordTrace tailWord_1472392 prefixEnd_1472392 336019914593292663657155 := by
  unfold tailWord_1472392
  simp only [CollatzResearch.WordTrace]
  refine ⟨26851274040891361689297715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35801698721188482252396953 26851274040891361689297715)
  ·
    refine ⟨40276911061337042533946573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26851274040891361689297715 40276911061337042533946573)
    ·
      refine ⟨15103841648001390950229965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40276911061337042533946573 15103841648001390950229965)
      ·
        refine ⟨5663940618000521606336237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15103841648001390950229965 5663940618000521606336237)
        ·
          refine ⟨2123977731750195602376089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5663940618000521606336237 2123977731750195602376089)
          ·
            refine ⟨1592983298812646701782067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2123977731750195602376089 1592983298812646701782067)
            ·
              refine ⟨2389474948218970052673101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592983298812646701782067 2389474948218970052673101)
              ·
                refine ⟨896053105582113769752413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2389474948218970052673101 896053105582113769752413)
                ·
                  refine ⟨336019914593292663657155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896053105582113769752413 336019914593292663657155)
                  ·
                    rfl

theorem cell21_1472392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 3].length) (baseStart_1472392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472392 prefixEnd_1472392 := by exact prefixLift 1472392
  have htrace : WordTrace (prefixWord ++ tailWord_1472392) baseStart_1472392 baseEnd_1472392 := by
    simpa [prefixWord, tailWord_1472392, baseEnd_1472392] using wordTrace_append hprefix tailTrace_1472392
  have hstable : (prefixWord ++ tailWord_1472392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472392).length < 2 ^ (prefixWord ++ tailWord_1472392).sum := by decide
  have hdescent : baseEnd_1472392 < baseStart_1472392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472400 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_1472400 : Nat := 118140960795 + 1472400 * 2 ^ 59
def prefixEnd_1472400 : Nat := 4983230072969 + 3 ^ 40 * 1472400 * 2
def baseEnd_1472400 : Nat := 336021740302286427523805

theorem tailTrace_1472400 : CollatzResearch.WordTrace tailWord_1472400 prefixEnd_1472400 336021740302286427523805 := by
  unfold tailWord_1472400
  simp only [CollatzResearch.WordTrace]
  refine ⟨26851419932876870372443327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35801893243835827163257769 26851419932876870372443327)
  ·
    refine ⟨40277129899315305558664991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26851419932876870372443327 40277129899315305558664991)
    ·
      refine ⟨60415694848972958337997487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40277129899315305558664991 60415694848972958337997487)
      ·
        refine ⟨90623542273459437506996231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60415694848972958337997487 90623542273459437506996231)
        ·
          refine ⟨135935313410189156260494347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90623542273459437506996231 135935313410189156260494347)
          ·
            refine ⟨203902970115283734390741521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135935313410189156260494347 203902970115283734390741521)
            ·
              refine ⟨152927227586462800793056141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203902970115283734390741521 152927227586462800793056141)
              ·
                refine ⟨57347710344923550297396053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152927227586462800793056141 57347710344923550297396053)
                ·
                  refine ⟨336021740302286427523805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57347710344923550297396053 336021740302286427523805)
                  ·
                    rfl

theorem cell21_1472400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_1472400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472400 prefixEnd_1472400 := by exact prefixLift 1472400
  have htrace : WordTrace (prefixWord ++ tailWord_1472400) baseStart_1472400 baseEnd_1472400 := by
    simpa [prefixWord, tailWord_1472400, baseEnd_1472400] using wordTrace_append hprefix tailTrace_1472400
  have hstable : (prefixWord ++ tailWord_1472400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472400).length < 2 ^ (prefixWord ++ tailWord_1472400).sum := by decide
  have hdescent : baseEnd_1472400 < baseStart_1472400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472479 : List Nat := [1, 1, 2, 3, 4, 3, 1, 6]
def baseStart_1472479 : Nat := 118140960795 + 1472479 * 2 ^ 59
def prefixEnd_1472479 : Nat := 4983230072969 + 3 ^ 40 * 1472479 * 2
def baseEnd_1472479 : Nat := 112013256392866615235659

theorem tailTrace_1472479 : CollatzResearch.WordTrace tailWord_1472479 prefixEnd_1472479 112013256392866615235659 := by
  unfold tailWord_1472479
  simp only [CollatzResearch.WordTrace]
  refine ⟨53705721232467537237012491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35803814154978358158008327 53705721232467537237012491)
  ·
    refine ⟨80558581848701305855518737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53705721232467537237012491 80558581848701305855518737)
    ·
      refine ⟨60418936386525979391639053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80558581848701305855518737 60418936386525979391639053)
      ·
        refine ⟨22657101144947242271864645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60418936386525979391639053 22657101144947242271864645)
        ·
          refine ⟨4248206464677607925974621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22657101144947242271864645 4248206464677607925974621)
          ·
            refine ⟨1593077424254102972240483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4248206464677607925974621 1593077424254102972240483)
            ·
              refine ⟨2389616136381154458360725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1593077424254102972240483 2389616136381154458360725)
              ·
                refine ⟨112013256392866615235659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2389616136381154458360725 112013256392866615235659)
                ·
                  rfl

theorem cell21_1472479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 6].length) (baseStart_1472479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472479 prefixEnd_1472479 := by exact prefixLift 1472479
  have htrace : WordTrace (prefixWord ++ tailWord_1472479) baseStart_1472479 baseEnd_1472479 := by
    simpa [prefixWord, tailWord_1472479, baseEnd_1472479] using wordTrace_append hprefix tailTrace_1472479
  have hstable : (prefixWord ++ tailWord_1472479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472479).length < 2 ^ (prefixWord ++ tailWord_1472479).sum := by decide
  have hdescent : baseEnd_1472479 < baseStart_1472479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
