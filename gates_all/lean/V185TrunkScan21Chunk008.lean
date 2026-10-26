import V185TrunkScan21Chunk007

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_95950 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_95950 : Nat := 118140960795 + 95950 * 2 ^ 59
def prefixEnd_95950 : Nat := 4983230072969 + 3 ^ 40 * 95950 * 2
def baseEnd_95950 : Nat := 21897097244002146170551

theorem tailTrace_95950 : CollatzResearch.WordTrace tailWord_95950 prefixEnd_95950 21897097244002146170551 := by
  unfold tailWord_95950
  simp only [CollatzResearch.WordTrace]
  refine ⟨437448000299626475059663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2333056001598007866984869 437448000299626475059663)
  ·
    refine ⟨656172000449439712589495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437448000299626475059663 656172000449439712589495)
    ·
      refine ⟨984258000674159568884243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 656172000449439712589495 984258000674159568884243)
      ·
        refine ⟨1476387001011239353326365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 984258000674159568884243 1476387001011239353326365)
        ·
          refine ⟨553645125379214757497387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1476387001011239353326365 553645125379214757497387)
          ·
            refine ⟨830467688068822136246081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553645125379214757497387 830467688068822136246081)
            ·
              refine ⟨622850766051616602184561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830467688068822136246081 622850766051616602184561)
              ·
                refine ⟨467138074538712451638421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622850766051616602184561 467138074538712451638421)
                ·
                  refine ⟨21897097244002146170551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 467138074538712451638421 21897097244002146170551)
                  ·
                    rfl

theorem cell21_95950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_95950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95950 prefixEnd_95950 := by exact prefixLift 95950
  have htrace : WordTrace (prefixWord ++ tailWord_95950) baseStart_95950 baseEnd_95950 := by
    simpa [prefixWord, tailWord_95950, baseEnd_95950] using wordTrace_append hprefix tailTrace_95950
  have hstable : (prefixWord ++ tailWord_95950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95950).length < 2 ^ (prefixWord ++ tailWord_95950).sum := by decide
  have hdescent : baseEnd_95950 < baseStart_95950 := by decide
  rcases family_descends (prefixWord ++ tailWord_95950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95953 : List Nat := [1, 2, 2, 1, 2, 5, 2, 3, 3]
def baseStart_95953 : Nat := 118140960795 + 95953 * 2 ^ 59
def prefixEnd_95953 : Nat := 4983230072969 + 3 ^ 40 * 95953 * 2
def baseEnd_95953 : Nat := 21897781884874807620545

theorem tailTrace_95953 : CollatzResearch.WordTrace tailWord_95953 prefixEnd_95953 21897781884874807620545 := by
  unfold tailWord_95953
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499693421386143312836513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2333128947590762208557675 3499693421386143312836513)
  ·
    refine ⟨2624770066039607484627385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3499693421386143312836513 2624770066039607484627385)
    ·
      refine ⟨1968577549529705613470539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2624770066039607484627385 1968577549529705613470539)
      ·
        refine ⟨2952866324294558420205809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968577549529705613470539 2952866324294558420205809)
        ·
          refine ⟨2214649743220918815154357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2952866324294558420205809 2214649743220918815154357)
          ·
            refine ⟨207623413426961138920721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2214649743220918815154357 207623413426961138920721)
            ·
              refine ⟨155717560070220854190541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207623413426961138920721 155717560070220854190541)
              ·
                refine ⟨58394085026332820321453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155717560070220854190541 58394085026332820321453)
                ·
                  refine ⟨21897781884874807620545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58394085026332820321453 21897781884874807620545)
                  ·
                    rfl

theorem cell21_95953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 3].length) (baseStart_95953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95953 prefixEnd_95953 := by exact prefixLift 95953
  have htrace : WordTrace (prefixWord ++ tailWord_95953) baseStart_95953 baseEnd_95953 := by
    simpa [prefixWord, tailWord_95953, baseEnd_95953] using wordTrace_append hprefix tailTrace_95953
  have hstable : (prefixWord ++ tailWord_95953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95953).length < 2 ^ (prefixWord ++ tailWord_95953).sum := by decide
  have hdescent : baseEnd_95953 < baseStart_95953 := by decide
  rcases family_descends (prefixWord ++ tailWord_95953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95998 : List Nat := [4, 2, 2, 1, 3, 1, 1, 7]
def baseStart_95998 : Nat := 118140960795 + 95998 * 2 ^ 59
def prefixEnd_95998 : Nat := 4983230072969 + 3 ^ 40 * 95998 * 2
def baseEnd_95998 : Nat := 7302683832654909790151

theorem tailTrace_95998 : CollatzResearch.WordTrace tailWord_95998 prefixEnd_95998 7302683832654909790151 := by
  unfold tailWord_95998
  simp only [CollatzResearch.WordTrace]
  refine ⟨437666838277889499778081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2334223137482077332149765 437666838277889499778081)
  ·
    refine ⟨328250128708417124833561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 437666838277889499778081 328250128708417124833561)
    ·
      refine ⟨246187596531312843625171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328250128708417124833561 246187596531312843625171)
      ·
        refine ⟨369281394796969265437757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246187596531312843625171 369281394796969265437757)
        ·
          refine ⟨138480523048863474539159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369281394796969265437757 138480523048863474539159)
          ·
            refine ⟨207720784573295211808739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138480523048863474539159 207720784573295211808739)
            ·
              refine ⟨311581176859942817713109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207720784573295211808739 311581176859942817713109)
              ·
                refine ⟨7302683832654909790151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 311581176859942817713109 7302683832654909790151)
                ·
                  rfl

theorem cell21_95998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_95998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95998 prefixEnd_95998 := by exact prefixLift 95998
  have htrace : WordTrace (prefixWord ++ tailWord_95998) baseStart_95998 baseEnd_95998 := by
    simpa [prefixWord, tailWord_95998, baseEnd_95998] using wordTrace_append hprefix tailTrace_95998
  have hstable : (prefixWord ++ tailWord_95998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95998).length < 2 ^ (prefixWord ++ tailWord_95998).sum := by decide
  have hdescent : baseEnd_95998 < baseStart_95998 := by decide
  rcases family_descends (prefixWord ++ tailWord_95998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96026 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_96026 : Nat := 118140960795 + 96026 * 2 ^ 59
def prefixEnd_96026 : Nat := 4983230072969 + 3 ^ 40 * 96026 * 2
def baseEnd_96026 : Nat := 21914441479442902903729

theorem tailTrace_96026 : CollatzResearch.WordTrace tailWord_96026 prefixEnd_96026 21914441479442902903729 := by
  unfold tailWord_96026
  simp only [CollatzResearch.WordTrace]
  refine ⟨875588987530419195060983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2334903966747784520162621 875588987530419195060983)
  ·
    refine ⟨1313383481295628792591475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 875588987530419195060983 1313383481295628792591475)
    ·
      refine ⟨1970075221943443188887213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1313383481295628792591475 1970075221943443188887213)
      ·
        refine ⟨738778208228791195832705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1970075221943443188887213 738778208228791195832705)
        ·
          refine ⟨554083656171593396874529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738778208228791195832705 554083656171593396874529)
          ·
            refine ⟨415562742128695047655897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554083656171593396874529 415562742128695047655897)
            ·
              refine ⟨311672056596521285741923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415562742128695047655897 311672056596521285741923)
              ·
                refine ⟨467508084894781928612885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311672056596521285741923 467508084894781928612885)
                ·
                  refine ⟨21914441479442902903729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 467508084894781928612885 21914441479442902903729)
                  ·
                    rfl

theorem cell21_96026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_96026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96026 prefixEnd_96026 := by exact prefixLift 96026
  have htrace : WordTrace (prefixWord ++ tailWord_96026) baseStart_96026 baseEnd_96026 := by
    simpa [prefixWord, tailWord_96026, baseEnd_96026] using wordTrace_append hprefix tailTrace_96026
  have hstable : (prefixWord ++ tailWord_96026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96026).length < 2 ^ (prefixWord ++ tailWord_96026).sum := by decide
  have hdescent : baseEnd_96026 < baseStart_96026 := by decide
  rcases family_descends (prefixWord ++ tailWord_96026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96136 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 4]
def baseStart_96136 : Nat := 118140960795 + 96136 * 2 ^ 59
def prefixEnd_96136 : Nat := 4983230072969 + 3 ^ 40 * 96136 * 2
def baseEnd_96136 : Nat := 21939544978107156070171

theorem tailTrace_96136 : CollatzResearch.WordTrace tailWord_96136 prefixEnd_96136 21939544978107156070171 := by
  unfold tailWord_96136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753183989861582783374131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2337578653148777044498841 1753183989861582783374131)
  ·
    refine ⟨2629775984792374175061197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1753183989861582783374131 2629775984792374175061197)
    ·
      refine ⟨986165994297140315647949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2629775984792374175061197 986165994297140315647949)
      ·
        refine ⟨369812247861427618367981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 986165994297140315647949 369812247861427618367981)
        ·
          refine ⟨138679592948035356887993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369812247861427618367981 138679592948035356887993)
          ·
            refine ⟨104009694711026517665995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138679592948035356887993 104009694711026517665995)
            ·
              refine ⟨156014542066539776498993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104009694711026517665995 156014542066539776498993)
              ·
                refine ⟨117010906549904832374245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156014542066539776498993 117010906549904832374245)
                ·
                  refine ⟨21939544978107156070171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117010906549904832374245 21939544978107156070171)
                  ·
                    rfl

theorem cell21_96136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_96136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96136 prefixEnd_96136 := by exact prefixLift 96136
  have htrace : WordTrace (prefixWord ++ tailWord_96136) baseStart_96136 baseEnd_96136 := by
    simpa [prefixWord, tailWord_96136, baseEnd_96136] using wordTrace_append hprefix tailTrace_96136
  have hstable : (prefixWord ++ tailWord_96136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96136).length < 2 ^ (prefixWord ++ tailWord_96136).sum := by decide
  have hdescent : baseEnd_96136 < baseStart_96136 := by decide
  rcases family_descends (prefixWord ++ tailWord_96136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96181 : List Nat := [1, 3, 3, 2, 1, 2, 3, 3, 3]
def baseStart_96181 : Nat := 118140960795 + 96181 * 2 ^ 59
def prefixEnd_96181 : Nat := 4983230072969 + 3 ^ 40 * 96181 * 2
def baseEnd_96181 : Nat := 21949814591197077820079

theorem tailTrace_96181 : CollatzResearch.WordTrace tailWord_96181 prefixEnd_96181 21949814591197077820079 := by
  unfold tailWord_96181
  simp only [CollatzResearch.WordTrace]
  refine ⟨3508009264560138252136397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2338672843040092168090931 3508009264560138252136397)
  ·
    refine ⟨1315503474210051844551149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3508009264560138252136397 1315503474210051844551149)
    ·
      refine ⟨493313802828769441706681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1315503474210051844551149 493313802828769441706681)
      ·
        refine ⟨369985352121577081280011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493313802828769441706681 369985352121577081280011)
        ·
          refine ⟨554978028182365621920017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369985352121577081280011 554978028182365621920017)
          ·
            refine ⟨416233521136774216440013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554978028182365621920017 416233521136774216440013)
            ·
              refine ⟨156087570426290331165005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 416233521136774216440013 156087570426290331165005)
              ·
                refine ⟨58532838909858874186877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156087570426290331165005 58532838909858874186877)
                ·
                  refine ⟨21949814591197077820079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58532838909858874186877 21949814591197077820079)
                  ·
                    rfl

theorem cell21_96181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_96181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96181 prefixEnd_96181 := by exact prefixLift 96181
  have htrace : WordTrace (prefixWord ++ tailWord_96181) baseStart_96181 baseEnd_96181 := by
    simpa [prefixWord, tailWord_96181, baseEnd_96181] using wordTrace_append hprefix tailTrace_96181
  have hstable : (prefixWord ++ tailWord_96181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96181).length < 2 ^ (prefixWord ++ tailWord_96181).sum := by decide
  have hdescent : baseEnd_96181 < baseStart_96181 := by decide
  rcases family_descends (prefixWord ++ tailWord_96181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96316 : List Nat := [2, 2, 2, 2, 2, 1, 1, 6, 3]
def baseStart_96316 : Nat := 118140960795 + 96316 * 2 ^ 59
def prefixEnd_96316 : Nat := 4983230072969 + 3 ^ 40 * 96316 * 2
def baseEnd_96316 : Nat := 21980623430466843069803

theorem tailTrace_96316 : CollatzResearch.WordTrace tailWord_96316 prefixEnd_96316 21980623430466843069803 := by
  unfold tailWord_96316
  simp only [CollatzResearch.WordTrace]
  refine ⟨1756466559535528154150401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2341955412714037538867201 1756466559535528154150401)
  ·
    refine ⟨1317349919651646115612801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1756466559535528154150401 1317349919651646115612801)
    ·
      refine ⟨988012439738734586709601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1317349919651646115612801 988012439738734586709601)
      ·
        refine ⟨741009329804050940032201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 988012439738734586709601 741009329804050940032201)
        ·
          refine ⟨555756997353038205024151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 741009329804050940032201 555756997353038205024151)
          ·
            refine ⟨833635496029557307536227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555756997353038205024151 833635496029557307536227)
            ·
              refine ⟨1250453244044335961304341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833635496029557307536227 1250453244044335961304341)
              ·
                refine ⟨58614995814578248186141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1250453244044335961304341 58614995814578248186141)
                ·
                  refine ⟨21980623430466843069803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58614995814578248186141 21980623430466843069803)
                  ·
                    rfl

theorem cell21_96316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_96316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96316 prefixEnd_96316 := by exact prefixLift 96316
  have htrace : WordTrace (prefixWord ++ tailWord_96316) baseStart_96316 baseEnd_96316 := by
    simpa [prefixWord, tailWord_96316, baseEnd_96316] using wordTrace_append hprefix tailTrace_96316
  have hstable : (prefixWord ++ tailWord_96316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96316).length < 2 ^ (prefixWord ++ tailWord_96316).sum := by decide
  have hdescent : baseEnd_96316 < baseStart_96316 := by decide
  rcases family_descends (prefixWord ++ tailWord_96316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96344 : List Nat := [2, 1, 2, 2, 1, 5, 1, 7]
def baseStart_96344 : Nat := 118140960795 + 96344 * 2 ^ 59
def prefixEnd_96344 : Nat := 4983230072969 + 3 ^ 40 * 96344 * 2
def baseEnd_96344 : Nat := 7329004470648338867693

theorem tailTrace_96344 : CollatzResearch.WordTrace tailWord_96344 prefixEnd_96344 7329004470648338867693 := by
  unfold tailWord_96344
  simp only [CollatzResearch.WordTrace]
  refine ⟨1756977181484808545160043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2342636241979744726880057 1756977181484808545160043)
  ·
    refine ⟨2635465772227212817740065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1756977181484808545160043 2635465772227212817740065)
    ·
      refine ⟨1976599329170409613305049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2635465772227212817740065 1976599329170409613305049)
      ·
        refine ⟨1482449496877807209978787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1976599329170409613305049 1482449496877807209978787)
        ·
          refine ⟨2223674245316710814968181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482449496877807209978787 2223674245316710814968181)
          ·
            refine ⟨208469460498441638903267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2223674245316710814968181 208469460498441638903267)
            ·
              refine ⟨312704190747662458354901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208469460498441638903267 312704190747662458354901)
              ·
                refine ⟨7329004470648338867693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 312704190747662458354901 7329004470648338867693)
                ·
                  rfl

theorem cell21_96344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_96344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96344 prefixEnd_96344 := by exact prefixLift 96344
  have htrace : WordTrace (prefixWord ++ tailWord_96344) baseStart_96344 baseEnd_96344 := by
    simpa [prefixWord, tailWord_96344, baseEnd_96344] using wordTrace_append hprefix tailTrace_96344
  have hstable : (prefixWord ++ tailWord_96344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96344).length < 2 ^ (prefixWord ++ tailWord_96344).sum := by decide
  have hdescent : baseEnd_96344 < baseStart_96344 := by decide
  rcases family_descends (prefixWord ++ tailWord_96344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96375 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 5]
def baseStart_96375 : Nat := 118140960795 + 96375 * 2 ^ 59
def prefixEnd_96375 : Nat := 4983230072969 + 3 ^ 40 * 96375 * 2
def baseEnd_96375 : Nat := 21994088034295851586349

theorem tailTrace_96375 : CollatzResearch.WordTrace tailWord_96375 prefixEnd_96375 21994088034295851586349 := by
  unfold tailWord_96375
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515085025857309384698579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2343390017238206256465719 3515085025857309384698579)
  ·
    refine ⟨5272627538785964077047869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3515085025857309384698579 5272627538785964077047869)
    ·
      refine ⟨1977235327044736528892951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5272627538785964077047869 1977235327044736528892951)
      ·
        refine ⟨2965852990567104793339427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1977235327044736528892951 2965852990567104793339427)
        ·
          refine ⟨4448779485850657190009141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2965852990567104793339427 4448779485850657190009141)
          ·
            refine ⟨417073076798499111563357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4448779485850657190009141 417073076798499111563357)
            ·
              refine ⟨156402403799437166836259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417073076798499111563357 156402403799437166836259)
              ·
                refine ⟨234603605699155750254389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156402403799437166836259 234603605699155750254389)
                ·
                  refine ⟨21994088034295851586349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 234603605699155750254389 21994088034295851586349)
                  ·
                    rfl

theorem cell21_96375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 5].length) (baseStart_96375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96375 prefixEnd_96375 := by exact prefixLift 96375
  have htrace : WordTrace (prefixWord ++ tailWord_96375) baseStart_96375 baseEnd_96375 := by
    simpa [prefixWord, tailWord_96375, baseEnd_96375] using wordTrace_append hprefix tailTrace_96375
  have hstable : (prefixWord ++ tailWord_96375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96375).length < 2 ^ (prefixWord ++ tailWord_96375).sum := by decide
  have hdescent : baseEnd_96375 < baseStart_96375 := by decide
  rcases family_descends (prefixWord ++ tailWord_96375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96420 : List Nat := [2, 3, 1, 2, 4, 9]
def baseStart_96420 : Nat := 118140960795 + 96420 * 2 ^ 59
def prefixEnd_96420 : Nat := 4983230072969 + 3 ^ 40 * 96420 * 2
def baseEnd_96420 : Nat := 814976209162436049491

theorem tailTrace_96420 : CollatzResearch.WordTrace tailWord_96420 prefixEnd_96420 814976209162436049491 := by
  unfold tailWord_96420
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758363155347141035043357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2344484207129521380057809 1758363155347141035043357)
  ·
    refine ⟨659386183255177888141259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1758363155347141035043357 659386183255177888141259)
    ·
      refine ⟨989079274882766832211889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 659386183255177888141259 989079274882766832211889)
      ·
        refine ⟨741809456162075124158917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 989079274882766832211889 741809456162075124158917)
        ·
          refine ⟨139089273030389085779797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 741809456162075124158917 139089273030389085779797)
          ·
            refine ⟨814976209162436049491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 139089273030389085779797 814976209162436049491)
            ·
              rfl

theorem cell21_96420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 9].length) (baseStart_96420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96420 prefixEnd_96420 := by exact prefixLift 96420
  have htrace : WordTrace (prefixWord ++ tailWord_96420) baseStart_96420 baseEnd_96420 := by
    simpa [prefixWord, tailWord_96420, baseEnd_96420] using wordTrace_append hprefix tailTrace_96420
  have hstable : (prefixWord ++ tailWord_96420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96420).length < 2 ^ (prefixWord ++ tailWord_96420).sum := by decide
  have hdescent : baseEnd_96420 < baseStart_96420 := by decide
  rcases family_descends (prefixWord ++ tailWord_96420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96426 : List Nat := [3, 1, 5, 1, 2, 1, 1, 4, 3]
def baseStart_96426 : Nat := 118140960795 + 96426 * 2 ^ 59
def prefixEnd_96426 : Nat := 4983230072969 + 3 ^ 40 * 96426 * 2
def baseEnd_96426 : Nat := 22005726929131096236245

theorem tailTrace_96426 : CollatzResearch.WordTrace tailWord_96426 prefixEnd_96426 22005726929131096236245 := by
  unfold tailWord_96426
  simp only [CollatzResearch.WordTrace]
  refine ⟨879236287168136273701283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2344630099115030063203421 879236287168136273701283)
  ·
    refine ⟨1318854430752204410551925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 879236287168136273701283 1318854430752204410551925)
    ·
      refine ⟨123642602883019163489243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1318854430752204410551925 123642602883019163489243)
      ·
        refine ⟨185463904324528745233865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123642602883019163489243 185463904324528745233865)
        ·
          refine ⟨139097928243396558925399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185463904324528745233865 139097928243396558925399)
          ·
            refine ⟨208646892365094838388099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139097928243396558925399 208646892365094838388099)
            ·
              refine ⟨312970338547642257582149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208646892365094838388099 312970338547642257582149)
              ·
                refine ⟨58681938477682923296653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312970338547642257582149 58681938477682923296653)
                ·
                  refine ⟨22005726929131096236245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58681938477682923296653 22005726929131096236245)
                  ·
                    rfl

theorem cell21_96426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_96426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96426 prefixEnd_96426 := by exact prefixLift 96426
  have htrace : WordTrace (prefixWord ++ tailWord_96426) baseStart_96426 baseEnd_96426 := by
    simpa [prefixWord, tailWord_96426, baseEnd_96426] using wordTrace_append hprefix tailTrace_96426
  have hstable : (prefixWord ++ tailWord_96426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96426).length < 2 ^ (prefixWord ++ tailWord_96426).sum := by decide
  have hdescent : baseEnd_96426 < baseStart_96426 := by decide
  rcases family_descends (prefixWord ++ tailWord_96426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96519 : List Nat := [1, 1, 4, 5, 2, 1, 1, 3, 3]
def baseStart_96519 : Nat := 118140960795 + 96519 * 2 ^ 59
def prefixEnd_96519 : Nat := 4983230072969 + 3 ^ 40 * 96519 * 2
def baseEnd_96519 : Nat := 22026950796183601186055

theorem tailTrace_96519 : CollatzResearch.WordTrace tailWord_96519 prefixEnd_96519 22026950796183601186055 := by
  unfold tailWord_96519
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520337137335621977940611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2346891424890414651960407 3520337137335621977940611)
  ·
    refine ⟨5280505706003432966910917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3520337137335621977940611 5280505706003432966910917)
    ·
      refine ⟨990094819875643681295797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5280505706003432966910917 990094819875643681295797)
      ·
        refine ⟨92821389363341595121481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 990094819875643681295797 92821389363341595121481)
        ·
          refine ⟨69616042022506196341111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92821389363341595121481 69616042022506196341111)
          ·
            refine ⟨104424063033759294511667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69616042022506196341111 104424063033759294511667)
            ·
              refine ⟨156636094550638941767501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104424063033759294511667 156636094550638941767501)
              ·
                refine ⟨58738535456489603162813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156636094550638941767501 58738535456489603162813)
                ·
                  refine ⟨22026950796183601186055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58738535456489603162813 22026950796183601186055)
                  ·
                    rfl

theorem cell21_96519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 3].length) (baseStart_96519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96519 prefixEnd_96519 := by exact prefixLift 96519
  have htrace : WordTrace (prefixWord ++ tailWord_96519) baseStart_96519 baseEnd_96519 := by
    simpa [prefixWord, tailWord_96519, baseEnd_96519] using wordTrace_append hprefix tailTrace_96519
  have hstable : (prefixWord ++ tailWord_96519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96519).length < 2 ^ (prefixWord ++ tailWord_96519).sum := by decide
  have hdescent : baseEnd_96519 < baseStart_96519 := by decide
  rcases family_descends (prefixWord ++ tailWord_96519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96544 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 5]
def baseStart_96544 : Nat := 118140960795 + 96544 * 2 ^ 59
def prefixEnd_96544 : Nat := 4983230072969 + 3 ^ 40 * 96544 * 2
def baseEnd_96544 : Nat := 22032656136789113269337

theorem tailTrace_96544 : CollatzResearch.WordTrace tailWord_96544 prefixEnd_96544 22032656136789113269337 := by
  unfold tailWord_96544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760624481122525623800343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2347499308163367498400457 1760624481122525623800343)
  ·
    refine ⟨2640936721683788435700515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1760624481122525623800343 2640936721683788435700515)
    ·
      refine ⟨3961405082525682653550773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2640936721683788435700515 3961405082525682653550773)
      ·
        refine ⟨371381726486782748770385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3961405082525682653550773 371381726486782748770385)
        ·
          refine ⟨278536294865087061577789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371381726486782748770385 278536294865087061577789)
          ·
            refine ⟨104451110574407648091671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278536294865087061577789 104451110574407648091671)
            ·
              refine ⟨156676665861611472137507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104451110574407648091671 156676665861611472137507)
              ·
                refine ⟨235014998792417208206261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156676665861611472137507 235014998792417208206261)
                ·
                  refine ⟨22032656136789113269337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235014998792417208206261 22032656136789113269337)
                  ·
                    rfl

theorem cell21_96544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_96544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96544 prefixEnd_96544 := by exact prefixLift 96544
  have htrace : WordTrace (prefixWord ++ tailWord_96544) baseStart_96544 baseEnd_96544 := by
    simpa [prefixWord, tailWord_96544, baseEnd_96544] using wordTrace_append hprefix tailTrace_96544
  have hstable : (prefixWord ++ tailWord_96544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96544).length < 2 ^ (prefixWord ++ tailWord_96544).sum := by decide
  have hdescent : baseEnd_96544 < baseStart_96544 := by decide
  rcases family_descends (prefixWord ++ tailWord_96544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96617 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 4]
def baseStart_96617 : Nat := 118140960795 + 96617 * 2 ^ 59
def prefixEnd_96617 : Nat := 4983230072969 + 3 ^ 40 * 96617 * 2
def baseEnd_96617 : Nat := 22049315731357208552521

theorem tailTrace_96617 : CollatzResearch.WordTrace tailWord_96617 prefixEnd_96617 22049315731357208552521 := by
  unfold tailWord_96617
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523911490980584715008105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2349274327320389810005403 3523911490980584715008105)
  ·
    refine ⟨2642933618235438536256079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3523911490980584715008105 2642933618235438536256079)
    ·
      refine ⟨3964400427353157804384119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2642933618235438536256079 3964400427353157804384119)
      ·
        refine ⟨5946600641029736706576179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3964400427353157804384119 5946600641029736706576179)
        ·
          refine ⟨8919900961544605059864269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5946600641029736706576179 8919900961544605059864269)
          ·
            refine ⟨3344962860579226897449101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8919900961544605059864269 3344962860579226897449101)
            ·
              refine ⟨1254361072717210086543413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3344962860579226897449101 1254361072717210086543413)
              ·
                refine ⟨117596350567238445613445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1254361072717210086543413 117596350567238445613445)
                ·
                  refine ⟨22049315731357208552521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117596350567238445613445 22049315731357208552521)
                  ·
                    rfl

theorem cell21_96617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_96617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96617 prefixEnd_96617 := by exact prefixLift 96617
  have htrace : WordTrace (prefixWord ++ tailWord_96617) baseStart_96617 baseEnd_96617 := by
    simpa [prefixWord, tailWord_96617, baseEnd_96617] using wordTrace_append hprefix tailTrace_96617
  have hstable : (prefixWord ++ tailWord_96617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96617).length < 2 ^ (prefixWord ++ tailWord_96617).sum := by decide
  have hdescent : baseEnd_96617 < baseStart_96617 := by decide
  rcases family_descends (prefixWord ++ tailWord_96617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96679 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 5]
def baseStart_96679 : Nat := 118140960795 + 96679 * 2 ^ 59
def prefixEnd_96679 : Nat := 4983230072969 + 3 ^ 40 * 96679 * 2
def baseEnd_96679 : Nat := 22063464976058878519061

theorem tailTrace_96679 : CollatzResearch.WordTrace tailWord_96679 prefixEnd_96679 22063464976058878519061 := by
  unfold tailWord_96679
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526172816755969303765091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2350781877837312869176727 3526172816755969303765091)
  ·
    refine ⟨5289259225133953955647637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3526172816755969303765091 5289259225133953955647637)
    ·
      refine ⟨247934026178154091670983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5289259225133953955647637 247934026178154091670983)
      ·
        refine ⟨371901039267231137506475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247934026178154091670983 371901039267231137506475)
        ·
          refine ⟨557851558900846706259713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371901039267231137506475 557851558900846706259713)
          ·
            refine ⟨418388669175635029694785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557851558900846706259713 418388669175635029694785)
            ·
              refine ⟨313791501881726272271089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418388669175635029694785 313791501881726272271089)
              ·
                refine ⟨235343626411294704203317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313791501881726272271089 235343626411294704203317)
                ·
                  refine ⟨22063464976058878519061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235343626411294704203317 22063464976058878519061)
                  ·
                    rfl

theorem cell21_96679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_96679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96679 prefixEnd_96679 := by exact prefixLift 96679
  have htrace : WordTrace (prefixWord ++ tailWord_96679) baseStart_96679 baseEnd_96679 := by
    simpa [prefixWord, tailWord_96679, baseEnd_96679] using wordTrace_append hprefix tailTrace_96679
  have hstable : (prefixWord ++ tailWord_96679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96679).length < 2 ^ (prefixWord ++ tailWord_96679).sum := by decide
  have hdescent : baseEnd_96679 < baseStart_96679 := by decide
  rcases family_descends (prefixWord ++ tailWord_96679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96724 : List Nat := [2, 4, 1, 2, 2, 1, 1, 8]
def baseStart_96724 : Nat := 118140960795 + 96724 * 2 ^ 59
def prefixEnd_96724 : Nat := 4983230072969 + 3 ^ 40 * 96724 * 2
def baseEnd_96724 : Nat := 7357911529716266756323

theorem tailTrace_96724 : CollatzResearch.WordTrace tailWord_96724 prefixEnd_96724 7357911529716266756323 := by
  unfold tailWord_96724
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763907050796470994576613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2351876067728627992768817 1763907050796470994576613)
  ·
    refine ⟨330732572024338311483115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1763907050796470994576613 330732572024338311483115)
    ·
      refine ⟨496098858036507467224673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330732572024338311483115 496098858036507467224673)
      ·
        refine ⟨372074143527380600418505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496098858036507467224673 372074143527380600418505)
        ·
          refine ⟨279055607645535450313879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372074143527380600418505 279055607645535450313879)
          ·
            refine ⟨418583411468303175470819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279055607645535450313879 418583411468303175470819)
            ·
              refine ⟨627875117202454763206229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418583411468303175470819 627875117202454763206229)
              ·
                refine ⟨7357911529716266756323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 627875117202454763206229 7357911529716266756323)
                ·
                  rfl

theorem cell21_96724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_96724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96724 prefixEnd_96724 := by exact prefixLift 96724
  have htrace : WordTrace (prefixWord ++ tailWord_96724) baseStart_96724 baseEnd_96724 := by
    simpa [prefixWord, tailWord_96724, baseEnd_96724] using wordTrace_append hprefix tailTrace_96724
  have hstable : (prefixWord ++ tailWord_96724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96724).length < 2 ^ (prefixWord ++ tailWord_96724).sum := by decide
  have hdescent : baseEnd_96724 < baseStart_96724 := by decide
  rcases family_descends (prefixWord ++ tailWord_96724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96755 : List Nat := [1, 1, 1, 2, 2, 2, 4, 5, 3]
def baseStart_96755 : Nat := 118140960795 + 96755 * 2 ^ 59
def prefixEnd_96755 : Nat := 4983230072969 + 3 ^ 40 * 96755 * 2
def baseEnd_96755 : Nat := 22080809211499635252239

theorem tailTrace_96755 : CollatzResearch.WordTrace tailWord_96755 prefixEnd_96755 22080809211499635252239 := by
  unfold tailWord_96755
  simp only [CollatzResearch.WordTrace]
  refine ⟨3528944764480634283531719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2352629842987089522354479 3528944764480634283531719)
  ·
    refine ⟨5293417146720951425297579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3528944764480634283531719 5293417146720951425297579)
    ·
      refine ⟨7940125720081427137946369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5293417146720951425297579 7940125720081427137946369)
      ·
        refine ⟨5955094290061070353459777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7940125720081427137946369 5955094290061070353459777)
        ·
          refine ⟨4466320717545802765094833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5955094290061070353459777 4466320717545802765094833)
          ·
            refine ⟨3349740538159352073821125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4466320717545802765094833 3349740538159352073821125)
            ·
              refine ⟨628076350904878513841461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3349740538159352073821125 628076350904878513841461)
              ·
                refine ⟨58882157897332360672637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 628076350904878513841461 58882157897332360672637)
                ·
                  refine ⟨22080809211499635252239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58882157897332360672637 22080809211499635252239)
                  ·
                    rfl

theorem cell21_96755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 3].length) (baseStart_96755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96755 prefixEnd_96755 := by exact prefixLift 96755
  have htrace : WordTrace (prefixWord ++ tailWord_96755) baseStart_96755 baseEnd_96755 := by
    simpa [prefixWord, tailWord_96755, baseEnd_96755] using wordTrace_append hprefix tailTrace_96755
  have hstable : (prefixWord ++ tailWord_96755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96755).length < 2 ^ (prefixWord ++ tailWord_96755).sum := by decide
  have hdescent : baseEnd_96755 < baseStart_96755 := by decide
  rcases family_descends (prefixWord ++ tailWord_96755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96831 : List Nat := [1, 1, 2, 2, 3, 2, 1, 6, 3]
def baseStart_96831 : Nat := 118140960795 + 96831 * 2 ^ 59
def prefixEnd_96831 : Nat := 4983230072969 + 3 ^ 40 * 96831 * 2
def baseEnd_96831 : Nat := 22098153446940391985417

theorem tailTrace_96831 : CollatzResearch.WordTrace tailWord_96831 prefixEnd_96831 22098153446940391985417 := by
  unfold tailWord_96831
  simp only [CollatzResearch.WordTrace]
  refine ⟨3531716712205299263298347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2354477808136866175532231 3531716712205299263298347)
  ·
    refine ⟨5297575068307948894947521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3531716712205299263298347 5297575068307948894947521)
    ·
      refine ⟨3973181301230961671210641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5297575068307948894947521 3973181301230961671210641)
      ·
        refine ⟨2979885975923221253407981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3973181301230961671210641 2979885975923221253407981)
        ·
          refine ⟨1117457240971207970027993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2979885975923221253407981 1117457240971207970027993)
          ·
            refine ⟨838092930728405977520995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1117457240971207970027993 838092930728405977520995)
            ·
              refine ⟨1257139396092608966281493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838092930728405977520995 1257139396092608966281493)
              ·
                refine ⟨58928409191841045294445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1257139396092608966281493 58928409191841045294445)
                ·
                  refine ⟨22098153446940391985417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58928409191841045294445 22098153446940391985417)
                  ·
                    rfl

theorem cell21_96831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 3].length) (baseStart_96831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96831 prefixEnd_96831 := by exact prefixLift 96831
  have htrace : WordTrace (prefixWord ++ tailWord_96831) baseStart_96831 baseEnd_96831 := by
    simpa [prefixWord, tailWord_96831, baseEnd_96831] using wordTrace_append hprefix tailTrace_96831
  have hstable : (prefixWord ++ tailWord_96831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96831).length < 2 ^ (prefixWord ++ tailWord_96831).sum := by decide
  have hdescent : baseEnd_96831 < baseStart_96831 := by decide
  rcases family_descends (prefixWord ++ tailWord_96831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96941 : List Nat := [1, 5, 2, 1, 1, 2, 4, 2, 3]
def baseStart_96941 : Nat := 118140960795 + 96941 * 2 ^ 59
def prefixEnd_96941 : Nat := 4983230072969 + 3 ^ 40 * 96941 * 2
def baseEnd_96941 : Nat := 22123256945604645151859

theorem tailTrace_96941 : CollatzResearch.WordTrace tailWord_96941 prefixEnd_96941 22123256945604645151859 := by
  unfold tailWord_96941
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535728741806788049802677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2357152494537858699868451 3535728741806788049802677)
  ·
    refine ⟨331474569544386379669001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3535728741806788049802677 331474569544386379669001)
    ·
      refine ⟨248605927158289784751751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331474569544386379669001 248605927158289784751751)
      ·
        refine ⟨372908890737434677127627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248605927158289784751751 372908890737434677127627)
        ·
          refine ⟨559363336106152015691441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372908890737434677127627 559363336106152015691441)
          ·
            refine ⟨419522502079614011768581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559363336106152015691441 419522502079614011768581)
            ·
              refine ⟨78660469139927627206609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 419522502079614011768581 78660469139927627206609)
              ·
                refine ⟨58995351854945720404957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78660469139927627206609 58995351854945720404957)
                ·
                  refine ⟨22123256945604645151859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58995351854945720404957 22123256945604645151859)
                  ·
                    rfl

theorem cell21_96941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_96941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96941 prefixEnd_96941 := by exact prefixLift 96941
  have htrace : WordTrace (prefixWord ++ tailWord_96941) baseStart_96941 baseEnd_96941 := by
    simpa [prefixWord, tailWord_96941, baseEnd_96941] using wordTrace_append hprefix tailTrace_96941
  have hstable : (prefixWord ++ tailWord_96941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96941).length < 2 ^ (prefixWord ++ tailWord_96941).sum := by decide
  have hdescent : baseEnd_96941 < baseStart_96941 := by decide
  rcases family_descends (prefixWord ++ tailWord_96941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96983 : List Nat := [1, 1, 3, 2, 1, 4, 1, 5, 3]
def baseStart_96983 : Nat := 118140960795 + 96983 * 2 ^ 59
def prefixEnd_96983 : Nat := 4983230072969 + 3 ^ 40 * 96983 * 2
def baseEnd_96983 : Nat := 22132841917821905451773

theorem tailTrace_96983 : CollatzResearch.WordTrace tailWord_96983 prefixEnd_96983 22132841917821905451773 := by
  unfold tailWord_96983
  simp only [CollatzResearch.WordTrace]
  refine ⟨3537260607654629222831603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2358173738436419481887735 3537260607654629222831603)
  ·
    refine ⟨5305890911481943834247405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3537260607654629222831603 5305890911481943834247405)
    ·
      refine ⟨1989709091805728937842777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5305890911481943834247405 1989709091805728937842777)
      ·
        refine ⟨1492281818854296703382083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1989709091805728937842777 1492281818854296703382083)
        ·
          refine ⟨2238422728281445055073125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492281818854296703382083 2238422728281445055073125)
          ·
            refine ⟨419704261552770947826211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2238422728281445055073125 419704261552770947826211)
            ·
              refine ⟨629556392329156421739317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419704261552770947826211 629556392329156421739317)
              ·
                refine ⟨59020911780858414538061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 629556392329156421739317 59020911780858414538061)
                ·
                  refine ⟨22132841917821905451773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59020911780858414538061 22132841917821905451773)
                  ·
                    rfl

theorem cell21_96983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 3].length) (baseStart_96983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96983 prefixEnd_96983 := by exact prefixLift 96983
  have htrace : WordTrace (prefixWord ++ tailWord_96983) baseStart_96983 baseEnd_96983 := by
    simpa [prefixWord, tailWord_96983, baseEnd_96983] using wordTrace_append hprefix tailTrace_96983
  have hstable : (prefixWord ++ tailWord_96983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96983).length < 2 ^ (prefixWord ++ tailWord_96983).sum := by decide
  have hdescent : baseEnd_96983 < baseStart_96983 := by decide
  rcases family_descends (prefixWord ++ tailWord_96983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96997 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 6]
def baseStart_96997 : Nat := 118140960795 + 96997 * 2 ^ 59
def prefixEnd_96997 : Nat := 4983230072969 + 3 ^ 40 * 96997 * 2
def baseEnd_96997 : Nat := 22136036908560992218411

theorem tailTrace_96997 : CollatzResearch.WordTrace tailWord_96997 prefixEnd_96997 22136036908560992218411 := by
  unfold tailWord_96997
  simp only [CollatzResearch.WordTrace]
  refine ⟨3537771229603909613841245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2358514153069273075894163 3537771229603909613841245)
  ·
    refine ⟨1326664211101466105190467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3537771229603909613841245 1326664211101466105190467)
    ·
      refine ⟨1989996316652199157785701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1326664211101466105190467 1989996316652199157785701)
      ·
        refine ⟨373124309372287342084819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1989996316652199157785701 373124309372287342084819)
        ·
          refine ⟨559686464058431013127229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373124309372287342084819 559686464058431013127229)
          ·
            refine ⟨209882424021911629922711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 559686464058431013127229 209882424021911629922711)
            ·
              refine ⟨314823636032867444884067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209882424021911629922711 314823636032867444884067)
              ·
                refine ⟨472235454049301167326101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314823636032867444884067 472235454049301167326101)
                ·
                  refine ⟨22136036908560992218411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 472235454049301167326101 22136036908560992218411)
                  ·
                    rfl

theorem cell21_96997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_96997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_96997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_96997 prefixEnd_96997 := by exact prefixLift 96997
  have htrace : WordTrace (prefixWord ++ tailWord_96997) baseStart_96997 baseEnd_96997 := by
    simpa [prefixWord, tailWord_96997, baseEnd_96997] using wordTrace_append hprefix tailTrace_96997
  have hstable : (prefixWord ++ tailWord_96997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96997).length < 2 ^ (prefixWord ++ tailWord_96997).sum := by decide
  have hdescent : baseEnd_96997 < baseStart_96997 := by decide
  rcases family_descends (prefixWord ++ tailWord_96997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97073 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 4]
def baseStart_97073 : Nat := 118140960795 + 97073 * 2 ^ 59
def prefixEnd_97073 : Nat := 4983230072969 + 3 ^ 40 * 97073 * 2
def baseEnd_97073 : Nat := 22153381144001748951589

theorem tailTrace_97073 : CollatzResearch.WordTrace tailWord_97073 prefixEnd_97073 22153381144001748951589 := by
  unfold tailWord_97073
  simp only [CollatzResearch.WordTrace]
  refine ⟨3540543177328574593607873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2360362118219049729071915 3540543177328574593607873)
  ·
    refine ⟨2655407382996430945205905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3540543177328574593607873 2655407382996430945205905)
    ·
      refine ⟨1991555537247323208904429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2655407382996430945205905 1991555537247323208904429)
      ·
        refine ⟨746833326467746203339161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1991555537247323208904429 746833326467746203339161)
        ·
          refine ⟨560124994850809652504371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746833326467746203339161 560124994850809652504371)
          ·
            refine ⟨840187492276214478756557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560124994850809652504371 840187492276214478756557)
            ·
              refine ⟨315070309603580429533709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 840187492276214478756557 315070309603580429533709)
              ·
                refine ⟨118151366101342661075141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315070309603580429533709 118151366101342661075141)
                ·
                  refine ⟨22153381144001748951589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118151366101342661075141 22153381144001748951589)
                  ·
                    rfl

theorem cell21_97073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_97073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97073 prefixEnd_97073 := by exact prefixLift 97073
  have htrace : WordTrace (prefixWord ++ tailWord_97073) baseStart_97073 baseEnd_97073 := by
    simpa [prefixWord, tailWord_97073, baseEnd_97073] using wordTrace_append hprefix tailTrace_97073
  have hstable : (prefixWord ++ tailWord_97073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97073).length < 2 ^ (prefixWord ++ tailWord_97073).sum := by decide
  have hdescent : baseEnd_97073 < baseStart_97073 := by decide
  rcases family_descends (prefixWord ++ tailWord_97073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97087 : List Nat := [1, 1, 2, 2, 5, 1, 2, 7]
def baseStart_97087 : Nat := 118140960795 + 97087 * 2 ^ 59
def prefixEnd_97087 : Nat := 4983230072969 + 3 ^ 40 * 97087 * 2
def baseEnd_97087 : Nat := 7385525378246945239409

theorem tailTrace_97087 : CollatzResearch.WordTrace tailWord_97087 prefixEnd_97087 7385525378246945239409 := by
  unfold tailWord_97087
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541053799277854984617515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2360702532851903323078343 3541053799277854984617515)
  ·
    refine ⟨5311580698916782476926273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3541053799277854984617515 5311580698916782476926273)
    ·
      refine ⟨3983685524187586857694705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5311580698916782476926273 3983685524187586857694705)
      ·
        refine ⟨2987764143140690143271029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3983685524187586857694705 2987764143140690143271029)
        ·
          refine ⟨280102888419439700931659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2987764143140690143271029 280102888419439700931659)
          ·
            refine ⟨420154332629159551397489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280102888419439700931659 420154332629159551397489)
            ·
              refine ⟨315115749471869663548117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420154332629159551397489 315115749471869663548117)
              ·
                refine ⟨7385525378246945239409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 315115749471869663548117 7385525378246945239409)
                ·
                  rfl

theorem cell21_97087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 7].length) (baseStart_97087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97087 prefixEnd_97087 := by exact prefixLift 97087
  have htrace : WordTrace (prefixWord ++ tailWord_97087) baseStart_97087 baseEnd_97087 := by
    simpa [prefixWord, tailWord_97087, baseEnd_97087] using wordTrace_append hprefix tailTrace_97087
  have hstable : (prefixWord ++ tailWord_97087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97087).length < 2 ^ (prefixWord ++ tailWord_97087).sum := by decide
  have hdescent : baseEnd_97087 < baseStart_97087 := by decide
  rcases family_descends (prefixWord ++ tailWord_97087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97197 : List Nat := [1, 5, 2, 3, 1, 1, 1, 7]
def baseStart_97197 : Nat := 118140960795 + 97197 * 2 ^ 59
def prefixEnd_97197 : Nat := 4983230072969 + 3 ^ 40 * 97197 * 2
def baseEnd_97197 : Nat := 7393893211135029628223

theorem tailTrace_97197 : CollatzResearch.WordTrace tailWord_97197 prefixEnd_97197 7393893211135029628223 := by
  unfold tailWord_97197
  simp only [CollatzResearch.WordTrace]
  refine ⟨3545065828879343771121845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2363377219252895847414563 3545065828879343771121845)
  ·
    refine ⟨332349921457438478542673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3545065828879343771121845 332349921457438478542673)
    ·
      refine ⟨249262441093078858907005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332349921457438478542673 249262441093078858907005)
      ·
        refine ⟨93473415409904572090127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249262441093078858907005 93473415409904572090127)
        ·
          refine ⟨140210123114856858135191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93473415409904572090127 140210123114856858135191)
          ·
            refine ⟨210315184672285287202787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140210123114856858135191 210315184672285287202787)
            ·
              refine ⟨315472777008427930804181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210315184672285287202787 315472777008427930804181)
              ·
                refine ⟨7393893211135029628223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 315472777008427930804181 7393893211135029628223)
                ·
                  rfl

theorem cell21_97197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 7].length) (baseStart_97197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97197 prefixEnd_97197 := by exact prefixLift 97197
  have htrace : WordTrace (prefixWord ++ tailWord_97197) baseStart_97197 baseEnd_97197 := by
    simpa [prefixWord, tailWord_97197, baseEnd_97197] using wordTrace_append hprefix tailTrace_97197
  have hstable : (prefixWord ++ tailWord_97197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97197).length < 2 ^ (prefixWord ++ tailWord_97197).sum := by decide
  have hdescent : baseEnd_97197 < baseStart_97197 := by decide
  rcases family_descends (prefixWord ++ tailWord_97197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97208 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_97208 : Nat := 118140960795 + 97208 * 2 ^ 59
def prefixEnd_97208 : Nat := 4983230072969 + 3 ^ 40 * 97208 * 2
def baseEnd_97208 : Nat := 22184189983271514201313

theorem tailTrace_97208 : CollatzResearch.WordTrace tailWord_97208 prefixEnd_97208 22184189983271514201313 := by
  unfold tailWord_97208
  simp only [CollatzResearch.WordTrace]
  refine ⟨1772733515919746324886139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2363644687892995099848185 1772733515919746324886139)
  ·
    refine ⟨2659100273879619487329209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1772733515919746324886139 2659100273879619487329209)
    ·
      refine ⟨1994325205409714615496907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2659100273879619487329209 1994325205409714615496907)
      ·
        refine ⟨2991487808114571923245361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994325205409714615496907 2991487808114571923245361)
        ·
          refine ⟨2243615856085928942434021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2991487808114571923245361 2243615856085928942434021)
          ·
            refine ⟨420677973016111676706379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2243615856085928942434021 420677973016111676706379)
            ·
              refine ⟨631016959524167515059569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420677973016111676706379 631016959524167515059569)
              ·
                refine ⟨473262719643125636294677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631016959524167515059569 473262719643125636294677)
                ·
                  refine ⟨22184189983271514201313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 473262719643125636294677 22184189983271514201313)
                  ·
                    rfl

theorem cell21_97208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_97208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97208 prefixEnd_97208 := by exact prefixLift 97208
  have htrace : WordTrace (prefixWord ++ tailWord_97208) baseStart_97208 baseEnd_97208 := by
    simpa [prefixWord, tailWord_97208, baseEnd_97208] using wordTrace_append hprefix tailTrace_97208
  have hstable : (prefixWord ++ tailWord_97208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97208).length < 2 ^ (prefixWord ++ tailWord_97208).sum := by decide
  have hdescent : baseEnd_97208 < baseStart_97208 := by decide
  rcases family_descends (prefixWord ++ tailWord_97208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97228 : List Nat := [2, 2, 1, 4, 1, 1, 5, 2, 3]
def baseStart_97228 : Nat := 118140960795 + 97228 * 2 ^ 59
def prefixEnd_97228 : Nat := 4983230072969 + 3 ^ 40 * 97228 * 2
def baseEnd_97228 : Nat := 22188754255755923867939

theorem tailTrace_97228 : CollatzResearch.WordTrace tailWord_97228 prefixEnd_97228 22188754255755923867939 := by
  unfold tailWord_97228
  simp only [CollatzResearch.WordTrace]
  refine ⟨1773098245883518032750169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2364130994511357377000225 1773098245883518032750169)
  ·
    refine ⟨1329823684412638524562627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1773098245883518032750169 1329823684412638524562627)
    ·
      refine ⟨1994735526618957786843941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1329823684412638524562627 1994735526618957786843941)
      ·
        refine ⟨374012911241054585033239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1994735526618957786843941 374012911241054585033239)
        ·
          refine ⟨561019366861581877549859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374012911241054585033239 561019366861581877549859)
          ·
            refine ⟨841529050292372816324789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561019366861581877549859 841529050292372816324789)
            ·
              refine ⟨78893348464909951530449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 841529050292372816324789 78893348464909951530449)
              ·
                refine ⟨59170011348682463647837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78893348464909951530449 59170011348682463647837)
                ·
                  refine ⟨22188754255755923867939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59170011348682463647837 22188754255755923867939)
                  ·
                    rfl

theorem cell21_97228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_97228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97228 prefixEnd_97228 := by exact prefixLift 97228
  have htrace : WordTrace (prefixWord ++ tailWord_97228) baseStart_97228 baseEnd_97228 := by
    simpa [prefixWord, tailWord_97228, baseEnd_97228] using wordTrace_append hprefix tailTrace_97228
  have hstable : (prefixWord ++ tailWord_97228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97228).length < 2 ^ (prefixWord ++ tailWord_97228).sum := by decide
  have hdescent : baseEnd_97228 < baseStart_97228 := by decide
  rcases family_descends (prefixWord ++ tailWord_97228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97242 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_97242 : Nat := 118140960795 + 97242 * 2 ^ 59
def prefixEnd_97242 : Nat := 4983230072969 + 3 ^ 40 * 97242 * 2
def baseEnd_97242 : Nat := 22191949246495010634577

theorem tailTrace_97242 : CollatzResearch.WordTrace tailWord_97242 prefixEnd_97242 22191949246495010634577 := by
  unfold tailWord_97242
  simp only [CollatzResearch.WordTrace]
  refine ⟨886676778429079114127495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2364471409144210971006653 886676778429079114127495)
  ·
    refine ⟨1330015167643618671191243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 886676778429079114127495 1330015167643618671191243)
    ·
      refine ⟨1995022751465428006786865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330015167643618671191243 1995022751465428006786865)
      ·
        refine ⟨1496267063599071005090149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1995022751465428006786865 1496267063599071005090149)
        ·
          refine ⟨280550074424825813454403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1496267063599071005090149 280550074424825813454403)
          ·
            refine ⟨420825111637238720181605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280550074424825813454403 420825111637238720181605)
            ·
              refine ⟨78904708431982260034051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 420825111637238720181605 78904708431982260034051)
              ·
                refine ⟨118357062647973390051077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78904708431982260034051 118357062647973390051077)
                ·
                  refine ⟨22191949246495010634577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118357062647973390051077 22191949246495010634577)
                  ·
                    rfl

theorem cell21_97242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_97242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97242 prefixEnd_97242 := by exact prefixLift 97242
  have htrace : WordTrace (prefixWord ++ tailWord_97242) baseStart_97242 baseEnd_97242 := by
    simpa [prefixWord, tailWord_97242, baseEnd_97242] using wordTrace_append hprefix tailTrace_97242
  have hstable : (prefixWord ++ tailWord_97242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97242).length < 2 ^ (prefixWord ++ tailWord_97242).sum := by decide
  have hdescent : baseEnd_97242 < baseStart_97242 := by decide
  rcases family_descends (prefixWord ++ tailWord_97242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97287 : List Nat := [1, 1, 4, 3, 1, 1, 3, 4, 3]
def baseStart_97287 : Nat := 118140960795 + 97287 * 2 ^ 59
def prefixEnd_97287 : Nat := 4983230072969 + 3 ^ 40 * 97287 * 2
def baseEnd_97287 : Nat := 22202218859584932384485

theorem tailTrace_97287 : CollatzResearch.WordTrace tailWord_97287 prefixEnd_97287 22202218859584932384485 := by
  unfold tailWord_97287
  simp only [CollatzResearch.WordTrace]
  refine ⟨3548348398553289141898115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2365565599035526094598743 3548348398553289141898115)
  ·
    refine ⟨5322522597829933712847173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3548348398553289141898115 5322522597829933712847173)
    ·
      refine ⟨997972987093112571158845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5322522597829933712847173 997972987093112571158845)
      ·
        refine ⟨374239870159917214184567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 997972987093112571158845 374239870159917214184567)
        ·
          refine ⟨561359805239875821276851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374239870159917214184567 561359805239875821276851)
          ·
            refine ⟨842039707859813731915277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561359805239875821276851 842039707859813731915277)
            ·
              refine ⟨315764890447430149468229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 842039707859813731915277 315764890447430149468229)
              ·
                refine ⟨59205916958893153025293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315764890447430149468229 59205916958893153025293)
                ·
                  refine ⟨22202218859584932384485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59205916958893153025293 22202218859584932384485)
                  ·
                    rfl

theorem cell21_97287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 3].length) (baseStart_97287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97287 prefixEnd_97287 := by exact prefixLift 97287
  have htrace : WordTrace (prefixWord ++ tailWord_97287) baseStart_97287 baseEnd_97287 := by
    simpa [prefixWord, tailWord_97287, baseEnd_97287] using wordTrace_append hprefix tailTrace_97287
  have hstable : (prefixWord ++ tailWord_97287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97287).length < 2 ^ (prefixWord ++ tailWord_97287).sum := by decide
  have hdescent : baseEnd_97287 < baseStart_97287 := by decide
  rcases family_descends (prefixWord ++ tailWord_97287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97301 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 4]
def baseStart_97301 : Nat := 118140960795 + 97301 * 2 ^ 59
def prefixEnd_97301 : Nat := 4983230072969 + 3 ^ 40 * 97301 * 2
def baseEnd_97301 : Nat := 22205413850324019151123

theorem tailTrace_97301 : CollatzResearch.WordTrace tailWord_97301 prefixEnd_97301 22205413850324019151123 := by
  unfold tailWord_97301
  simp only [CollatzResearch.WordTrace]
  refine ⟨3548859020502569532907757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2365906013668379688605171 3548859020502569532907757)
  ·
    refine ⟨1330822132688463574840409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3548859020502569532907757 1330822132688463574840409)
    ·
      refine ⟨998116599516347681130307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1330822132688463574840409 998116599516347681130307)
      ·
        refine ⟨1497174899274521521695461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998116599516347681130307 1497174899274521521695461)
        ·
          refine ⟨280720293613972785317899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1497174899274521521695461 280720293613972785317899)
          ·
            refine ⟨421080440420959177976849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280720293613972785317899 421080440420959177976849)
            ·
              refine ⟨315810330315719383482637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421080440420959177976849 315810330315719383482637)
              ·
                refine ⟨118428873868394768805989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315810330315719383482637 118428873868394768805989)
                ·
                  refine ⟨22205413850324019151123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118428873868394768805989 22205413850324019151123)
                  ·
                    rfl

theorem cell21_97301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_97301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97301 prefixEnd_97301 := by exact prefixLift 97301
  have htrace : WordTrace (prefixWord ++ tailWord_97301) baseStart_97301 baseEnd_97301 := by
    simpa [prefixWord, tailWord_97301, baseEnd_97301] using wordTrace_append hprefix tailTrace_97301
  have hstable : (prefixWord ++ tailWord_97301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97301).length < 2 ^ (prefixWord ++ tailWord_97301).sum := by decide
  have hdescent : baseEnd_97301 < baseStart_97301 := by decide
  rcases family_descends (prefixWord ++ tailWord_97301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97329 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 7]
def baseStart_97329 : Nat := 118140960795 + 97329 * 2 ^ 59
def prefixEnd_97329 : Nat := 4983230072969 + 3 ^ 40 * 97329 * 2
def baseEnd_97329 : Nat := 22211803831802192684399

theorem tailTrace_97329 : CollatzResearch.WordTrace tailWord_97329 prefixEnd_97329 22211803831802192684399 := by
  unfold tailWord_97329
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549880264401130314927041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2366586842934086876618027 3549880264401130314927041)
  ·
    refine ⟨2662410198300847736195281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3549880264401130314927041 2662410198300847736195281)
    ·
      refine ⟨1996807648725635802146461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2662410198300847736195281 1996807648725635802146461)
      ·
        refine ⟨748802868272113425804923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1996807648725635802146461 748802868272113425804923)
        ·
          refine ⟨1123204302408170138707385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748802868272113425804923 1123204302408170138707385)
          ·
            refine ⟨842403226806127604030539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1123204302408170138707385 842403226806127604030539)
            ·
              refine ⟨1263604840209191406045809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842403226806127604030539 1263604840209191406045809)
              ·
                refine ⟨947703630156893554534357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263604840209191406045809 947703630156893554534357)
                ·
                  refine ⟨22211803831802192684399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 947703630156893554534357 22211803831802192684399)
                  ·
                    rfl

theorem cell21_97329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_97329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97329 prefixEnd_97329 := by exact prefixLift 97329
  have htrace : WordTrace (prefixWord ++ tailWord_97329) baseStart_97329 baseEnd_97329 := by
    simpa [prefixWord, tailWord_97329, baseEnd_97329] using wordTrace_append hprefix tailTrace_97329
  have hstable : (prefixWord ++ tailWord_97329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97329).length < 2 ^ (prefixWord ++ tailWord_97329).sum := by decide
  have hdescent : baseEnd_97329 < baseStart_97329 := by decide
  rcases family_descends (prefixWord ++ tailWord_97329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97332 : List Nat := [2, 5, 1, 2, 1, 2, 8]
def baseStart_97332 : Nat := 118140960795 + 97332 * 2 ^ 59
def prefixEnd_97332 : Nat := 4983230072969 + 3 ^ 40 * 97332 * 2
def baseEnd_97332 : Nat := 2468054274741650459377

theorem tailTrace_97332 : CollatzResearch.WordTrace tailWord_97332 prefixEnd_97332 2468054274741650459377 := by
  unfold tailWord_97332
  simp only [CollatzResearch.WordTrace]
  refine ⟨1774994841695130913643125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2366659788926841218190833 1774994841695130913643125)
  ·
    refine ⟨166405766408918523154043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1774994841695130913643125 166405766408918523154043)
    ·
      refine ⟨249608649613377784731065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166405766408918523154043 249608649613377784731065)
      ·
        refine ⟨187206487210033338548299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249608649613377784731065 187206487210033338548299)
        ·
          refine ⟨280809730815050007822449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187206487210033338548299 280809730815050007822449)
          ·
            refine ⟨210607298111287505866837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280809730815050007822449 210607298111287505866837)
            ·
              refine ⟨2468054274741650459377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 210607298111287505866837 2468054274741650459377)
              ·
                rfl

theorem cell21_97332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 8].length) (baseStart_97332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97332 prefixEnd_97332 := by exact prefixLift 97332
  have htrace : WordTrace (prefixWord ++ tailWord_97332) baseStart_97332 baseEnd_97332 := by
    simpa [prefixWord, tailWord_97332, baseEnd_97332] using wordTrace_append hprefix tailTrace_97332
  have hstable : (prefixWord ++ tailWord_97332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97332).length < 2 ^ (prefixWord ++ tailWord_97332).sum := by decide
  have hdescent : baseEnd_97332 < baseStart_97332 := by decide
  rcases family_descends (prefixWord ++ tailWord_97332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97360 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 4]
def baseStart_97360 : Nat := 118140960795 + 97360 * 2 ^ 59
def prefixEnd_97360 : Nat := 4983230072969 + 3 ^ 40 * 97360 * 2
def baseEnd_97360 : Nat := 22218878454153027667669

theorem tailTrace_97360 : CollatzResearch.WordTrace tailWord_97360 prefixEnd_97360 22218878454153027667669 := by
  unfold tailWord_97360
  simp only [CollatzResearch.WordTrace]
  refine ⟨1775505463644411304652767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2367340618192548406203689 1775505463644411304652767)
  ·
    refine ⟨2663258195466616956979151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1775505463644411304652767 2663258195466616956979151)
    ·
      refine ⟨3994887293199925435468727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2663258195466616956979151 3994887293199925435468727)
      ·
        refine ⟨5992330939799888153203091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3994887293199925435468727 5992330939799888153203091)
        ·
          refine ⟨8988496409699832229804637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5992330939799888153203091 8988496409699832229804637)
          ·
            refine ⟨3370686153637437086176739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8988496409699832229804637 3370686153637437086176739)
            ·
              refine ⟨5056029230456155629265109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370686153637437086176739 5056029230456155629265109)
              ·
                refine ⟨118500685088816147560901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5056029230456155629265109 118500685088816147560901)
                ·
                  refine ⟨22218878454153027667669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118500685088816147560901 22218878454153027667669)
                  ·
                    rfl

theorem cell21_97360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_97360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97360 prefixEnd_97360 := by exact prefixLift 97360
  have htrace : WordTrace (prefixWord ++ tailWord_97360) baseStart_97360 baseEnd_97360 := by
    simpa [prefixWord, tailWord_97360, baseEnd_97360] using wordTrace_append hprefix tailTrace_97360
  have hstable : (prefixWord ++ tailWord_97360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97360).length < 2 ^ (prefixWord ++ tailWord_97360).sum := by decide
  have hdescent : baseEnd_97360 < baseStart_97360 := by decide
  rcases family_descends (prefixWord ++ tailWord_97360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97397 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 5]
def baseStart_97397 : Nat := 118140960795 + 97397 * 2 ^ 59
def prefixEnd_97397 : Nat := 4983230072969 + 3 ^ 40 * 97397 * 2
def baseEnd_97397 : Nat := 22227322358249185550927

theorem tailTrace_97397 : CollatzResearch.WordTrace tailWord_97397 prefixEnd_97397 22227322358249185550927 := by
  unfold tailWord_97397
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552360428154777928402445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2368240285436518618934963 3552360428154777928402445)
  ·
    refine ⟨1332135160558041723150917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3552360428154777928402445 1332135160558041723150917)
    ·
      refine ⟨249775342604632823090797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1332135160558041723150917 249775342604632823090797)
      ·
        refine ⟨93665753476737308659049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249775342604632823090797 93665753476737308659049)
        ·
          refine ⟨70249315107552981494287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93665753476737308659049 70249315107552981494287)
          ·
            refine ⟨105373972661329472241431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70249315107552981494287 105373972661329472241431)
            ·
              refine ⟨158060958991994208362147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105373972661329472241431 158060958991994208362147)
              ·
                refine ⟨237091438487991312543221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158060958991994208362147 237091438487991312543221)
                ·
                  refine ⟨22227322358249185550927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237091438487991312543221 22227322358249185550927)
                  ·
                    rfl

theorem cell21_97397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_97397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97397 prefixEnd_97397 := by exact prefixLift 97397
  have htrace : WordTrace (prefixWord ++ tailWord_97397) baseStart_97397 baseEnd_97397 := by
    simpa [prefixWord, tailWord_97397, baseEnd_97397] using wordTrace_append hprefix tailTrace_97397
  have hstable : (prefixWord ++ tailWord_97397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97397).length < 2 ^ (prefixWord ++ tailWord_97397).sum := by decide
  have hdescent : baseEnd_97397 < baseStart_97397 := by decide
  rcases family_descends (prefixWord ++ tailWord_97397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97512 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_97512 : Nat := 118140960795 + 97512 * 2 ^ 59
def prefixEnd_97512 : Nat := 4983230072969 + 3 ^ 40 * 97512 * 2
def baseEnd_97512 : Nat := 22253566925034541134025

theorem tailTrace_97512 : CollatzResearch.WordTrace tailWord_97512 prefixEnd_97512 22253566925034541134025 := by
  unfold tailWord_97512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778277411369076284419395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2371036548492101712559193 1778277411369076284419395)
  ·
    refine ⟨2667416117053614426629093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1778277411369076284419395 2667416117053614426629093)
    ·
      refine ⟨500140521947552704992955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2667416117053614426629093 500140521947552704992955)
      ·
        refine ⟨750210782921329057489433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500140521947552704992955 750210782921329057489433)
        ·
          refine ⟨562658087190996793117075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 750210782921329057489433 562658087190996793117075)
          ·
            refine ⟨843987130786495189675613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562658087190996793117075 843987130786495189675613)
            ·
              refine ⟨316495174044935696128355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 843987130786495189675613 316495174044935696128355)
              ·
                refine ⟨474742761067403544192533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316495174044935696128355 474742761067403544192533)
                ·
                  refine ⟨22253566925034541134025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 474742761067403544192533 22253566925034541134025)
                  ·
                    rfl

theorem cell21_97512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_97512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97512 prefixEnd_97512 := by exact prefixLift 97512
  have htrace : WordTrace (prefixWord ++ tailWord_97512) baseStart_97512 baseEnd_97512 := by
    simpa [prefixWord, tailWord_97512, baseEnd_97512] using wordTrace_append hprefix tailTrace_97512
  have hstable : (prefixWord ++ tailWord_97512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97512).length < 2 ^ (prefixWord ++ tailWord_97512).sum := by decide
  have hdescent : baseEnd_97512 < baseStart_97512 := by decide
  rcases family_descends (prefixWord ++ tailWord_97512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97529 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 4]
def baseStart_97529 : Nat := 118140960795 + 97529 * 2 ^ 59
def prefixEnd_97529 : Nat := 4983230072969 + 3 ^ 40 * 97529 * 2
def baseEnd_97529 : Nat := 22257446556646289350657

theorem tailTrace_97529 : CollatzResearch.WordTrace tailWord_97529 prefixEnd_97529 22257446556646289350657 := by
  unfold tailWord_97529
  simp only [CollatzResearch.WordTrace]
  refine ⟨3557174863676564472207641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2371449909117709648138427 3557174863676564472207641)
  ·
    refine ⟨2667881147757423354155731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3557174863676564472207641 2667881147757423354155731)
    ·
      refine ⟨4001821721636135031233597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2667881147757423354155731 4001821721636135031233597)
      ·
        refine ⟨1500683145613550636712599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4001821721636135031233597 1500683145613550636712599)
        ·
          refine ⟨2251024718420325955068899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1500683145613550636712599 2251024718420325955068899)
          ·
            refine ⟨3376537077630488932603349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251024718420325955068899 3376537077630488932603349)
            ·
              refine ⟨79137587756964584357891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3376537077630488932603349 79137587756964584357891)
              ·
                refine ⟨118706381635446876536837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79137587756964584357891 118706381635446876536837)
                ·
                  refine ⟨22257446556646289350657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118706381635446876536837 22257446556646289350657)
                  ·
                    rfl

theorem cell21_97529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_97529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97529 prefixEnd_97529 := by exact prefixLift 97529
  have htrace : WordTrace (prefixWord ++ tailWord_97529) baseStart_97529 baseEnd_97529 := by
    simpa [prefixWord, tailWord_97529, baseEnd_97529] using wordTrace_append hprefix tailTrace_97529
  have hstable : (prefixWord ++ tailWord_97529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97529).length < 2 ^ (prefixWord ++ tailWord_97529).sum := by decide
  have hdescent : baseEnd_97529 < baseStart_97529 := by decide
  rcases family_descends (prefixWord ++ tailWord_97529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97566 : List Nat := [4, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_97566 : Nat := 118140960795 + 97566 * 2 ^ 59
def prefixEnd_97566 : Nat := 4983230072969 + 3 ^ 40 * 97566 * 2
def baseEnd_97566 : Nat := 22265890460742447233915

theorem tailTrace_97566 : CollatzResearch.WordTrace tailWord_97566 prefixEnd_97566 22265890460742447233915 := by
  unfold tailWord_97566
  simp only [CollatzResearch.WordTrace]
  refine ⟨444815545567814973913069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2372349576361679860869701 444815545567814973913069)
  ·
    refine ⟨166805829587930615217401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 444815545567814973913069 166805829587930615217401)
    ·
      refine ⟨125104372190947961413051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166805829587930615217401 125104372190947961413051)
      ·
        refine ⟨187656558286421942119577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125104372190947961413051 187656558286421942119577)
        ·
          refine ⟨140742418714816456589683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187656558286421942119577 140742418714816456589683)
          ·
            refine ⟨211113628072224684884525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140742418714816456589683 211113628072224684884525)
            ·
              refine ⟨79167610527084256831697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211113628072224684884525 79167610527084256831697)
              ·
                refine ⟨59375707895313192623773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79167610527084256831697 59375707895313192623773)
                ·
                  refine ⟨22265890460742447233915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59375707895313192623773 22265890460742447233915)
                  ·
                    rfl

theorem cell21_97566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_97566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97566 prefixEnd_97566 := by exact prefixLift 97566
  have htrace : WordTrace (prefixWord ++ tailWord_97566) baseStart_97566 baseEnd_97566 := by
    simpa [prefixWord, tailWord_97566, baseEnd_97566] using wordTrace_append hprefix tailTrace_97566
  have hstable : (prefixWord ++ tailWord_97566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97566).length < 2 ^ (prefixWord ++ tailWord_97566).sum := by decide
  have hdescent : baseEnd_97566 < baseStart_97566 := by decide
  rcases family_descends (prefixWord ++ tailWord_97566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97667 : List Nat := [1, 1, 1, 3, 5, 2, 2, 3, 3]
def baseStart_97667 : Nat := 118140960795 + 97667 * 2 ^ 59
def prefixEnd_97667 : Nat := 4983230072969 + 3 ^ 40 * 97667 * 2
def baseEnd_97667 : Nat := 22288940036788716050375

theorem tailTrace_97667 : CollatzResearch.WordTrace tailWord_97667 prefixEnd_97667 22288940036788716050375 := by
  unfold tailWord_97667
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562208137176614040731255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2374805424784409360487503 3562208137176614040731255)
  ·
    refine ⟨5343312205764921061096883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3562208137176614040731255 5343312205764921061096883)
    ·
      refine ⟨8014968308647381591645325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5343312205764921061096883 8014968308647381591645325)
      ·
        refine ⟨3005613115742768096866997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8014968308647381591645325 3005613115742768096866997)
        ·
          refine ⟨281776229600884509081281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3005613115742768096866997 281776229600884509081281)
          ·
            refine ⟨211332172200663381810961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281776229600884509081281 211332172200663381810961)
            ·
              refine ⟨158499129150497536358221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211332172200663381810961 158499129150497536358221)
              ·
                refine ⟨59437173431436576134333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158499129150497536358221 59437173431436576134333)
                ·
                  refine ⟨22288940036788716050375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59437173431436576134333 22288940036788716050375)
                  ·
                    rfl

theorem cell21_97667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 3].length) (baseStart_97667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97667 prefixEnd_97667 := by exact prefixLift 97667
  have htrace : WordTrace (prefixWord ++ tailWord_97667) baseStart_97667 baseEnd_97667 := by
    simpa [prefixWord, tailWord_97667, baseEnd_97667] using wordTrace_append hprefix tailTrace_97667
  have hstable : (prefixWord ++ tailWord_97667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97667).length < 2 ^ (prefixWord ++ tailWord_97667).sum := by decide
  have hdescent : baseEnd_97667 < baseStart_97667 := by decide
  rcases family_descends (prefixWord ++ tailWord_97667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97698 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_97698 : Nat := 118140960795 + 97698 * 2 ^ 59
def prefixEnd_97698 : Nat := 4983230072969 + 3 ^ 40 * 97698 * 2
def baseEnd_97698 : Nat := 22296014659139551033645

theorem tailTrace_97698 : CollatzResearch.WordTrace tailWord_97698 prefixEnd_97698 22296014659139551033645 := by
  unfold tailWord_97698
  simp only [CollatzResearch.WordTrace]
  refine ⟨890834700016076583777437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2375559200042870890073165 890834700016076583777437)
  ·
    refine ⟨334063012506028718916539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 890834700016076583777437 334063012506028718916539)
    ·
      refine ⟨501094518759043078374809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334063012506028718916539 501094518759043078374809)
      ·
        refine ⟨375820889069282308781107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501094518759043078374809 375820889069282308781107)
        ·
          refine ⟨563731333603923463171661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375820889069282308781107 563731333603923463171661)
          ·
            refine ⟨211399250101471298689373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 563731333603923463171661 211399250101471298689373)
            ·
              refine ⟨79274718788051737008515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211399250101471298689373 79274718788051737008515)
              ·
                refine ⟨118912078182077605512773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79274718788051737008515 118912078182077605512773)
                ·
                  refine ⟨22296014659139551033645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118912078182077605512773 22296014659139551033645)
                  ·
                    rfl

theorem cell21_97698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_97698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97698 prefixEnd_97698 := by exact prefixLift 97698
  have htrace : WordTrace (prefixWord ++ tailWord_97698) baseStart_97698 baseEnd_97698 := by
    simpa [prefixWord, tailWord_97698, baseEnd_97698] using wordTrace_append hprefix tailTrace_97698
  have hstable : (prefixWord ++ tailWord_97698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97698).length < 2 ^ (prefixWord ++ tailWord_97698).sum := by decide
  have hdescent : baseEnd_97698 < baseStart_97698 := by decide
  rcases family_descends (prefixWord ++ tailWord_97698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97740 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_97740 : Nat := 118140960795 + 97740 * 2 ^ 59
def prefixEnd_97740 : Nat := 4983230072969 + 3 ^ 40 * 97740 * 2
def baseEnd_97740 : Nat := 22305599631356811333559

theorem tailTrace_97740 : CollatzResearch.WordTrace tailWord_97740 prefixEnd_97740 22305599631356811333559 := by
  unfold tailWord_97740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1782435332956073754069337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2376580443941431672092449 1782435332956073754069337)
  ·
    refine ⟨1336826499717055315552003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1782435332956073754069337 1336826499717055315552003)
    ·
      refine ⟨2005239749575582973328005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336826499717055315552003 2005239749575582973328005)
      ·
        refine ⟨375982453045421807499001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2005239749575582973328005 375982453045421807499001)
        ·
          refine ⟨281986839784066355624251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375982453045421807499001 281986839784066355624251)
          ·
            refine ⟨422980259676099533436377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281986839784066355624251 422980259676099533436377)
            ·
              refine ⟨317235194757074650077283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422980259676099533436377 317235194757074650077283)
              ·
                refine ⟨475852792135611975115925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317235194757074650077283 475852792135611975115925)
                ·
                  refine ⟨22305599631356811333559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 475852792135611975115925 22305599631356811333559)
                  ·
                    rfl

theorem cell21_97740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_97740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97740 prefixEnd_97740 := by exact prefixLift 97740
  have htrace : WordTrace (prefixWord ++ tailWord_97740) baseStart_97740 baseEnd_97740 := by
    simpa [prefixWord, tailWord_97740, baseEnd_97740] using wordTrace_append hprefix tailTrace_97740
  have hstable : (prefixWord ++ tailWord_97740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97740).length < 2 ^ (prefixWord ++ tailWord_97740).sum := by decide
  have hdescent : baseEnd_97740 < baseStart_97740 := by decide
  rcases family_descends (prefixWord ++ tailWord_97740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97754 : List Nat := [3, 1, 1, 2, 3, 2, 1, 8]
def baseStart_97754 : Nat := 118140960795 + 97754 * 2 ^ 59
def prefixEnd_97754 : Nat := 4983230072969 + 3 ^ 40 * 97754 * 2
def baseEnd_97754 : Nat := 7436264874031966033399

theorem tailTrace_97754 : CollatzResearch.WordTrace tailWord_97754 prefixEnd_97754 7436264874031966033399 := by
  unfold tailWord_97754
  simp only [CollatzResearch.WordTrace]
  refine ⟨891345321965356974787079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2376920858574285266098877 891345321965356974787079)
  ·
    refine ⟨1337017982948035462180619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 891345321965356974787079 1337017982948035462180619)
    ·
      refine ⟨2005526974422053193270929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337017982948035462180619 2005526974422053193270929)
      ·
        refine ⟨1504145230816539894953197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2005526974422053193270929 1504145230816539894953197)
        ·
          refine ⟨564054461556202460607449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1504145230816539894953197 564054461556202460607449)
          ·
            refine ⟨423040846167151845455587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564054461556202460607449 423040846167151845455587)
            ·
              refine ⟨634561269250727768183381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423040846167151845455587 634561269250727768183381)
              ·
                refine ⟨7436264874031966033399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 634561269250727768183381 7436264874031966033399)
                ·
                  rfl

theorem cell21_97754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_97754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97754 prefixEnd_97754 := by exact prefixLift 97754
  have htrace : WordTrace (prefixWord ++ tailWord_97754) baseStart_97754 baseEnd_97754 := by
    simpa [prefixWord, tailWord_97754, baseEnd_97754] using wordTrace_append hprefix tailTrace_97754
  have hstable : (prefixWord ++ tailWord_97754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97754).length < 2 ^ (prefixWord ++ tailWord_97754).sum := by decide
  have hdescent : baseEnd_97754 < baseStart_97754 := by decide
  rcases family_descends (prefixWord ++ tailWord_97754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97757 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 4]
def baseStart_97757 : Nat := 118140960795 + 97757 * 2 ^ 59
def prefixEnd_97757 : Nat := 4983230072969 + 3 ^ 40 * 97757 * 2
def baseEnd_97757 : Nat := 22309479262968559550191

theorem tailTrace_97757 : CollatzResearch.WordTrace tailWord_97757 prefixEnd_97757 22309479262968559550191 := by
  unfold tailWord_97757
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565490706850559411507525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2376993804567039607671683 3565490706850559411507525)
  ·
    refine ⟨668529507534479889657661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3565490706850559411507525 668529507534479889657661)
    ·
      refine ⟨250698565325429958621623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 668529507534479889657661 250698565325429958621623)
      ·
        refine ⟨376047847988144937932435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250698565325429958621623 376047847988144937932435)
        ·
          refine ⟨564071771982217406898653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376047847988144937932435 564071771982217406898653)
          ·
            refine ⟨211526914493331527586995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 564071771982217406898653 211526914493331527586995)
            ·
              refine ⟨317290371739997291380493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211526914493331527586995 317290371739997291380493)
              ·
                refine ⟨118983889402498984267685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317290371739997291380493 118983889402498984267685)
                ·
                  refine ⟨22309479262968559550191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118983889402498984267685 22309479262968559550191)
                  ·
                    rfl

theorem cell21_97757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_97757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97757 prefixEnd_97757 := by exact prefixLift 97757
  have htrace : WordTrace (prefixWord ++ tailWord_97757) baseStart_97757 baseEnd_97757 := by
    simpa [prefixWord, tailWord_97757, baseEnd_97757] using wordTrace_append hprefix tailTrace_97757
  have hstable : (prefixWord ++ tailWord_97757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97757).length < 2 ^ (prefixWord ++ tailWord_97757).sum := by decide
  have hdescent : baseEnd_97757 < baseStart_97757 := by decide
  rcases family_descends (prefixWord ++ tailWord_97757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97861 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 5]
def baseStart_97861 : Nat := 118140960795 + 97861 * 2 ^ 59
def prefixEnd_97861 : Nat := 4983230072969 + 3 ^ 40 * 97861 * 2
def baseEnd_97861 : Nat := 22333213479887489816645

theorem tailTrace_97861 : CollatzResearch.WordTrace tailWord_97861 prefixEnd_97861 22333213479887489816645 := by
  unfold tailWord_97861
  simp only [CollatzResearch.WordTrace]
  refine ⟨3569283898473785173293437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2379522598982523448862291 3569283898473785173293437)
  ·
    refine ⟨1338481461927669439985039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3569283898473785173293437 1338481461927669439985039)
    ·
      refine ⟨2007722192891504159977559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1338481461927669439985039 2007722192891504159977559)
      ·
        refine ⟨3011583289337256239966339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2007722192891504159977559 3011583289337256239966339)
        ·
          refine ⟨4517374934005884359949509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011583289337256239966339 4517374934005884359949509)
          ·
            refine ⟨847007800126103317490533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4517374934005884359949509 847007800126103317490533)
            ·
              refine ⟨158813962523644372029475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 847007800126103317490533 158813962523644372029475)
              ·
                refine ⟨238220943785466558044213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158813962523644372029475 238220943785466558044213)
                ·
                  refine ⟨22333213479887489816645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 238220943785466558044213 22333213479887489816645)
                  ·
                    rfl

theorem cell21_97861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_97861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97861 prefixEnd_97861 := by exact prefixLift 97861
  have htrace : WordTrace (prefixWord ++ tailWord_97861) baseStart_97861 baseEnd_97861 := by
    simpa [prefixWord, tailWord_97861, baseEnd_97861] using wordTrace_append hprefix tailTrace_97861
  have hstable : (prefixWord ++ tailWord_97861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97861).length < 2 ^ (prefixWord ++ tailWord_97861).sum := by decide
  have hdescent : baseEnd_97861 < baseStart_97861 := by decide
  rcases family_descends (prefixWord ++ tailWord_97861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97906 : List Nat := [3, 2, 1, 2, 3, 1, 9]
def baseStart_97906 : Nat := 118140960795 + 97906 * 2 ^ 59
def prefixEnd_97906 : Nat := 4983230072969 + 3 ^ 40 * 97906 * 2
def baseEnd_97906 : Nat := 2482609232553045729617

theorem tailTrace_97906 : CollatzResearch.WordTrace tailWord_97906 prefixEnd_97906 2482609232553045729617 := by
  unfold tailWord_97906
  simp only [CollatzResearch.WordTrace]
  refine ⟨892731295827689464670393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2380616788873838572454381 892731295827689464670393)
  ·
    refine ⟨669548471870767098502795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 892731295827689464670393 669548471870767098502795)
    ·
      refine ⟨1004322707806150647754193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 669548471870767098502795 1004322707806150647754193)
      ·
        refine ⟨753242030854612985815645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1004322707806150647754193 753242030854612985815645)
        ·
          refine ⟨282465761570479869680867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 753242030854612985815645 282465761570479869680867)
          ·
            refine ⟨423698642355719804521301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282465761570479869680867 423698642355719804521301)
            ·
              refine ⟨2482609232553045729617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 423698642355719804521301 2482609232553045729617)
              ·
                rfl

theorem cell21_97906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 9].length) (baseStart_97906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_97906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_97906 prefixEnd_97906 := by exact prefixLift 97906
  have htrace : WordTrace (prefixWord ++ tailWord_97906) baseStart_97906 baseEnd_97906 := by
    simpa [prefixWord, tailWord_97906, baseEnd_97906] using wordTrace_append hprefix tailTrace_97906
  have hstable : (prefixWord ++ tailWord_97906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97906).length < 2 ^ (prefixWord ++ tailWord_97906).sum := by decide
  have hdescent : baseEnd_97906 < baseStart_97906 := by decide
  rcases family_descends (prefixWord ++ tailWord_97906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98030 : List Nat := [4, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_98030 : Nat := 118140960795 + 98030 * 2 ^ 59
def prefixEnd_98030 : Nat := 4983230072969 + 3 ^ 40 * 98030 * 2
def baseEnd_98030 : Nat := 22371781582380751499633

theorem tailTrace_98030 : CollatzResearch.WordTrace tailWord_98030 prefixEnd_98030 22371781582380751499633 := by
  unfold tailWord_98030
  simp only [CollatzResearch.WordTrace]
  refine ⟨446930979357690879524443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2383631889907684690797029 446930979357690879524443)
  ·
    refine ⟨670396469036536319286665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 446930979357690879524443 670396469036536319286665)
    ·
      refine ⟨502797351777402239464999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 670396469036536319286665 502797351777402239464999)
      ·
        refine ⟨754196027666103359197499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502797351777402239464999 754196027666103359197499)
        ·
          refine ⟨1131294041499155038796249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754196027666103359197499 1131294041499155038796249)
          ·
            refine ⟨848470531124366279097187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131294041499155038796249 848470531124366279097187)
            ·
              refine ⟨1272705796686549418645781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848470531124366279097187 1272705796686549418645781)
              ·
                refine ⟨59658084219682003999021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1272705796686549418645781 59658084219682003999021)
                ·
                  refine ⟨22371781582380751499633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59658084219682003999021 22371781582380751499633)
                  ·
                    rfl

theorem cell21_98030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_98030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98030 prefixEnd_98030 := by exact prefixLift 98030
  have htrace : WordTrace (prefixWord ++ tailWord_98030) baseStart_98030 baseEnd_98030 := by
    simpa [prefixWord, tailWord_98030, baseEnd_98030] using wordTrace_append hprefix tailTrace_98030
  have hstable : (prefixWord ++ tailWord_98030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98030).length < 2 ^ (prefixWord ++ tailWord_98030).sum := by decide
  have hdescent : baseEnd_98030 < baseStart_98030 := by decide
  rcases family_descends (prefixWord ++ tailWord_98030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98058 : List Nat := [3, 1, 2, 2, 1, 4, 1, 7]
def baseStart_98058 : Nat := 118140960795 + 98058 * 2 ^ 59
def prefixEnd_98058 : Nat := 4983230072969 + 3 ^ 40 * 98058 * 2
def baseEnd_98058 : Nat := 7459390521286308344303

theorem tailTrace_98058 : CollatzResearch.WordTrace tailWord_98058 prefixEnd_98058 7459390521286308344303 := by
  unfold tailWord_98058
  simp only [CollatzResearch.WordTrace]
  refine ⟨894117269690021954553707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2384312719173391878809885 894117269690021954553707)
  ·
    refine ⟨1341175904535032931830561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 894117269690021954553707 1341175904535032931830561)
    ·
      refine ⟨1005881928401274698872921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1341175904535032931830561 1005881928401274698872921)
      ·
        refine ⟨754411446300956024154691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1005881928401274698872921 754411446300956024154691)
        ·
          refine ⟨1131617169451434036232037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754411446300956024154691 1131617169451434036232037)
          ·
            refine ⟨212178219272143881793507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1131617169451434036232037 212178219272143881793507)
            ·
              refine ⟨318267328908215822690261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212178219272143881793507 318267328908215822690261)
              ·
                refine ⟨7459390521286308344303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 318267328908215822690261 7459390521286308344303)
                ·
                  rfl

theorem cell21_98058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_98058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98058 prefixEnd_98058 := by exact prefixLift 98058
  have htrace : WordTrace (prefixWord ++ tailWord_98058) baseStart_98058 baseEnd_98058 := by
    simpa [prefixWord, tailWord_98058, baseEnd_98058] using wordTrace_append hprefix tailTrace_98058
  have hstable : (prefixWord ++ tailWord_98058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98058).length < 2 ^ (prefixWord ++ tailWord_98058).sum := by decide
  have hdescent : baseEnd_98058 < baseStart_98058 := by decide
  rcases family_descends (prefixWord ++ tailWord_98058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98072 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_98072 : Nat := 118140960795 + 98072 * 2 ^ 59
def prefixEnd_98072 : Nat := 4983230072969 + 3 ^ 40 * 98072 * 2
def baseEnd_98072 : Nat := 22381366554598011799547

theorem tailTrace_98072 : CollatzResearch.WordTrace tailWord_98072 prefixEnd_98072 22381366554598011799547 := by
  unfold tailWord_98072
  simp only [CollatzResearch.WordTrace]
  refine ⟨1788489850354684104612235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2384653133806245472816313 1788489850354684104612235)
  ·
    refine ⟨2682734775532026156918353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1788489850354684104612235 2682734775532026156918353)
    ·
      refine ⟨2012051081649019617688765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2682734775532026156918353 2012051081649019617688765)
      ·
        refine ⟨754519155618382356633287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2012051081649019617688765 754519155618382356633287)
        ·
          refine ⟨1131778733427573534949931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754519155618382356633287 1131778733427573534949931)
          ·
            refine ⟨1697668100141360302424897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131778733427573534949931 1697668100141360302424897)
            ·
              refine ⟨1273251075106020226818673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697668100141360302424897 1273251075106020226818673)
              ·
                refine ⟨954938306329515170114005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273251075106020226818673 954938306329515170114005)
                ·
                  refine ⟨22381366554598011799547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 954938306329515170114005 22381366554598011799547)
                  ·
                    rfl

theorem cell21_98072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_98072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98072 prefixEnd_98072 := by exact prefixLift 98072
  have htrace : WordTrace (prefixWord ++ tailWord_98072) baseStart_98072 baseEnd_98072 := by
    simpa [prefixWord, tailWord_98072, baseEnd_98072] using wordTrace_append hprefix tailTrace_98072
  have hstable : (prefixWord ++ tailWord_98072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98072).length < 2 ^ (prefixWord ++ tailWord_98072).sum := by decide
  have hdescent : baseEnd_98072 < baseStart_98072 := by decide
  rcases family_descends (prefixWord ++ tailWord_98072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98117 : List Nat := [1, 3, 1, 1, 1, 2, 3, 9]
def baseStart_98117 : Nat := 118140960795 + 98117 * 2 ^ 59
def prefixEnd_98117 : Nat := 4983230072969 + 3 ^ 40 * 98117 * 2
def baseEnd_98117 : Nat := 7463878722562644516485

theorem tailTrace_98117 : CollatzResearch.WordTrace tailWord_98117 prefixEnd_98117 7463878722562644516485 := by
  unfold tailWord_98117
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578620985546340894612605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2385747323697560596408403 3578620985546340894612605)
  ·
    refine ⟨1341982869579877835479727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3578620985546340894612605 1341982869579877835479727)
    ·
      refine ⟨2012974304369816753219591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341982869579877835479727 2012974304369816753219591)
      ·
        refine ⟨3019461456554725129829387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012974304369816753219591 3019461456554725129829387)
        ·
          refine ⟨4529192184832087694744081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019461456554725129829387 4529192184832087694744081)
          ·
            refine ⟨3396894138624065771058061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4529192184832087694744081 3396894138624065771058061)
            ·
              refine ⟨1273835301984024664146773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3396894138624065771058061 1273835301984024664146773)
              ·
                refine ⟨7463878722562644516485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1273835301984024664146773 7463878722562644516485)
                ·
                  rfl

theorem cell21_98117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 9].length) (baseStart_98117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98117 prefixEnd_98117 := by exact prefixLift 98117
  have htrace : WordTrace (prefixWord ++ tailWord_98117) baseStart_98117 baseEnd_98117 := by
    simpa [prefixWord, tailWord_98117, baseEnd_98117] using wordTrace_append hprefix tailTrace_98117
  have hstable : (prefixWord ++ tailWord_98117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98117).length < 2 ^ (prefixWord ++ tailWord_98117).sum := by decide
  have hdescent : baseEnd_98117 < baseStart_98117 := by decide
  rcases family_descends (prefixWord ++ tailWord_98117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98165 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 5]
def baseStart_98165 : Nat := 118140960795 + 98165 * 2 ^ 59
def prefixEnd_98165 : Nat := 4983230072969 + 3 ^ 40 * 98165 * 2
def baseEnd_98165 : Nat := 22402590421650516749357

theorem tailTrace_98165 : CollatzResearch.WordTrace tailWord_98165 prefixEnd_98165 22402590421650516749357 := by
  unfold tailWord_98165
  simp only [CollatzResearch.WordTrace]
  refine ⟨3580371689372445092359949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2386914459581630061573299 3580371689372445092359949)
  ·
    refine ⟨1342639383514666909634981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3580371689372445092359949 1342639383514666909634981)
    ·
      refine ⟨251744884409000045556559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1342639383514666909634981 251744884409000045556559)
      ·
        refine ⟨377617326613500068334839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251744884409000045556559 377617326613500068334839)
        ·
          refine ⟨566425989920250102502259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377617326613500068334839 566425989920250102502259)
          ·
            refine ⟨849638984880375153753389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566425989920250102502259 849638984880375153753389)
            ·
              refine ⟨318614619330140682657521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849638984880375153753389 318614619330140682657521)
              ·
                refine ⟨238960964497605511993141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318614619330140682657521 238960964497605511993141)
                ·
                  refine ⟨22402590421650516749357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 238960964497605511993141 22402590421650516749357)
                  ·
                    rfl

theorem cell21_98165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_98165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98165 prefixEnd_98165 := by exact prefixLift 98165
  have htrace : WordTrace (prefixWord ++ tailWord_98165) baseStart_98165 baseEnd_98165 := by
    simpa [prefixWord, tailWord_98165, baseEnd_98165] using wordTrace_append hprefix tailTrace_98165
  have hstable : (prefixWord ++ tailWord_98165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98165).length < 2 ^ (prefixWord ++ tailWord_98165).sum := by decide
  have hdescent : baseEnd_98165 < baseStart_98165 := by decide
  rcases family_descends (prefixWord ++ tailWord_98165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98196 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 6]
def baseStart_98196 : Nat := 118140960795 + 98196 * 2 ^ 59
def prefixEnd_98196 : Nat := 4983230072969 + 3 ^ 40 * 98196 * 2
def baseEnd_98196 : Nat := 22409665044001351732627

theorem tailTrace_98196 : CollatzResearch.WordTrace tailWord_98196 prefixEnd_98196 22409665044001351732627 := by
  unfold tailWord_98196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790751176130068693369221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2387668234840091591158961 1790751176130068693369221)
  ·
    refine ⟨335765845524387880006729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1790751176130068693369221 335765845524387880006729)
    ·
      refine ⟨251824384143290910005047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335765845524387880006729 251824384143290910005047)
      ·
        refine ⟨377736576214936365007571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251824384143290910005047 377736576214936365007571)
        ·
          refine ⟨566604864322404547511357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377736576214936365007571 566604864322404547511357)
          ·
            refine ⟨212476824120901705316759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 566604864322404547511357 212476824120901705316759)
            ·
              refine ⟨318715236181352557975139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212476824120901705316759 318715236181352557975139)
              ·
                refine ⟨478072854272028836962709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318715236181352557975139 478072854272028836962709)
                ·
                  refine ⟨22409665044001351732627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 478072854272028836962709 22409665044001351732627)
                  ·
                    rfl

theorem cell21_98196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_98196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98196 prefixEnd_98196 := by exact prefixLift 98196
  have htrace : WordTrace (prefixWord ++ tailWord_98196) baseStart_98196 baseEnd_98196 := by
    simpa [prefixWord, tailWord_98196, baseEnd_98196] using wordTrace_append hprefix tailTrace_98196
  have hstable : (prefixWord ++ tailWord_98196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98196).length < 2 ^ (prefixWord ++ tailWord_98196).sum := by decide
  have hdescent : baseEnd_98196 < baseStart_98196 := by decide
  rcases family_descends (prefixWord ++ tailWord_98196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98255 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 4]
def baseStart_98255 : Nat := 118140960795 + 98255 * 2 ^ 59
def prefixEnd_98255 : Nat := 4983230072969 + 3 ^ 40 * 98255 * 2
def baseEnd_98255 : Nat := 22423129647830360249173

theorem tailTrace_98255 : CollatzResearch.WordTrace tailWord_98255 prefixEnd_98255 22423129647830360249173 := by
  unfold tailWord_98255
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583654259046390463136219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2389102839364260308757479 3583654259046390463136219)
  ·
    refine ⟨5375481388569585694704329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3583654259046390463136219 5375481388569585694704329)
    ·
      refine ⟨4031611041427189271028247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5375481388569585694704329 4031611041427189271028247)
      ·
        refine ⟨6047416562140783906542371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4031611041427189271028247 6047416562140783906542371)
        ·
          refine ⟨9071124843211175859813557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047416562140783906542371 9071124843211175859813557)
          ·
            refine ⟨850417954051047736857521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9071124843211175859813557 850417954051047736857521)
            ·
              refine ⟨637813465538285802643141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850417954051047736857521 637813465538285802643141)
              ·
                refine ⟨119590024788428587995589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 637813465538285802643141 119590024788428587995589)
                ·
                  refine ⟨22423129647830360249173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119590024788428587995589 22423129647830360249173)
                  ·
                    rfl

theorem cell21_98255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 4].length) (baseStart_98255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98255 prefixEnd_98255 := by exact prefixLift 98255
  have htrace : WordTrace (prefixWord ++ tailWord_98255) baseStart_98255 baseEnd_98255 := by
    simpa [prefixWord, tailWord_98255, baseEnd_98255] using wordTrace_append hprefix tailTrace_98255
  have hstable : (prefixWord ++ tailWord_98255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98255).length < 2 ^ (prefixWord ++ tailWord_98255).sum := by decide
  have hdescent : baseEnd_98255 < baseStart_98255 := by decide
  rcases family_descends (prefixWord ++ tailWord_98255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98286 : List Nat := [4, 1, 2, 1, 3, 1, 2, 7]
def baseStart_98286 : Nat := 118140960795 + 98286 * 2 ^ 59
def prefixEnd_98286 : Nat := 4983230072969 + 3 ^ 40 * 98286 * 2
def baseEnd_98286 : Nat := 7476734756727065077481

theorem tailTrace_98286 : CollatzResearch.WordTrace tailWord_98286 prefixEnd_98286 7476734756727065077481 := by
  unfold tailWord_98286
  simp only [CollatzResearch.WordTrace]
  refine ⟨448098115241760344689339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2389856614622721838343141 448098115241760344689339)
  ·
    refine ⟨672147172862640517034009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 448098115241760344689339 672147172862640517034009)
    ·
      refine ⟨504110379646980387775507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 672147172862640517034009 504110379646980387775507)
      ·
        refine ⟨756165569470470581663261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504110379646980387775507 756165569470470581663261)
        ·
          refine ⟨283562088551426468123723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 756165569470470581663261 283562088551426468123723)
          ·
            refine ⟨425343132827139702185585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283562088551426468123723 425343132827139702185585)
            ·
              refine ⟨319007349620354776639189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425343132827139702185585 319007349620354776639189)
              ·
                refine ⟨7476734756727065077481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 319007349620354776639189 7476734756727065077481)
                ·
                  rfl

theorem cell21_98286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_98286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98286 prefixEnd_98286 := by exact prefixLift 98286
  have htrace : WordTrace (prefixWord ++ tailWord_98286) baseStart_98286 baseEnd_98286 := by
    simpa [prefixWord, tailWord_98286, baseEnd_98286] using wordTrace_append hprefix tailTrace_98286
  have hstable : (prefixWord ++ tailWord_98286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98286).length < 2 ^ (prefixWord ++ tailWord_98286).sum := by decide
  have hdescent : baseEnd_98286 < baseStart_98286 := by decide
  rcases family_descends (prefixWord ++ tailWord_98286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98469 : List Nat := [1, 3, 1, 2, 1, 3, 2, 5, 3]
def baseStart_98469 : Nat := 118140960795 + 98469 * 2 ^ 59
def prefixEnd_98469 : Nat := 4983230072969 + 3 ^ 40 * 98469 * 2
def baseEnd_98469 : Nat := 22471967363413543682069

theorem tailTrace_98469 : CollatzResearch.WordTrace tailWord_98469 prefixEnd_98469 22471967363413543682069 := by
  unfold tailWord_98469
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591459480271105011426461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2394306320180736674284307 3591459480271105011426461)
  ·
    refine ⟨1346797305101664379284923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3591459480271105011426461 1346797305101664379284923)
    ·
      refine ⟨2020195957652496568927385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346797305101664379284923 2020195957652496568927385)
      ·
        refine ⟨1515146968239372426695539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2020195957652496568927385 1515146968239372426695539)
        ·
          refine ⟨2272720452359058640043309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515146968239372426695539 2272720452359058640043309)
          ·
            refine ⟨852270169634646990016241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2272720452359058640043309 852270169634646990016241)
            ·
              refine ⟨639202627225985242512181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852270169634646990016241 639202627225985242512181)
              ·
                refine ⟨59925246302436116485517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 639202627225985242512181 59925246302436116485517)
                ·
                  refine ⟨22471967363413543682069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59925246302436116485517 22471967363413543682069)
                  ·
                    rfl

theorem cell21_98469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_98469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98469 prefixEnd_98469 := by exact prefixLift 98469
  have htrace : WordTrace (prefixWord ++ tailWord_98469) baseStart_98469 baseEnd_98469 := by
    simpa [prefixWord, tailWord_98469, baseEnd_98469] using wordTrace_append hprefix tailTrace_98469
  have hstable : (prefixWord ++ tailWord_98469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98469).length < 2 ^ (prefixWord ++ tailWord_98469).sum := by decide
  have hdescent : baseEnd_98469 < baseStart_98469 := by decide
  rcases family_descends (prefixWord ++ tailWord_98469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98478 : List Nat := [4, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_98478 : Nat := 118140960795 + 98478 * 2 ^ 59
def prefixEnd_98478 : Nat := 4983230072969 + 3 ^ 40 * 98478 * 2
def baseEnd_98478 : Nat := 22474021286031528032051

theorem tailTrace_98478 : CollatzResearch.WordTrace tailWord_98478 prefixEnd_98478 22474021286031528032051 := by
  unfold tailWord_98478
  simp only [CollatzResearch.WordTrace]
  refine ⟨448973467154812443563011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2394525158158999699002725 448973467154812443563011)
  ·
    refine ⟨673460200732218665344517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 448973467154812443563011 673460200732218665344517)
    ·
      refine ⟨126273787637290999752097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 673460200732218665344517 126273787637290999752097)
      ·
        refine ⟨94705340727968249814073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126273787637290999752097 94705340727968249814073)
        ·
          refine ⟨71029005545976187360555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94705340727968249814073 71029005545976187360555)
          ·
            refine ⟨106543508318964281040833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71029005545976187360555 106543508318964281040833)
            ·
              refine ⟨79907631239223210780625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106543508318964281040833 79907631239223210780625)
              ·
                refine ⟨59930723429417408085469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79907631239223210780625 59930723429417408085469)
                ·
                  refine ⟨22474021286031528032051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59930723429417408085469 22474021286031528032051)
                  ·
                    rfl

theorem cell21_98478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_98478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98478 prefixEnd_98478 := by exact prefixLift 98478
  have htrace : WordTrace (prefixWord ++ tailWord_98478) baseStart_98478 baseEnd_98478 := by
    simpa [prefixWord, tailWord_98478, baseEnd_98478] using wordTrace_append hprefix tailTrace_98478
  have hstable : (prefixWord ++ tailWord_98478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98478).length < 2 ^ (prefixWord ++ tailWord_98478).sum := by decide
  have hdescent : baseEnd_98478 < baseStart_98478 := by decide
  rcases family_descends (prefixWord ++ tailWord_98478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98500 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 4]
def baseStart_98500 : Nat := 118140960795 + 98500 * 2 ^ 59
def prefixEnd_98500 : Nat := 4983230072969 + 3 ^ 40 * 98500 * 2
def baseEnd_98500 : Nat := 22479041985764378665339

theorem tailTrace_98500 : CollatzResearch.WordTrace tailWord_98500 prefixEnd_98500 22479041985764378665339 := by
  unfold tailWord_98500
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796295071579398652902477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2395060095439198203869969 1796295071579398652902477)
  ·
    refine ⟨673610651842274494838429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1796295071579398652902477 673610651842274494838429)
    ·
      refine ⟨252603994440852935564411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 673610651842274494838429 252603994440852935564411)
      ·
        refine ⟨378905991661279403346617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252603994440852935564411 378905991661279403346617)
        ·
          refine ⟨284179493745959552509963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378905991661279403346617 284179493745959552509963)
          ·
            refine ⟨426269240618939328764945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284179493745959552509963 426269240618939328764945)
            ·
              refine ⟨319701930464204496573709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426269240618939328764945 319701930464204496573709)
              ·
                refine ⟨119888223924076686215141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319701930464204496573709 119888223924076686215141)
                ·
                  refine ⟨22479041985764378665339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119888223924076686215141 22479041985764378665339)
                  ·
                    rfl

theorem cell21_98500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_98500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98500 prefixEnd_98500 := by exact prefixLift 98500
  have htrace : WordTrace (prefixWord ++ tailWord_98500) baseStart_98500 baseEnd_98500 := by
    simpa [prefixWord, tailWord_98500, baseEnd_98500] using wordTrace_append hprefix tailTrace_98500
  have hstable : (prefixWord ++ tailWord_98500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98500).length < 2 ^ (prefixWord ++ tailWord_98500).sum := by decide
  have hdescent : baseEnd_98500 < baseStart_98500 := by decide
  rcases family_descends (prefixWord ++ tailWord_98500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98545 : List Nat := [1, 2, 2, 2, 2, 1, 4, 4, 3]
def baseStart_98545 : Nat := 118140960795 + 98545 * 2 ^ 59
def prefixEnd_98545 : Nat := 4983230072969 + 3 ^ 40 * 98545 * 2
def baseEnd_98545 : Nat := 22489311598854300415247

theorem tailTrace_98545 : CollatzResearch.WordTrace tailWord_98545 prefixEnd_98545 22489311598854300415247 := by
  unfold tailWord_98545
  simp only [CollatzResearch.WordTrace]
  refine ⟨3594231427995769991193089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2396154285330513327462059 3594231427995769991193089)
  ·
    refine ⟨2695673570996827493394817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3594231427995769991193089 2695673570996827493394817)
    ·
      refine ⟨2021755178247620620046113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2695673570996827493394817 2021755178247620620046113)
      ·
        refine ⟨1516316383685715465034585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2021755178247620620046113 1516316383685715465034585)
        ·
          refine ⟨1137237287764286598775939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1516316383685715465034585 1137237287764286598775939)
          ·
            refine ⟨1705855931646429898163909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137237287764286598775939 1705855931646429898163909)
            ·
              refine ⟨319847987183705605905733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1705855931646429898163909 319847987183705605905733)
              ·
                refine ⟨59971497596944801107325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319847987183705605905733 59971497596944801107325)
                ·
                  refine ⟨22489311598854300415247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59971497596944801107325 22489311598854300415247)
                  ·
                    rfl

theorem cell21_98545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 3].length) (baseStart_98545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98545 prefixEnd_98545 := by exact prefixLift 98545
  have htrace : WordTrace (prefixWord ++ tailWord_98545) baseStart_98545 baseEnd_98545 := by
    simpa [prefixWord, tailWord_98545, baseEnd_98545] using wordTrace_append hprefix tailTrace_98545
  have hstable : (prefixWord ++ tailWord_98545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98545).length < 2 ^ (prefixWord ++ tailWord_98545).sum := by decide
  have hdescent : baseEnd_98545 < baseStart_98545 := by decide
  rcases family_descends (prefixWord ++ tailWord_98545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98587 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 7]
def baseStart_98587 : Nat := 118140960795 + 98587 * 2 ^ 59
def prefixEnd_98587 : Nat := 4983230072969 + 3 ^ 40 * 98587 * 2
def baseEnd_98587 : Nat := 22498896571071560715161

theorem tailTrace_98587 : CollatzResearch.WordTrace tailWord_98587 prefixEnd_98587 22498896571071560715161 := by
  unfold tailWord_98587
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595763293843611164222015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2397175529229074109481343 3595763293843611164222015)
  ·
    refine ⟨5393644940765416746333023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3595763293843611164222015 5393644940765416746333023)
    ·
      refine ⟨8090467411148125119499535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5393644940765416746333023 8090467411148125119499535)
      ·
        refine ⟨12135701116722187679249303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8090467411148125119499535 12135701116722187679249303)
        ·
          refine ⟨18203551675083281518873955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12135701116722187679249303 18203551675083281518873955)
          ·
            refine ⟨27305327512624922278310933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18203551675083281518873955 27305327512624922278310933)
            ·
              refine ⟨1279937227154293231795825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27305327512624922278310933 1279937227154293231795825)
              ·
                refine ⟨959952920365719923846869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279937227154293231795825 959952920365719923846869)
                ·
                  refine ⟨22498896571071560715161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 959952920365719923846869 22498896571071560715161)
                  ·
                    rfl

theorem cell21_98587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_98587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98587 prefixEnd_98587 := by exact prefixLift 98587
  have htrace : WordTrace (prefixWord ++ tailWord_98587) baseStart_98587 baseEnd_98587 := by
    simpa [prefixWord, tailWord_98587, baseEnd_98587] using wordTrace_append hprefix tailTrace_98587
  have hstable : (prefixWord ++ tailWord_98587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98587).length < 2 ^ (prefixWord ++ tailWord_98587).sum := by decide
  have hdescent : baseEnd_98587 < baseStart_98587 := by decide
  rcases family_descends (prefixWord ++ tailWord_98587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98604 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 5]
def baseStart_98604 : Nat := 118140960795 + 98604 * 2 ^ 59
def prefixEnd_98604 : Nat := 4983230072969 + 3 ^ 40 * 98604 * 2
def baseEnd_98604 : Nat := 22502776202683308931793

theorem tailTrace_98604 : CollatzResearch.WordTrace tailWord_98604 prefixEnd_98604 22502776202683308931793 := by
  unfold tailWord_98604
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798191667391011533795433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2397588889854682045060577 1798191667391011533795433)
  ·
    refine ⟨1348643750543258650346575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1798191667391011533795433 1348643750543258650346575)
    ·
      refine ⟨2022965625814887975519863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1348643750543258650346575 2022965625814887975519863)
      ·
        refine ⟨3034448438722331963279795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2022965625814887975519863 3034448438722331963279795)
        ·
          refine ⟨4551672658083497944919693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034448438722331963279795 4551672658083497944919693)
          ·
            refine ⟨1706877246781311729344885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4551672658083497944919693 1706877246781311729344885)
            ·
              refine ⟨160019741885747974626083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1706877246781311729344885 160019741885747974626083)
              ·
                refine ⟨240029612828621961939125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160019741885747974626083 240029612828621961939125)
                ·
                  refine ⟨22502776202683308931793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240029612828621961939125 22502776202683308931793)
                  ·
                    rfl

theorem cell21_98604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_98604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98604 prefixEnd_98604 := by exact prefixLift 98604
  have htrace : WordTrace (prefixWord ++ tailWord_98604) baseStart_98604 baseEnd_98604 := by
    simpa [prefixWord, tailWord_98604, baseEnd_98604] using wordTrace_append hprefix tailTrace_98604
  have hstable : (prefixWord ++ tailWord_98604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98604).length < 2 ^ (prefixWord ++ tailWord_98604).sum := by decide
  have hdescent : baseEnd_98604 < baseStart_98604 := by decide
  rcases family_descends (prefixWord ++ tailWord_98604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98610 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 4]
def baseStart_98610 : Nat := 118140960795 + 98610 * 2 ^ 59
def prefixEnd_98610 : Nat := 4983230072969 + 3 ^ 40 * 98610 * 2
def baseEnd_98610 : Nat := 22504145484428631831781

theorem tailTrace_98610 : CollatzResearch.WordTrace tailWord_98610 prefixEnd_98610 22504145484428631831781 := by
  unfold tailWord_98610
  simp only [CollatzResearch.WordTrace]
  refine ⟨899150543190071523077321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2397734781840190728206189 899150543190071523077321)
  ·
    refine ⟨674362907392553642307991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 899150543190071523077321 674362907392553642307991)
    ·
      refine ⟨1011544361088830463461987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674362907392553642307991 1011544361088830463461987)
      ·
        refine ⟨1517316541633245695192981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011544361088830463461987 1517316541633245695192981)
        ·
          refine ⟨71124212889058391962171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1517316541633245695192981 71124212889058391962171)
          ·
            refine ⟨106686319333587587943257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71124212889058391962171 106686319333587587943257)
            ·
              refine ⟨80014739500190690957443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106686319333587587943257 80014739500190690957443)
              ·
                refine ⟨120022109250286036436165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80014739500190690957443 120022109250286036436165)
                ·
                  refine ⟨22504145484428631831781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120022109250286036436165 22504145484428631831781)
                  ·
                    rfl

theorem cell21_98610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_98610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98610 prefixEnd_98610 := by exact prefixLift 98610
  have htrace : WordTrace (prefixWord ++ tailWord_98610) baseStart_98610 baseEnd_98610 := by
    simpa [prefixWord, tailWord_98610, baseEnd_98610] using wordTrace_append hprefix tailTrace_98610
  have hstable : (prefixWord ++ tailWord_98610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98610).length < 2 ^ (prefixWord ++ tailWord_98610).sum := by decide
  have hdescent : baseEnd_98610 < baseStart_98610 := by decide
  rcases family_descends (prefixWord ++ tailWord_98610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98666 : List Nat := [3, 1, 3, 3, 1, 1, 3, 6]
def baseStart_98666 : Nat := 118140960795 + 98666 * 2 ^ 59
def prefixEnd_98666 : Nat := 4983230072969 + 3 ^ 40 * 98666 * 2
def baseEnd_98666 : Nat := 7505641815794992966111

theorem tailTrace_98666 : CollatzResearch.WordTrace tailWord_98666 prefixEnd_98666 7505641815794992966111 := by
  unfold tailWord_98666
  simp only [CollatzResearch.WordTrace]
  refine ⟨899661165139351914086963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2399096440371605104231901 899661165139351914086963)
  ·
    refine ⟨1349491747709027871130445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 899661165139351914086963 1349491747709027871130445)
    ·
      refine ⟨506059405390885451673917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1349491747709027871130445 506059405390885451673917)
      ·
        refine ⟨189772277021582044377719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506059405390885451673917 189772277021582044377719)
        ·
          refine ⟨284658415532373066566579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189772277021582044377719 284658415532373066566579)
          ·
            refine ⟨426987623298559599849869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284658415532373066566579 426987623298559599849869)
            ·
              refine ⟨160120358736959849943701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426987623298559599849869 160120358736959849943701)
              ·
                refine ⟨7505641815794992966111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160120358736959849943701 7505641815794992966111)
                ·
                  rfl

theorem cell21_98666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_98666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98666 prefixEnd_98666 := by exact prefixLift 98666
  have htrace : WordTrace (prefixWord ++ tailWord_98666) baseStart_98666 baseEnd_98666 := by
    simpa [prefixWord, tailWord_98666, baseEnd_98666] using wordTrace_append hprefix tailTrace_98666
  have hstable : (prefixWord ++ tailWord_98666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98666).length < 2 ^ (prefixWord ++ tailWord_98666).sum := by decide
  have hdescent : baseEnd_98666 < baseStart_98666 := by decide
  rcases family_descends (prefixWord ++ tailWord_98666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98697 : List Nat := [1, 2, 1, 1, 6, 1, 1, 5, 3]
def baseStart_98697 : Nat := 118140960795 + 98697 * 2 ^ 59
def prefixEnd_98697 : Nat := 4983230072969 + 3 ^ 40 * 98697 * 2
def baseEnd_98697 : Nat := 22524000069735813881603

theorem tailTrace_98697 : CollatzResearch.WordTrace tailWord_98697 prefixEnd_98697 22524000069735813881603 := by
  unfold tailWord_98697
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599775323445099950726345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2399850215630066633817563 3599775323445099950726345)
  ·
    refine ⟨2699831492583824963044759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3599775323445099950726345 2699831492583824963044759)
    ·
      refine ⟨4049747238875737444567139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2699831492583824963044759 4049747238875737444567139)
      ·
        refine ⟨6074620858313606166850709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4049747238875737444567139 6074620858313606166850709)
        ·
          refine ⟨284747852733450289071127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6074620858313606166850709 284747852733450289071127)
          ·
            refine ⟨427121779100175433606691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284747852733450289071127 427121779100175433606691)
            ·
              refine ⟨640682668650263150410037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427121779100175433606691 640682668650263150410037)
              ·
                refine ⟨60064000185962170350941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 640682668650263150410037 60064000185962170350941)
                ·
                  refine ⟨22524000069735813881603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60064000185962170350941 22524000069735813881603)
                  ·
                    rfl

theorem cell21_98697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 3].length) (baseStart_98697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98697 prefixEnd_98697 := by exact prefixLift 98697
  have htrace : WordTrace (prefixWord ++ tailWord_98697) baseStart_98697 baseEnd_98697 := by
    simpa [prefixWord, tailWord_98697, baseEnd_98697] using wordTrace_append hprefix tailTrace_98697
  have hstable : (prefixWord ++ tailWord_98697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98697).length < 2 ^ (prefixWord ++ tailWord_98697).sum := by decide
  have hdescent : baseEnd_98697 < baseStart_98697 := by decide
  rcases family_descends (prefixWord ++ tailWord_98697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98711 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 4]
def baseStart_98711 : Nat := 118140960795 + 98711 * 2 ^ 59
def prefixEnd_98711 : Nat := 4983230072969 + 3 ^ 40 * 98711 * 2
def baseEnd_98711 : Nat := 22527195060474900648241

theorem tailTrace_98711 : CollatzResearch.WordTrace tailWord_98711 prefixEnd_98711 22527195060474900648241 := by
  unfold tailWord_98711
  simp only [CollatzResearch.WordTrace]
  refine ⟨3600285945394380341735987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2400190630262920227823991 3600285945394380341735987)
  ·
    refine ⟨5400428918091570512603981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3600285945394380341735987 5400428918091570512603981)
    ·
      refine ⟨2025160844284338942226493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5400428918091570512603981 2025160844284338942226493)
      ·
        refine ⟨759435316606627103334935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2025160844284338942226493 759435316606627103334935)
        ·
          refine ⟨1139152974909940655002403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759435316606627103334935 1139152974909940655002403)
          ·
            refine ⟨1708729462364910982503605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139152974909940655002403 1708729462364910982503605)
            ·
              refine ⟨160193387096710404609713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1708729462364910982503605 160193387096710404609713)
              ·
                refine ⟨120145040322532803457285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160193387096710404609713 120145040322532803457285)
                ·
                  refine ⟨22527195060474900648241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120145040322532803457285 22527195060474900648241)
                  ·
                    rfl

theorem cell21_98711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 4].length) (baseStart_98711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98711 prefixEnd_98711 := by exact prefixLift 98711
  have htrace : WordTrace (prefixWord ++ tailWord_98711) baseStart_98711 baseEnd_98711 := by
    simpa [prefixWord, tailWord_98711, baseEnd_98711] using wordTrace_append hprefix tailTrace_98711
  have hstable : (prefixWord ++ tailWord_98711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98711).length < 2 ^ (prefixWord ++ tailWord_98711).sum := by decide
  have hdescent : baseEnd_98711 < baseStart_98711 := by decide
  rcases family_descends (prefixWord ++ tailWord_98711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98773 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 5]
def baseStart_98773 : Nat := 118140960795 + 98773 * 2 ^ 59
def prefixEnd_98773 : Nat := 4983230072969 + 3 ^ 40 * 98773 * 2
def baseEnd_98773 : Nat := 22541344305176570614781

theorem tailTrace_98773 : CollatzResearch.WordTrace tailWord_98773 prefixEnd_98773 22541344305176570614781 := by
  unfold tailWord_98773
  simp only [CollatzResearch.WordTrace]
  refine ⟨3602547271169764930492973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2401698180779843286995315 3602547271169764930492973)
  ·
    refine ⟨1350955226688661848934865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3602547271169764930492973 1350955226688661848934865)
    ·
      refine ⟨1013216420016496386701149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1350955226688661848934865 1013216420016496386701149)
      ·
        refine ⟨379956157506186145012931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1013216420016496386701149 379956157506186145012931)
        ·
          refine ⟨569934236259279217519397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379956157506186145012931 569934236259279217519397)
          ·
            refine ⟨106862669298614853284887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 569934236259279217519397 106862669298614853284887)
            ·
              refine ⟨160294003947922279927331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106862669298614853284887 160294003947922279927331)
              ·
                refine ⟨240441005921883419890997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160294003947922279927331 240441005921883419890997)
                ·
                  refine ⟨22541344305176570614781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240441005921883419890997 22541344305176570614781)
                  ·
                    rfl

theorem cell21_98773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_98773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98773 prefixEnd_98773 := by exact prefixLift 98773
  have htrace : WordTrace (prefixWord ++ tailWord_98773) baseStart_98773 baseEnd_98773 := by
    simpa [prefixWord, tailWord_98773, baseEnd_98773] using wordTrace_append hprefix tailTrace_98773
  have hstable : (prefixWord ++ tailWord_98773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98773).length < 2 ^ (prefixWord ++ tailWord_98773).sum := by decide
  have hdescent : baseEnd_98773 < baseStart_98773 := by decide
  rcases family_descends (prefixWord ++ tailWord_98773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98818 : List Nat := [3, 4, 1, 2, 2, 9]
def baseStart_98818 : Nat := 118140960795 + 98818 * 2 ^ 59
def prefixEnd_98818 : Nat := 4983230072969 + 3 ^ 40 * 98818 * 2
def baseEnd_98818 : Nat := 835244959935796013507

theorem tailTrace_98818 : CollatzResearch.WordTrace tailWord_98818 prefixEnd_98818 835244959935796013507 := by
  unfold tailWord_98818
  simp only [CollatzResearch.WordTrace]
  refine ⟨901047139001684403970277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2402792370671158410587405 901047139001684403970277)
  ·
    refine ⟨168946338562815825744427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 901047139001684403970277 168946338562815825744427)
    ·
      refine ⟨253419507844223738616641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168946338562815825744427 253419507844223738616641)
      ·
        refine ⟨190064630883167803962481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253419507844223738616641 190064630883167803962481)
        ·
          refine ⟨142548473162375852971861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190064630883167803962481 142548473162375852971861)
          ·
            refine ⟨835244959935796013507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 142548473162375852971861 835244959935796013507)
            ·
              rfl

theorem cell21_98818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 9].length) (baseStart_98818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98818 prefixEnd_98818 := by exact prefixLift 98818
  have htrace : WordTrace (prefixWord ++ tailWord_98818) baseStart_98818 baseEnd_98818 := by
    simpa [prefixWord, tailWord_98818, baseEnd_98818] using wordTrace_append hprefix tailTrace_98818
  have hstable : (prefixWord ++ tailWord_98818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98818).length < 2 ^ (prefixWord ++ tailWord_98818).sum := by decide
  have hdescent : baseEnd_98818 < baseStart_98818 := by decide
  rcases family_descends (prefixWord ++ tailWord_98818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98860 : List Nat := [2, 2, 1, 1, 1, 2, 1, 11]
def baseStart_98860 : Nat := 118140960795 + 98860 * 2 ^ 59
def prefixEnd_98860 : Nat := 4983230072969 + 3 ^ 40 * 98860 * 2
def baseEnd_98860 : Nat := 7520399630161250888201

theorem tailTrace_98860 : CollatzResearch.WordTrace tailWord_98860 prefixEnd_98860 7520399630161250888201 := by
  unfold tailWord_98860
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802860210927289394455017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2403813614569719192606689 1802860210927289394455017)
  ·
    refine ⟨1352145158195467045841263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1802860210927289394455017 1352145158195467045841263)
    ·
      refine ⟨2028217737293200568761895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1352145158195467045841263 2028217737293200568761895)
      ·
        refine ⟨3042326605939800853142843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2028217737293200568761895 3042326605939800853142843)
        ·
          refine ⟨4563489908909701279714265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042326605939800853142843 4563489908909701279714265)
          ·
            refine ⟨3422617431682275959785699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4563489908909701279714265 3422617431682275959785699)
            ·
              refine ⟨5133926147523413939678549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422617431682275959785699 5133926147523413939678549)
              ·
                refine ⟨7520399630161250888201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 5133926147523413939678549 7520399630161250888201)
                ·
                  rfl

theorem cell21_98860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_98860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98860 prefixEnd_98860 := by exact prefixLift 98860
  have htrace : WordTrace (prefixWord ++ tailWord_98860) baseStart_98860 baseEnd_98860 := by
    simpa [prefixWord, tailWord_98860, baseEnd_98860] using wordTrace_append hprefix tailTrace_98860
  have hstable : (prefixWord ++ tailWord_98860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98860).length < 2 ^ (prefixWord ++ tailWord_98860).sum := by decide
  have hdescent : baseEnd_98860 < baseStart_98860 := by decide
  rcases family_descends (prefixWord ++ tailWord_98860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98877 : List Nat := [1, 4, 1, 3, 2, 2, 8]
def baseStart_98877 : Nat := 118140960795 + 98877 * 2 ^ 59
def prefixEnd_98877 : Nat := 4983230072969 + 3 ^ 40 * 98877 * 2
def baseEnd_98877 : Nat := 2507230946899500097915

theorem tailTrace_98877 : CollatzResearch.WordTrace tailWord_98877 prefixEnd_98877 2507230946899500097915 := by
  unfold tailWord_98877
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606340462792990692278885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2404226975195327128185923 3606340462792990692278885)
  ·
    refine ⟨676188836773685754802291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3606340462792990692278885 676188836773685754802291)
    ·
      refine ⟨1014283255160528632203437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676188836773685754802291 1014283255160528632203437)
      ·
        refine ⟨380356220685198237076289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1014283255160528632203437 380356220685198237076289)
        ·
          refine ⟨285267165513898677807217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380356220685198237076289 285267165513898677807217)
          ·
            refine ⟨213950374135424008355413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285267165513898677807217 213950374135424008355413)
            ·
              refine ⟨2507230946899500097915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 213950374135424008355413 2507230946899500097915)
              ·
                rfl

theorem cell21_98877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 8].length) (baseStart_98877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98877 prefixEnd_98877 := by exact prefixLift 98877
  have htrace : WordTrace (prefixWord ++ tailWord_98877) baseStart_98877 baseEnd_98877 := by
    simpa [prefixWord, tailWord_98877, baseEnd_98877] using wordTrace_append hprefix tailTrace_98877
  have hstable : (prefixWord ++ tailWord_98877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98877).length < 2 ^ (prefixWord ++ tailWord_98877).sum := by decide
  have hdescent : baseEnd_98877 < baseStart_98877 := by decide
  rcases family_descends (prefixWord ++ tailWord_98877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98891 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 5]
def baseStart_98891 : Nat := 118140960795 + 98891 * 2 ^ 59
def prefixEnd_98891 : Nat := 4983230072969 + 3 ^ 40 * 98891 * 2
def baseEnd_98891 : Nat := 22568273512834587647873

theorem tailTrace_98891 : CollatzResearch.WordTrace tailWord_98891 prefixEnd_98891 22568273512834587647873 := by
  unfold tailWord_98891
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606851084742271083288527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2404567389828180722192351 3606851084742271083288527)
  ·
    refine ⟨5410276627113406624932791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3606851084742271083288527 5410276627113406624932791)
    ·
      refine ⟨8115414940670109937399187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5410276627113406624932791 8115414940670109937399187)
      ·
        refine ⟨12173122411005164906098781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8115414940670109937399187 12173122411005164906098781)
        ·
          refine ⟨4564920904126936839787043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12173122411005164906098781 4564920904126936839787043)
          ·
            refine ⟨6847381356190405259680565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564920904126936839787043 6847381356190405259680565)
            ·
              refine ⟨641942002142850493095053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6847381356190405259680565 641942002142850493095053)
              ·
                refine ⟨240728250803568934910645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 641942002142850493095053 240728250803568934910645)
                ·
                  refine ⟨22568273512834587647873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240728250803568934910645 22568273512834587647873)
                  ·
                    rfl

theorem cell21_98891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_98891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98891 prefixEnd_98891 := by exact prefixLift 98891
  have htrace : WordTrace (prefixWord ++ tailWord_98891) baseStart_98891 baseEnd_98891 := by
    simpa [prefixWord, tailWord_98891, baseEnd_98891] using wordTrace_append hprefix tailTrace_98891
  have hstable : (prefixWord ++ tailWord_98891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98891).length < 2 ^ (prefixWord ++ tailWord_98891).sum := by decide
  have hdescent : baseEnd_98891 < baseStart_98891 := by decide
  rcases family_descends (prefixWord ++ tailWord_98891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98922 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_98922 : Nat := 118140960795 + 98922 * 2 ^ 59
def prefixEnd_98922 : Nat := 4983230072969 + 3 ^ 40 * 98922 * 2
def baseEnd_98922 : Nat := 22575348135185422631143

theorem tailTrace_98922 : CollatzResearch.WordTrace tailWord_98922 prefixEnd_98922 22575348135185422631143 := by
  unfold tailWord_98922
  simp only [CollatzResearch.WordTrace]
  refine ⟨901995436907490844416755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2405321165086642251778013 901995436907490844416755)
  ·
    refine ⟨1352993155361236266625133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 901995436907490844416755 1352993155361236266625133)
    ·
      refine ⟨507372433260463599984425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1352993155361236266625133 507372433260463599984425)
      ·
        refine ⟨380529324945347699988319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507372433260463599984425 380529324945347699988319)
        ·
          refine ⟨570793987418021549982479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380529324945347699988319 570793987418021549982479)
          ·
            refine ⟨856190981127032324973719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570793987418021549982479 856190981127032324973719)
            ·
              refine ⟨1284286471690548487460579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856190981127032324973719 1284286471690548487460579)
              ·
                refine ⟨1926429707535822731190869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284286471690548487460579 1926429707535822731190869)
                ·
                  refine ⟨22575348135185422631143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1926429707535822731190869 22575348135185422631143)
                  ·
                    rfl

theorem cell21_98922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_98922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98922 prefixEnd_98922 := by exact prefixLift 98922
  have htrace : WordTrace (prefixWord ++ tailWord_98922) baseStart_98922 baseEnd_98922 := by
    simpa [prefixWord, tailWord_98922, baseEnd_98922] using wordTrace_append hprefix tailTrace_98922
  have hstable : (prefixWord ++ tailWord_98922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98922).length < 2 ^ (prefixWord ++ tailWord_98922).sum := by decide
  have hdescent : baseEnd_98922 < baseStart_98922 := by decide
  rcases family_descends (prefixWord ++ tailWord_98922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98967 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 7]
def baseStart_98967 : Nat := 118140960795 + 98967 * 2 ^ 59
def prefixEnd_98967 : Nat := 4983230072969 + 3 ^ 40 * 98967 * 2
def baseEnd_98967 : Nat := 22585617748275344381051

theorem tailTrace_98967 : CollatzResearch.WordTrace tailWord_98967 prefixEnd_98967 22585617748275344381051 := by
  unfold tailWord_98967
  simp only [CollatzResearch.WordTrace]
  refine ⟨3609623032466936063055155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2406415354977957375370103 3609623032466936063055155)
  ·
    refine ⟨5414434548700404094582733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3609623032466936063055155 5414434548700404094582733)
    ·
      refine ⟨2030412955762651535468525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5414434548700404094582733 2030412955762651535468525)
      ·
        refine ⟨761404858410994325800697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2030412955762651535468525 761404858410994325800697)
        ·
          refine ⟨571053643808245744350523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761404858410994325800697 571053643808245744350523)
          ·
            refine ⟨856580465712368616525785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571053643808245744350523 856580465712368616525785)
            ·
              refine ⟨642435349284276462394339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856580465712368616525785 642435349284276462394339)
              ·
                refine ⟨963653023926414693591509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642435349284276462394339 963653023926414693591509)
                ·
                  refine ⟨22585617748275344381051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 963653023926414693591509 22585617748275344381051)
                  ·
                    rfl

theorem cell21_98967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_98967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_98967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_98967 prefixEnd_98967 := by exact prefixLift 98967
  have htrace : WordTrace (prefixWord ++ tailWord_98967) baseStart_98967 baseEnd_98967 := by
    simpa [prefixWord, tailWord_98967, baseEnd_98967] using wordTrace_append hprefix tailTrace_98967
  have hstable : (prefixWord ++ tailWord_98967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98967).length < 2 ^ (prefixWord ++ tailWord_98967).sum := by decide
  have hdescent : baseEnd_98967 < baseStart_98967 := by decide
  rcases family_descends (prefixWord ++ tailWord_98967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99170 : List Nat := [3, 3, 2, 1, 3, 1, 1, 4, 3]
def baseStart_99170 : Nat := 118140960795 + 99170 * 2 ^ 59
def prefixEnd_99170 : Nat := 4983230072969 + 3 ^ 40 * 99170 * 2
def baseEnd_99170 : Nat := 22631945113992102497303

theorem tailTrace_99170 : CollatzResearch.WordTrace tailWord_99170 prefixEnd_99170 22631945113992102497303 := by
  unfold tailWord_99170
  simp only [CollatzResearch.WordTrace]
  refine ⟨904256762682875433173741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2411351367154334488463309 904256762682875433173741)
  ·
    refine ⟨339096286006078287440153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 904256762682875433173741 339096286006078287440153)
    ·
      refine ⟨254322214504558715580115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339096286006078287440153 254322214504558715580115)
      ·
        refine ⟨381483321756838073370173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254322214504558715580115 381483321756838073370173)
        ·
          refine ⟨143056245658814277513815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381483321756838073370173 143056245658814277513815)
          ·
            refine ⟨214584368488221416270723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143056245658814277513815 214584368488221416270723)
            ·
              refine ⟨321876552732332124406085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214584368488221416270723 321876552732332124406085)
              ·
                refine ⟨60351853637312273326141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321876552732332124406085 60351853637312273326141)
                ·
                  refine ⟨22631945113992102497303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60351853637312273326141 22631945113992102497303)
                  ·
                    rfl

theorem cell21_99170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_99170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99170 prefixEnd_99170 := by exact prefixLift 99170
  have htrace : WordTrace (prefixWord ++ tailWord_99170) baseStart_99170 baseEnd_99170 := by
    simpa [prefixWord, tailWord_99170, baseEnd_99170] using wordTrace_append hprefix tailTrace_99170
  have hstable : (prefixWord ++ tailWord_99170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99170).length < 2 ^ (prefixWord ++ tailWord_99170).sum := by decide
  have hdescent : baseEnd_99170 < baseStart_99170 := by decide
  rcases family_descends (prefixWord ++ tailWord_99170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99212 : List Nat := [2, 2, 1, 2, 1, 2, 3, 5, 3]
def baseStart_99212 : Nat := 118140960795 + 99212 * 2 ^ 59
def prefixEnd_99212 : Nat := 4983230072969 + 3 ^ 40 * 99212 * 2
def baseEnd_99212 : Nat := 22641530086209362797217

theorem tailTrace_99212 : CollatzResearch.WordTrace tailWord_99212 prefixEnd_99212 22641530086209362797217 := by
  unfold tailWord_99212
  simp only [CollatzResearch.WordTrace]
  refine ⟨1809279458289671452861945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2412372611052895270482593 1809279458289671452861945)
  ·
    refine ⟨1356959593717253589646459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1809279458289671452861945 1356959593717253589646459)
    ·
      refine ⟨2035439390575880384469689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356959593717253589646459 2035439390575880384469689)
      ·
        refine ⟨1526579542931910288352267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2035439390575880384469689 1526579542931910288352267)
        ·
          refine ⟨2289869314397865432528401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526579542931910288352267 2289869314397865432528401)
          ·
            refine ⟨1717401985798399074396301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2289869314397865432528401 1717401985798399074396301)
            ·
              refine ⟨644025744674399652898613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1717401985798399074396301 644025744674399652898613)
              ·
                refine ⟨60377413563224967459245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 644025744674399652898613 60377413563224967459245)
                ·
                  refine ⟨22641530086209362797217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60377413563224967459245 22641530086209362797217)
                  ·
                    rfl

theorem cell21_99212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_99212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99212 prefixEnd_99212 := by exact prefixLift 99212
  have htrace : WordTrace (prefixWord ++ tailWord_99212) baseStart_99212 baseEnd_99212 := by
    simpa [prefixWord, tailWord_99212, baseEnd_99212] using wordTrace_append hprefix tailTrace_99212
  have hstable : (prefixWord ++ tailWord_99212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99212).length < 2 ^ (prefixWord ++ tailWord_99212).sum := by decide
  have hdescent : baseEnd_99212 < baseStart_99212 := by decide
  rcases family_descends (prefixWord ++ tailWord_99212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99257 : List Nat := [1, 2, 1, 4, 2, 2, 4, 5]
def baseStart_99257 : Nat := 118140960795 + 99257 * 2 ^ 59
def prefixEnd_99257 : Nat := 4983230072969 + 3 ^ 40 * 99257 * 2
def baseEnd_99257 : Nat := 7550599899766428182375

theorem tailTrace_99257 : CollatzResearch.WordTrace tailWord_99257 prefixEnd_99257 7550599899766428182375 := by
  unfold tailWord_99257
  simp only [CollatzResearch.WordTrace]
  refine ⟨3620200201416315591112025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2413466800944210394074683 3620200201416315591112025)
  ·
    refine ⟨2715150151062236693334019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3620200201416315591112025 2715150151062236693334019)
    ·
      refine ⟨4072725226593355040001029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2715150151062236693334019 4072725226593355040001029)
      ·
        refine ⟨763635979986254070000193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4072725226593355040001029 763635979986254070000193)
        ·
          refine ⟨572726984989690552500145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763635979986254070000193 572726984989690552500145)
          ·
            refine ⟨429545238742267914375109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572726984989690552500145 429545238742267914375109)
            ·
              refine ⟨80539732264175233945333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 429545238742267914375109 80539732264175233945333)
              ·
                refine ⟨7550599899766428182375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80539732264175233945333 7550599899766428182375)
                ·
                  rfl

theorem cell21_99257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 5].length) (baseStart_99257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99257 prefixEnd_99257 := by exact prefixLift 99257
  have htrace : WordTrace (prefixWord ++ tailWord_99257) baseStart_99257 baseEnd_99257 := by
    simpa [prefixWord, tailWord_99257, baseEnd_99257] using wordTrace_append hprefix tailTrace_99257
  have hstable : (prefixWord ++ tailWord_99257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99257).length < 2 ^ (prefixWord ++ tailWord_99257).sum := by decide
  have hdescent : baseEnd_99257 < baseStart_99257 := by decide
  rcases family_descends (prefixWord ++ tailWord_99257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99288 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 5]
def baseStart_99288 : Nat := 118140960795 + 99288 * 2 ^ 59
def prefixEnd_99288 : Nat := 4983230072969 + 3 ^ 40 * 99288 * 2
def baseEnd_99288 : Nat := 22658874321650119530395

theorem tailTrace_99288 : CollatzResearch.WordTrace tailWord_99288 prefixEnd_99288 22658874321650119530395 := by
  unfold tailWord_99288
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810665432152003942745259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2414220576202671923660345 1810665432152003942745259)
  ·
    refine ⟨2715998148228005914117889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1810665432152003942745259 2715998148228005914117889)
    ·
      refine ⟨2036998611171004435588417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2715998148228005914117889 2036998611171004435588417)
      ·
        refine ⟨1527748958378253326691313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2036998611171004435588417 1527748958378253326691313)
        ·
          refine ⟨1145811718783689995018485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1527748958378253326691313 1145811718783689995018485)
          ·
            refine ⟨107419848635970937032983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1145811718783689995018485 107419848635970937032983)
            ·
              refine ⟨161129772953956405549475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107419848635970937032983 161129772953956405549475)
              ·
                refine ⟨241694659430934608324213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161129772953956405549475 241694659430934608324213)
                ·
                  refine ⟨22658874321650119530395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 241694659430934608324213 22658874321650119530395)
                  ·
                    rfl

theorem cell21_99288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_99288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99288 prefixEnd_99288 := by exact prefixLift 99288
  have htrace : WordTrace (prefixWord ++ tailWord_99288) baseStart_99288 baseEnd_99288 := by
    simpa [prefixWord, tailWord_99288, baseEnd_99288] using wordTrace_append hprefix tailTrace_99288
  have hstable : (prefixWord ++ tailWord_99288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99288).length < 2 ^ (prefixWord ++ tailWord_99288).sum := by decide
  have hdescent : baseEnd_99288 < baseStart_99288 := by decide
  rcases family_descends (prefixWord ++ tailWord_99288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99364 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 5]
def baseStart_99364 : Nat := 118140960795 + 99364 * 2 ^ 59
def prefixEnd_99364 : Nat := 4983230072969 + 3 ^ 40 * 99364 * 2
def baseEnd_99364 : Nat := 22676218557090876263573

theorem tailTrace_99364 : CollatzResearch.WordTrace tailWord_99364 prefixEnd_99364 22676218557090876263573 := by
  unfold tailWord_99364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1812051406014336432628573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2416068541352448576838097 1812051406014336432628573)
  ·
    refine ⟨679519277255376162235715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1812051406014336432628573 679519277255376162235715)
    ·
      refine ⟨1019278915883064243353573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679519277255376162235715 1019278915883064243353573)
      ·
        refine ⟨191114796728074545628795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1019278915883064243353573 191114796728074545628795)
        ·
          refine ⟨286672195092111818443193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191114796728074545628795 286672195092111818443193)
          ·
            refine ⟨215004146319083863832395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286672195092111818443193 215004146319083863832395)
            ·
              refine ⟨322506219478625795748593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215004146319083863832395 322506219478625795748593)
              ·
                refine ⟨241879664608969346811445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322506219478625795748593 241879664608969346811445)
                ·
                  refine ⟨22676218557090876263573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 241879664608969346811445 22676218557090876263573)
                  ·
                    rfl

theorem cell21_99364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_99364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99364 prefixEnd_99364 := by exact prefixLift 99364
  have htrace : WordTrace (prefixWord ++ tailWord_99364) baseStart_99364 baseEnd_99364 := by
    simpa [prefixWord, tailWord_99364, baseEnd_99364] using wordTrace_append hprefix tailTrace_99364
  have hstable : (prefixWord ++ tailWord_99364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99364).length < 2 ^ (prefixWord ++ tailWord_99364).sum := by decide
  have hdescent : baseEnd_99364 < baseStart_99364 := by decide
  rcases family_descends (prefixWord ++ tailWord_99364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99398 : List Nat := [6, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_99398 : Nat := 118140960795 + 99398 * 2 ^ 59
def prefixEnd_99398 : Nat := 4983230072969 + 3 ^ 40 * 99398 * 2
def baseEnd_99398 : Nat := 22683977820314372696837

theorem tailTrace_99398 : CollatzResearch.WordTrace tailWord_99398 prefixEnd_99398 22683977820314372696837 := by
  unfold tailWord_99398
  simp only [CollatzResearch.WordTrace]
  refine ⟨113291965434546770999839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2416895262603664447996565 113291965434546770999839)
  ·
    refine ⟨169937948151820156499759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113291965434546770999839 169937948151820156499759)
    ·
      refine ⟨254906922227730234749639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169937948151820156499759 254906922227730234749639)
      ·
        refine ⟨382360383341595352124459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254906922227730234749639 382360383341595352124459)
        ·
          refine ⟨573540575012393028186689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382360383341595352124459 573540575012393028186689)
          ·
            refine ⟨430155431259294771140017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573540575012393028186689 430155431259294771140017)
            ·
              refine ⟨322616573444471078355013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430155431259294771140017 322616573444471078355013)
              ·
                refine ⟨60490607520838327191565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322616573444471078355013 60490607520838327191565)
                ·
                  refine ⟨22683977820314372696837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60490607520838327191565 22683977820314372696837)
                  ·
                    rfl

theorem cell21_99398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_99398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99398 prefixEnd_99398 := by exact prefixLift 99398
  have htrace : WordTrace (prefixWord ++ tailWord_99398) baseStart_99398 baseEnd_99398 := by
    simpa [prefixWord, tailWord_99398, baseEnd_99398] using wordTrace_append hprefix tailTrace_99398
  have hstable : (prefixWord ++ tailWord_99398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99398).length < 2 ^ (prefixWord ++ tailWord_99398).sum := by decide
  have hdescent : baseEnd_99398 < baseStart_99398 := by decide
  rcases family_descends (prefixWord ++ tailWord_99398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99426 : List Nat := [3, 3, 2, 2, 1, 1, 4, 5]
def baseStart_99426 : Nat := 118140960795 + 99426 * 2 ^ 59
def prefixEnd_99426 : Nat := 4983230072969 + 3 ^ 40 * 99426 * 2
def baseEnd_99426 : Nat := 7563455933930848743371

theorem tailTrace_99426 : CollatzResearch.WordTrace tailWord_99426 prefixEnd_99426 7563455933930848743371 := by
  unfold tailWord_99426
  simp only [CollatzResearch.WordTrace]
  refine ⟨906591034451014363503533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2417576091869371636009421 906591034451014363503533)
  ·
    refine ⟨339971637919130386313825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 906591034451014363503533 339971637919130386313825)
    ·
      refine ⟨254978728439347789735369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339971637919130386313825 254978728439347789735369)
      ·
        refine ⟨191234046329510842301527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254978728439347789735369 191234046329510842301527)
        ·
          refine ⟨286851069494266263452291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191234046329510842301527 286851069494266263452291)
          ·
            refine ⟨430276604241399395178437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286851069494266263452291 430276604241399395178437)
            ·
              refine ⟨80676863295262386595957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 430276604241399395178437 80676863295262386595957)
              ·
                refine ⟨7563455933930848743371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80676863295262386595957 7563455933930848743371)
                ·
                  rfl

theorem cell21_99426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_99426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99426 prefixEnd_99426 := by exact prefixLift 99426
  have htrace : WordTrace (prefixWord ++ tailWord_99426) baseStart_99426 baseEnd_99426 := by
    simpa [prefixWord, tailWord_99426, baseEnd_99426] using wordTrace_append hprefix tailTrace_99426
  have hstable : (prefixWord ++ tailWord_99426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99426).length < 2 ^ (prefixWord ++ tailWord_99426).sum := by decide
  have hdescent : baseEnd_99426 < baseStart_99426 := by decide
  rcases family_descends (prefixWord ++ tailWord_99426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99530 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_99530 : Nat := 118140960795 + 99530 * 2 ^ 59
def prefixEnd_99530 : Nat := 4983230072969 + 3 ^ 40 * 99530 * 2
def baseEnd_99530 : Nat := 22714102018711476496567

theorem tailTrace_99530 : CollatzResearch.WordTrace tailWord_99530 prefixEnd_99530 22714102018711476496567 := by
  unfold tailWord_99530
  simp only [CollatzResearch.WordTrace]
  refine ⟨907539332356820803950011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2420104886284855477200029 907539332356820803950011)
  ·
    refine ⟨1361308998535231205925017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 907539332356820803950011 1361308998535231205925017)
    ·
      refine ⟨1020981748901423404443763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1361308998535231205925017 1020981748901423404443763)
      ·
        refine ⟨1531472623352135106665645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020981748901423404443763 1531472623352135106665645)
        ·
          refine ⟨574302233757050664999617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1531472623352135106665645 574302233757050664999617)
          ·
            refine ⟨430726675317787998749713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574302233757050664999617 430726675317787998749713)
            ·
              refine ⟨323045006488340999062285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430726675317787998749713 323045006488340999062285)
              ·
                refine ⟨121141877433127874648357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323045006488340999062285 121141877433127874648357)
                ·
                  refine ⟨22714102018711476496567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121141877433127874648357 22714102018711476496567)
                  ·
                    rfl

theorem cell21_99530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_99530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99530 prefixEnd_99530 := by exact prefixLift 99530
  have htrace : WordTrace (prefixWord ++ tailWord_99530) baseStart_99530 baseEnd_99530 := by
    simpa [prefixWord, tailWord_99530, baseEnd_99530] using wordTrace_append hprefix tailTrace_99530
  have hstable : (prefixWord ++ tailWord_99530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99530).length < 2 ^ (prefixWord ++ tailWord_99530).sum := by decide
  have hdescent : baseEnd_99530 < baseStart_99530 := by decide
  rcases family_descends (prefixWord ++ tailWord_99530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99626 : List Nat := [3, 1, 4, 2, 1, 2, 3, 2, 3]
def baseStart_99626 : Nat := 118140960795 + 99626 * 2 ^ 59
def prefixEnd_99626 : Nat := 4983230072969 + 3 ^ 40 * 99626 * 2
def baseEnd_99626 : Nat := 22736010526636642896371

theorem tailTrace_99626 : CollatzResearch.WordTrace tailWord_99626 prefixEnd_99626 22736010526636642896371 := by
  unfold tailWord_99626
  simp only [CollatzResearch.WordTrace]
  refine ⟨908414684269872902823683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2422439158052994407529821 908414684269872902823683)
  ·
    refine ⟨1362622026404809354235525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 908414684269872902823683 1362622026404809354235525)
    ·
      refine ⟨255491629950901753919161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1362622026404809354235525 255491629950901753919161)
      ·
        refine ⟨191618722463176315439371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255491629950901753919161 191618722463176315439371)
        ·
          refine ⟨287428083694764473159057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191618722463176315439371 287428083694764473159057)
          ·
            refine ⟨215571062771073354869293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287428083694764473159057 215571062771073354869293)
            ·
              refine ⟨80839148539152508075985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215571062771073354869293 80839148539152508075985)
              ·
                refine ⟨60629361404364381056989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80839148539152508075985 60629361404364381056989)
                ·
                  refine ⟨22736010526636642896371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60629361404364381056989 22736010526636642896371)
                  ·
                    rfl

theorem cell21_99626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_99626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99626 prefixEnd_99626 := by exact prefixLift 99626
  have htrace : WordTrace (prefixWord ++ tailWord_99626) baseStart_99626 baseEnd_99626 := by
    simpa [prefixWord, tailWord_99626, baseEnd_99626] using wordTrace_append hprefix tailTrace_99626
  have hstable : (prefixWord ++ tailWord_99626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99626).length < 2 ^ (prefixWord ++ tailWord_99626).sum := by decide
  have hdescent : baseEnd_99626 < baseStart_99626 := by decide
  rcases family_descends (prefixWord ++ tailWord_99626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99668 : List Nat := [2, 4, 1, 1, 2, 1, 2, 5, 3]
def baseStart_99668 : Nat := 118140960795 + 99668 * 2 ^ 59
def prefixEnd_99668 : Nat := 4983230072969 + 3 ^ 40 * 99668 * 2
def baseEnd_99668 : Nat := 22745595498853903196285

theorem tailTrace_99668 : CollatzResearch.WordTrace tailWord_99668 prefixEnd_99668 22745595498853903196285 := by
  unfold tailWord_99668
  simp only [CollatzResearch.WordTrace]
  refine ⟨1817595301463666392161829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2423460401951555189549105 1817595301463666392161829)
  ·
    refine ⟨340799119024437448530343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1817595301463666392161829 340799119024437448530343)
    ·
      refine ⟨511198678536656172795515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340799119024437448530343 511198678536656172795515)
      ·
        refine ⟨766798017804984259193273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511198678536656172795515 766798017804984259193273)
        ·
          refine ⟨575098513353738194394955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 766798017804984259193273 575098513353738194394955)
          ·
            refine ⟨862647770030607291592433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575098513353738194394955 862647770030607291592433)
            ·
              refine ⟨646985827522955468694325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 862647770030607291592433 646985827522955468694325)
              ·
                refine ⟨60654921330277075190093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 646985827522955468694325 60654921330277075190093)
                ·
                  refine ⟨22745595498853903196285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60654921330277075190093 22745595498853903196285)
                  ·
                    rfl

theorem cell21_99668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_99668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99668 prefixEnd_99668 := by exact prefixLift 99668
  have htrace : WordTrace (prefixWord ++ tailWord_99668) baseStart_99668 baseEnd_99668 := by
    simpa [prefixWord, tailWord_99668, baseEnd_99668] using wordTrace_append hprefix tailTrace_99668
  have hstable : (prefixWord ++ tailWord_99668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99668).length < 2 ^ (prefixWord ++ tailWord_99668).sum := by decide
  have hdescent : baseEnd_99668 < baseStart_99668 := by decide
  rcases family_descends (prefixWord ++ tailWord_99668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99677 : List Nat := [1, 4, 5, 1, 2, 1, 2, 2, 3]
def baseStart_99677 : Nat := 118140960795 + 99677 * 2 ^ 59
def prefixEnd_99677 : Nat := 4983230072969 + 3 ^ 40 * 99677 * 2
def baseEnd_99677 : Nat := 22747649421471887546267

theorem tailTrace_99677 : CollatzResearch.WordTrace tailWord_99677 prefixEnd_99677 22747649421471887546267 := by
  unfold tailWord_99677
  simp only [CollatzResearch.WordTrace]
  refine ⟨3635518859894727321401285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2423679239929818214267523 3635518859894727321401285)
  ·
    refine ⟨681659786230261372762741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3635518859894727321401285 681659786230261372762741)
    ·
      refine ⟨63905604959087003696507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 681659786230261372762741 63905604959087003696507)
      ·
        refine ⟨95858407438630505544761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63905604959087003696507 95858407438630505544761)
        ·
          refine ⟨71893805578972879158571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95858407438630505544761 71893805578972879158571)
          ·
            refine ⟨107840708368459318737857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71893805578972879158571 107840708368459318737857)
            ·
              refine ⟨80880531276344489053393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107840708368459318737857 80880531276344489053393)
              ·
                refine ⟨60660398457258366790045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80880531276344489053393 60660398457258366790045)
                ·
                  refine ⟨22747649421471887546267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60660398457258366790045 22747649421471887546267)
                  ·
                    rfl

theorem cell21_99677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_99677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99677 prefixEnd_99677 := by exact prefixLift 99677
  have htrace : WordTrace (prefixWord ++ tailWord_99677) baseStart_99677 baseEnd_99677 := by
    simpa [prefixWord, tailWord_99677, baseEnd_99677] using wordTrace_append hprefix tailTrace_99677
  have hstable : (prefixWord ++ tailWord_99677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99677).length < 2 ^ (prefixWord ++ tailWord_99677).sum := by decide
  have hdescent : baseEnd_99677 < baseStart_99677 := by decide
  rcases family_descends (prefixWord ++ tailWord_99677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99854 : List Nat := [4, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_99854 : Nat := 118140960795 + 99854 * 2 ^ 59
def prefixEnd_99854 : Nat := 4983230072969 + 3 ^ 40 * 99854 * 2
def baseEnd_99854 : Nat := 22788043232958913095905

theorem tailTrace_99854 : CollatzResearch.WordTrace tailWord_99854 prefixEnd_99854 22788043232958913095905 := by
  unfold tailWord_99854
  simp only [CollatzResearch.WordTrace]
  refine ⟨455246822531685818824327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2427983053502324367063077 455246822531685818824327)
  ·
    refine ⟨682870233797528728236491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 455246822531685818824327 682870233797528728236491)
    ·
      refine ⟨1024305350696293092354737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682870233797528728236491 1024305350696293092354737)
      ·
        refine ⟨768229013022219819266053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024305350696293092354737 768229013022219819266053)
        ·
          refine ⟨144042939941666216112385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 768229013022219819266053 144042939941666216112385)
          ·
            refine ⟨108032204956249662084289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144042939941666216112385 108032204956249662084289)
            ·
              refine ⟨81024153717187246563217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108032204956249662084289 81024153717187246563217)
              ·
                refine ⟨60768115287890434922413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81024153717187246563217 60768115287890434922413)
                ·
                  refine ⟨22788043232958913095905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60768115287890434922413 22788043232958913095905)
                  ·
                    rfl

theorem cell21_99854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_99854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99854 prefixEnd_99854 := by exact prefixLift 99854
  have htrace : WordTrace (prefixWord ++ tailWord_99854) baseStart_99854 baseEnd_99854 := by
    simpa [prefixWord, tailWord_99854, baseEnd_99854] using wordTrace_append hprefix tailTrace_99854
  have hstable : (prefixWord ++ tailWord_99854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99854).length < 2 ^ (prefixWord ++ tailWord_99854).sum := by decide
  have hdescent : baseEnd_99854 < baseStart_99854 := by decide
  rcases family_descends (prefixWord ++ tailWord_99854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99896 : List Nat := [2, 1, 2, 1, 4, 3, 2, 3, 3]
def baseStart_99896 : Nat := 118140960795 + 99896 * 2 ^ 59
def prefixEnd_99896 : Nat := 4983230072969 + 3 ^ 40 * 99896 * 2
def baseEnd_99896 : Nat := 22797628205176173395819

theorem tailTrace_99896 : CollatzResearch.WordTrace tailWord_99896 prefixEnd_99896 22797628205176173395819 := by
  unfold tailWord_99896
  simp only [CollatzResearch.WordTrace]
  refine ⟨1821753223050663861811771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2429004297400885149082361 1821753223050663861811771)
  ·
    refine ⟨2732629834575995792717657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1821753223050663861811771 2732629834575995792717657)
    ·
      refine ⟨2049472375931996844538243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2732629834575995792717657 2049472375931996844538243)
      ·
        refine ⟨3074208563897995266807365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049472375931996844538243 3074208563897995266807365)
        ·
          refine ⟨576414105730874112526381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3074208563897995266807365 576414105730874112526381)
          ·
            refine ⟨216155289649077792197393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 576414105730874112526381 216155289649077792197393)
            ·
              refine ⟨162116467236808344148045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216155289649077792197393 162116467236808344148045)
              ·
                refine ⟨60793675213803129055517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162116467236808344148045 60793675213803129055517)
                ·
                  refine ⟨22797628205176173395819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60793675213803129055517 22797628205176173395819)
                  ·
                    rfl

theorem cell21_99896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 3].length) (baseStart_99896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99896 prefixEnd_99896 := by exact prefixLift 99896
  have htrace : WordTrace (prefixWord ++ tailWord_99896) baseStart_99896 baseEnd_99896 := by
    simpa [prefixWord, tailWord_99896, baseEnd_99896] using wordTrace_append hprefix tailTrace_99896
  have hstable : (prefixWord ++ tailWord_99896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99896).length < 2 ^ (prefixWord ++ tailWord_99896).sum := by decide
  have hdescent : baseEnd_99896 < baseStart_99896 := by decide
  rcases family_descends (prefixWord ++ tailWord_99896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99941 : List Nat := [1, 3, 1, 3, 3, 3, 2, 5]
def baseStart_99941 : Nat := 118140960795 + 99941 * 2 ^ 59
def prefixEnd_99941 : Nat := 4983230072969 + 3 ^ 40 * 99941 * 2
def baseEnd_99941 : Nat := 7602632606088698381909

theorem tailTrace_99941 : CollatzResearch.WordTrace tailWord_99941 prefixEnd_99941 7602632606088698381909 := by
  unfold tailWord_99941
  simp only [CollatzResearch.WordTrace]
  refine ⟨3645147730938300409011677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2430098487292200272674451 3645147730938300409011677)
  ·
    refine ⟨1366930399101862653379379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3645147730938300409011677 1366930399101862653379379)
    ·
      refine ⟨2050395598652793980069069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366930399101862653379379 2050395598652793980069069)
      ·
        refine ⟨768898349494797742525901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2050395598652793980069069 768898349494797742525901)
        ·
          refine ⟨288336881060549153447213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 768898349494797742525901 288336881060549153447213)
          ·
            refine ⟨108126330397705932542705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288336881060549153447213 108126330397705932542705)
            ·
              refine ⟨81094747798279449407029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108126330397705932542705 81094747798279449407029)
              ·
                refine ⟨7602632606088698381909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81094747798279449407029 7602632606088698381909)
                ·
                  rfl

theorem cell21_99941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 5].length) (baseStart_99941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99941 prefixEnd_99941 := by exact prefixLift 99941
  have htrace : WordTrace (prefixWord ++ tailWord_99941) baseStart_99941 baseEnd_99941 := by
    simpa [prefixWord, tailWord_99941, baseEnd_99941] using wordTrace_append hprefix tailTrace_99941
  have hstable : (prefixWord ++ tailWord_99941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99941).length < 2 ^ (prefixWord ++ tailWord_99941).sum := by decide
  have hdescent : baseEnd_99941 < baseStart_99941 := by decide
  rcases family_descends (prefixWord ++ tailWord_99941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99969 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 6]
def baseStart_99969 : Nat := 118140960795 + 99969 * 2 ^ 59
def prefixEnd_99969 : Nat := 4983230072969 + 3 ^ 40 * 99969 * 2
def baseEnd_99969 : Nat := 22814287799744268679003

theorem tailTrace_99969 : CollatzResearch.WordTrace tailWord_99969 prefixEnd_99969 22814287799744268679003 := by
  unfold tailWord_99969
  simp only [CollatzResearch.WordTrace]
  refine ⟨3646168974836861191030961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2430779316557907460687307 3646168974836861191030961)
  ·
    refine ⟨2734626731127645893273221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3646168974836861191030961 2734626731127645893273221)
    ·
      refine ⟨512742512086433604988729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2734626731127645893273221 512742512086433604988729)
      ·
        refine ⟨384556884064825203741547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512742512086433604988729 384556884064825203741547)
        ·
          refine ⟨576835326097237805612321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384556884064825203741547 576835326097237805612321)
          ·
            refine ⟨432626494572928354209241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576835326097237805612321 432626494572928354209241)
            ·
              refine ⟨324469870929696265656931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432626494572928354209241 324469870929696265656931)
              ·
                refine ⟨486704806394544398485397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324469870929696265656931 486704806394544398485397)
                ·
                  refine ⟨22814287799744268679003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 486704806394544398485397 22814287799744268679003)
                  ·
                    rfl

theorem cell21_99969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_99969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99969 prefixEnd_99969 := by exact prefixLift 99969
  have htrace : WordTrace (prefixWord ++ tailWord_99969) baseStart_99969 baseEnd_99969 := by
    simpa [prefixWord, tailWord_99969, baseEnd_99969] using wordTrace_append hprefix tailTrace_99969
  have hstable : (prefixWord ++ tailWord_99969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99969).length < 2 ^ (prefixWord ++ tailWord_99969).sum := by decide
  have hdescent : baseEnd_99969 < baseStart_99969 := by decide
  rcases family_descends (prefixWord ++ tailWord_99969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99972 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 5]
def baseStart_99972 : Nat := 118140960795 + 99972 * 2 ^ 59
def prefixEnd_99972 : Nat := 4983230072969 + 3 ^ 40 * 99972 * 2
def baseEnd_99972 : Nat := 22814972440616930128997

theorem tailTrace_99972 : CollatzResearch.WordTrace tailWord_99972 prefixEnd_99972 22814972440616930128997 := by
  unfold tailWord_99972
  simp only [CollatzResearch.WordTrace]
  refine ⟨1823139196912996351695085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2430852262550661802260113 1823139196912996351695085)
  ·
    refine ⟨683677198842373631885657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1823139196912996351695085 683677198842373631885657)
    ·
      refine ⟨512757899131780223914243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 683677198842373631885657 512757899131780223914243)
      ·
        refine ⟨769136848697670335871365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512757899131780223914243 769136848697670335871365)
        ·
          refine ⟨144213159130813187975881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 769136848697670335871365 144213159130813187975881)
          ·
            refine ⟨108159869348109890981911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144213159130813187975881 108159869348109890981911)
            ·
              refine ⟨162239804022164836472867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108159869348109890981911 162239804022164836472867)
              ·
                refine ⟨243359706033247254709301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162239804022164836472867 243359706033247254709301)
                ·
                  refine ⟨22814972440616930128997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243359706033247254709301 22814972440616930128997)
                  ·
                    rfl

theorem cell21_99972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_99972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_99972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_99972 prefixEnd_99972 := by exact prefixLift 99972
  have htrace : WordTrace (prefixWord ++ tailWord_99972) baseStart_99972 baseEnd_99972 := by
    simpa [prefixWord, tailWord_99972, baseEnd_99972] using wordTrace_append hprefix tailTrace_99972
  have hstable : (prefixWord ++ tailWord_99972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99972).length < 2 ^ (prefixWord ++ tailWord_99972).sum := by decide
  have hdescent : baseEnd_99972 < baseStart_99972 := by decide
  rcases family_descends (prefixWord ++ tailWord_99972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100031 : List Nat := [1, 1, 2, 2, 2, 3, 3, 4, 3]
def baseStart_100031 : Nat := 118140960795 + 100031 * 2 ^ 59
def prefixEnd_100031 : Nat := 4983230072969 + 3 ^ 40 * 100031 * 2
def baseEnd_100031 : Nat := 22828437044445938645543

theorem tailTrace_100031 : CollatzResearch.WordTrace tailWord_100031 prefixEnd_100031 22828437044445938645543 := by
  unfold tailWord_100031
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648430300612245779787947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2432286867074830519858631 3648430300612245779787947)
  ·
    refine ⟨5472645450918368669681921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3648430300612245779787947 5472645450918368669681921)
    ·
      refine ⟨4104484088188776502261441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5472645450918368669681921 4104484088188776502261441)
      ·
        refine ⟨3078363066141582376696081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4104484088188776502261441 3078363066141582376696081)
        ·
          refine ⟨2308772299606186782522061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3078363066141582376696081 2308772299606186782522061)
          ·
            refine ⟨865789612352320043445773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2308772299606186782522061 865789612352320043445773)
            ·
              refine ⟨324671104632120016292165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 865789612352320043445773 324671104632120016292165)
              ·
                refine ⟨60875832118522503054781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324671104632120016292165 60875832118522503054781)
                ·
                  refine ⟨22828437044445938645543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60875832118522503054781 22828437044445938645543)
                  ·
                    rfl

theorem cell21_100031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 3].length) (baseStart_100031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100031 prefixEnd_100031 := by exact prefixLift 100031
  have htrace : WordTrace (prefixWord ++ tailWord_100031) baseStart_100031 baseEnd_100031 := by
    simpa [prefixWord, tailWord_100031, baseEnd_100031] using wordTrace_append hprefix tailTrace_100031
  have hstable : (prefixWord ++ tailWord_100031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100031).length < 2 ^ (prefixWord ++ tailWord_100031).sum := by decide
  have hdescent : baseEnd_100031 < baseStart_100031 := by decide
  rcases family_descends (prefixWord ++ tailWord_100031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100073 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 9]
def baseStart_100073 : Nat := 118140960795 + 100073 * 2 ^ 59
def prefixEnd_100073 : Nat := 4983230072969 + 3 ^ 40 * 100073 * 2
def baseEnd_100073 : Nat := 22838022016663198945457

theorem tailTrace_100073 : CollatzResearch.WordTrace tailWord_100073 prefixEnd_100073 22838022016663198945457 := by
  unfold tailWord_100073
  simp only [CollatzResearch.WordTrace]
  refine ⟨3649962166460086952816873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2433308110973391301877915 3649962166460086952816873)
  ·
    refine ⟨2737471624845065214612655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3649962166460086952816873 2737471624845065214612655)
    ·
      refine ⟨4106207437267597821918983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2737471624845065214612655 4106207437267597821918983)
      ·
        refine ⟨6159311155901396732878475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106207437267597821918983 6159311155901396732878475)
        ·
          refine ⟨9238966733852095099317713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6159311155901396732878475 9238966733852095099317713)
          ·
            refine ⟨6929225050389071324488285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9238966733852095099317713 6929225050389071324488285)
            ·
              refine ⟨2598459393895901746683107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6929225050389071324488285 2598459393895901746683107)
              ·
                refine ⟨3897689090843852620024661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598459393895901746683107 3897689090843852620024661)
                ·
                  refine ⟨22838022016663198945457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3897689090843852620024661 22838022016663198945457)
                  ·
                    rfl

theorem cell21_100073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_100073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100073 prefixEnd_100073 := by exact prefixLift 100073
  have htrace : WordTrace (prefixWord ++ tailWord_100073) baseStart_100073 baseEnd_100073 := by
    simpa [prefixWord, tailWord_100073, baseEnd_100073] using wordTrace_append hprefix tailTrace_100073
  have hstable : (prefixWord ++ tailWord_100073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100073).length < 2 ^ (prefixWord ++ tailWord_100073).sum := by decide
  have hdescent : baseEnd_100073 < baseStart_100073 := by decide
  rcases family_descends (prefixWord ++ tailWord_100073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100102 : List Nat := [6, 2, 2, 1, 2, 1, 2, 5]
def baseStart_100102 : Nat := 118140960795 + 100102 * 2 ^ 59
def prefixEnd_100102 : Nat := 4983230072969 + 3 ^ 40 * 100102 * 2
def baseEnd_100102 : Nat := 7614880070588530987355

theorem tailTrace_100102 : CollatzResearch.WordTrace tailWord_100102 prefixEnd_100102 7614880070588530987355 := by
  unfold tailWord_100102
  simp only [CollatzResearch.WordTrace]
  refine ⟨114094371354844528300705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2434013255570016603748373 114094371354844528300705)
  ·
    refine ⟨85570778516133396225529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114094371354844528300705 85570778516133396225529)
    ·
      refine ⟨64178083887100047169147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85570778516133396225529 64178083887100047169147)
      ·
        refine ⟨96267125830650070753721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64178083887100047169147 96267125830650070753721)
        ·
          refine ⟨72200344372987553065291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96267125830650070753721 72200344372987553065291)
          ·
            refine ⟨108300516559481329597937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72200344372987553065291 108300516559481329597937)
            ·
              refine ⟨81225387419610997198453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108300516559481329597937 81225387419610997198453)
              ·
                refine ⟨7614880070588530987355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81225387419610997198453 7614880070588530987355)
                ·
                  rfl

theorem cell21_100102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_100102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100102 prefixEnd_100102 := by exact prefixLift 100102
  have htrace : WordTrace (prefixWord ++ tailWord_100102) baseStart_100102 baseEnd_100102 := by
    simpa [prefixWord, tailWord_100102, baseEnd_100102] using wordTrace_append hprefix tailTrace_100102
  have hstable : (prefixWord ++ tailWord_100102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100102).length < 2 ^ (prefixWord ++ tailWord_100102).sum := by decide
  have hdescent : baseEnd_100102 < baseStart_100102 := by decide
  rcases family_descends (prefixWord ++ tailWord_100102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100116 : List Nat := [2, 4, 4, 1, 2, 1, 1, 3, 3]
def baseStart_100116 : Nat := 118140960795 + 100116 * 2 ^ 59
def prefixEnd_100116 : Nat := 4983230072969 + 3 ^ 40 * 100116 * 2
def baseEnd_100116 : Nat := 22847835202504679728703

theorem tailTrace_100116 : CollatzResearch.WordTrace tailWord_100116 prefixEnd_100116 22847835202504679728703 := by
  unfold tailWord_100116
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825765252652152648316101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2434353670202870197754801 1825765252652152648316101)
  ·
    refine ⟨342330984872278621559269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1825765252652152648316101 342330984872278621559269)
    ·
      refine ⟨64187059663552241542363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342330984872278621559269 64187059663552241542363)
      ·
        refine ⟨96280589495328362313545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64187059663552241542363 96280589495328362313545)
        ·
          refine ⟨72210442121496271735159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96280589495328362313545 72210442121496271735159)
          ·
            refine ⟨108315663182244407602739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72210442121496271735159 108315663182244407602739)
            ·
              refine ⟨162473494773366611404109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108315663182244407602739 162473494773366611404109)
              ·
                refine ⟨60927560540012479276541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162473494773366611404109 60927560540012479276541)
                ·
                  refine ⟨22847835202504679728703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60927560540012479276541 22847835202504679728703)
                  ·
                    rfl

theorem cell21_100116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_100116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100116 prefixEnd_100116 := by exact prefixLift 100116
  have htrace : WordTrace (prefixWord ++ tailWord_100116) baseStart_100116 baseEnd_100116 := by
    simpa [prefixWord, tailWord_100116, baseEnd_100116] using wordTrace_append hprefix tailTrace_100116
  have hstable : (prefixWord ++ tailWord_100116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100116).length < 2 ^ (prefixWord ++ tailWord_100116).sum := by decide
  have hdescent : baseEnd_100116 < baseStart_100116 := by decide
  rcases family_descends (prefixWord ++ tailWord_100116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100248 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 4]
def baseStart_100248 : Nat := 118140960795 + 100248 * 2 ^ 59
def prefixEnd_100248 : Nat := 4983230072969 + 3 ^ 40 * 100248 * 2
def baseEnd_100248 : Nat := 22877959400901783528433

theorem tailTrace_100248 : CollatzResearch.WordTrace tailWord_100248 prefixEnd_100248 22877959400901783528433 := by
  unfold tailWord_100248
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828172470413045920218699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2437563293884061226958265 1828172470413045920218699)
  ·
    refine ⟨2742258705619568880328049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1828172470413045920218699 2742258705619568880328049)
    ·
      refine ⟨2056694029214676660246037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2742258705619568880328049 2056694029214676660246037)
      ·
        refine ⟨96407532619437968449033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2056694029214676660246037 96407532619437968449033)
        ·
          refine ⟨72305649464578476336775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96407532619437968449033 72305649464578476336775)
          ·
            refine ⟨108458474196867714505163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72305649464578476336775 108458474196867714505163)
            ·
              refine ⟨162687711295301571757745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108458474196867714505163 162687711295301571757745)
              ·
                refine ⟨122015783471476178818309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162687711295301571757745 122015783471476178818309)
                ·
                  refine ⟨22877959400901783528433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122015783471476178818309 22877959400901783528433)
                  ·
                    rfl

theorem cell21_100248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 4].length) (baseStart_100248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100248 prefixEnd_100248 := by exact prefixLift 100248
  have htrace : WordTrace (prefixWord ++ tailWord_100248) baseStart_100248 baseEnd_100248 := by
    simpa [prefixWord, tailWord_100248, baseEnd_100248] using wordTrace_append hprefix tailTrace_100248
  have hstable : (prefixWord ++ tailWord_100248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100248).length < 2 ^ (prefixWord ++ tailWord_100248).sum := by decide
  have hdescent : baseEnd_100248 < baseStart_100248 := by decide
  rcases family_descends (prefixWord ++ tailWord_100248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100310 : List Nat := [5, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_100310 : Nat := 118140960795 + 100310 * 2 ^ 59
def prefixEnd_100310 : Nat := 4983230072969 + 3 ^ 40 * 100310 * 2
def baseEnd_100310 : Nat := 22892108645603453494973

theorem tailTrace_100310 : CollatzResearch.WordTrace tailWord_100310 prefixEnd_100310 22892108645603453494973 := by
  unfold tailWord_100310
  simp only [CollatzResearch.WordTrace]
  refine ⟨228662891662592276824649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2439070844400984286129589 228662891662592276824649)
  ·
    refine ⟨171497168746944207618487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228662891662592276824649 171497168746944207618487)
    ·
      refine ⟨257245753120416311427731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171497168746944207618487 257245753120416311427731)
      ·
        refine ⟨385868629680624467141597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257245753120416311427731 385868629680624467141597)
        ·
          refine ⟨144700736130234175178099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385868629680624467141597 144700736130234175178099)
          ·
            refine ⟨217051104195351262767149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144700736130234175178099 217051104195351262767149)
            ·
              refine ⟨81394164073256723537681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217051104195351262767149 81394164073256723537681)
              ·
                refine ⟨61045623054942542653261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81394164073256723537681 61045623054942542653261)
                ·
                  refine ⟨22892108645603453494973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61045623054942542653261 22892108645603453494973)
                  ·
                    rfl

theorem cell21_100310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_100310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100310 prefixEnd_100310 := by exact prefixLift 100310
  have htrace : WordTrace (prefixWord ++ tailWord_100310) baseStart_100310 baseEnd_100310 := by
    simpa [prefixWord, tailWord_100310, baseEnd_100310] using wordTrace_append hprefix tailTrace_100310
  have hstable : (prefixWord ++ tailWord_100310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100310).length < 2 ^ (prefixWord ++ tailWord_100310).sum := by decide
  have hdescent : baseEnd_100310 < baseStart_100310 := by decide
  rcases family_descends (prefixWord ++ tailWord_100310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100377 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 5]
def baseStart_100377 : Nat := 118140960795 + 100377 * 2 ^ 59
def prefixEnd_100377 : Nat := 4983230072969 + 3 ^ 40 * 100377 * 2
def baseEnd_100377 : Nat := 22907398958426225878169

theorem tailTrace_100377 : CollatzResearch.WordTrace tailWord_100377 prefixEnd_100377 22907398958426225878169 := by
  unfold tailWord_100377
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661049957358746871883385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2440699971572497914588923 3661049957358746871883385)
  ·
    refine ⟨2745787468019060153912539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3661049957358746871883385 2745787468019060153912539)
    ·
      refine ⟨4118681202028590230868809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2745787468019060153912539 4118681202028590230868809)
      ·
        refine ⟨3089010901521442673151607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4118681202028590230868809 3089010901521442673151607)
        ·
          refine ⟨4633516352282164009727411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3089010901521442673151607 4633516352282164009727411)
          ·
            refine ⟨6950274528423246014591117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4633516352282164009727411 6950274528423246014591117)
            ·
              refine ⟨2606352948158717255471669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6950274528423246014591117 2606352948158717255471669)
              ·
                refine ⟨244345588889879742700469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2606352948158717255471669 244345588889879742700469)
                ·
                  refine ⟨22907398958426225878169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 244345588889879742700469 22907398958426225878169)
                  ·
                    rfl

theorem cell21_100377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_100377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100377 prefixEnd_100377 := by exact prefixLift 100377
  have htrace : WordTrace (prefixWord ++ tailWord_100377) baseStart_100377 baseEnd_100377 := by
    simpa [prefixWord, tailWord_100377, baseEnd_100377] using wordTrace_append hprefix tailTrace_100377
  have hstable : (prefixWord ++ tailWord_100377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100377).length < 2 ^ (prefixWord ++ tailWord_100377).sum := by decide
  have hdescent : baseEnd_100377 < baseStart_100377 := by decide
  rcases family_descends (prefixWord ++ tailWord_100377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100380 : List Nat := [2, 2, 3, 1, 3, 3, 1, 6]
def baseStart_100380 : Nat := 118140960795 + 100380 * 2 ^ 59
def prefixEnd_100380 : Nat := 4983230072969 + 3 ^ 40 * 100380 * 2
def baseEnd_100380 : Nat := 7636027866432962442721

theorem tailTrace_100380 : CollatzResearch.WordTrace tailWord_100380 prefixEnd_100380 7636027866432962442721 := by
  unfold tailWord_100380
  simp only [CollatzResearch.WordTrace]
  refine ⟨1830579688173939192121297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2440772917565252256161729 1830579688173939192121297)
  ·
    refine ⟨1372934766130454394090973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1830579688173939192121297 1372934766130454394090973)
    ·
      refine ⟨514850537298920397784115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1372934766130454394090973 514850537298920397784115)
      ·
        refine ⟨772275805948380596676173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514850537298920397784115 772275805948380596676173)
        ·
          refine ⟨289603427230642723753565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 772275805948380596676173 289603427230642723753565)
          ·
            refine ⟨108601285211491021407587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289603427230642723753565 108601285211491021407587)
            ·
              refine ⟨162901927817236532111381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108601285211491021407587 162901927817236532111381)
              ·
                refine ⟨7636027866432962442721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162901927817236532111381 7636027866432962442721)
                ·
                  rfl

theorem cell21_100380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_100380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100380 prefixEnd_100380 := by exact prefixLift 100380
  have htrace : WordTrace (prefixWord ++ tailWord_100380) baseStart_100380 baseEnd_100380 := by
    simpa [prefixWord, tailWord_100380, baseEnd_100380] using wordTrace_append hprefix tailTrace_100380
  have hstable : (prefixWord ++ tailWord_100380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100380).length < 2 ^ (prefixWord ++ tailWord_100380).sum := by decide
  have hdescent : baseEnd_100380 < baseStart_100380 := by decide
  rcases family_descends (prefixWord ++ tailWord_100380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100394 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_100394 : Nat := 118140960795 + 100394 * 2 ^ 59
def prefixEnd_100394 : Nat := 4983230072969 + 3 ^ 40 * 100394 * 2
def baseEnd_100394 : Nat := 22911278590037974094801

theorem tailTrace_100394 : CollatzResearch.WordTrace tailWord_100394 prefixEnd_100394 22911278590037974094801 := by
  unfold tailWord_100394
  simp only [CollatzResearch.WordTrace]
  refine ⟨915417499574289693813059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2441113332198105850168157 915417499574289693813059)
  ·
    refine ⟨1373126249361434540719589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 915417499574289693813059 1373126249361434540719589)
    ·
      refine ⟨257461171755268976384923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1373126249361434540719589 257461171755268976384923)
      ·
        refine ⟨386191757632903464577385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257461171755268976384923 386191757632903464577385)
        ·
          refine ⟨289643818224677598433039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386191757632903464577385 289643818224677598433039)
          ·
            refine ⟨434465727337016397649559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289643818224677598433039 434465727337016397649559)
            ·
              refine ⟨651698591005524596474339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434465727337016397649559 651698591005524596474339)
              ·
                refine ⟨977547886508286894711509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651698591005524596474339 977547886508286894711509)
                ·
                  refine ⟨22911278590037974094801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 977547886508286894711509 22911278590037974094801)
                  ·
                    rfl

theorem cell21_100394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_100394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100394 prefixEnd_100394 := by exact prefixLift 100394
  have htrace : WordTrace (prefixWord ++ tailWord_100394) baseStart_100394 baseEnd_100394 := by
    simpa [prefixWord, tailWord_100394, baseEnd_100394] using wordTrace_append hprefix tailTrace_100394
  have hstable : (prefixWord ++ tailWord_100394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100394).length < 2 ^ (prefixWord ++ tailWord_100394).sum := by decide
  have hdescent : baseEnd_100394 < baseStart_100394 := by decide
  rcases family_descends (prefixWord ++ tailWord_100394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100484 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_100484 : Nat := 118140960795 + 100484 * 2 ^ 59
def prefixEnd_100484 : Nat := 4983230072969 + 3 ^ 40 * 100484 * 2
def baseEnd_100484 : Nat := 22931817816217817594617

theorem tailTrace_100484 : CollatzResearch.WordTrace tailWord_100484 prefixEnd_100484 22931817816217817594617 := by
  unfold tailWord_100484
  simp only [CollatzResearch.WordTrace]
  refine ⟨1832476283985552073014253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2443301711980736097352337 1832476283985552073014253)
  ·
    refine ⟨687178606494582027380345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1832476283985552073014253 687178606494582027380345)
    ·
      refine ⟨515383954870936520535259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 687178606494582027380345 515383954870936520535259)
      ·
        refine ⟨773075932306404780802889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515383954870936520535259 773075932306404780802889)
        ·
          refine ⟨579806949229803585602167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773075932306404780802889 579806949229803585602167)
          ·
            refine ⟨869710423844705378403251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579806949229803585602167 869710423844705378403251)
            ·
              refine ⟨1304565635767058067604877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869710423844705378403251 1304565635767058067604877)
              ·
                refine ⟨489212113412646775351829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1304565635767058067604877 489212113412646775351829)
                ·
                  refine ⟨22931817816217817594617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 489212113412646775351829 22931817816217817594617)
                  ·
                    rfl

theorem cell21_100484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_100484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100484 prefixEnd_100484 := by exact prefixLift 100484
  have htrace : WordTrace (prefixWord ++ tailWord_100484) baseStart_100484 baseEnd_100484 := by
    simpa [prefixWord, tailWord_100484, baseEnd_100484] using wordTrace_append hprefix tailTrace_100484
  have hstable : (prefixWord ++ tailWord_100484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100484).length < 2 ^ (prefixWord ++ tailWord_100484).sum := by decide
  have hdescent : baseEnd_100484 < baseStart_100484 := by decide
  rcases family_descends (prefixWord ++ tailWord_100484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100594 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_100594 : Nat := 118140960795 + 100594 * 2 ^ 59
def prefixEnd_100594 : Nat := 4983230072969 + 3 ^ 40 * 100594 * 2
def baseEnd_100594 : Nat := 22956921314882070761059

theorem tailTrace_100594 : CollatzResearch.WordTrace tailWord_100594 prefixEnd_100594 22956921314882070761059 := by
  unfold tailWord_100594
  simp only [CollatzResearch.WordTrace]
  refine ⟨917241149393148233133209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2445976398381728621688557 917241149393148233133209)
  ·
    refine ⟨687930862044861174849907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 917241149393148233133209 687930862044861174849907)
    ·
      refine ⟨1031896293067291762274861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687930862044861174849907 1031896293067291762274861)
      ·
        refine ⟨386961109900234410853073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1031896293067291762274861 386961109900234410853073)
        ·
          refine ⟨290220832425175808139805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386961109900234410853073 290220832425175808139805)
          ·
            refine ⟨108832812159440928052427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290220832425175808139805 108832812159440928052427)
            ·
              refine ⟨163249218239161392078641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108832812159440928052427 163249218239161392078641)
              ·
                refine ⟨122436913679371044058981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163249218239161392078641 122436913679371044058981)
                ·
                  refine ⟨22956921314882070761059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122436913679371044058981 22956921314882070761059)
                  ·
                    rfl

theorem cell21_100594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_100594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100594 prefixEnd_100594 := by exact prefixLift 100594
  have htrace : WordTrace (prefixWord ++ tailWord_100594) baseStart_100594 baseEnd_100594 := by
    simpa [prefixWord, tailWord_100594, baseEnd_100594] using wordTrace_append hprefix tailTrace_100594
  have hstable : (prefixWord ++ tailWord_100594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100594).length < 2 ^ (prefixWord ++ tailWord_100594).sum := by decide
  have hdescent : baseEnd_100594 < baseStart_100594 := by decide
  rcases family_descends (prefixWord ++ tailWord_100594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100639 : List Nat := [1, 1, 2, 4, 3, 1, 3, 3, 3]
def baseStart_100639 : Nat := 118140960795 + 100639 * 2 ^ 59
def prefixEnd_100639 : Nat := 4983230072969 + 3 ^ 40 * 100639 * 2
def baseEnd_100639 : Nat := 22967190927971992510967

theorem tailTrace_100639 : CollatzResearch.WordTrace tailWord_100639 prefixEnd_100639 22967190927971992510967 := by
  unfold tailWord_100639
  simp only [CollatzResearch.WordTrace]
  refine ⟨3670605882409565617920971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2447070588273043745280647 3670605882409565617920971)
  ·
    refine ⟨5505908823614348426881457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3670605882409565617920971 5505908823614348426881457)
    ·
      refine ⟨4129431617710761320161093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5505908823614348426881457 4129431617710761320161093)
      ·
        refine ⟨774268428320767747530205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4129431617710761320161093 774268428320767747530205)
        ·
          refine ⟨290350660620287905323827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 774268428320767747530205 290350660620287905323827)
          ·
            refine ⟨435525990930431857985741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290350660620287905323827 435525990930431857985741)
            ·
              refine ⟨163322246598911946744653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435525990930431857985741 163322246598911946744653)
              ·
                refine ⟨61245842474591980029245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163322246598911946744653 61245842474591980029245)
                ·
                  refine ⟨22967190927971992510967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61245842474591980029245 22967190927971992510967)
                  ·
                    rfl

theorem cell21_100639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 3].length) (baseStart_100639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100639 prefixEnd_100639 := by exact prefixLift 100639
  have htrace : WordTrace (prefixWord ++ tailWord_100639) baseStart_100639 baseEnd_100639 := by
    simpa [prefixWord, tailWord_100639, baseEnd_100639] using wordTrace_append hprefix tailTrace_100639
  have hstable : (prefixWord ++ tailWord_100639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100639).length < 2 ^ (prefixWord ++ tailWord_100639).sum := by decide
  have hdescent : baseEnd_100639 < baseStart_100639 := by decide
  rcases family_descends (prefixWord ++ tailWord_100639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100670 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_100670 : Nat := 118140960795 + 100670 * 2 ^ 59
def prefixEnd_100670 : Nat := 4983230072969 + 3 ^ 40 * 100670 * 2
def baseEnd_100670 : Nat := 22974265550322827494237

theorem tailTrace_100670 : CollatzResearch.WordTrace tailWord_100670 prefixEnd_100670 22974265550322827494237 := by
  unfold tailWord_100670
  simp only [CollatzResearch.WordTrace]
  refine ⟨458967068162157239037433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2447824363531505274866309 458967068162157239037433)
  ·
    refine ⟨344225301121617929278075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 458967068162157239037433 344225301121617929278075)
    ·
      refine ⟨516337951682426893917113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344225301121617929278075 516337951682426893917113)
      ·
        refine ⟨387253463761820170437835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516337951682426893917113 387253463761820170437835)
        ·
          refine ⟨580880195642730255656753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387253463761820170437835 580880195642730255656753)
          ·
            refine ⟨435660146732047691742565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 580880195642730255656753 435660146732047691742565)
            ·
              refine ⟨81686277512258942201731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 435660146732047691742565 81686277512258942201731)
              ·
                refine ⟨122529416268388413302597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81686277512258942201731 122529416268388413302597)
                ·
                  refine ⟨22974265550322827494237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122529416268388413302597 22974265550322827494237)
                  ·
                    rfl

theorem cell21_100670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_100670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100670 prefixEnd_100670 := by exact prefixLift 100670
  have htrace : WordTrace (prefixWord ++ tailWord_100670) baseStart_100670 baseEnd_100670 := by
    simpa [prefixWord, tailWord_100670, baseEnd_100670] using wordTrace_append hprefix tailTrace_100670
  have hstable : (prefixWord ++ tailWord_100670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100670).length < 2 ^ (prefixWord ++ tailWord_100670).sum := by decide
  have hdescent : baseEnd_100670 < baseStart_100670 := by decide
  rcases family_descends (prefixWord ++ tailWord_100670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100698 : List Nat := [3, 1, 1, 2, 1, 2, 1, 7, 3]
def baseStart_100698 : Nat := 118140960795 + 100698 * 2 ^ 59
def prefixEnd_100698 : Nat := 4983230072969 + 3 ^ 40 * 100698 * 2
def baseEnd_100698 : Nat := 22980655531801001027513

theorem tailTrace_100698 : CollatzResearch.WordTrace tailWord_100698 prefixEnd_100698 22980655531801001027513 := by
  unfold tailWord_100698
  simp only [CollatzResearch.WordTrace]
  refine ⟨918189447298954673579687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2448505192797212462879165 918189447298954673579687)
  ·
    refine ⟨1377284170948432010369531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918189447298954673579687 1377284170948432010369531)
    ·
      refine ⟨2065926256422648015554297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1377284170948432010369531 2065926256422648015554297)
      ·
        refine ⟨1549444692316986011665723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2065926256422648015554297 1549444692316986011665723)
        ·
          refine ⟨2324167038475479017498585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549444692316986011665723 2324167038475479017498585)
          ·
            refine ⟨1743125278856609263123939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2324167038475479017498585 1743125278856609263123939)
            ·
              refine ⟨2614687918284913894685909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743125278856609263123939 2614687918284913894685909)
              ·
                refine ⟨61281748084802669406701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2614687918284913894685909 61281748084802669406701)
                ·
                  refine ⟨22980655531801001027513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61281748084802669406701 22980655531801001027513)
                  ·
                    rfl

theorem cell21_100698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_100698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100698 prefixEnd_100698 := by exact prefixLift 100698
  have htrace : WordTrace (prefixWord ++ tailWord_100698) baseStart_100698 baseEnd_100698 := by
    simpa [prefixWord, tailWord_100698, baseEnd_100698] using wordTrace_append hprefix tailTrace_100698
  have hstable : (prefixWord ++ tailWord_100698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100698).length < 2 ^ (prefixWord ++ tailWord_100698).sum := by decide
  have hdescent : baseEnd_100698 < baseStart_100698 := by decide
  rcases family_descends (prefixWord ++ tailWord_100698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100743 : List Nat := [1, 1, 4, 2, 2, 1, 5, 5]
def baseStart_100743 : Nat := 118140960795 + 100743 * 2 ^ 59
def prefixEnd_100743 : Nat := 4983230072969 + 3 ^ 40 * 100743 * 2
def baseEnd_100743 : Nat := 7663641714963640925807

theorem tailTrace_100743 : CollatzResearch.WordTrace tailWord_100743 prefixEnd_100743 7663641714963640925807 := by
  unfold tailWord_100743
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674399074032791379706883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2449599382688527586471255 3674399074032791379706883)
  ·
    refine ⟨5511598611049187069560325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3674399074032791379706883 5511598611049187069560325)
    ·
      refine ⟨1033424739571722575542561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5511598611049187069560325 1033424739571722575542561)
      ·
        refine ⟨775068554678791931656921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1033424739571722575542561 775068554678791931656921)
        ·
          refine ⟨581301416009093948742691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775068554678791931656921 581301416009093948742691)
          ·
            refine ⟨871952124013640923114037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581301416009093948742691 871952124013640923114037)
            ·
              refine ⟨81745511626278836541941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 871952124013640923114037 81745511626278836541941)
              ·
                refine ⟨7663641714963640925807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81745511626278836541941 7663641714963640925807)
                ·
                  rfl

theorem cell21_100743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 5].length) (baseStart_100743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100743 prefixEnd_100743 := by exact prefixLift 100743
  have htrace : WordTrace (prefixWord ++ tailWord_100743) baseStart_100743 baseEnd_100743 := by
    simpa [prefixWord, tailWord_100743, baseEnd_100743] using wordTrace_append hprefix tailTrace_100743
  have hstable : (prefixWord ++ tailWord_100743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100743).length < 2 ^ (prefixWord ++ tailWord_100743).sum := by decide
  have hdescent : baseEnd_100743 < baseStart_100743 := by decide
  rcases family_descends (prefixWord ++ tailWord_100743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100878 : List Nat := [4, 1, 1, 2, 3, 10]
def baseStart_100878 : Nat := 118140960795 + 100878 * 2 ^ 59
def prefixEnd_100878 : Nat := 4983230072969 + 3 ^ 40 * 100878 * 2
def baseEnd_100878 : Nat := 852656814228173630635

theorem tailTrace_100878 : CollatzResearch.WordTrace tailWord_100878 prefixEnd_100878 852656814228173630635 := by
  unfold tailWord_100878
  simp only [CollatzResearch.WordTrace]
  refine ⟨459915366067963679483911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2452881952362472957247525 459915366067963679483911)
  ·
    refine ⟨689873049101945519225867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 459915366067963679483911 689873049101945519225867)
    ·
      refine ⟨1034809573652918278838801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689873049101945519225867 1034809573652918278838801)
      ·
        refine ⟨776107180239688709129101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1034809573652918278838801 776107180239688709129101)
        ·
          refine ⟨291040192589883265923413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 776107180239688709129101 291040192589883265923413)
          ·
            refine ⟨852656814228173630635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 291040192589883265923413 852656814228173630635)
            ·
              rfl

theorem cell21_100878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 10].length) (baseStart_100878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100878 prefixEnd_100878 := by exact prefixLift 100878
  have htrace : WordTrace (prefixWord ++ tailWord_100878) baseStart_100878 baseEnd_100878 := by
    simpa [prefixWord, tailWord_100878, baseEnd_100878] using wordTrace_append hprefix tailTrace_100878
  have hstable : (prefixWord ++ tailWord_100878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100878).length < 2 ^ (prefixWord ++ tailWord_100878).sum := by decide
  have hdescent : baseEnd_100878 < baseStart_100878 := by decide
  rcases family_descends (prefixWord ++ tailWord_100878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100884 : List Nat := [2, 4, 3, 1, 1, 2, 1, 4, 3]
def baseStart_100884 : Nat := 118140960795 + 100884 * 2 ^ 59
def prefixEnd_100884 : Nat := 4983230072969 + 3 ^ 40 * 100884 * 2
def baseEnd_100884 : Nat := 23023103265906010927133

theorem tailTrace_100884 : CollatzResearch.WordTrace tailWord_100884 prefixEnd_100884 23023103265906010927133 := by
  unfold tailWord_100884
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839770883260986230294853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2453027844347981640393137 1839770883260986230294853)
  ·
    refine ⟨344957040611434918180285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1839770883260986230294853 344957040611434918180285)
    ·
      refine ⟨129358890229288094317607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344957040611434918180285 129358890229288094317607)
      ·
        refine ⟨194038335343932141476411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129358890229288094317607 194038335343932141476411)
        ·
          refine ⟨291057503015898212214617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194038335343932141476411 291057503015898212214617)
          ·
            refine ⟨218293127261923659160963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291057503015898212214617 218293127261923659160963)
            ·
              refine ⟨327439690892885488741445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218293127261923659160963 327439690892885488741445)
              ·
                refine ⟨61394942042416029139021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327439690892885488741445 61394942042416029139021)
                ·
                  refine ⟨23023103265906010927133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61394942042416029139021 23023103265906010927133)
                  ·
                    rfl

theorem cell21_100884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_100884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100884 prefixEnd_100884 := by exact prefixLift 100884
  have htrace : WordTrace (prefixWord ++ tailWord_100884) baseStart_100884 baseEnd_100884 := by
    simpa [prefixWord, tailWord_100884, baseEnd_100884] using wordTrace_append hprefix tailTrace_100884
  have hstable : (prefixWord ++ tailWord_100884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100884).length < 2 ^ (prefixWord ++ tailWord_100884).sum := by decide
  have hdescent : baseEnd_100884 < baseStart_100884 := by decide
  rcases family_descends (prefixWord ++ tailWord_100884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100932 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 4]
def baseStart_100932 : Nat := 118140960795 + 100932 * 2 ^ 59
def prefixEnd_100932 : Nat := 4983230072969 + 3 ^ 40 * 100932 * 2
def baseEnd_100932 : Nat := 23034057519868594127035

theorem tailTrace_100932 : CollatzResearch.WordTrace tailWord_100932 prefixEnd_100932 23034057519868594127035 := by
  unfold tailWord_100932
  simp only [CollatzResearch.WordTrace]
  refine ⟨1840646235174038329168525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2454194980232051105558033 1840646235174038329168525)
  ·
    refine ⟨690242338190264373438197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1840646235174038329168525 690242338190264373438197)
    ·
      refine ⟨64710219205337285009831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 690242338190264373438197 64710219205337285009831)
      ·
        refine ⟨97065328808005927514747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64710219205337285009831 97065328808005927514747)
        ·
          refine ⟨145597993212008891272121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97065328808005927514747 145597993212008891272121)
          ·
            refine ⟨109198494909006668454091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145597993212008891272121 109198494909006668454091)
            ·
              refine ⟨163797742363510002681137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109198494909006668454091 163797742363510002681137)
              ·
                refine ⟨122848306772632502010853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163797742363510002681137 122848306772632502010853)
                ·
                  refine ⟨23034057519868594127035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122848306772632502010853 23034057519868594127035)
                  ·
                    rfl

theorem cell21_100932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_100932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100932 prefixEnd_100932 := by exact prefixLift 100932
  have htrace : WordTrace (prefixWord ++ tailWord_100932) baseStart_100932 baseEnd_100932 := by
    simpa [prefixWord, tailWord_100932, baseEnd_100932] using wordTrace_append hprefix tailTrace_100932
  have hstable : (prefixWord ++ tailWord_100932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100932).length < 2 ^ (prefixWord ++ tailWord_100932).sum := by decide
  have hdescent : baseEnd_100932 < baseStart_100932 := by decide
  rcases family_descends (prefixWord ++ tailWord_100932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100994 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 5]
def baseStart_100994 : Nat := 118140960795 + 100994 * 2 ^ 59
def prefixEnd_100994 : Nat := 4983230072969 + 3 ^ 40 * 100994 * 2
def baseEnd_100994 : Nat := 23048206764570264093575

theorem tailTrace_100994 : CollatzResearch.WordTrace tailWord_100994 prefixEnd_100994 23048206764570264093575 := by
  unfold tailWord_100994
  simp only [CollatzResearch.WordTrace]
  refine ⟨920888449030865311773509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2455702530748974164729357 920888449030865311773509)
  ·
    refine ⟨172666584193287245957533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 920888449030865311773509 172666584193287245957533)
    ·
      refine ⟨64749969072482717234075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172666584193287245957533 64749969072482717234075)
      ·
        refine ⟨97124953608724075851113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64749969072482717234075 97124953608724075851113)
        ·
          refine ⟨72843715206543056888335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97124953608724075851113 72843715206543056888335)
          ·
            refine ⟨109265572809814585332503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72843715206543056888335 109265572809814585332503)
            ·
              refine ⟨163898359214721877998755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109265572809814585332503 163898359214721877998755)
              ·
                refine ⟨245847538822082816998133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163898359214721877998755 245847538822082816998133)
                ·
                  refine ⟨23048206764570264093575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 245847538822082816998133 23048206764570264093575)
                  ·
                    rfl

theorem cell21_100994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_100994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100994 prefixEnd_100994 := by exact prefixLift 100994
  have htrace : WordTrace (prefixWord ++ tailWord_100994) baseStart_100994 baseEnd_100994 := by
    simpa [prefixWord, tailWord_100994, baseEnd_100994] using wordTrace_append hprefix tailTrace_100994
  have hstable : (prefixWord ++ tailWord_100994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100994).length < 2 ^ (prefixWord ++ tailWord_100994).sum := by decide
  have hdescent : baseEnd_100994 < baseStart_100994 := by decide
  rcases family_descends (prefixWord ++ tailWord_100994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100999 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 6]
def baseStart_100999 : Nat := 118140960795 + 100999 * 2 ^ 59
def prefixEnd_100999 : Nat := 4983230072969 + 3 ^ 40 * 100999 * 2
def baseEnd_100999 : Nat := 23049347832691366510231

theorem tailTrace_100999 : CollatzResearch.WordTrace tailWord_100999 prefixEnd_100999 23049347832691366510231 := by
  unfold tailWord_100999
  simp only [CollatzResearch.WordTrace]
  refine ⟨3683736161105347101026051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2455824107403564734017367 3683736161105347101026051)
  ·
    refine ⟨5525604241658020651539077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3683736161105347101026051 5525604241658020651539077)
    ·
      refine ⟨1036050795310878872163577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5525604241658020651539077 1036050795310878872163577)
      ·
        refine ⟨777038096483159154122683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1036050795310878872163577 777038096483159154122683)
        ·
          refine ⟨1165557144724738731184025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777038096483159154122683 1165557144724738731184025)
          ·
            refine ⟨874167858543554048388019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1165557144724738731184025 874167858543554048388019)
            ·
              refine ⟨1311251787815331072582029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874167858543554048388019 1311251787815331072582029)
              ·
                refine ⟨491719420430749152218261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1311251787815331072582029 491719420430749152218261)
                ·
                  refine ⟨23049347832691366510231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 491719420430749152218261 23049347832691366510231)
                  ·
                    rfl

theorem cell21_100999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_100999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_100999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_100999 prefixEnd_100999 := by exact prefixLift 100999
  have htrace : WordTrace (prefixWord ++ tailWord_100999) baseStart_100999 baseEnd_100999 := by
    simpa [prefixWord, tailWord_100999, baseEnd_100999] using wordTrace_append hprefix tailTrace_100999
  have hstable : (prefixWord ++ tailWord_100999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100999).length < 2 ^ (prefixWord ++ tailWord_100999).sum := by decide
  have hdescent : baseEnd_100999 < baseStart_100999 := by decide
  rcases family_descends (prefixWord ++ tailWord_100999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101016 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 4]
def baseStart_101016 : Nat := 118140960795 + 101016 * 2 ^ 59
def prefixEnd_101016 : Nat := 4983230072969 + 3 ^ 40 * 101016 * 2
def baseEnd_101016 : Nat := 23053227464303114726863

theorem tailTrace_101016 : CollatzResearch.WordTrace tailWord_101016 prefixEnd_101016 23053227464303114726863 := by
  unfold tailWord_101016
  simp only [CollatzResearch.WordTrace]
  refine ⟨1842178101021879502197451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2456237468029172669596601 1842178101021879502197451)
  ·
    refine ⟨2763267151532819253296177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1842178101021879502197451 2763267151532819253296177)
    ·
      refine ⟨2072450363649614439972133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2763267151532819253296177 2072450363649614439972133)
      ·
        refine ⟨388584443184302707494775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2072450363649614439972133 388584443184302707494775)
        ·
          refine ⟨582876664776454061242163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388584443184302707494775 582876664776454061242163)
          ·
            refine ⟨874314997164681091863245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582876664776454061242163 874314997164681091863245)
            ·
              refine ⟨327868123936755409448717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 874314997164681091863245 327868123936755409448717)
              ·
                refine ⟨122950546476283278543269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327868123936755409448717 122950546476283278543269)
                ·
                  refine ⟨23053227464303114726863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122950546476283278543269 23053227464303114726863)
                  ·
                    rfl

theorem cell21_101016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_101016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101016 prefixEnd_101016 := by exact prefixLift 101016
  have htrace : WordTrace (prefixWord ++ tailWord_101016) baseStart_101016 baseEnd_101016 := by
    simpa [prefixWord, tailWord_101016, baseEnd_101016] using wordTrace_append hprefix tailTrace_101016
  have hstable : (prefixWord ++ tailWord_101016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101016).length < 2 ^ (prefixWord ++ tailWord_101016).sum := by decide
  have hdescent : baseEnd_101016 < baseStart_101016 := by decide
  rcases family_descends (prefixWord ++ tailWord_101016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101106 : List Nat := [3, 2, 1, 3, 1, 3, 8]
def baseStart_101106 : Nat := 118140960795 + 101106 * 2 ^ 59
def prefixEnd_101106 : Nat := 4983230072969 + 3 ^ 40 * 101106 * 2
def baseEnd_101106 : Nat := 2563751854498106469631

theorem tailTrace_101106 : CollatzResearch.WordTrace tailWord_101106 prefixEnd_101106 2563751854498106469631 := by
  unfold tailWord_101106
  simp only [CollatzResearch.WordTrace]
  refine ⟨921909692929426093792793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2458425847811802916780781 921909692929426093792793)
  ·
    refine ⟨691432269697069570344595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 921909692929426093792793 691432269697069570344595)
    ·
      refine ⟨1037148404545604355516893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 691432269697069570344595 1037148404545604355516893)
      ·
        refine ⟨388930651704601633318835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1037148404545604355516893 388930651704601633318835)
        ·
          refine ⟨583395977556902449978253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388930651704601633318835 583395977556902449978253)
          ·
            refine ⟨218773491583838418741845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 583395977556902449978253 218773491583838418741845)
            ·
              refine ⟨2563751854498106469631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 218773491583838418741845 2563751854498106469631)
              ·
                rfl

theorem cell21_101106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 8].length) (baseStart_101106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101106 prefixEnd_101106 := by exact prefixLift 101106
  have htrace : WordTrace (prefixWord ++ tailWord_101106) baseStart_101106 baseEnd_101106 := by
    simpa [prefixWord, tailWord_101106, baseEnd_101106] using wordTrace_append hprefix tailTrace_101106
  have hstable : (prefixWord ++ tailWord_101106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101106).length < 2 ^ (prefixWord ++ tailWord_101106).sum := by decide
  have hdescent : baseEnd_101106 < baseStart_101106 := by decide
  rcases family_descends (prefixWord ++ tailWord_101106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101151 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 6]
def baseStart_101151 : Nat := 118140960795 + 101151 * 2 ^ 59
def prefixEnd_101151 : Nat := 4983230072969 + 3 ^ 40 * 101151 * 2
def baseEnd_101151 : Nat := 23084036303572879976587

theorem tailTrace_101151 : CollatzResearch.WordTrace tailWord_101151 prefixEnd_101151 23084036303572879976587 := by
  unfold tailWord_101151
  simp only [CollatzResearch.WordTrace]
  refine ⟨3689280056554677060559307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2459520037703118040372871 3689280056554677060559307)
  ·
    refine ⟨5533920084832015590838961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3689280056554677060559307 5533920084832015590838961)
    ·
      refine ⟨4150440063624011693129221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5533920084832015590838961 4150440063624011693129221)
      ·
        refine ⟨778207511929502192461729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4150440063624011693129221 778207511929502192461729)
        ·
          refine ⟨583655633947126644346297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 778207511929502192461729 583655633947126644346297)
          ·
            refine ⟨437741725460344983259723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583655633947126644346297 437741725460344983259723)
            ·
              refine ⟨656612588190517474889585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437741725460344983259723 656612588190517474889585)
              ·
                refine ⟨492459441142888106167189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656612588190517474889585 492459441142888106167189)
                ·
                  refine ⟨23084036303572879976587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 492459441142888106167189 23084036303572879976587)
                  ·
                    rfl

theorem cell21_101151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_101151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101151 prefixEnd_101151 := by exact prefixLift 101151
  have htrace : WordTrace (prefixWord ++ tailWord_101151) baseStart_101151 baseEnd_101151 := by
    simpa [prefixWord, tailWord_101151, baseEnd_101151] using wordTrace_append hprefix tailTrace_101151
  have hstable : (prefixWord ++ tailWord_101151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101151).length < 2 ^ (prefixWord ++ tailWord_101151).sum := by decide
  have hdescent : baseEnd_101151 < baseStart_101151 := by decide
  rcases family_descends (prefixWord ++ tailWord_101151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101171 : List Nat := [1, 1, 1, 2, 6, 2, 3, 2, 3]
def baseStart_101171 : Nat := 118140960795 + 101171 * 2 ^ 59
def prefixEnd_101171 : Nat := 4983230072969 + 3 ^ 40 * 101171 * 2
def baseEnd_101171 : Nat := 23088600576057289643213

theorem tailTrace_101171 : CollatzResearch.WordTrace tailWord_101171 prefixEnd_101171 23088600576057289643213 := by
  unfold tailWord_101171
  simp only [CollatzResearch.WordTrace]
  refine ⟨3690009516482220476287367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2460006344321480317524911 3690009516482220476287367)
  ·
    refine ⟨5535014274723330714431051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3690009516482220476287367 5535014274723330714431051)
    ·
      refine ⟨8302521412084996071646577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5535014274723330714431051 8302521412084996071646577)
      ·
        refine ⟨6226891059063747053734933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8302521412084996071646577 6226891059063747053734933)
        ·
          refine ⟨291885518393613143143825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6226891059063747053734933 291885518393613143143825)
          ·
            refine ⟨218914138795209857357869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291885518393613143143825 218914138795209857357869)
            ·
              refine ⟨82092802048203696509201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218914138795209857357869 82092802048203696509201)
              ·
                refine ⟨61569601536152772381901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82092802048203696509201 61569601536152772381901)
                ·
                  refine ⟨23088600576057289643213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61569601536152772381901 23088600576057289643213)
                  ·
                    rfl

theorem cell21_101171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 3].length) (baseStart_101171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101171 prefixEnd_101171 := by exact prefixLift 101171
  have htrace : WordTrace (prefixWord ++ tailWord_101171) baseStart_101171 baseEnd_101171 := by
    simpa [prefixWord, tailWord_101171, baseEnd_101171] using wordTrace_append hprefix tailTrace_101171
  have hstable : (prefixWord ++ tailWord_101171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101171).length < 2 ^ (prefixWord ++ tailWord_101171).sum := by decide
  have hdescent : baseEnd_101171 < baseStart_101171 := by decide
  rcases family_descends (prefixWord ++ tailWord_101171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101227 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 4]
def baseStart_101227 : Nat := 118140960795 + 101227 * 2 ^ 59
def prefixEnd_101227 : Nat := 4983230072969 + 3 ^ 40 * 101227 * 2
def baseEnd_101227 : Nat := 23101380539013636709765

theorem tailTrace_101227 : CollatzResearch.WordTrace tailWord_101227 prefixEnd_101227 23101380539013636709765 := by
  unfold tailWord_101227
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692052004279342040325935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2461368002852894693550623 3692052004279342040325935)
  ·
    refine ⟨5538078006419013060488903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3692052004279342040325935 5538078006419013060488903)
    ·
      refine ⟨8307117009628519590733355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5538078006419013060488903 8307117009628519590733355)
      ·
        refine ⟨12460675514442779386100033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8307117009628519590733355 12460675514442779386100033)
        ·
          refine ⟨9345506635832084539575025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12460675514442779386100033 9345506635832084539575025)
          ·
            refine ⟨7009129976874063404681269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9345506635832084539575025 7009129976874063404681269)
            ·
              refine ⟨657105935331943444188869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7009129976874063404681269 657105935331943444188869)
              ·
                refine ⟨123207362874739395785413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 657105935331943444188869 123207362874739395785413)
                ·
                  refine ⟨23101380539013636709765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123207362874739395785413 23101380539013636709765)
                  ·
                    rfl

theorem cell21_101227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 4].length) (baseStart_101227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101227 prefixEnd_101227 := by exact prefixLift 101227
  have htrace : WordTrace (prefixWord ++ tailWord_101227) baseStart_101227 baseEnd_101227 := by
    simpa [prefixWord, tailWord_101227, baseEnd_101227] using wordTrace_append hprefix tailTrace_101227
  have hstable : (prefixWord ++ tailWord_101227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101227).length < 2 ^ (prefixWord ++ tailWord_101227).sum := by decide
  have hdescent : baseEnd_101227 < baseStart_101227 := by decide
  rcases family_descends (prefixWord ++ tailWord_101227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101289 : List Nat := [1, 2, 1, 1, 1, 1, 5, 6, 3]
def baseStart_101289 : Nat := 118140960795 + 101289 * 2 ^ 59
def prefixEnd_101289 : Nat := 4983230072969 + 3 ^ 40 * 101289 * 2
def baseEnd_101289 : Nat := 23115529783715306676305

theorem tailTrace_101289 : CollatzResearch.WordTrace tailWord_101289 prefixEnd_101289 23115529783715306676305 := by
  unfold tailWord_101289
  simp only [CollatzResearch.WordTrace]
  refine ⟨3694313330054726629082921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2462875553369817752721947 3694313330054726629082921)
  ·
    refine ⟨2770734997541044971812191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3694313330054726629082921 2770734997541044971812191)
    ·
      refine ⟨4156102496311567457718287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2770734997541044971812191 4156102496311567457718287)
      ·
        refine ⟨6234153744467351186577431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4156102496311567457718287 6234153744467351186577431)
        ·
          refine ⟨9351230616701026779866147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6234153744467351186577431 9351230616701026779866147)
          ·
            refine ⟨14026845925051540169799221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9351230616701026779866147 14026845925051540169799221)
            ·
              refine ⟨1315016805473581890918677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14026845925051540169799221 1315016805473581890918677)
              ·
                refine ⟨61641412756574151136813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1315016805473581890918677 61641412756574151136813)
                ·
                  refine ⟨23115529783715306676305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61641412756574151136813 23115529783715306676305)
                  ·
                    rfl

theorem cell21_101289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 3].length) (baseStart_101289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101289 prefixEnd_101289 := by exact prefixLift 101289
  have htrace : WordTrace (prefixWord ++ tailWord_101289) baseStart_101289 baseEnd_101289 := by
    simpa [prefixWord, tailWord_101289, baseEnd_101289] using wordTrace_append hprefix tailTrace_101289
  have hstable : (prefixWord ++ tailWord_101289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101289).length < 2 ^ (prefixWord ++ tailWord_101289).sum := by decide
  have hdescent : baseEnd_101289 < baseStart_101289 := by decide
  rcases family_descends (prefixWord ++ tailWord_101289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101303 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 4]
def baseStart_101303 : Nat := 118140960795 + 101303 * 2 ^ 59
def prefixEnd_101303 : Nat := 4983230072969 + 3 ^ 40 * 101303 * 2
def baseEnd_101303 : Nat := 23118724774454393442943

theorem tailTrace_101303 : CollatzResearch.WordTrace tailWord_101303 prefixEnd_101303 23118724774454393442943 := by
  unfold tailWord_101303
  simp only [CollatzResearch.WordTrace]
  refine ⟨3694823952004007020092563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2463215968002671346728375 3694823952004007020092563)
  ·
    refine ⟨5542235928006010530138845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3694823952004007020092563 5542235928006010530138845)
    ·
      refine ⟨2078338473002253948802067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5542235928006010530138845 2078338473002253948802067)
      ·
        refine ⟨3117507709503380923203101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2078338473002253948802067 3117507709503380923203101)
        ·
          refine ⟨1169065391063767846201163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3117507709503380923203101 1169065391063767846201163)
          ·
            refine ⟨1753598086595651769301745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169065391063767846201163 1753598086595651769301745)
            ·
              refine ⟨1315198564946738826976309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753598086595651769301745 1315198564946738826976309)
              ·
                refine ⟨123299865463756765029029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1315198564946738826976309 123299865463756765029029)
                ·
                  refine ⟨23118724774454393442943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123299865463756765029029 23118724774454393442943)
                  ·
                    rfl

theorem cell21_101303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 4].length) (baseStart_101303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101303 prefixEnd_101303 := by exact prefixLift 101303
  have htrace : WordTrace (prefixWord ++ tailWord_101303) baseStart_101303 baseEnd_101303 := by
    simpa [prefixWord, tailWord_101303, baseEnd_101303] using wordTrace_append hprefix tailTrace_101303
  have hstable : (prefixWord ++ tailWord_101303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101303).length < 2 ^ (prefixWord ++ tailWord_101303).sum := by decide
  have hdescent : baseEnd_101303 < baseStart_101303 := by decide
  rcases family_descends (prefixWord ++ tailWord_101303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101348 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_101348 : Nat := 118140960795 + 101348 * 2 ^ 59
def prefixEnd_101348 : Nat := 4983230072969 + 3 ^ 40 * 101348 * 2
def baseEnd_101348 : Nat := 23128994387544315192851

theorem tailTrace_101348 : CollatzResearch.WordTrace tailWord_101348 prefixEnd_101348 23128994387544315192851 := by
  unfold tailWord_101348
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848232618420489852740349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2464310157893986470320465 1848232618420489852740349)
  ·
    refine ⟨693087231907683694777631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1848232618420489852740349 693087231907683694777631)
    ·
      refine ⟨1039630847861525542166447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693087231907683694777631 1039630847861525542166447)
      ·
        refine ⟨1559446271792288313249671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039630847861525542166447 1559446271792288313249671)
        ·
          refine ⟨2339169407688432469874507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1559446271792288313249671 2339169407688432469874507)
          ·
            refine ⟨3508754111532648704811761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339169407688432469874507 3508754111532648704811761)
            ·
              refine ⟨2631565583649486528608821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508754111532648704811761 2631565583649486528608821)
              ·
                refine ⟨246709273467139362057077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2631565583649486528608821 246709273467139362057077)
                ·
                  refine ⟨23128994387544315192851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 246709273467139362057077 23128994387544315192851)
                  ·
                    rfl

theorem cell21_101348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_101348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101348 prefixEnd_101348 := by exact prefixLift 101348
  have htrace : WordTrace (prefixWord ++ tailWord_101348) baseStart_101348 baseEnd_101348 := by
    simpa [prefixWord, tailWord_101348, baseEnd_101348] using wordTrace_append hprefix tailTrace_101348
  have hstable : (prefixWord ++ tailWord_101348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101348).length < 2 ^ (prefixWord ++ tailWord_101348).sum := by decide
  have hdescent : baseEnd_101348 < baseStart_101348 := by decide
  rcases family_descends (prefixWord ++ tailWord_101348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101399 : List Nat := [1, 1, 3, 5, 1, 1, 4, 2, 3]
def baseStart_101399 : Nat := 118140960795 + 101399 * 2 ^ 59
def prefixEnd_101399 : Nat := 4983230072969 + 3 ^ 40 * 101399 * 2
def baseEnd_101399 : Nat := 23140633282379559842747

theorem tailTrace_101399 : CollatzResearch.WordTrace tailWord_101399 prefixEnd_101399 23140633282379559842747 := by
  unfold tailWord_101399
  simp only [CollatzResearch.WordTrace]
  refine ⟨3698325359656215415587251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2465550239770810277058167 3698325359656215415587251)
  ·
    refine ⟨5547488039484323123380877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3698325359656215415587251 5547488039484323123380877)
    ·
      refine ⟨2080308014806621171267829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5547488039484323123380877 2080308014806621171267829)
      ·
        refine ⟨195028876388120734806359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2080308014806621171267829 195028876388120734806359)
        ·
          refine ⟨292543314582181102209539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195028876388120734806359 292543314582181102209539)
          ·
            refine ⟨438814971873271653314309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292543314582181102209539 438814971873271653314309)
            ·
              refine ⟨82277807226238434996433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 438814971873271653314309 82277807226238434996433)
              ·
                refine ⟨61708355419678826247325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82277807226238434996433 61708355419678826247325)
                ·
                  refine ⟨23140633282379559842747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61708355419678826247325 23140633282379559842747)
                  ·
                    rfl

theorem cell21_101399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 3].length) (baseStart_101399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101399 prefixEnd_101399 := by exact prefixLift 101399
  have htrace : WordTrace (prefixWord ++ tailWord_101399) baseStart_101399 baseEnd_101399 := by
    simpa [prefixWord, tailWord_101399, baseEnd_101399] using wordTrace_append hprefix tailTrace_101399
  have hstable : (prefixWord ++ tailWord_101399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101399).length < 2 ^ (prefixWord ++ tailWord_101399).sum := by decide
  have hdescent : baseEnd_101399 < baseStart_101399 := by decide
  rcases family_descends (prefixWord ++ tailWord_101399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101410 : List Nat := [3, 3, 1, 1, 1, 3, 3, 6]
def baseStart_101410 : Nat := 118140960795 + 101410 * 2 ^ 59
def prefixEnd_101410 : Nat := 4983230072969 + 3 ^ 40 * 101410 * 2
def baseEnd_101410 : Nat := 7714381210748661719797

theorem tailTrace_101410 : CollatzResearch.WordTrace tailWord_101410 prefixEnd_101410 7714381210748661719797 := by
  unfold tailWord_101410
  simp only [CollatzResearch.WordTrace]
  refine ⟨924681640654091073559421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2465817708410909529491789 924681640654091073559421)
  ·
    refine ⟨346755615245284152584783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 924681640654091073559421 346755615245284152584783)
    ·
      refine ⟨520133422867926228877175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346755615245284152584783 520133422867926228877175)
      ·
        refine ⟨780200134301889343315763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520133422867926228877175 780200134301889343315763)
        ·
          refine ⟨1170300201452834014973645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780200134301889343315763 1170300201452834014973645)
          ·
            refine ⟨438862575544812755615117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1170300201452834014973645 438862575544812755615117)
            ·
              refine ⟨164573465829304783355669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438862575544812755615117 164573465829304783355669)
              ·
                refine ⟨7714381210748661719797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164573465829304783355669 7714381210748661719797)
                ·
                  rfl

theorem cell21_101410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_101410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101410 prefixEnd_101410 := by exact prefixLift 101410
  have htrace : WordTrace (prefixWord ++ tailWord_101410) baseStart_101410 baseEnd_101410 := by
    simpa [prefixWord, tailWord_101410, baseEnd_101410] using wordTrace_append hprefix tailTrace_101410
  have hstable : (prefixWord ++ tailWord_101410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101410).length < 2 ^ (prefixWord ++ tailWord_101410).sum := by decide
  have hdescent : baseEnd_101410 < baseStart_101410 := by decide
  rcases family_descends (prefixWord ++ tailWord_101410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101424 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_101424 : Nat := 118140960795 + 101424 * 2 ^ 59
def prefixEnd_101424 : Nat := 4983230072969 + 3 ^ 40 * 101424 * 2
def baseEnd_101424 : Nat := 23146338622985071926029

theorem tailTrace_101424 : CollatzResearch.WordTrace tailWord_101424 prefixEnd_101424 23146338622985071926029 := by
  unfold tailWord_101424
  simp only [CollatzResearch.WordTrace]
  refine ⟨1849618592282822342623663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2466158123043763123498217 1849618592282822342623663)
  ·
    refine ⟨2774427888424233513935495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1849618592282822342623663 2774427888424233513935495)
    ·
      refine ⟨4161641832636350270903243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2774427888424233513935495 4161641832636350270903243)
      ·
        refine ⟨6242462748954525406354865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4161641832636350270903243 6242462748954525406354865)
        ·
          refine ⟨4681847061715894054766149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6242462748954525406354865 4681847061715894054766149)
          ·
            refine ⟨877846324071730135268653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4681847061715894054766149 877846324071730135268653)
            ·
              refine ⟨329192371526898800725745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 877846324071730135268653 329192371526898800725745)
              ·
                refine ⟨246894278645174100544309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329192371526898800725745 246894278645174100544309)
                ·
                  refine ⟨23146338622985071926029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 246894278645174100544309 23146338622985071926029)
                  ·
                    rfl

theorem cell21_101424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_101424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101424 prefixEnd_101424 := by exact prefixLift 101424
  have htrace : WordTrace (prefixWord ++ tailWord_101424) baseStart_101424 baseEnd_101424 := by
    simpa [prefixWord, tailWord_101424, baseEnd_101424] using wordTrace_append hprefix tailTrace_101424
  have hstable : (prefixWord ++ tailWord_101424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101424).length < 2 ^ (prefixWord ++ tailWord_101424).sum := by decide
  have hdescent : baseEnd_101424 < baseStart_101424 := by decide
  rcases family_descends (prefixWord ++ tailWord_101424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101458 : List Nat := [3, 2, 2, 1, 3, 1, 2, 4, 3]
def baseStart_101458 : Nat := 118140960795 + 101458 * 2 ^ 59
def prefixEnd_101458 : Nat := 4983230072969 + 3 ^ 40 * 101458 * 2
def baseEnd_101458 : Nat := 23154097886208568359293

theorem tailTrace_101458 : CollatzResearch.WordTrace tailWord_101458 prefixEnd_101458 23154097886208568359293 := by
  unfold tailWord_101458
  simp only [CollatzResearch.WordTrace]
  refine ⟨925119316610617122996257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2466984844294978994656685 925119316610617122996257)
  ·
    refine ⟨693839487457962842247193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 925119316610617122996257 693839487457962842247193)
    ·
      refine ⟨520379615593472131685395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 693839487457962842247193 520379615593472131685395)
      ·
        refine ⟨780569423390208197528093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520379615593472131685395 780569423390208197528093)
        ·
          refine ⟨292713533771328074073035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 780569423390208197528093 292713533771328074073035)
          ·
            refine ⟨439070300656992111109553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292713533771328074073035 439070300656992111109553)
            ·
              refine ⟨329302725492744083332165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439070300656992111109553 329302725492744083332165)
              ·
                refine ⟨61744261029889515624781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329302725492744083332165 61744261029889515624781)
                ·
                  refine ⟨23154097886208568359293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61744261029889515624781 23154097886208568359293)
                  ·
                    rfl

theorem cell21_101458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_101458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101458 prefixEnd_101458 := by exact prefixLift 101458
  have htrace : WordTrace (prefixWord ++ tailWord_101458) baseStart_101458 baseEnd_101458 := by
    simpa [prefixWord, tailWord_101458, baseEnd_101458] using wordTrace_append hprefix tailTrace_101458
  have hstable : (prefixWord ++ tailWord_101458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101458).length < 2 ^ (prefixWord ++ tailWord_101458).sum := by decide
  have hdescent : baseEnd_101458 < baseStart_101458 := by decide
  rcases family_descends (prefixWord ++ tailWord_101458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101472 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 4]
def baseStart_101472 : Nat := 118140960795 + 101472 * 2 ^ 59
def prefixEnd_101472 : Nat := 4983230072969 + 3 ^ 40 * 101472 * 2
def baseEnd_101472 : Nat := 23157292876947655125931

theorem tailTrace_101472 : CollatzResearch.WordTrace tailWord_101472 prefixEnd_101472 23157292876947655125931 := by
  unfold tailWord_101472
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850493944195874441497335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2467325258927832588663113 1850493944195874441497335)
  ·
    refine ⟨2775740916293811662246003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1850493944195874441497335 2775740916293811662246003)
    ·
      refine ⟨4163611374440717493369005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2775740916293811662246003 4163611374440717493369005)
      ·
        refine ⟨1561354265415269060013377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4163611374440717493369005 1561354265415269060013377)
        ·
          refine ⟨1171015699061451795010033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1561354265415269060013377 1171015699061451795010033)
          ·
            refine ⟨878261774296088846257525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1171015699061451795010033 878261774296088846257525)
            ·
              refine ⟨82337041340258329336643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 878261774296088846257525 82337041340258329336643)
              ·
                refine ⟨123505562010387494004965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82337041340258329336643 123505562010387494004965)
                ·
                  refine ⟨23157292876947655125931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123505562010387494004965 23157292876947655125931)
                  ·
                    rfl

theorem cell21_101472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_101472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101472 prefixEnd_101472 := by exact prefixLift 101472
  have htrace : WordTrace (prefixWord ++ tailWord_101472) baseStart_101472 baseEnd_101472 := by
    simpa [prefixWord, tailWord_101472, baseEnd_101472] using wordTrace_append hprefix tailTrace_101472
  have hstable : (prefixWord ++ tailWord_101472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101472).length < 2 ^ (prefixWord ++ tailWord_101472).sum := by decide
  have hdescent : baseEnd_101472 < baseStart_101472 := by decide
  rcases family_descends (prefixWord ++ tailWord_101472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101486 : List Nat := [4, 1, 2, 2, 1, 3, 1, 7]
def baseStart_101486 : Nat := 118140960795 + 101486 * 2 ^ 59
def prefixEnd_101486 : Nat := 4983230072969 + 3 ^ 40 * 101486 * 2
def baseEnd_101486 : Nat := 7720162622562247297523

theorem tailTrace_101486 : CollatzResearch.WordTrace tailWord_101486 prefixEnd_101486 7720162622562247297523 := by
  unfold tailWord_101486
  simp only [CollatzResearch.WordTrace]
  refine ⟨462687313792628659250539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2467665673560686182669541 462687313792628659250539)
  ·
    refine ⟨694030970688942988875809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 462687313792628659250539 694030970688942988875809)
    ·
      refine ⟨520523228016707241656857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 694030970688942988875809 520523228016707241656857)
      ·
        refine ⟨390392421012530431242643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520523228016707241656857 390392421012530431242643)
        ·
          refine ⟨585588631518795646863965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390392421012530431242643 585588631518795646863965)
          ·
            refine ⟨219595736819548367573987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 585588631518795646863965 219595736819548367573987)
            ·
              refine ⟨329393605229322551360981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219595736819548367573987 329393605229322551360981)
              ·
                refine ⟨7720162622562247297523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 329393605229322551360981 7720162622562247297523)
                ·
                  rfl

theorem cell21_101486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_101486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101486 prefixEnd_101486 := by exact prefixLift 101486
  have htrace : WordTrace (prefixWord ++ tailWord_101486) baseStart_101486 baseEnd_101486 := by
    simpa [prefixWord, tailWord_101486, baseEnd_101486] using wordTrace_append hprefix tailTrace_101486
  have hstable : (prefixWord ++ tailWord_101486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101486).length < 2 ^ (prefixWord ++ tailWord_101486).sum := by decide
  have hdescent : baseEnd_101486 < baseStart_101486 := by decide
  rcases family_descends (prefixWord ++ tailWord_101486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101568 : List Nat := [2, 1, 1, 2, 7, 1, 2, 2, 3]
def baseStart_101568 : Nat := 118140960795 + 101568 * 2 ^ 59
def prefixEnd_101568 : Nat := 4983230072969 + 3 ^ 40 * 101568 * 2
def baseEnd_101568 : Nat := 23179201384872821525735

theorem tailTrace_101568 : CollatzResearch.WordTrace tailWord_101568 prefixEnd_101568 23179201384872821525735 := by
  unfold tailWord_101568
  simp only [CollatzResearch.WordTrace]
  refine ⟨1852244648021978639244679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2469659530695971518992905 1852244648021978639244679)
  ·
    refine ⟨2778366972032967958867019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1852244648021978639244679 2778366972032967958867019)
    ·
      refine ⟨4167550458049451938300529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2778366972032967958867019 4167550458049451938300529)
      ·
        refine ⟨3125662843537088953725397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4167550458049451938300529 3125662843537088953725397)
        ·
          refine ⟨73257722895400522352939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3125662843537088953725397 73257722895400522352939)
          ·
            refine ⟨109886584343100783529409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73257722895400522352939 109886584343100783529409)
            ·
              refine ⟨82414938257325587647057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109886584343100783529409 82414938257325587647057)
              ·
                refine ⟨61811203692994190735293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82414938257325587647057 61811203692994190735293)
                ·
                  refine ⟨23179201384872821525735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61811203692994190735293 23179201384872821525735)
                  ·
                    rfl

theorem cell21_101568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 3].length) (baseStart_101568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101568 prefixEnd_101568 := by exact prefixLift 101568
  have htrace : WordTrace (prefixWord ++ tailWord_101568) baseStart_101568 baseEnd_101568 := by
    simpa [prefixWord, tailWord_101568, baseEnd_101568] using wordTrace_append hprefix tailTrace_101568
  have hstable : (prefixWord ++ tailWord_101568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101568).length < 2 ^ (prefixWord ++ tailWord_101568).sum := by decide
  have hdescent : baseEnd_101568 < baseStart_101568 := by decide
  rcases family_descends (prefixWord ++ tailWord_101568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101610 : List Nat := [3, 1, 3, 1, 1, 4, 2, 3, 3]
def baseStart_101610 : Nat := 118140960795 + 101610 * 2 ^ 59
def prefixEnd_101610 : Nat := 4983230072969 + 3 ^ 40 * 101610 * 2
def baseEnd_101610 : Nat := 23188786357090081825649

theorem tailTrace_101610 : CollatzResearch.WordTrace tailWord_101610 prefixEnd_101610 23188786357090081825649 := by
  unfold tailWord_101610
  simp only [CollatzResearch.WordTrace]
  refine ⟨926505290472949612879571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2470680774594532301012189 926505290472949612879571)
  ·
    refine ⟨1389757935709424419319357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 926505290472949612879571 1389757935709424419319357)
    ·
      refine ⟨521159225891034157244759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1389757935709424419319357 521159225891034157244759)
      ·
        refine ⟨781738838836551235867139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521159225891034157244759 781738838836551235867139)
        ·
          refine ⟨1172608258254826853800709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781738838836551235867139 1172608258254826853800709)
          ·
            refine ⟨219864048422780035087633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1172608258254826853800709 219864048422780035087633)
            ·
              refine ⟨164898036317085026315725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219864048422780035087633 164898036317085026315725)
              ·
                refine ⟨61836763618906884868397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164898036317085026315725 61836763618906884868397)
                ·
                  refine ⟨23188786357090081825649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61836763618906884868397 23188786357090081825649)
                  ·
                    rfl

theorem cell21_101610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_101610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101610 prefixEnd_101610 := by exact prefixLift 101610
  have htrace : WordTrace (prefixWord ++ tailWord_101610) baseStart_101610 baseEnd_101610 := by
    simpa [prefixWord, tailWord_101610, baseEnd_101610] using wordTrace_append hprefix tailTrace_101610
  have hstable : (prefixWord ++ tailWord_101610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101610).length < 2 ^ (prefixWord ++ tailWord_101610).sum := by decide
  have hdescent : baseEnd_101610 < baseStart_101610 := by decide
  rcases family_descends (prefixWord ++ tailWord_101610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101762 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_101762 : Nat := 118140960795 + 101762 * 2 ^ 59
def prefixEnd_101762 : Nat := 4983230072969 + 3 ^ 40 * 101762 * 2
def baseEnd_101762 : Nat := 23223474827971595292005

theorem tailTrace_101762 : CollatzResearch.WordTrace tailWord_101762 prefixEnd_101762 23223474827971595292005 := by
  unfold tailWord_101762
  simp only [CollatzResearch.WordTrace]
  refine ⟨927891264335282102762885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2474376704894085607367693 927891264335282102762885)
  ·
    refine ⟨173979612062865394268041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 927891264335282102762885 173979612062865394268041)
    ·
      refine ⟨130484709047149045701031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173979612062865394268041 130484709047149045701031)
      ·
        refine ⟨195727063570723568551547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130484709047149045701031 195727063570723568551547)
        ·
          refine ⟨293590595356085352827321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195727063570723568551547 293590595356085352827321)
          ·
            refine ⟨220192946517064014620491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293590595356085352827321 220192946517064014620491)
            ·
              refine ⟨330289419775596021930737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220192946517064014620491 330289419775596021930737)
              ·
                refine ⟨247717064831697016448053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330289419775596021930737 247717064831697016448053)
                ·
                  refine ⟨23223474827971595292005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 247717064831697016448053 23223474827971595292005)
                  ·
                    rfl

theorem cell21_101762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_101762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101762 prefixEnd_101762 := by exact prefixLift 101762
  have htrace : WordTrace (prefixWord ++ tailWord_101762) baseStart_101762 baseEnd_101762 := by
    simpa [prefixWord, tailWord_101762, baseEnd_101762] using wordTrace_append hprefix tailTrace_101762
  have hstable : (prefixWord ++ tailWord_101762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101762).length < 2 ^ (prefixWord ++ tailWord_101762).sum := by decide
  have hdescent : baseEnd_101762 < baseStart_101762 := by decide
  rcases family_descends (prefixWord ++ tailWord_101762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101849 : List Nat := [1, 2, 1, 2, 4, 4, 7]
def baseStart_101849 : Nat := 118140960795 + 101849 * 2 ^ 59
def prefixEnd_101849 : Nat := 4983230072969 + 3 ^ 40 * 101849 * 2
def baseEnd_101849 : Nat := 2582592157030975260203

theorem tailTrace_101849 : CollatzResearch.WordTrace tailWord_101849 prefixEnd_101849 2582592157030975260203 := by
  unfold tailWord_101849
  simp only [CollatzResearch.WordTrace]
  refine ⟨3714738208025942269468601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2476492138683961512979067 3714738208025942269468601)
  ·
    refine ⟨2786053656019456702101451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3714738208025942269468601 2786053656019456702101451)
    ·
      refine ⟨4179080484029185053152177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2786053656019456702101451 4179080484029185053152177)
      ·
        refine ⟨3134310363021888789864133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4179080484029185053152177 3134310363021888789864133)
        ·
          refine ⟨587683193066604148099525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3134310363021888789864133 587683193066604148099525)
          ·
            refine ⟨110190598699988277768661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 587683193066604148099525 110190598699988277768661)
            ·
              refine ⟨2582592157030975260203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110190598699988277768661 2582592157030975260203)
              ·
                rfl

theorem cell21_101849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 7].length) (baseStart_101849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101849 prefixEnd_101849 := by exact prefixLift 101849
  have htrace : WordTrace (prefixWord ++ tailWord_101849) baseStart_101849 baseEnd_101849 := by
    simpa [prefixWord, tailWord_101849, baseEnd_101849] using wordTrace_append hprefix tailTrace_101849
  have hstable : (prefixWord ++ tailWord_101849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101849).length < 2 ^ (prefixWord ++ tailWord_101849).sum := by decide
  have hdescent : baseEnd_101849 < baseStart_101849 := by decide
  rcases family_descends (prefixWord ++ tailWord_101849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101866 : List Nat := [3, 1, 3, 1, 4, 1, 2, 6]
def baseStart_101866 : Nat := 118140960795 + 101866 * 2 ^ 59
def prefixEnd_101866 : Nat := 4983230072969 + 3 ^ 40 * 101866 * 2
def baseEnd_101866 : Nat := 7749069681630175186153

theorem tailTrace_101866 : CollatzResearch.WordTrace tailWord_101866 prefixEnd_101866 7749069681630175186153 := by
  unfold tailWord_101866
  simp only [CollatzResearch.WordTrace]
  refine ⟨928839562241088543209363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2476905499309569448558301 928839562241088543209363)
  ·
    refine ⟨1393259343361632814814045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 928839562241088543209363 1393259343361632814814045)
    ·
      refine ⟨522472253760612305555267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1393259343361632814814045 522472253760612305555267)
      ·
        refine ⟨783708380640918458332901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522472253760612305555267 783708380640918458332901)
        ·
          refine ⟨146945321370172210937419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 783708380640918458332901 146945321370172210937419)
          ·
            refine ⟨220417982055258316406129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146945321370172210937419 220417982055258316406129)
            ·
              refine ⟨165313486541443737304597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220417982055258316406129 165313486541443737304597)
              ·
                refine ⟨7749069681630175186153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165313486541443737304597 7749069681630175186153)
                ·
                  rfl

theorem cell21_101866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_101866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101866 prefixEnd_101866 := by exact prefixLift 101866
  have htrace : WordTrace (prefixWord ++ tailWord_101866) baseStart_101866 baseEnd_101866 := by
    simpa [prefixWord, tailWord_101866, baseEnd_101866] using wordTrace_append hprefix tailTrace_101866
  have hstable : (prefixWord ++ tailWord_101866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101866).length < 2 ^ (prefixWord ++ tailWord_101866).sum := by decide
  have hdescent : baseEnd_101866 < baseStart_101866 := by decide
  rcases family_descends (prefixWord ++ tailWord_101866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101939 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 7]
def baseStart_101939 : Nat := 118140960795 + 101939 * 2 ^ 59
def prefixEnd_101939 : Nat := 4983230072969 + 3 ^ 40 * 101939 * 2
def baseEnd_101939 : Nat := 23263868639458620841643

theorem tailTrace_101939 : CollatzResearch.WordTrace tailWord_101939 prefixEnd_101939 23263868639458620841643 := by
  unfold tailWord_101939
  simp only [CollatzResearch.WordTrace]
  refine ⟨3718020777699887640244871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2478680518466591760163247 3718020777699887640244871)
  ·
    refine ⟨5577031166549831460367307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3718020777699887640244871 5577031166549831460367307)
    ·
      refine ⟨8365546749824747190550961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5577031166549831460367307 8365546749824747190550961)
      ·
        refine ⟨6274160062368560392913221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8365546749824747190550961 6274160062368560392913221)
        ·
          refine ⟨1176405011694105073671229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6274160062368560392913221 1176405011694105073671229)
          ·
            refine ⟨441151879385289402626711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1176405011694105073671229 441151879385289402626711)
            ·
              refine ⟨661727819077934103940067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441151879385289402626711 661727819077934103940067)
              ·
                refine ⟨992591728616901155910101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661727819077934103940067 992591728616901155910101)
                ·
                  refine ⟨23263868639458620841643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 992591728616901155910101 23263868639458620841643)
                  ·
                    rfl

theorem cell21_101939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_101939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101939 prefixEnd_101939 := by exact prefixLift 101939
  have htrace : WordTrace (prefixWord ++ tailWord_101939) baseStart_101939 baseEnd_101939 := by
    simpa [prefixWord, tailWord_101939, baseEnd_101939] using wordTrace_append hprefix tailTrace_101939
  have hstable : (prefixWord ++ tailWord_101939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101939).length < 2 ^ (prefixWord ++ tailWord_101939).sum := by decide
  have hdescent : baseEnd_101939 < baseStart_101939 := by decide
  rcases family_descends (prefixWord ++ tailWord_101939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101984 : List Nat := [2, 1, 1, 3, 2, 1, 1, 10]
def baseStart_101984 : Nat := 118140960795 + 101984 * 2 ^ 59
def prefixEnd_101984 : Nat := 4983230072969 + 3 ^ 40 * 101984 * 2
def baseEnd_101984 : Nat := 7758046084182847530517

theorem tailTrace_101984 : CollatzResearch.WordTrace tailWord_101984 prefixEnd_101984 7758046084182847530517 := by
  unfold tailWord_101984
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859831031268430162816503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2479774708357906883755337 1859831031268430162816503)
  ·
    refine ⟨2789746546902645244224755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1859831031268430162816503 2789746546902645244224755)
    ·
      refine ⟨4184619820353967866337133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2789746546902645244224755 4184619820353967866337133)
      ·
        refine ⟨1569232432632737949876425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4184619820353967866337133 1569232432632737949876425)
        ·
          refine ⟨1176924324474553462407319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1569232432632737949876425 1176924324474553462407319)
          ·
            refine ⟨1765386486711830193610979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176924324474553462407319 1765386486711830193610979)
            ·
              refine ⟨2648079730067745290416469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765386486711830193610979 2648079730067745290416469)
              ·
                refine ⟨7758046084182847530517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2648079730067745290416469 7758046084182847530517)
                ·
                  rfl

theorem cell21_101984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_101984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_101984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_101984 prefixEnd_101984 := by exact prefixLift 101984
  have htrace : WordTrace (prefixWord ++ tailWord_101984) baseStart_101984 baseEnd_101984 := by
    simpa [prefixWord, tailWord_101984, baseEnd_101984] using wordTrace_append hprefix tailTrace_101984
  have hstable : (prefixWord ++ tailWord_101984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101984).length < 2 ^ (prefixWord ++ tailWord_101984).sum := by decide
  have hdescent : baseEnd_101984 < baseStart_101984 := by decide
  rcases family_descends (prefixWord ++ tailWord_101984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102032 : List Nat := [2, 1, 1, 1, 1, 1, 3, 8, 3]
def baseStart_102032 : Nat := 118140960795 + 102032 * 2 ^ 59
def prefixEnd_102032 : Nat := 4983230072969 + 3 ^ 40 * 102032 * 2
def baseEnd_102032 : Nat := 23285092506511125791453

theorem tailTrace_102032 : CollatzResearch.WordTrace tailWord_102032 prefixEnd_102032 23285092506511125791453 := by
  unfold tailWord_102032
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860706383181482261690175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2480941844241976348920233 1860706383181482261690175)
  ·
    refine ⟨2791059574772223392535263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1860706383181482261690175 2791059574772223392535263)
    ·
      refine ⟨4186589362158335088802895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2791059574772223392535263 4186589362158335088802895)
      ·
        refine ⟨6279884043237502633204343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186589362158335088802895 6279884043237502633204343)
        ·
          refine ⟨9419826064856253949806515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279884043237502633204343 9419826064856253949806515)
          ·
            refine ⟨14129739097284380924709773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9419826064856253949806515 14129739097284380924709773)
            ·
              refine ⟨5298652161481642846766165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14129739097284380924709773 5298652161481642846766165)
              ·
                refine ⟨62093580017363002110541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5298652161481642846766165 62093580017363002110541)
                ·
                  refine ⟨23285092506511125791453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62093580017363002110541 23285092506511125791453)
                  ·
                    rfl

theorem cell21_102032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 3].length) (baseStart_102032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102032 prefixEnd_102032 := by exact prefixLift 102032
  have htrace : WordTrace (prefixWord ++ tailWord_102032) baseStart_102032 baseEnd_102032 := by
    simpa [prefixWord, tailWord_102032, baseEnd_102032] using wordTrace_append hprefix tailTrace_102032
  have hstable : (prefixWord ++ tailWord_102032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102032).length < 2 ^ (prefixWord ++ tailWord_102032).sum := by decide
  have hdescent : baseEnd_102032 < baseStart_102032 := by decide
  rcases family_descends (prefixWord ++ tailWord_102032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102125 : List Nat := [1, 5, 1, 2, 1, 2, 1, 5, 3]
def baseStart_102125 : Nat := 118140960795 + 102125 * 2 ^ 59
def prefixEnd_102125 : Nat := 4983230072969 + 3 ^ 40 * 102125 * 2
def baseEnd_102125 : Nat := 23306316373563630741263

theorem tailTrace_102125 : CollatzResearch.WordTrace tailWord_102125 prefixEnd_102125 23306316373563630741263 := by
  unfold tailWord_102125
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724804755026041406515829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2483203170017360937677219 3724804755026041406515829)
  ·
    refine ⟨349200445783691381860859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3724804755026041406515829 349200445783691381860859)
    ·
      refine ⟨523800668675537072791289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349200445783691381860859 523800668675537072791289)
      ·
        refine ⟨392850501506652804593467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523800668675537072791289 392850501506652804593467)
        ·
          refine ⟨589275752259979206890201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392850501506652804593467 589275752259979206890201)
          ·
            refine ⟨441956814194984405167651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589275752259979206890201 441956814194984405167651)
            ·
              refine ⟨662935221292476607751477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441956814194984405167651 662935221292476607751477)
              ·
                refine ⟨62150176996169681976701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 662935221292476607751477 62150176996169681976701)
                ·
                  refine ⟨23306316373563630741263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62150176996169681976701 23306316373563630741263)
                  ·
                    rfl

theorem cell21_102125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_102125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102125 prefixEnd_102125 := by exact prefixLift 102125
  have htrace : WordTrace (prefixWord ++ tailWord_102125) baseStart_102125 baseEnd_102125 := by
    simpa [prefixWord, tailWord_102125, baseEnd_102125] using wordTrace_append hprefix tailTrace_102125
  have hstable : (prefixWord ++ tailWord_102125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102125).length < 2 ^ (prefixWord ++ tailWord_102125).sum := by decide
  have hdescent : baseEnd_102125 < baseStart_102125 := by decide
  rcases family_descends (prefixWord ++ tailWord_102125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102170 : List Nat := [3, 1, 1, 3, 2, 4, 2, 5]
def baseStart_102170 : Nat := 118140960795 + 102170 * 2 ^ 59
def prefixEnd_102170 : Nat := 4983230072969 + 3 ^ 40 * 102170 * 2
def baseEnd_102170 : Nat := 7772195328884517497057

theorem tailTrace_102170 : CollatzResearch.WordTrace tailWord_102170 prefixEnd_102170 7772195328884517497057 := by
  unfold tailWord_102170
  simp only [CollatzResearch.WordTrace]
  refine ⟨931611509965753522975991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2484297359908676061269309 931611509965753522975991)
  ·
    refine ⟨1397417264948630284463987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 931611509965753522975991 1397417264948630284463987)
    ·
      refine ⟨2096125897422945426695981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1397417264948630284463987 2096125897422945426695981)
      ·
        refine ⟨786047211533604535010993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2096125897422945426695981 786047211533604535010993)
        ·
          refine ⟨589535408650203401258245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786047211533604535010993 589535408650203401258245)
          ·
            refine ⟨110537889121913137735921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 589535408650203401258245 110537889121913137735921)
            ·
              refine ⟨82903416841434853301941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110537889121913137735921 82903416841434853301941)
              ·
                refine ⟨7772195328884517497057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82903416841434853301941 7772195328884517497057)
                ·
                  rfl

theorem cell21_102170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_102170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102170 prefixEnd_102170 := by exact prefixLift 102170
  have htrace : WordTrace (prefixWord ++ tailWord_102170) baseStart_102170 baseEnd_102170 := by
    simpa [prefixWord, tailWord_102170, baseEnd_102170] using wordTrace_append hprefix tailTrace_102170
  have hstable : (prefixWord ++ tailWord_102170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102170).length < 2 ^ (prefixWord ++ tailWord_102170).sum := by decide
  have hdescent : baseEnd_102170 < baseStart_102170 := by decide
  rcases family_descends (prefixWord ++ tailWord_102170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102215 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 4]
def baseStart_102215 : Nat := 118140960795 + 102215 * 2 ^ 59
def prefixEnd_102215 : Nat := 4983230072969 + 3 ^ 40 * 102215 * 2
def baseEnd_102215 : Nat := 23326855599743474241079

theorem tailTrace_102215 : CollatzResearch.WordTrace tailWord_102215 prefixEnd_102215 23326855599743474241079 := by
  unfold tailWord_102215
  simp only [CollatzResearch.WordTrace]
  refine ⟨3728087324699986777292099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2485391549799991184861399 3728087324699986777292099)
  ·
    refine ⟨5592130987049980165938149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3728087324699986777292099 5592130987049980165938149)
    ·
      refine ⟨1048524560071871281113403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5592130987049980165938149 1048524560071871281113403)
      ·
        refine ⟨1572786840107806921670105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048524560071871281113403 1572786840107806921670105)
        ·
          refine ⟨1179590130080855191252579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1572786840107806921670105 1179590130080855191252579)
          ·
            refine ⟨1769385195121282786878869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179590130080855191252579 1769385195121282786878869)
            ·
              refine ⟨82939931021310130634947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1769385195121282786878869 82939931021310130634947)
              ·
                refine ⟨124409896531965195952421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82939931021310130634947 124409896531965195952421)
                ·
                  refine ⟨23326855599743474241079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124409896531965195952421 23326855599743474241079)
                  ·
                    rfl

theorem cell21_102215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 4].length) (baseStart_102215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102215 prefixEnd_102215 := by exact prefixLift 102215
  have htrace : WordTrace (prefixWord ++ tailWord_102215) baseStart_102215 baseEnd_102215 := by
    simpa [prefixWord, tailWord_102215, baseEnd_102215] using wordTrace_append hprefix tailTrace_102215
  have hstable : (prefixWord ++ tailWord_102215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102215).length < 2 ^ (prefixWord ++ tailWord_102215).sum := by decide
  have hdescent : baseEnd_102215 < baseStart_102215 := by decide
  rcases family_descends (prefixWord ++ tailWord_102215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102305 : List Nat := [1, 2, 3, 4, 2, 1, 8]
def baseStart_102305 : Nat := 118140960795 + 102305 * 2 ^ 59
def prefixEnd_102305 : Nat := 4983230072969 + 3 ^ 40 * 102305 * 2
def baseEnd_102305 : Nat := 2594154980658146415655

theorem tailTrace_102305 : CollatzResearch.WordTrace tailWord_102305 prefixEnd_102305 2594154980658146415655 := by
  unfold tailWord_102305
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731369894373932148068369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2487579929582621432045579 3731369894373932148068369)
  ·
    refine ⟨2798527420780449111051277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3731369894373932148068369 2798527420780449111051277)
    ·
      refine ⟨1049447782792668416644229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2798527420780449111051277 1049447782792668416644229)
      ·
        refine ⟨196771459273625328120793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1049447782792668416644229 196771459273625328120793)
        ·
          refine ⟨147578594455218996090595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196771459273625328120793 147578594455218996090595)
          ·
            refine ⟨221367891682828494135893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147578594455218996090595 221367891682828494135893)
            ·
              refine ⟨2594154980658146415655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 221367891682828494135893 2594154980658146415655)
              ·
                rfl

theorem cell21_102305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 8].length) (baseStart_102305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102305 prefixEnd_102305 := by exact prefixLift 102305
  have htrace : WordTrace (prefixWord ++ tailWord_102305) baseStart_102305 baseEnd_102305 := by
    simpa [prefixWord, tailWord_102305, baseEnd_102305] using wordTrace_append hprefix tailTrace_102305
  have hstable : (prefixWord ++ tailWord_102305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102305).length < 2 ^ (prefixWord ++ tailWord_102305).sum := by decide
  have hdescent : baseEnd_102305 < baseStart_102305 := by decide
  rcases family_descends (prefixWord ++ tailWord_102305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102319 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 5]
def baseStart_102319 : Nat := 118140960795 + 102319 * 2 ^ 59
def prefixEnd_102319 : Nat := 4983230072969 + 3 ^ 40 * 102319 * 2
def baseEnd_102319 : Nat := 23350589816662404507533

theorem tailTrace_102319 : CollatzResearch.WordTrace tailWord_102319 prefixEnd_102319 23350589816662404507533 := by
  unfold tailWord_102319
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731880516323212539078011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2487920344215475026052007 3731880516323212539078011)
  ·
    refine ⟨5597820774484818808617017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3731880516323212539078011 5597820774484818808617017)
    ·
      refine ⟨4198365580863614106462763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5597820774484818808617017 4198365580863614106462763)
      ·
        refine ⟨6297548371295421159694145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198365580863614106462763 6297548371295421159694145)
        ·
          refine ⟨4723161278471565869770609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6297548371295421159694145 4723161278471565869770609)
          ·
            refine ⟨3542370958853674402327957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4723161278471565869770609 3542370958853674402327957)
            ·
              refine ⟨166048638696265987609123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3542370958853674402327957 166048638696265987609123)
              ·
                refine ⟨249072958044398981413685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166048638696265987609123 249072958044398981413685)
                ·
                  refine ⟨23350589816662404507533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 249072958044398981413685 23350589816662404507533)
                  ·
                    rfl

theorem cell21_102319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 5].length) (baseStart_102319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102319 prefixEnd_102319 := by exact prefixLift 102319
  have htrace : WordTrace (prefixWord ++ tailWord_102319) baseStart_102319 baseEnd_102319 := by
    simpa [prefixWord, tailWord_102319, baseEnd_102319] using wordTrace_append hprefix tailTrace_102319
  have hstable : (prefixWord ++ tailWord_102319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102319).length < 2 ^ (prefixWord ++ tailWord_102319).sum := by decide
  have hdescent : baseEnd_102319 < baseStart_102319 := by decide
  rcases family_descends (prefixWord ++ tailWord_102319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102370 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_102370 : Nat := 118140960795 + 102370 * 2 ^ 59
def prefixEnd_102370 : Nat := 4983230072969 + 3 ^ 40 * 102370 * 2
def baseEnd_102370 : Nat := 23362228711497649157429

theorem tailTrace_102370 : CollatzResearch.WordTrace tailWord_102370 prefixEnd_102370 23362228711497649157429 := by
  unfold tailWord_102370
  simp only [CollatzResearch.WordTrace]
  refine ⟨933435159784612062296141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2489160426092298832789709 933435159784612062296141)
  ·
    refine ⟨350038184919229523361053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 933435159784612062296141 350038184919229523361053)
    ·
      refine ⟨131264319344711071260395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350038184919229523361053 131264319344711071260395)
      ·
        refine ⟨196896479017066606890593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131264319344711071260395 196896479017066606890593)
        ·
          refine ⟨147672359262799955167945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196896479017066606890593 147672359262799955167945)
          ·
            refine ⟨110754269447099966375959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147672359262799955167945 110754269447099966375959)
            ·
              refine ⟨166131404170649949563939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110754269447099966375959 166131404170649949563939)
              ·
                refine ⟨249197106255974924345909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166131404170649949563939 249197106255974924345909)
                ·
                  refine ⟨23362228711497649157429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 249197106255974924345909 23362228711497649157429)
                  ·
                    rfl

theorem cell21_102370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_102370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102370 prefixEnd_102370 := by exact prefixLift 102370
  have htrace : WordTrace (prefixWord ++ tailWord_102370) baseStart_102370 baseEnd_102370 := by
    simpa [prefixWord, tailWord_102370, baseEnd_102370] using wordTrace_append hprefix tailTrace_102370
  have hstable : (prefixWord ++ tailWord_102370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102370).length < 2 ^ (prefixWord ++ tailWord_102370).sum := by decide
  have hdescent : baseEnd_102370 < baseStart_102370 := by decide
  rcases family_descends (prefixWord ++ tailWord_102370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102412 : List Nat := [2, 2, 1, 2, 3, 1, 2, 5, 3]
def baseStart_102412 : Nat := 118140960795 + 102412 * 2 ^ 59
def prefixEnd_102412 : Nat := 4983230072969 + 3 ^ 40 * 102412 * 2
def baseEnd_102412 : Nat := 23371813683714909457343

theorem tailTrace_102412 : CollatzResearch.WordTrace tailWord_102412 prefixEnd_102412 23371813683714909457343 := by
  unfold tailWord_102412
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867636252493144711106745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2490181669990859614808993 1867636252493144711106745)
  ·
    refine ⟨1400727189369858533330059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1867636252493144711106745 1400727189369858533330059)
    ·
      refine ⟨2101090784054787799995089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1400727189369858533330059 2101090784054787799995089)
      ·
        refine ⟨1575818088041090849996317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2101090784054787799995089 1575818088041090849996317)
        ·
          refine ⟨590931783015409068748619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1575818088041090849996317 590931783015409068748619)
          ·
            refine ⟨886397674523113603122929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590931783015409068748619 886397674523113603122929)
            ·
              refine ⟨664798255892335202342197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886397674523113603122929 664798255892335202342197)
              ·
                refine ⟨62324836489906425219581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 664798255892335202342197 62324836489906425219581)
                ·
                  refine ⟨23371813683714909457343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62324836489906425219581 23371813683714909457343)
                  ·
                    rfl

theorem cell21_102412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_102412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102412 prefixEnd_102412 := by exact prefixLift 102412
  have htrace : WordTrace (prefixWord ++ tailWord_102412) baseStart_102412 baseEnd_102412 := by
    simpa [prefixWord, tailWord_102412, baseEnd_102412] using wordTrace_append hprefix tailTrace_102412
  have hstable : (prefixWord ++ tailWord_102412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102412).length < 2 ^ (prefixWord ++ tailWord_102412).sum := by decide
  have hdescent : baseEnd_102412 < baseStart_102412 := by decide
  rcases family_descends (prefixWord ++ tailWord_102412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102426 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_102426 : Nat := 118140960795 + 102426 * 2 ^ 59
def prefixEnd_102426 : Nat := 4983230072969 + 3 ^ 40 * 102426 * 2
def baseEnd_102426 : Nat := 23375008674453996223981

theorem tailTrace_102426 : CollatzResearch.WordTrace tailWord_102426 prefixEnd_102426 23375008674453996223981 := by
  unfold tailWord_102426
  simp only [CollatzResearch.WordTrace]
  refine ⟨933945781733892453305783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2490522084623713208815421 933945781733892453305783)
  ·
    refine ⟨1400918672600838679958675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 933945781733892453305783 1400918672600838679958675)
    ·
      refine ⟨2101378008901258019938013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1400918672600838679958675 2101378008901258019938013)
      ·
        refine ⟨788016753337971757476755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2101378008901258019938013 788016753337971757476755)
        ·
          refine ⟨1182025130006957636215133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788016753337971757476755 1182025130006957636215133)
          ·
            refine ⟨443259423752609113580675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1182025130006957636215133 443259423752609113580675)
            ·
              refine ⟨664889135628913670371013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443259423752609113580675 664889135628913670371013)
              ·
                refine ⟨124666712930421313194565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 664889135628913670371013 124666712930421313194565)
                ·
                  refine ⟨23375008674453996223981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124666712930421313194565 23375008674453996223981)
                  ·
                    rfl

theorem cell21_102426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_102426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102426 prefixEnd_102426 := by exact prefixLift 102426
  have htrace : WordTrace (prefixWord ++ tailWord_102426) baseStart_102426 baseEnd_102426 := by
    simpa [prefixWord, tailWord_102426, baseEnd_102426] using wordTrace_append hprefix tailTrace_102426
  have hstable : (prefixWord ++ tailWord_102426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102426).length < 2 ^ (prefixWord ++ tailWord_102426).sum := by decide
  have hdescent : baseEnd_102426 < baseStart_102426 := by decide
  rcases family_descends (prefixWord ++ tailWord_102426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102429 : List Nat := [1, 4, 2, 2, 2, 2, 1, 4, 3]
def baseStart_102429 : Nat := 118140960795 + 102429 * 2 ^ 59
def prefixEnd_102429 : Nat := 4983230072969 + 3 ^ 40 * 102429 * 2
def baseEnd_102429 : Nat := 23375693315326657673975

theorem tailTrace_102429 : CollatzResearch.WordTrace tailWord_102429 prefixEnd_102429 23375693315326657673975 := by
  unfold tailWord_102429
  simp only [CollatzResearch.WordTrace]
  refine ⟨3735892545924701325582341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2490595030616467550388227 3735892545924701325582341)
  ·
    refine ⟨700479852360881498546689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3735892545924701325582341 700479852360881498546689)
    ·
      refine ⟨525359889270661123910017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 700479852360881498546689 525359889270661123910017)
      ·
        refine ⟨394019916952995842932513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525359889270661123910017 394019916952995842932513)
        ·
          refine ⟨295514937714746882199385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394019916952995842932513 295514937714746882199385)
          ·
            refine ⟨221636203286060161649539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295514937714746882199385 221636203286060161649539)
            ·
              refine ⟨332454304929090242474309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221636203286060161649539 332454304929090242474309)
              ·
                refine ⟨62335182174204420463933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 332454304929090242474309 62335182174204420463933)
                ·
                  refine ⟨23375693315326657673975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62335182174204420463933 23375693315326657673975)
                  ·
                    rfl

theorem cell21_102429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_102429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102429 prefixEnd_102429 := by exact prefixLift 102429
  have htrace : WordTrace (prefixWord ++ tailWord_102429) baseStart_102429 baseEnd_102429 := by
    simpa [prefixWord, tailWord_102429, baseEnd_102429] using wordTrace_append hprefix tailTrace_102429
  have hstable : (prefixWord ++ tailWord_102429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102429).length < 2 ^ (prefixWord ++ tailWord_102429).sum := by decide
  have hdescent : baseEnd_102429 < baseStart_102429 := by decide
  rcases family_descends (prefixWord ++ tailWord_102429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102488 : List Nat := [2, 1, 2, 2, 1, 4, 2, 4, 3]
def baseStart_102488 : Nat := 118140960795 + 102488 * 2 ^ 59
def prefixEnd_102488 : Nat := 4983230072969 + 3 ^ 40 * 102488 * 2
def baseEnd_102488 : Nat := 23389157919155666190521

theorem tailTrace_102488 : CollatzResearch.WordTrace tailWord_102488 prefixEnd_102488 23389157919155666190521 := by
  unfold tailWord_102488
  simp only [CollatzResearch.WordTrace]
  refine ⟨1869022226355477200990059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2492029635140636267986745 1869022226355477200990059)
  ·
    refine ⟨2803533339533215801485089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1869022226355477200990059 2803533339533215801485089)
    ·
      refine ⟨2102650004649911851113817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2803533339533215801485089 2102650004649911851113817)
      ·
        refine ⟨1576987503487433888335363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2102650004649911851113817 1576987503487433888335363)
        ·
          refine ⟨2365481255231150832503045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1576987503487433888335363 2365481255231150832503045)
          ·
            refine ⟨443527735355840781094321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2365481255231150832503045 443527735355840781094321)
            ·
              refine ⟨332645801516880585820741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443527735355840781094321 332645801516880585820741)
              ·
                refine ⟨62371087784415109841389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 332645801516880585820741 62371087784415109841389)
                ·
                  refine ⟨23389157919155666190521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62371087784415109841389 23389157919155666190521)
                  ·
                    rfl

theorem cell21_102488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 3].length) (baseStart_102488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102488 prefixEnd_102488 := by exact prefixLift 102488
  have htrace : WordTrace (prefixWord ++ tailWord_102488) baseStart_102488 baseEnd_102488 := by
    simpa [prefixWord, tailWord_102488, baseEnd_102488] using wordTrace_append hprefix tailTrace_102488
  have hstable : (prefixWord ++ tailWord_102488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102488).length < 2 ^ (prefixWord ++ tailWord_102488).sum := by decide
  have hdescent : baseEnd_102488 < baseStart_102488 := by decide
  rcases family_descends (prefixWord ++ tailWord_102488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102494 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_102494 : Nat := 118140960795 + 102494 * 2 ^ 59
def prefixEnd_102494 : Nat := 4983230072969 + 3 ^ 40 * 102494 * 2
def baseEnd_102494 : Nat := 23390527200900989090509

theorem tailTrace_102494 : CollatzResearch.WordTrace tailWord_102494 prefixEnd_102494 23390527200900989090509 := by
  unfold tailWord_102494
  simp only [CollatzResearch.WordTrace]
  refine ⟨467282911336152178337317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2492175527126144951132357 467282911336152178337317)
  ·
    refine ⟨87615545875528533438247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 467282911336152178337317 87615545875528533438247)
    ·
      refine ⟨131423318813292800157371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87615545875528533438247 131423318813292800157371)
      ·
        refine ⟨197134978219939200236057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131423318813292800157371 197134978219939200236057)
        ·
          refine ⟨147851233664954400177043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197134978219939200236057 147851233664954400177043)
          ·
            refine ⟨221776850497431600265565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147851233664954400177043 221776850497431600265565)
            ·
              refine ⟨83166318936536850099587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221776850497431600265565 83166318936536850099587)
              ·
                refine ⟨124749478404805275149381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83166318936536850099587 124749478404805275149381)
                ·
                  refine ⟨23390527200900989090509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124749478404805275149381 23390527200900989090509)
                  ·
                    rfl

theorem cell21_102494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_102494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102494 prefixEnd_102494 := by exact prefixLift 102494
  have htrace : WordTrace (prefixWord ++ tailWord_102494) baseStart_102494 baseEnd_102494 := by
    simpa [prefixWord, tailWord_102494, baseEnd_102494] using wordTrace_append hprefix tailTrace_102494
  have hstable : (prefixWord ++ tailWord_102494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102494).length < 2 ^ (prefixWord ++ tailWord_102494).sum := by decide
  have hdescent : baseEnd_102494 < baseStart_102494 := by decide
  rcases family_descends (prefixWord ++ tailWord_102494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102654 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_102654 : Nat := 118140960795 + 102654 * 2 ^ 59
def prefixEnd_102654 : Nat := 4983230072969 + 3 ^ 40 * 102654 * 2
def baseEnd_102654 : Nat := 23427041380776266423515

theorem tailTrace_102654 : CollatzResearch.WordTrace tailWord_102654 prefixEnd_102654 23427041380776266423515 := by
  unfold tailWord_102654
  simp only [CollatzResearch.WordTrace]
  refine ⟨468012371263695594065377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2496065980073043168348677 468012371263695594065377)
  ·
    refine ⟨351009278447771695549033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 468012371263695594065377 351009278447771695549033)
    ·
      refine ⟨263256958835828771661775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351009278447771695549033 263256958835828771661775)
      ·
        refine ⟨394885438253743157492663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263256958835828771661775 394885438253743157492663)
        ·
          refine ⟨592328157380614736238995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394885438253743157492663 592328157380614736238995)
          ·
            refine ⟨888492236070922104358493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592328157380614736238995 888492236070922104358493)
            ·
              refine ⟨333184588526595789134435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 888492236070922104358493 333184588526595789134435)
              ·
                refine ⟨499776882789893683701653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333184588526595789134435 499776882789893683701653)
                ·
                  refine ⟨23427041380776266423515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 499776882789893683701653 23427041380776266423515)
                  ·
                    rfl

theorem cell21_102654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_102654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102654 prefixEnd_102654 := by exact prefixLift 102654
  have htrace : WordTrace (prefixWord ++ tailWord_102654) baseStart_102654 baseEnd_102654 := by
    simpa [prefixWord, tailWord_102654, baseEnd_102654] using wordTrace_append hprefix tailTrace_102654
  have hstable : (prefixWord ++ tailWord_102654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102654).length < 2 ^ (prefixWord ++ tailWord_102654).sum := by decide
  have hdescent : baseEnd_102654 < baseStart_102654 := by decide
  rcases family_descends (prefixWord ++ tailWord_102654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102685 : List Nat := [1, 4, 2, 3, 2, 1, 1, 7]
def baseStart_102685 : Nat := 118140960795 + 102685 * 2 ^ 59
def prefixEnd_102685 : Nat := 4983230072969 + 3 ^ 40 * 102685 * 2
def baseEnd_102685 : Nat := 7811372001042367135595

theorem tailTrace_102685 : CollatzResearch.WordTrace tailWord_102685 prefixEnd_102685 7811372001042367135595 := by
  unfold tailWord_102685
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745229632997257046901509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2496819755331504697934339 3745229632997257046901509)
  ·
    refine ⟨702230556186985696294033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3745229632997257046901509 702230556186985696294033)
    ·
      refine ⟨526672917140239272220525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 702230556186985696294033 526672917140239272220525)
      ·
        refine ⟨197502343927589727082697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526672917140239272220525 197502343927589727082697)
        ·
          refine ⟨148126757945692295312023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197502343927589727082697 148126757945692295312023)
          ·
            refine ⟨222190136918538442968035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148126757945692295312023 222190136918538442968035)
            ·
              refine ⟨333285205377807664452053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222190136918538442968035 333285205377807664452053)
              ·
                refine ⟨7811372001042367135595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 333285205377807664452053 7811372001042367135595)
                ·
                  rfl

theorem cell21_102685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 7].length) (baseStart_102685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102685 prefixEnd_102685 := by exact prefixLift 102685
  have htrace : WordTrace (prefixWord ++ tailWord_102685) baseStart_102685 baseEnd_102685 := by
    simpa [prefixWord, tailWord_102685, baseEnd_102685] using wordTrace_append hprefix tailTrace_102685
  have hstable : (prefixWord ++ tailWord_102685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102685).length < 2 ^ (prefixWord ++ tailWord_102685).sum := by decide
  have hdescent : baseEnd_102685 < baseStart_102685 := by decide
  rcases family_descends (prefixWord ++ tailWord_102685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102702 : List Nat := [4, 1, 3, 3, 1, 2, 7]
def baseStart_102702 : Nat := 118140960795 + 102702 * 2 ^ 59
def prefixEnd_102702 : Nat := 4983230072969 + 3 ^ 40 * 102702 * 2
def baseEnd_102702 : Nat := 2604221737193205513713

theorem tailTrace_102702 : CollatzResearch.WordTrace tailWord_102702 prefixEnd_102702 2604221737193205513713 := by
  unfold tailWord_102702
  simp only [CollatzResearch.WordTrace]
  refine ⟨468231209241958618783795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2497233115957112633513573 468231209241958618783795)
  ·
    refine ⟨702346813862937928175693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 468231209241958618783795 702346813862937928175693)
    ·
      refine ⟨263380055198601723065885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 702346813862937928175693 263380055198601723065885)
      ·
        refine ⟨98767520699475646149707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263380055198601723065885 98767520699475646149707)
        ·
          refine ⟨148151281049213469224561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98767520699475646149707 148151281049213469224561)
          ·
            refine ⟨111113460786910101918421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148151281049213469224561 111113460786910101918421)
            ·
              refine ⟨2604221737193205513713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 111113460786910101918421 2604221737193205513713)
              ·
                rfl

theorem cell21_102702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 7].length) (baseStart_102702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102702 prefixEnd_102702 := by exact prefixLift 102702
  have htrace : WordTrace (prefixWord ++ tailWord_102702) baseStart_102702 baseEnd_102702 := by
    simpa [prefixWord, tailWord_102702, baseEnd_102702] using wordTrace_append hprefix tailTrace_102702
  have hstable : (prefixWord ++ tailWord_102702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102702).length < 2 ^ (prefixWord ++ tailWord_102702).sum := by decide
  have hdescent : baseEnd_102702 < baseStart_102702 := by decide
  rcases family_descends (prefixWord ++ tailWord_102702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102823 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 4]
def baseStart_102823 : Nat := 118140960795 + 102823 * 2 ^ 59
def prefixEnd_102823 : Nat := 4983230072969 + 3 ^ 40 * 102823 * 2
def baseEnd_102823 : Nat := 23465609483269528106503

theorem tailTrace_102823 : CollatzResearch.WordTrace tailWord_102823 prefixEnd_102823 23465609483269528106503 := by
  unfold tailWord_102823
  simp only [CollatzResearch.WordTrace]
  refine ⟨3750262906497306615425123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2500175270998204410283415 3750262906497306615425123)
  ·
    refine ⟨5625394359745959923137685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3750262906497306615425123 5625394359745959923137685)
    ·
      refine ⟨263690360613091871397079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5625394359745959923137685 263690360613091871397079)
      ·
        refine ⟨395535540919637807095619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263690360613091871397079 395535540919637807095619)
        ·
          refine ⟨593303311379456710643429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395535540919637807095619 593303311379456710643429)
          ·
            refine ⟨111244370883648133245643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 593303311379456710643429 111244370883648133245643)
            ·
              refine ⟨166866556325472199868465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111244370883648133245643 166866556325472199868465)
              ·
                refine ⟨125149917244104149901349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166866556325472199868465 125149917244104149901349)
                ·
                  refine ⟨23465609483269528106503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125149917244104149901349 23465609483269528106503)
                  ·
                    rfl

theorem cell21_102823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 4].length) (baseStart_102823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102823 prefixEnd_102823 := by exact prefixLift 102823
  have htrace : WordTrace (prefixWord ++ tailWord_102823) baseStart_102823 baseEnd_102823 := by
    simpa [prefixWord, tailWord_102823, baseEnd_102823] using wordTrace_append hprefix tailTrace_102823
  have hstable : (prefixWord ++ tailWord_102823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102823).length < 2 ^ (prefixWord ++ tailWord_102823).sum := by decide
  have hdescent : baseEnd_102823 < baseStart_102823 := by decide
  rcases family_descends (prefixWord ++ tailWord_102823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102826 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 5]
def baseStart_102826 : Nat := 118140960795 + 102826 * 2 ^ 59
def prefixEnd_102826 : Nat := 4983230072969 + 3 ^ 40 * 102826 * 2
def baseEnd_102826 : Nat := 23466294124142189556497

theorem tailTrace_102826 : CollatzResearch.WordTrace tailWord_102826 prefixEnd_102826 23466294124142189556497 := by
  unfold tailWord_102826
  simp only [CollatzResearch.WordTrace]
  refine ⟨937593081371609531946083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2500248216990958751856221 937593081371609531946083)
  ·
    refine ⟨1406389622057414297919125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 937593081371609531946083 1406389622057414297919125)
    ·
      refine ⟨65924513533941295214959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1406389622057414297919125 65924513533941295214959)
      ·
        refine ⟨98886770300911942822439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65924513533941295214959 98886770300911942822439)
        ·
          refine ⟨148330155451367914233659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98886770300911942822439 148330155451367914233659)
          ·
            refine ⟨222495233177051871350489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148330155451367914233659 222495233177051871350489)
            ·
              refine ⟨166871424882788903512867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222495233177051871350489 166871424882788903512867)
              ·
                refine ⟨250307137324183355269301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166871424882788903512867 250307137324183355269301)
                ·
                  refine ⟨23466294124142189556497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250307137324183355269301 23466294124142189556497)
                  ·
                    rfl

theorem cell21_102826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_102826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102826 prefixEnd_102826 := by exact prefixLift 102826
  have htrace : WordTrace (prefixWord ++ tailWord_102826) baseStart_102826 baseEnd_102826 := by
    simpa [prefixWord, tailWord_102826, baseEnd_102826] using wordTrace_append hprefix tailTrace_102826
  have hstable : (prefixWord ++ tailWord_102826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102826).length < 2 ^ (prefixWord ++ tailWord_102826).sum := by decide
  have hdescent : baseEnd_102826 < baseStart_102826 := by decide
  rcases family_descends (prefixWord ++ tailWord_102826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102879 : List Nat := [1, 1, 2, 3, 3, 2, 9]
def baseStart_102879 : Nat := 118140960795 + 102879 * 2 ^ 59
def prefixEnd_102879 : Nat := 4983230072969 + 3 ^ 40 * 102879 * 2
def baseEnd_102879 : Nat := 2608709938469541685895

theorem tailTrace_102879 : CollatzResearch.WordTrace tailWord_102879 prefixEnd_102879 2608709938469541685895 := by
  unfold tailWord_102879
  simp only [CollatzResearch.WordTrace]
  refine ⟨3752305394294428179463691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2501536929529618786309127 3752305394294428179463691)
  ·
    refine ⟨5628458091441642269195537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3752305394294428179463691 5628458091441642269195537)
    ·
      refine ⟨4221343568581231701896653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5628458091441642269195537 4221343568581231701896653)
      ·
        refine ⟨1583003838217961888211245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4221343568581231701896653 1583003838217961888211245)
        ·
          refine ⟨593626439331735708079217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1583003838217961888211245 593626439331735708079217)
          ·
            refine ⟨445219829498801781059413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593626439331735708079217 445219829498801781059413)
            ·
              refine ⟨2608709938469541685895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 445219829498801781059413 2608709938469541685895)
              ·
                rfl

theorem cell21_102879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 9].length) (baseStart_102879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102879 prefixEnd_102879 := by exact prefixLift 102879
  have htrace : WordTrace (prefixWord ++ tailWord_102879) baseStart_102879 baseEnd_102879 := by
    simpa [prefixWord, tailWord_102879, baseEnd_102879] using wordTrace_append hprefix tailTrace_102879
  have hstable : (prefixWord ++ tailWord_102879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102879).length < 2 ^ (prefixWord ++ tailWord_102879).sum := by decide
  have hdescent : baseEnd_102879 < baseStart_102879 := by decide
  rcases family_descends (prefixWord ++ tailWord_102879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102885 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 5]
def baseStart_102885 : Nat := 118140960795 + 102885 * 2 ^ 59
def prefixEnd_102885 : Nat := 4983230072969 + 3 ^ 40 * 102885 * 2
def baseEnd_102885 : Nat := 23479758727971198073043

theorem tailTrace_102885 : CollatzResearch.WordTrace tailWord_102885 prefixEnd_102885 23479758727971198073043 := by
  unfold tailWord_102885
  simp only [CollatzResearch.WordTrace]
  refine ⟨3752524232272691204182109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2501682821515127469454739 3752524232272691204182109)
  ·
    refine ⟨1407196587102259201568291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3752524232272691204182109 1407196587102259201568291)
    ·
      refine ⟨2110794880653388802352437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407196587102259201568291 2110794880653388802352437)
      ·
        refine ⟨197887020061255200220541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2110794880653388802352437 197887020061255200220541)
        ·
          refine ⟨74207632522970700082703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197887020061255200220541 74207632522970700082703)
          ·
            refine ⟨111311448784456050124055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74207632522970700082703 111311448784456050124055)
            ·
              refine ⟨166967173176684075186083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111311448784456050124055 166967173176684075186083)
              ·
                refine ⟨250450759765026112779125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166967173176684075186083 250450759765026112779125)
                ·
                  refine ⟨23479758727971198073043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250450759765026112779125 23479758727971198073043)
                  ·
                    rfl

theorem cell21_102885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_102885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_102885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_102885 prefixEnd_102885 := by exact prefixLift 102885
  have htrace : WordTrace (prefixWord ++ tailWord_102885) baseStart_102885 baseEnd_102885 := by
    simpa [prefixWord, tailWord_102885, baseEnd_102885] using wordTrace_append hprefix tailTrace_102885
  have hstable : (prefixWord ++ tailWord_102885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102885).length < 2 ^ (prefixWord ++ tailWord_102885).sum := by decide
  have hdescent : baseEnd_102885 < baseStart_102885 := by decide
  rcases family_descends (prefixWord ++ tailWord_102885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103037 : List Nat := [1, 4, 1, 1, 5, 2, 1, 3, 3]
def baseStart_103037 : Nat := 118140960795 + 103037 * 2 ^ 59
def prefixEnd_103037 : Nat := 4983230072969 + 3 ^ 40 * 103037 * 2
def baseEnd_103037 : Nat := 23514447198852711539399

theorem tailTrace_103037 : CollatzResearch.WordTrace tailWord_103037 prefixEnd_103037 23514447198852711539399 := by
  unfold tailWord_103037
  simp only [CollatzResearch.WordTrace]
  refine ⟨3758068127722021163715365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2505378751814680775810243 3758068127722021163715365)
  ·
    refine ⟨704637773947878968196631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3758068127722021163715365 704637773947878968196631)
    ·
      refine ⟨1056956660921818452294947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704637773947878968196631 1056956660921818452294947)
      ·
        refine ⟨1585434991382727678442421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056956660921818452294947 1585434991382727678442421)
        ·
          refine ⟨148634530442130719853977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1585434991382727678442421 148634530442130719853977)
          ·
            refine ⟨111475897831598039890483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148634530442130719853977 111475897831598039890483)
            ·
              refine ⟨167213846747397059835725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111475897831598039890483 167213846747397059835725)
              ·
                refine ⟨62705192530273897438397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167213846747397059835725 62705192530273897438397)
                ·
                  refine ⟨23514447198852711539399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62705192530273897438397 23514447198852711539399)
                  ·
                    rfl

theorem cell21_103037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_103037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103037 prefixEnd_103037 := by exact prefixLift 103037
  have htrace : WordTrace (prefixWord ++ tailWord_103037) baseStart_103037 baseEnd_103037 := by
    simpa [prefixWord, tailWord_103037, baseEnd_103037] using wordTrace_append hprefix tailTrace_103037
  have hstable : (prefixWord ++ tailWord_103037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103037).length < 2 ^ (prefixWord ++ tailWord_103037).sum := by decide
  have hdescent : baseEnd_103037 < baseStart_103037 := by decide
  rcases family_descends (prefixWord ++ tailWord_103037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103152 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_103152 : Nat := 118140960795 + 103152 * 2 ^ 59
def prefixEnd_103152 : Nat := 4983230072969 + 3 ^ 40 * 103152 * 2
def baseEnd_103152 : Nat := 23540691765638067122497

theorem tailTrace_103152 : CollatzResearch.WordTrace tailWord_103152 prefixEnd_103152 23540691765638067122497 := by
  unfold tailWord_103152
  simp only [CollatzResearch.WordTrace]
  refine ⟨1881131261152697902075855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2508175014870263869434473 1881131261152697902075855)
  ·
    refine ⟨2821696891729046853113783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1881131261152697902075855 2821696891729046853113783)
    ·
      refine ⟨4232545337593570279670675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2821696891729046853113783 4232545337593570279670675)
      ·
        refine ⟨6348818006390355419506013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4232545337593570279670675 6348818006390355419506013)
        ·
          refine ⟨2380806752396383282314755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6348818006390355419506013 2380806752396383282314755)
          ·
            refine ⟨3571210128594574923472133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380806752396383282314755 3571210128594574923472133)
            ·
              refine ⟨669601899111482798151025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3571210128594574923472133 669601899111482798151025)
              ·
                refine ⟨502201424333612098613269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669601899111482798151025 502201424333612098613269)
                ·
                  refine ⟨23540691765638067122497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 502201424333612098613269 23540691765638067122497)
                  ·
                    rfl

theorem cell21_103152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_103152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103152 prefixEnd_103152 := by exact prefixLift 103152
  have htrace : WordTrace (prefixWord ++ tailWord_103152) baseStart_103152 baseEnd_103152 := by
    simpa [prefixWord, tailWord_103152, baseEnd_103152] using wordTrace_append hprefix tailTrace_103152
  have hstable : (prefixWord ++ tailWord_103152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103152).length < 2 ^ (prefixWord ++ tailWord_103152).sum := by decide
  have hdescent : baseEnd_103152 < baseStart_103152 := by decide
  rcases family_descends (prefixWord ++ tailWord_103152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103200 : List Nat := [2, 1, 1, 5, 1, 2, 4, 5]
def baseStart_103200 : Nat := 118140960795 + 103200 * 2 ^ 59
def prefixEnd_103200 : Nat := 4983230072969 + 3 ^ 40 * 103200 * 2
def baseEnd_103200 : Nat := 7850548673200216774133

theorem tailTrace_103200 : CollatzResearch.WordTrace tailWord_103200 prefixEnd_103200 7850548673200216774133 := by
  unfold tailWord_103200
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882006613065750000949527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2509342150754333334599369 1882006613065750000949527)
  ·
    refine ⟨2823009919598625001424291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1882006613065750000949527 2823009919598625001424291)
    ·
      refine ⟨4234514879397937502136437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823009919598625001424291 4234514879397937502136437)
      ·
        refine ⟨396985769943556640825291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4234514879397937502136437 396985769943556640825291)
        ·
          refine ⟨595478654915334961237937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396985769943556640825291 595478654915334961237937)
          ·
            refine ⟨446608991186501220928453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595478654915334961237937 446608991186501220928453)
            ·
              refine ⟨83739185847468978924085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 446608991186501220928453 83739185847468978924085)
              ·
                refine ⟨7850548673200216774133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83739185847468978924085 7850548673200216774133)
                ·
                  rfl

theorem cell21_103200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_103200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103200 prefixEnd_103200 := by exact prefixLift 103200
  have htrace : WordTrace (prefixWord ++ tailWord_103200) baseStart_103200 baseEnd_103200 := by
    simpa [prefixWord, tailWord_103200, baseEnd_103200] using wordTrace_append hprefix tailTrace_103200
  have hstable : (prefixWord ++ tailWord_103200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103200).length < 2 ^ (prefixWord ++ tailWord_103200).sum := by decide
  have hdescent : baseEnd_103200 < baseStart_103200 := by decide
  rcases family_descends (prefixWord ++ tailWord_103200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103231 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 5]
def baseStart_103231 : Nat := 118140960795 + 103231 * 2 ^ 59
def prefixEnd_103231 : Nat := 4983230072969 + 3 ^ 40 * 103231 * 2
def baseEnd_103231 : Nat := 23558720641951485305669

theorem tailTrace_103231 : CollatzResearch.WordTrace tailWord_103231 prefixEnd_103231 23558720641951485305669 := by
  unfold tailWord_103231
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765143889019192296277547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2510095926012794864185031 3765143889019192296277547)
  ·
    refine ⟨5647715833528788444416321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3765143889019192296277547 5647715833528788444416321)
    ·
      refine ⟨4235786875146591333312241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5647715833528788444416321 4235786875146591333312241)
      ·
        refine ⟨3176840156359943499984181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4235786875146591333312241 3176840156359943499984181)
        ·
          refine ⟨297828764658744703123517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3176840156359943499984181 297828764658744703123517)
          ·
            refine ⟨111685786747029263671319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297828764658744703123517 111685786747029263671319)
            ·
              refine ⟨167528680120543895506979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111685786747029263671319 167528680120543895506979)
              ·
                refine ⟨251293020180815843260469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167528680120543895506979 251293020180815843260469)
                ·
                  refine ⟨23558720641951485305669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 251293020180815843260469 23558720641951485305669)
                  ·
                    rfl

theorem cell21_103231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 5].length) (baseStart_103231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103231 prefixEnd_103231 := by exact prefixLift 103231
  have htrace : WordTrace (prefixWord ++ tailWord_103231) baseStart_103231 baseEnd_103231 := by
    simpa [prefixWord, tailWord_103231, baseEnd_103231] using wordTrace_append hprefix tailTrace_103231
  have hstable : (prefixWord ++ tailWord_103231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103231).length < 2 ^ (prefixWord ++ tailWord_103231).sum := by decide
  have hdescent : baseEnd_103231 < baseStart_103231 := by decide
  rcases family_descends (prefixWord ++ tailWord_103231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103414 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_103414 : Nat := 118140960795 + 103414 * 2 ^ 59
def prefixEnd_103414 : Nat := 4983230072969 + 3 ^ 40 * 103414 * 2
def baseEnd_103414 : Nat := 23600483735183833755295

theorem tailTrace_103414 : CollatzResearch.WordTrace tailWord_103414 prefixEnd_103414 23600483735183833755295 := by
  unfold tailWord_103414
  simp only [CollatzResearch.WordTrace]
  refine ⟨235738652959763409386831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2514545631570809700126197 235738652959763409386831)
  ·
    refine ⟨353607979439645114080247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235738652959763409386831 353607979439645114080247)
    ·
      refine ⟨530411969159467671120371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353607979439645114080247 530411969159467671120371)
      ·
        refine ⟨795617953739201506680557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530411969159467671120371 795617953739201506680557)
        ·
          refine ⟨298356732652200565005209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795617953739201506680557 298356732652200565005209)
          ·
            refine ⟨223767549489150423753907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298356732652200565005209 223767549489150423753907)
            ·
              refine ⟨335651324233725635630861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223767549489150423753907 335651324233725635630861)
              ·
                refine ⟨125869246587647113361573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335651324233725635630861 125869246587647113361573)
                ·
                  refine ⟨23600483735183833755295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125869246587647113361573 23600483735183833755295)
                  ·
                    rfl

theorem cell21_103414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_103414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103414 prefixEnd_103414 := by exact prefixLift 103414
  have htrace : WordTrace (prefixWord ++ tailWord_103414) baseStart_103414 baseEnd_103414 := by
    simpa [prefixWord, tailWord_103414, baseEnd_103414] using wordTrace_append hprefix tailTrace_103414
  have hstable : (prefixWord ++ tailWord_103414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103414).length < 2 ^ (prefixWord ++ tailWord_103414).sum := by decide
  have hdescent : baseEnd_103414 < baseStart_103414 := by decide
  rcases family_descends (prefixWord ++ tailWord_103414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103459 : List Nat := [1, 1, 1, 4, 3, 3, 1, 4, 3]
def baseStart_103459 : Nat := 118140960795 + 103459 * 2 ^ 59
def prefixEnd_103459 : Nat := 4983230072969 + 3 ^ 40 * 103459 * 2
def baseEnd_103459 : Nat := 23610753348273755505203

theorem tailTrace_103459 : CollatzResearch.WordTrace tailWord_103459 prefixEnd_103459 23610753348273755505203 := by
  unfold tailWord_103459
  simp only [CollatzResearch.WordTrace]
  refine ⟨3773459732193187235577431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2515639821462124823718287 3773459732193187235577431)
  ·
    refine ⟨5660189598289780853366147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3773459732193187235577431 5660189598289780853366147)
    ·
      refine ⟨8490284397434671280049221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5660189598289780853366147 8490284397434671280049221)
      ·
        refine ⟨1591928324519000865009229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8490284397434671280049221 1591928324519000865009229)
        ·
          refine ⟨596973121694625324378461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1591928324519000865009229 596973121694625324378461)
          ·
            refine ⟨223864920635484496641923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 596973121694625324378461 223864920635484496641923)
            ·
              refine ⟨335797380953226744962885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223864920635484496641923 335797380953226744962885)
              ·
                refine ⟨62962008928730014680541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335797380953226744962885 62962008928730014680541)
                ·
                  refine ⟨23610753348273755505203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62962008928730014680541 23610753348273755505203)
                  ·
                    rfl

theorem cell21_103459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 3].length) (baseStart_103459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103459 prefixEnd_103459 := by exact prefixLift 103459
  have htrace : WordTrace (prefixWord ++ tailWord_103459) baseStart_103459 baseEnd_103459 := by
    simpa [prefixWord, tailWord_103459, baseEnd_103459] using wordTrace_append hprefix tailTrace_103459
  have hstable : (prefixWord ++ tailWord_103459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103459).length < 2 ^ (prefixWord ++ tailWord_103459).sum := by decide
  have hdescent : baseEnd_103459 < baseStart_103459 := by decide
  rcases family_descends (prefixWord ++ tailWord_103459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103583 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 4]
def baseStart_103583 : Nat := 118140960795 + 103583 * 2 ^ 59
def prefixEnd_103583 : Nat := 4983230072969 + 3 ^ 40 * 103583 * 2
def baseEnd_103583 : Nat := 23639051837677095438283

theorem tailTrace_103583 : CollatzResearch.WordTrace tailWord_103583 prefixEnd_103583 23639051837677095438283 := by
  unfold tailWord_103583
  simp only [CollatzResearch.WordTrace]
  refine ⟨3777982383743956413091403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2518654922495970942060935 3777982383743956413091403)
  ·
    refine ⟨5666973575615934619637105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3777982383743956413091403 5666973575615934619637105)
    ·
      refine ⟨4250230181711950964727829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5666973575615934619637105 4250230181711950964727829)
      ·
        refine ⟨199229539767747701471617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4250230181711950964727829 199229539767747701471617)
        ·
          refine ⟨149422154825810776103713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199229539767747701471617 149422154825810776103713)
          ·
            refine ⟨112066616119358082077785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149422154825810776103713 112066616119358082077785)
            ·
              refine ⟨84049962089518561558339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112066616119358082077785 84049962089518561558339)
              ·
                refine ⟨126074943134277842337509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84049962089518561558339 126074943134277842337509)
                ·
                  refine ⟨23639051837677095438283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126074943134277842337509 23639051837677095438283)
                  ·
                    rfl

theorem cell21_103583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 4].length) (baseStart_103583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103583 prefixEnd_103583 := by exact prefixLift 103583
  have htrace : WordTrace (prefixWord ++ tailWord_103583) baseStart_103583 baseEnd_103583 := by
    simpa [prefixWord, tailWord_103583, baseEnd_103583] using wordTrace_append hprefix tailTrace_103583
  have hstable : (prefixWord ++ tailWord_103583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103583).length < 2 ^ (prefixWord ++ tailWord_103583).sum := by decide
  have hdescent : baseEnd_103583 < baseStart_103583 := by decide
  rcases family_descends (prefixWord ++ tailWord_103583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103715 : List Nat := [1, 1, 1, 4, 2, 3, 4, 5]
def baseStart_103715 : Nat := 118140960795 + 103715 * 2 ^ 59
def prefixEnd_103715 : Nat := 4983230072969 + 3 ^ 40 * 103715 * 2
def baseEnd_103715 : Nat := 7889725345358066412671

theorem tailTrace_103715 : CollatzResearch.WordTrace tailWord_103715 prefixEnd_103715 7889725345358066412671 := by
  unfold tailWord_103715
  simp only [CollatzResearch.WordTrace]
  refine ⟨3782796819265742956896599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2521864546177161971264399 3782796819265742956896599)
  ·
    refine ⟨5674195228898614435344899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3782796819265742956896599 5674195228898614435344899)
    ·
      refine ⟨8511292843347921653017349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5674195228898614435344899 8511292843347921653017349)
      ·
        refine ⟨1595867408127735309940753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8511292843347921653017349 1595867408127735309940753)
        ·
          refine ⟨1196900556095801482455565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1595867408127735309940753 1196900556095801482455565)
          ·
            refine ⟨448837708535925555920837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1196900556095801482455565 448837708535925555920837)
            ·
              refine ⟨84157070350486041735157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 448837708535925555920837 84157070350486041735157)
              ·
                refine ⟨7889725345358066412671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84157070350486041735157 7889725345358066412671)
                ·
                  rfl

theorem cell21_103715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 5].length) (baseStart_103715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103715 prefixEnd_103715 := by exact prefixLift 103715
  have htrace : WordTrace (prefixWord ++ tailWord_103715) baseStart_103715 baseEnd_103715 := by
    simpa [prefixWord, tailWord_103715, baseEnd_103715] using wordTrace_append hprefix tailTrace_103715
  have hstable : (prefixWord ++ tailWord_103715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103715).length < 2 ^ (prefixWord ++ tailWord_103715).sum := by decide
  have hdescent : baseEnd_103715 < baseStart_103715 := by decide
  rcases family_descends (prefixWord ++ tailWord_103715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103760 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 4]
def baseStart_103760 : Nat := 118140960795 + 103760 * 2 ^ 59
def prefixEnd_103760 : Nat := 4983230072969 + 3 ^ 40 * 103760 * 2
def baseEnd_103760 : Nat := 23679445649164120987921

theorem tailTrace_103760 : CollatzResearch.WordTrace tailWord_103760 prefixEnd_103760 23679445649164120987921 := by
  unfold tailWord_103760
  simp only [CollatzResearch.WordTrace]
  refine ⟨1892219052051357821142367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2522958736068477094856489 1892219052051357821142367)
  ·
    refine ⟨2838328578077036731713551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1892219052051357821142367 2838328578077036731713551)
    ·
      refine ⟨4257492867115555097570327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2838328578077036731713551 4257492867115555097570327)
      ·
        refine ⟨6386239300673332646355491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4257492867115555097570327 6386239300673332646355491)
        ·
          refine ⟨9579358951009998969533237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6386239300673332646355491 9579358951009998969533237)
          ·
            refine ⟨898064901657187403393741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9579358951009998969533237 898064901657187403393741)
            ·
              refine ⟨336774338121445276272653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 898064901657187403393741 336774338121445276272653)
              ·
                refine ⟨126290376795541978602245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336774338121445276272653 126290376795541978602245)
                ·
                  refine ⟨23679445649164120987921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126290376795541978602245 23679445649164120987921)
                  ·
                    rfl

theorem cell21_103760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_103760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103760 prefixEnd_103760 := by exact prefixLift 103760
  have htrace : WordTrace (prefixWord ++ tailWord_103760) baseStart_103760 baseEnd_103760 := by
    simpa [prefixWord, tailWord_103760, baseEnd_103760] using wordTrace_append hprefix tailTrace_103760
  have hstable : (prefixWord ++ tailWord_103760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103760).length < 2 ^ (prefixWord ++ tailWord_103760).sum := by decide
  have hdescent : baseEnd_103760 < baseStart_103760 := by decide
  rcases family_descends (prefixWord ++ tailWord_103760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103797 : List Nat := [1, 3, 4, 1, 3, 2, 2, 2, 3]
def baseStart_103797 : Nat := 118140960795 + 103797 * 2 ^ 59
def prefixEnd_103797 : Nat := 4983230072969 + 3 ^ 40 * 103797 * 2
def baseEnd_103797 : Nat := 23687889553260278871179

theorem tailTrace_103797 : CollatzResearch.WordTrace tailWord_103797 prefixEnd_103797 23687889553260278871179 := by
  unfold tailWord_103797
  simp only [CollatzResearch.WordTrace]
  refine ⟨3785787604968670961381645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2523858403312447307587763 3785787604968670961381645)
  ·
    refine ⟨1419670351863251610518117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3785787604968670961381645 1419670351863251610518117)
    ·
      refine ⟨266188190974359676972147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1419670351863251610518117 266188190974359676972147)
      ·
        refine ⟨399282286461539515458221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266188190974359676972147 399282286461539515458221)
        ·
          refine ⟨149730857423077318296833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399282286461539515458221 149730857423077318296833)
          ·
            refine ⟨112298143067307988722625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149730857423077318296833 112298143067307988722625)
            ·
              refine ⟨84223607300480991541969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112298143067307988722625 84223607300480991541969)
              ·
                refine ⟨63167705475360743656477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84223607300480991541969 63167705475360743656477)
                ·
                  refine ⟨23687889553260278871179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63167705475360743656477 23687889553260278871179)
                  ·
                    rfl

theorem cell21_103797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_103797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103797 prefixEnd_103797 := by exact prefixLift 103797
  have htrace : WordTrace (prefixWord ++ tailWord_103797) baseStart_103797 baseEnd_103797 := by
    simpa [prefixWord, tailWord_103797, baseEnd_103797] using wordTrace_append hprefix tailTrace_103797
  have hstable : (prefixWord ++ tailWord_103797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103797).length < 2 ^ (prefixWord ++ tailWord_103797).sum := by decide
  have hdescent : baseEnd_103797 < baseStart_103797 := by decide
  rcases family_descends (prefixWord ++ tailWord_103797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103805 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 5]
def baseStart_103805 : Nat := 118140960795 + 103805 * 2 ^ 59
def prefixEnd_103805 : Nat := 4983230072969 + 3 ^ 40 * 103805 * 2
def baseEnd_103805 : Nat := 23689715262254042737829

theorem tailTrace_103805 : CollatzResearch.WordTrace tailWord_103805 prefixEnd_103805 23689715262254042737829 := by
  unfold tailWord_103805
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786079388939688327672869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2524052925959792218448579 3786079388939688327672869)
  ·
    refine ⟨709889885426191561438663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3786079388939688327672869 709889885426191561438663)
    ·
      refine ⟨1064834828139287342157995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 709889885426191561438663 1064834828139287342157995)
      ·
        refine ⟨1597252242208931013236993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1064834828139287342157995 1597252242208931013236993)
        ·
          refine ⟨1197939181656698259927745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1597252242208931013236993 1197939181656698259927745)
          ·
            refine ⟨898454386242523694945809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197939181656698259927745 898454386242523694945809)
            ·
              refine ⟨673840789681892771209357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 898454386242523694945809 673840789681892771209357)
              ·
                refine ⟨252690296130709789203509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673840789681892771209357 252690296130709789203509)
                ·
                  refine ⟨23689715262254042737829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252690296130709789203509 23689715262254042737829)
                  ·
                    rfl

theorem cell21_103805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_103805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103805 prefixEnd_103805 := by exact prefixLift 103805
  have htrace : WordTrace (prefixWord ++ tailWord_103805) baseStart_103805 baseEnd_103805 := by
    simpa [prefixWord, tailWord_103805, baseEnd_103805] using wordTrace_append hprefix tailTrace_103805
  have hstable : (prefixWord ++ tailWord_103805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103805).length < 2 ^ (prefixWord ++ tailWord_103805).sum := by decide
  have hdescent : baseEnd_103805 < baseStart_103805 := by decide
  rcases family_descends (prefixWord ++ tailWord_103805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103839 : List Nat := [1, 1, 2, 5, 1, 3, 2, 3, 3]
def baseStart_103839 : Nat := 118140960795 + 103839 * 2 ^ 59
def prefixEnd_103839 : Nat := 4983230072969 + 3 ^ 40 * 103839 * 2
def baseEnd_103839 : Nat := 23697474525477539171093

theorem tailTrace_103839 : CollatzResearch.WordTrace tailWord_103839 prefixEnd_103839 23697474525477539171093 := by
  unfold tailWord_103839
  simp only [CollatzResearch.WordTrace]
  refine ⟨3787319470816512134410571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2524879647211008089607047 3787319470816512134410571)
  ·
    refine ⟨5680979206224768201615857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3787319470816512134410571 5680979206224768201615857)
    ·
      refine ⟨4260734404668576151211893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5680979206224768201615857 4260734404668576151211893)
      ·
        refine ⟨399443850437679014176115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4260734404668576151211893 399443850437679014176115)
        ·
          refine ⟨599165775656518521264173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399443850437679014176115 599165775656518521264173)
          ·
            refine ⟨224687165871194445474065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 599165775656518521264173 224687165871194445474065)
            ·
              refine ⟨168515374403395834105549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224687165871194445474065 168515374403395834105549)
              ·
                refine ⟨63193265401273437789581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168515374403395834105549 63193265401273437789581)
                ·
                  refine ⟨23697474525477539171093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63193265401273437789581 23697474525477539171093)
                  ·
                    rfl

theorem cell21_103839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 3].length) (baseStart_103839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103839 prefixEnd_103839 := by exact prefixLift 103839
  have htrace : WordTrace (prefixWord ++ tailWord_103839) baseStart_103839 baseEnd_103839 := by
    simpa [prefixWord, tailWord_103839, baseEnd_103839] using wordTrace_append hprefix tailTrace_103839
  have hstable : (prefixWord ++ tailWord_103839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103839).length < 2 ^ (prefixWord ++ tailWord_103839).sum := by decide
  have hdescent : baseEnd_103839 < baseStart_103839 := by decide
  rcases family_descends (prefixWord ++ tailWord_103839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103853 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 6]
def baseStart_103853 : Nat := 118140960795 + 103853 * 2 ^ 59
def prefixEnd_103853 : Nat := 4983230072969 + 3 ^ 40 * 103853 * 2
def baseEnd_103853 : Nat := 23700669516216625937731

theorem tailTrace_103853 : CollatzResearch.WordTrace tailWord_103853 prefixEnd_103853 23700669516216625937731 := by
  unfold tailWord_103853
  simp only [CollatzResearch.WordTrace]
  refine ⟨3787830092765792525420213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2525220061843861683613475 3787830092765792525420213)
  ·
    refine ⟨355109071196793049258145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3787830092765792525420213 355109071196793049258145)
    ·
      refine ⟨266331803397594786943609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355109071196793049258145 266331803397594786943609)
      ·
        refine ⟨199748852548196090207707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266331803397594786943609 199748852548196090207707)
        ·
          refine ⟨299623278822294135311561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199748852548196090207707 299623278822294135311561)
          ·
            refine ⟨224717459116720601483671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299623278822294135311561 224717459116720601483671)
            ·
              refine ⟨337076188675080902225507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224717459116720601483671 337076188675080902225507)
              ·
                refine ⟨505614283012621353338261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337076188675080902225507 505614283012621353338261)
                ·
                  refine ⟨23700669516216625937731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 505614283012621353338261 23700669516216625937731)
                  ·
                    rfl

theorem cell21_103853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_103853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103853 prefixEnd_103853 := by exact prefixLift 103853
  have htrace : WordTrace (prefixWord ++ tailWord_103853) baseStart_103853 baseEnd_103853 := by
    simpa [prefixWord, tailWord_103853, baseEnd_103853] using wordTrace_append hprefix tailTrace_103853
  have hstable : (prefixWord ++ tailWord_103853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103853).length < 2 ^ (prefixWord ++ tailWord_103853).sum := by decide
  have hdescent : baseEnd_103853 < baseStart_103853 := by decide
  rcases family_descends (prefixWord ++ tailWord_103853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103884 : List Nat := [2, 2, 1, 4, 2, 3, 2, 5]
def baseStart_103884 : Nat := 118140960795 + 103884 * 2 ^ 59
def prefixEnd_103884 : Nat := 4983230072969 + 3 ^ 40 * 103884 * 2
def baseEnd_103884 : Nat := 7902581379522486973667

theorem tailTrace_103884 : CollatzResearch.WordTrace tailWord_103884 prefixEnd_103884 7902581379522486973667 := by
  unfold tailWord_103884
  simp only [CollatzResearch.WordTrace]
  refine ⟨1894480377826742409899353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2525973837102323213199137 1894480377826742409899353)
  ·
    refine ⟨1420860283370056807424515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1894480377826742409899353 1420860283370056807424515)
    ·
      refine ⟨2131290425055085211136773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1420860283370056807424515 2131290425055085211136773)
      ·
        refine ⟨399616954697828477088145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2131290425055085211136773 399616954697828477088145)
        ·
          refine ⟨299712716023371357816109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399616954697828477088145 299712716023371357816109)
          ·
            refine ⟨112392268508764259181041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299712716023371357816109 112392268508764259181041)
            ·
              refine ⟨84294201381573194385781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112392268508764259181041 84294201381573194385781)
              ·
                refine ⟨7902581379522486973667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84294201381573194385781 7902581379522486973667)
                ·
                  rfl

theorem cell21_103884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_103884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103884 prefixEnd_103884 := by exact prefixLift 103884
  have htrace : WordTrace (prefixWord ++ tailWord_103884) baseStart_103884 baseEnd_103884 := by
    simpa [prefixWord, tailWord_103884, baseEnd_103884] using wordTrace_append hprefix tailTrace_103884
  have hstable : (prefixWord ++ tailWord_103884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103884).length < 2 ^ (prefixWord ++ tailWord_103884).sum := by decide
  have hdescent : baseEnd_103884 < baseStart_103884 := by decide
  rcases family_descends (prefixWord ++ tailWord_103884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103912 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 4]
def baseStart_103912 : Nat := 118140960795 + 103912 * 2 ^ 59
def prefixEnd_103912 : Nat := 4983230072969 + 3 ^ 40 * 103912 * 2
def baseEnd_103912 : Nat := 23714134120045634454277

theorem tailTrace_103912 : CollatzResearch.WordTrace tailWord_103912 prefixEnd_103912 23714134120045634454277 := by
  unfold tailWord_103912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1894990999776022800908995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2526654666368030401211993 1894990999776022800908995)
  ·
    refine ⟨2842486499664034201363493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1894990999776022800908995 2842486499664034201363493)
    ·
      refine ⟨532966218687006412755655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2842486499664034201363493 532966218687006412755655)
      ·
        refine ⟨799449328030509619133483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532966218687006412755655 799449328030509619133483)
        ·
          refine ⟨1199173992045764428700225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799449328030509619133483 1199173992045764428700225)
          ·
            refine ⟨899380494034323321525169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1199173992045764428700225 899380494034323321525169)
            ·
              refine ⟨674535370525742491143877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899380494034323321525169 674535370525742491143877)
              ·
                refine ⟨126475381973576717089477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674535370525742491143877 126475381973576717089477)
                ·
                  refine ⟨23714134120045634454277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126475381973576717089477 23714134120045634454277)
                  ·
                    rfl

theorem cell21_103912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_103912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103912 prefixEnd_103912 := by exact prefixLift 103912
  have htrace : WordTrace (prefixWord ++ tailWord_103912) baseStart_103912 baseEnd_103912 := by
    simpa [prefixWord, tailWord_103912, baseEnd_103912] using wordTrace_append hprefix tailTrace_103912
  have hstable : (prefixWord ++ tailWord_103912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103912).length < 2 ^ (prefixWord ++ tailWord_103912).sum := by decide
  have hdescent : baseEnd_103912 < baseStart_103912 := by decide
  rcases family_descends (prefixWord ++ tailWord_103912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103966 : List Nat := [4, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_103966 : Nat := 118140960795 + 103966 * 2 ^ 59
def prefixEnd_103966 : Nat := 4983230072969 + 3 ^ 40 * 103966 * 2
def baseEnd_103966 : Nat := 23726457655753540554167

theorem tailTrace_103966 : CollatzResearch.WordTrace tailWord_103966 prefixEnd_103966 23726457655753540554167 := by
  unfold tailWord_103966
  simp only [CollatzResearch.WordTrace]
  refine ⟨473993942669551603035469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2527967694237608549522501 473993942669551603035469)
  ·
    refine ⟨177747728501081851138301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 473993942669551603035469 177747728501081851138301)
    ·
      refine ⟨66655398187905694176863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177747728501081851138301 66655398187905694176863)
      ·
        refine ⟨99983097281858541265295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66655398187905694176863 99983097281858541265295)
        ·
          refine ⟨149974645922787811897943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99983097281858541265295 149974645922787811897943)
          ·
            refine ⟨224961968884181717846915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149974645922787811897943 224961968884181717846915)
            ·
              refine ⟨337442953326272576770373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224961968884181717846915 337442953326272576770373)
              ·
                refine ⟨63270553748676108144445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337442953326272576770373 63270553748676108144445)
                ·
                  refine ⟨23726457655753540554167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63270553748676108144445 23726457655753540554167)
                  ·
                    rfl

theorem cell21_103966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_103966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_103966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_103966 prefixEnd_103966 := by exact prefixLift 103966
  have htrace : WordTrace (prefixWord ++ tailWord_103966) baseStart_103966 baseEnd_103966 := by
    simpa [prefixWord, tailWord_103966, baseEnd_103966] using wordTrace_append hprefix tailTrace_103966
  have hstable : (prefixWord ++ tailWord_103966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103966).length < 2 ^ (prefixWord ++ tailWord_103966).sum := by decide
  have hdescent : baseEnd_103966 < baseStart_103966 := by decide
  rcases family_descends (prefixWord ++ tailWord_103966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104016 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_104016 : Nat := 118140960795 + 104016 * 2 ^ 59
def prefixEnd_104016 : Nat := 4983230072969 + 3 ^ 40 * 104016 * 2
def baseEnd_104016 : Nat := 23737868336964564720731

theorem tailTrace_104016 : CollatzResearch.WordTrace tailWord_104016 prefixEnd_104016 23737868336964564720731 := by
  unfold tailWord_104016
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896887595587635681801951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2529183460783514242402601 1896887595587635681801951)
  ·
    refine ⟨2845331393381453522702927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1896887595587635681801951 2845331393381453522702927)
    ·
      refine ⟨4267997090072180284054391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2845331393381453522702927 4267997090072180284054391)
      ·
        refine ⟨6401995635108270426081587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267997090072180284054391 6401995635108270426081587)
        ·
          refine ⟨9602993452662405639122381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401995635108270426081587 9602993452662405639122381)
          ·
            refine ⟨3601122544748402114670893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9602993452662405639122381 3601122544748402114670893)
            ·
              refine ⟨1350420954280650793001585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3601122544748402114670893 1350420954280650793001585)
              ·
                refine ⟨1012815715710488094751189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1350420954280650793001585 1012815715710488094751189)
                ·
                  refine ⟨23737868336964564720731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1012815715710488094751189 23737868336964564720731)
                  ·
                    rfl

theorem cell21_104016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_104016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104016 prefixEnd_104016 := by exact prefixLift 104016
  have htrace : WordTrace (prefixWord ++ tailWord_104016) baseStart_104016 baseEnd_104016 := by
    simpa [prefixWord, tailWord_104016, baseEnd_104016] using wordTrace_append hprefix tailTrace_104016
  have hstable : (prefixWord ++ tailWord_104016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104016).length < 2 ^ (prefixWord ++ tailWord_104016).sum := by decide
  have hdescent : baseEnd_104016 < baseStart_104016 := by decide
  rcases family_descends (prefixWord ++ tailWord_104016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104033 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 5]
def baseStart_104033 : Nat := 118140960795 + 104033 * 2 ^ 59
def prefixEnd_104033 : Nat := 4983230072969 + 3 ^ 40 * 104033 * 2
def baseEnd_104033 : Nat := 23741747968576312937363

theorem tailTrace_104033 : CollatzResearch.WordTrace tailWord_104033 prefixEnd_104033 23741747968576312937363 := by
  unfold tailWord_104033
  simp only [CollatzResearch.WordTrace]
  refine ⟨3794395232113683266972753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2529596821409122177981835 3794395232113683266972753)
  ·
    refine ⟨2845796424085262450229565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3794395232113683266972753 2845796424085262450229565)
    ·
      refine ⟨1067173659031973418836087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2845796424085262450229565 1067173659031973418836087)
      ·
        refine ⟨1600760488547960128254131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1067173659031973418836087 1600760488547960128254131)
        ·
          refine ⟨2401140732821940192381197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600760488547960128254131 2401140732821940192381197)
          ·
            refine ⟨900427774808227572142949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2401140732821940192381197 900427774808227572142949)
            ·
              refine ⟨168830207776542669776803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 900427774808227572142949 168830207776542669776803)
              ·
                refine ⟨253245311664814004665205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168830207776542669776803 253245311664814004665205)
                ·
                  refine ⟨23741747968576312937363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 253245311664814004665205 23741747968576312937363)
                  ·
                    rfl

theorem cell21_104033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_104033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104033 prefixEnd_104033 := by exact prefixLift 104033
  have htrace : WordTrace (prefixWord ++ tailWord_104033) baseStart_104033 baseEnd_104033 := by
    simpa [prefixWord, tailWord_104033, baseEnd_104033] using wordTrace_append hprefix tailTrace_104033
  have hstable : (prefixWord ++ tailWord_104033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104033).length < 2 ^ (prefixWord ++ tailWord_104033).sum := by decide
  have hdescent : baseEnd_104033 < baseStart_104033 := by decide
  rcases family_descends (prefixWord ++ tailWord_104033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104078 : List Nat := [4, 1, 1, 3, 1, 2, 9]
def baseStart_104078 : Nat := 118140960795 + 104078 * 2 ^ 59
def prefixEnd_104078 : Nat := 4983230072969 + 3 ^ 40 * 104078 * 2
def baseEnd_104078 : Nat := 2639113064629581631919

theorem tailTrace_104078 : CollatzResearch.WordTrace tailWord_104078 prefixEnd_104078 2639113064629581631919 := by
  unfold tailWord_104078
  simp only [CollatzResearch.WordTrace]
  refine ⟨474504564618831994045111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2530691011300437301573925 474504564618831994045111)
  ·
    refine ⟨711756846928247991067667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 474504564618831994045111 711756846928247991067667)
    ·
      refine ⟨1067635270392371986601501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 711756846928247991067667 1067635270392371986601501)
      ·
        refine ⟨400363226397139494975563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1067635270392371986601501 400363226397139494975563)
        ·
          refine ⟨600544839595709242463345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400363226397139494975563 600544839595709242463345)
          ·
            refine ⟨450408629696781931847509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600544839595709242463345 450408629696781931847509)
            ·
              refine ⟨2639113064629581631919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 450408629696781931847509 2639113064629581631919)
              ·
                rfl

theorem cell21_104078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 9].length) (baseStart_104078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104078 prefixEnd_104078 := by exact prefixLift 104078
  have htrace : WordTrace (prefixWord ++ tailWord_104078) baseStart_104078 baseEnd_104078 := by
    simpa [prefixWord, tailWord_104078, baseEnd_104078] using wordTrace_append hprefix tailTrace_104078
  have hstable : (prefixWord ++ tailWord_104078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104078).length < 2 ^ (prefixWord ++ tailWord_104078).sum := by decide
  have hdescent : baseEnd_104078 < baseStart_104078 := by decide
  rcases family_descends (prefixWord ++ tailWord_104078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104084 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 5]
def baseStart_104084 : Nat := 118140960795 + 104084 * 2 ^ 59
def prefixEnd_104084 : Nat := 4983230072969 + 3 ^ 40 * 104084 * 2
def baseEnd_104084 : Nat := 23753386863411557587259

theorem tailTrace_104084 : CollatzResearch.WordTrace tailWord_104084 prefixEnd_104084 23753386863411557587259 := by
  unfold tailWord_104084
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898127677464459488539653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2530836903285945984719537 1898127677464459488539653)
  ·
    refine ⟨355898939524586154101185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1898127677464459488539653 355898939524586154101185)
    ·
      refine ⟨266924204643439615575889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355898939524586154101185 266924204643439615575889)
      ·
        refine ⟨200193153482579711681917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266924204643439615575889 200193153482579711681917)
        ·
          refine ⟨75072432555967391880719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200193153482579711681917 75072432555967391880719)
          ·
            refine ⟨112608648833951087821079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75072432555967391880719 112608648833951087821079)
            ·
              refine ⟨168912973250926631731619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112608648833951087821079 168912973250926631731619)
              ·
                refine ⟨253369459876389947597429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168912973250926631731619 253369459876389947597429)
                ·
                  refine ⟨23753386863411557587259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 253369459876389947597429 23753386863411557587259)
                  ·
                    rfl

theorem cell21_104084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_104084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104084 prefixEnd_104084 := by exact prefixLift 104084
  have htrace : WordTrace (prefixWord ++ tailWord_104084) baseStart_104084 baseEnd_104084 := by
    simpa [prefixWord, tailWord_104084, baseEnd_104084] using wordTrace_append hprefix tailTrace_104084
  have hstable : (prefixWord ++ tailWord_104084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104084).length < 2 ^ (prefixWord ++ tailWord_104084).sum := by decide
  have hdescent : baseEnd_104084 < baseStart_104084 := by decide
  rcases family_descends (prefixWord ++ tailWord_104084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104098 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_104098 : Nat := 118140960795 + 104098 * 2 ^ 59
def prefixEnd_104098 : Nat := 4983230072969 + 3 ^ 40 * 104098 * 2
def baseEnd_104098 : Nat := 23756581854150644353897

theorem tailTrace_104098 : CollatzResearch.WordTrace tailWord_104098 prefixEnd_104098 23756581854150644353897 := by
  unfold tailWord_104098
  simp only [CollatzResearch.WordTrace]
  refine ⟨949191494219549842022237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2531177317918799578725965 949191494219549842022237)
  ·
    refine ⟨355946810332331190758339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 949191494219549842022237 355946810332331190758339)
    ·
      refine ⟨533920215498496786137509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355946810332331190758339 533920215498496786137509)
      ·
        refine ⟨100110040405968147400783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 533920215498496786137509 100110040405968147400783)
        ·
          refine ⟨150165060608952221101175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100110040405968147400783 150165060608952221101175)
          ·
            refine ⟨225247590913428331651763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150165060608952221101175 225247590913428331651763)
            ·
              refine ⟨337871386370142497477645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225247590913428331651763 337871386370142497477645)
              ·
                refine ⟨126701769888803436554117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337871386370142497477645 126701769888803436554117)
                ·
                  refine ⟨23756581854150644353897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126701769888803436554117 23756581854150644353897)
                  ·
                    rfl

theorem cell21_104098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_104098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104098 prefixEnd_104098 := by exact prefixLift 104098
  have htrace : WordTrace (prefixWord ++ tailWord_104098) baseStart_104098 baseEnd_104098 := by
    simpa [prefixWord, tailWord_104098, baseEnd_104098] using wordTrace_append hprefix tailTrace_104098
  have hstable : (prefixWord ++ tailWord_104098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104098).length < 2 ^ (prefixWord ++ tailWord_104098).sum := by decide
  have hdescent : baseEnd_104098 < baseStart_104098 := by decide
  rcases family_descends (prefixWord ++ tailWord_104098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104109 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 7]
def baseStart_104109 : Nat := 118140960795 + 104109 * 2 ^ 59
def prefixEnd_104109 : Nat := 4983230072969 + 3 ^ 40 * 104109 * 2
def baseEnd_104109 : Nat := 23759092204017069670541

theorem tailTrace_104109 : CollatzResearch.WordTrace tailWord_104109 prefixEnd_104109 23759092204017069670541 := by
  unfold tailWord_104109
  simp only [CollatzResearch.WordTrace]
  refine ⟨3797167179838348246739381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2531444786558898831159587 3797167179838348246739381)
  ·
    refine ⟨355984423109845148131817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3797167179838348246739381 355984423109845148131817)
    ·
      refine ⟨266988317332383861098863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355984423109845148131817 266988317332383861098863)
      ·
        refine ⟨400482475998575791648295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266988317332383861098863 400482475998575791648295)
        ·
          refine ⟨600723713997863687472443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400482475998575791648295 600723713997863687472443)
          ·
            refine ⟨901085570996795531208665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600723713997863687472443 901085570996795531208665)
            ·
              refine ⟨675814178247596648406499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901085570996795531208665 675814178247596648406499)
              ·
                refine ⟨1013721267371394972609749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675814178247596648406499 1013721267371394972609749)
                ·
                  refine ⟨23759092204017069670541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1013721267371394972609749 23759092204017069670541)
                  ·
                    rfl

theorem cell21_104109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_104109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104109 prefixEnd_104109 := by exact prefixLift 104109
  have htrace : WordTrace (prefixWord ++ tailWord_104109) baseStart_104109 baseEnd_104109 := by
    simpa [prefixWord, tailWord_104109, baseEnd_104109] using wordTrace_append hprefix tailTrace_104109
  have hstable : (prefixWord ++ tailWord_104109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104109).length < 2 ^ (prefixWord ++ tailWord_104109).sum := by decide
  have hdescent : baseEnd_104109 < baseStart_104109 := by decide
  rcases family_descends (prefixWord ++ tailWord_104109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104154 : List Nat := [3, 1, 1, 2, 2, 3, 3, 6]
def baseStart_104154 : Nat := 118140960795 + 104154 * 2 ^ 59
def prefixEnd_104154 : Nat := 4983230072969 + 3 ^ 40 * 104154 * 2
def baseEnd_104154 : Nat := 7923120605702330473483

theorem tailTrace_104154 : CollatzResearch.WordTrace tailWord_104154 prefixEnd_104154 7923120605702330473483 := by
  unfold tailWord_104154
  simp only [CollatzResearch.WordTrace]
  refine ⟨949702116168830233031879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2532538976450213954751677 949702116168830233031879)
  ·
    refine ⟨1424553174253245349547819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 949702116168830233031879 1424553174253245349547819)
    ·
      refine ⟨2136829761379868024321729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1424553174253245349547819 2136829761379868024321729)
      ·
        refine ⟨1602622321034901018241297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2136829761379868024321729 1602622321034901018241297)
        ·
          refine ⟨1201966740776175763680973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1602622321034901018241297 1201966740776175763680973)
          ·
            refine ⟨450737527791065911380365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1201966740776175763680973 450737527791065911380365)
            ·
              refine ⟨169026572921649716767637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 450737527791065911380365 169026572921649716767637)
              ·
                refine ⟨7923120605702330473483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 169026572921649716767637 7923120605702330473483)
                ·
                  rfl

theorem cell21_104154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_104154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104154 prefixEnd_104154 := by exact prefixLift 104154
  have htrace : WordTrace (prefixWord ++ tailWord_104154) baseStart_104154 baseEnd_104154 := by
    simpa [prefixWord, tailWord_104154, baseEnd_104154] using wordTrace_append hprefix tailTrace_104154
  have hstable : (prefixWord ++ tailWord_104154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104154).length < 2 ^ (prefixWord ++ tailWord_104154).sum := by decide
  have hdescent : baseEnd_104154 < baseStart_104154 := by decide
  rcases family_descends (prefixWord ++ tailWord_104154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104202 : List Nat := [3, 1, 2, 2, 1, 3, 2, 4, 3]
def baseStart_104202 : Nat := 118140960795 + 104202 * 2 ^ 59
def prefixEnd_104202 : Nat := 4983230072969 + 3 ^ 40 * 104202 * 2
def baseEnd_104202 : Nat := 23780316071069574620351

theorem tailTrace_104202 : CollatzResearch.WordTrace tailWord_104202 prefixEnd_104202 23780316071069574620351 := by
  unfold tailWord_104202
  simp only [CollatzResearch.WordTrace]
  refine ⟨950139792125356282468715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2533706112334283419916573 950139792125356282468715)
  ·
    refine ⟨1425209688188034423703073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 950139792125356282468715 1425209688188034423703073)
    ·
      refine ⟨1068907266141025817777305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1425209688188034423703073 1068907266141025817777305)
      ·
        refine ⟨801680449605769363332979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1068907266141025817777305 801680449605769363332979)
        ·
          refine ⟨1202520674408654044999469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801680449605769363332979 1202520674408654044999469)
          ·
            refine ⟨450945252903245266874801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1202520674408654044999469 450945252903245266874801)
            ·
              refine ⟨338208939677433950156101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450945252903245266874801 338208939677433950156101)
              ·
                refine ⟨63414176189518865654269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 338208939677433950156101 63414176189518865654269)
                ·
                  refine ⟨23780316071069574620351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63414176189518865654269 23780316071069574620351)
                  ·
                    rfl

theorem cell21_104202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_104202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104202 prefixEnd_104202 := by exact prefixLift 104202
  have htrace : WordTrace (prefixWord ++ tailWord_104202) baseStart_104202 baseEnd_104202 := by
    simpa [prefixWord, tailWord_104202, baseEnd_104202] using wordTrace_append hprefix tailTrace_104202
  have hstable : (prefixWord ++ tailWord_104202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104202).length < 2 ^ (prefixWord ++ tailWord_104202).sum := by decide
  have hdescent : baseEnd_104202 < baseStart_104202 := by decide
  rcases family_descends (prefixWord ++ tailWord_104202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104222 : List Nat := [4, 3, 2, 2, 1, 2, 2, 5]
def baseStart_104222 : Nat := 118140960795 + 104222 * 2 ^ 59
def prefixEnd_104222 : Nat := 4983230072969 + 3 ^ 40 * 104222 * 2
def baseEnd_104222 : Nat := 7928293447851328095659

theorem tailTrace_104222 : CollatzResearch.WordTrace tailWord_104222 prefixEnd_104222 7928293447851328095659 := by
  unfold tailWord_104222
  simp only [CollatzResearch.WordTrace]
  refine ⟨475161078553621068200365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2534192418952645697068613 475161078553621068200365)
  ·
    refine ⟨178185404457607900575137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 475161078553621068200365 178185404457607900575137)
    ·
      refine ⟨133639053343205925431353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178185404457607900575137 133639053343205925431353)
      ·
        refine ⟨100229290007404444073515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133639053343205925431353 100229290007404444073515)
        ·
          refine ⟨150343935011106666110273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100229290007404444073515 150343935011106666110273)
          ·
            refine ⟨112757951258329999582705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150343935011106666110273 112757951258329999582705)
            ·
              refine ⟨84568463443747499687029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112757951258329999582705 84568463443747499687029)
              ·
                refine ⟨7928293447851328095659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84568463443747499687029 7928293447851328095659)
                ·
                  rfl

theorem cell21_104222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_104222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104222 prefixEnd_104222 := by exact prefixLift 104222
  have htrace : WordTrace (prefixWord ++ tailWord_104222) baseStart_104222 baseEnd_104222 := by
    simpa [prefixWord, tailWord_104222, baseEnd_104222] using wordTrace_append hprefix tailTrace_104222
  have hstable : (prefixWord ++ tailWord_104222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104222).length < 2 ^ (prefixWord ++ tailWord_104222).sum := by decide
  have hdescent : baseEnd_104222 < baseStart_104222 := by decide
  rcases family_descends (prefixWord ++ tailWord_104222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104289 : List Nat := [1, 2, 3, 1, 1, 1, 3, 9]
def baseStart_104289 : Nat := 118140960795 + 104289 * 2 ^ 59
def prefixEnd_104289 : Nat := 4983230072969 + 3 ^ 40 * 104289 * 2
def baseEnd_104289 : Nat := 7933390218792252223391

theorem tailTrace_104289 : CollatzResearch.WordTrace tailWord_104289 prefixEnd_104289 7933390218792252223391 := by
  unfold tailWord_104289
  simp only [CollatzResearch.WordTrace]
  refine ⟨3803732319186238988291921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2535821546124159325527947 3803732319186238988291921)
  ·
    refine ⟨2852799239389679241218941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3803732319186238988291921 2852799239389679241218941)
    ·
      refine ⟨1069799714771129715457103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2852799239389679241218941 1069799714771129715457103)
      ·
        refine ⟨1604699572156694573185655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069799714771129715457103 1604699572156694573185655)
        ·
          refine ⟨2407049358235041859778483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604699572156694573185655 2407049358235041859778483)
          ·
            refine ⟨3610574037352562789667725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407049358235041859778483 3610574037352562789667725)
            ·
              refine ⟨1353965264007211046125397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3610574037352562789667725 1353965264007211046125397)
              ·
                refine ⟨7933390218792252223391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1353965264007211046125397 7933390218792252223391)
                ·
                  rfl

theorem cell21_104289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 9].length) (baseStart_104289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104289 prefixEnd_104289 := by exact prefixLift 104289
  have htrace : WordTrace (prefixWord ++ tailWord_104289) baseStart_104289 baseEnd_104289 := by
    simpa [prefixWord, tailWord_104289, baseEnd_104289] using wordTrace_append hprefix tailTrace_104289
  have hstable : (prefixWord ++ tailWord_104289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104289).length < 2 ^ (prefixWord ++ tailWord_104289).sum := by decide
  have hdescent : baseEnd_104289 < baseStart_104289 := by decide
  rcases family_descends (prefixWord ++ tailWord_104289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104320 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_104320 : Nat := 118140960795 + 104320 * 2 ^ 59
def prefixEnd_104320 : Nat := 4983230072969 + 3 ^ 40 * 104320 * 2
def baseEnd_104320 : Nat := 23807245278727591653443

theorem tailTrace_104320 : CollatzResearch.WordTrace tailWord_104320 prefixEnd_104320 23807245278727591653443 := by
  unfold tailWord_104320
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902431491036965641335207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2536575321382620855113609 1902431491036965641335207)
  ·
    refine ⟨2853647236555448462002811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1902431491036965641335207 2853647236555448462002811)
    ·
      refine ⟨4280470854833172693004217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2853647236555448462002811 4280470854833172693004217)
      ·
        refine ⟨3210353141124879519753163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4280470854833172693004217 3210353141124879519753163)
        ·
          refine ⟨4815529711687319279629745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210353141124879519753163 4815529711687319279629745)
          ·
            refine ⟨3611647283765489459722309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4815529711687319279629745 3611647283765489459722309)
            ·
              refine ⟨677183865706029273697933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3611647283765489459722309 677183865706029273697933)
              ·
                refine ⟨253943949639760977636725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 677183865706029273697933 253943949639760977636725)
                ·
                  refine ⟨23807245278727591653443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 253943949639760977636725 23807245278727591653443)
                  ·
                    rfl

theorem cell21_104320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_104320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104320 prefixEnd_104320 := by exact prefixLift 104320
  have htrace : WordTrace (prefixWord ++ tailWord_104320) baseStart_104320 baseEnd_104320 := by
    simpa [prefixWord, tailWord_104320, baseEnd_104320] using wordTrace_append hprefix tailTrace_104320
  have hstable : (prefixWord ++ tailWord_104320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104320).length < 2 ^ (prefixWord ++ tailWord_104320).sum := by decide
  have hdescent : baseEnd_104320 < baseStart_104320 := by decide
  rcases family_descends (prefixWord ++ tailWord_104320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104430 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_104430 : Nat := 118140960795 + 104430 * 2 ^ 59
def prefixEnd_104430 : Nat := 4983230072969 + 3 ^ 40 * 104430 * 2
def baseEnd_104430 : Nat := 23832348777391844819885

theorem tailTrace_104430 : CollatzResearch.WordTrace tailWord_104430 prefixEnd_104430 23832348777391844819885 := by
  unfold tailWord_104430
  simp only [CollatzResearch.WordTrace]
  refine ⟨476109376459427508646843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2539250007783613379449829 476109376459427508646843)
  ·
    refine ⟨714164064689141262970265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 476109376459427508646843 714164064689141262970265)
    ·
      refine ⟨535623048516855947227699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 714164064689141262970265 535623048516855947227699)
      ·
        refine ⟨803434572775283920841549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535623048516855947227699 803434572775283920841549)
        ·
          refine ⟨301287964790731470315581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 803434572775283920841549 301287964790731470315581)
          ·
            refine ⟨112982986796524301368343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301287964790731470315581 112982986796524301368343)
            ·
              refine ⟨169474480194786452052515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112982986796524301368343 169474480194786452052515)
              ·
                refine ⟨254211720292179678078773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169474480194786452052515 254211720292179678078773)
                ·
                  refine ⟨23832348777391844819885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 254211720292179678078773 23832348777391844819885)
                  ·
                    rfl

theorem cell21_104430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_104430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104430 prefixEnd_104430 := by exact prefixLift 104430
  have htrace : WordTrace (prefixWord ++ tailWord_104430) baseStart_104430 baseEnd_104430 := by
    simpa [prefixWord, tailWord_104430, baseEnd_104430] using wordTrace_append hprefix tailTrace_104430
  have hstable : (prefixWord ++ tailWord_104430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104430).length < 2 ^ (prefixWord ++ tailWord_104430).sum := by decide
  have hdescent : baseEnd_104430 < baseStart_104430 := by decide
  rcases family_descends (prefixWord ++ tailWord_104430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104441 : List Nat := [1, 2, 1, 3, 1, 4, 1, 8]
def baseStart_104441 : Nat := 118140960795 + 104441 * 2 ^ 59
def prefixEnd_104441 : Nat := 4983230072969 + 3 ^ 40 * 104441 * 2
def baseEnd_104441 : Nat := 7944953042419423378843

theorem tailTrace_104441 : CollatzResearch.WordTrace tailWord_104441 prefixEnd_104441 7944953042419423378843 := by
  unfold tailWord_104441
  simp only [CollatzResearch.WordTrace]
  refine ⟨3809276214635568947825177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2539517476423712631883451 3809276214635568947825177)
  ·
    refine ⟨2856957160976676710868883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3809276214635568947825177 2856957160976676710868883)
    ·
      refine ⟨4285435741465015066303325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2856957160976676710868883 4285435741465015066303325)
      ·
        refine ⟨1607038403049380649863747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4285435741465015066303325 1607038403049380649863747)
        ·
          refine ⟨2410557604574070974795621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1607038403049380649863747 2410557604574070974795621)
          ·
            refine ⟨451979550857638307774179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2410557604574070974795621 451979550857638307774179)
            ·
              refine ⟨677969326286457461661269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451979550857638307774179 677969326286457461661269)
              ·
                refine ⟨7944953042419423378843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 677969326286457461661269 7944953042419423378843)
                ·
                  rfl

theorem cell21_104441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 8].length) (baseStart_104441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104441 prefixEnd_104441 := by exact prefixLift 104441
  have htrace : WordTrace (prefixWord ++ tailWord_104441) baseStart_104441 baseEnd_104441 := by
    simpa [prefixWord, tailWord_104441, baseEnd_104441] using wordTrace_append hprefix tailTrace_104441
  have hstable : (prefixWord ++ tailWord_104441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104441).length < 2 ^ (prefixWord ++ tailWord_104441).sum := by decide
  have hdescent : baseEnd_104441 < baseStart_104441 := by decide
  rcases family_descends (prefixWord ++ tailWord_104441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104503 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 4]
def baseStart_104503 : Nat := 118140960795 + 104503 * 2 ^ 59
def prefixEnd_104503 : Nat := 4983230072969 + 3 ^ 40 * 104503 * 2
def baseEnd_104503 : Nat := 23849008371959940103069

theorem tailTrace_104503 : CollatzResearch.WordTrace tailWord_104503 prefixEnd_104503 23849008371959940103069 := by
  unfold tailWord_104503
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811537540410953536582163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2541025026940635691054775 3811537540410953536582163)
  ·
    refine ⟨5717306310616430304873245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3811537540410953536582163 5717306310616430304873245)
    ·
      refine ⟨2143989866481161364327467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5717306310616430304873245 2143989866481161364327467)
      ·
        refine ⟨3215984799721742046491201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143989866481161364327467 3215984799721742046491201)
        ·
          refine ⟨2411988599791306534868401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3215984799721742046491201 2411988599791306534868401)
          ·
            refine ⟨1808991449843479901151301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2411988599791306534868401 1808991449843479901151301)
            ·
              refine ⟨339185896845652481465869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1808991449843479901151301 339185896845652481465869)
              ·
                refine ⟨127194711317119680549701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339185896845652481465869 127194711317119680549701)
                ·
                  refine ⟨23849008371959940103069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127194711317119680549701 23849008371959940103069)
                  ·
                    rfl

theorem cell21_104503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 4].length) (baseStart_104503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104503 prefixEnd_104503 := by exact prefixLift 104503
  have htrace : WordTrace (prefixWord ++ tailWord_104503) baseStart_104503 baseEnd_104503 := by
    simpa [prefixWord, tailWord_104503, baseEnd_104503] using wordTrace_append hprefix tailTrace_104503
  have hstable : (prefixWord ++ tailWord_104503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104503).length < 2 ^ (prefixWord ++ tailWord_104503).sum := by decide
  have hdescent : baseEnd_104503 < baseStart_104503 := by decide
  rcases family_descends (prefixWord ++ tailWord_104503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104548 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_104548 : Nat := 118140960795 + 104548 * 2 ^ 59
def prefixEnd_104548 : Nat := 4983230072969 + 3 ^ 40 * 104548 * 2
def baseEnd_104548 : Nat := 23859277985049861852977

theorem tailTrace_104548 : CollatzResearch.WordTrace tailWord_104548 prefixEnd_104548 23859277985049861852977 := by
  unfold tailWord_104548
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906589412623963110985149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2542119216831950814646865 1906589412623963110985149)
  ·
    refine ⟨714971029733986166619431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1906589412623963110985149 714971029733986166619431)
    ·
      refine ⟨1072456544600979249929147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 714971029733986166619431 1072456544600979249929147)
      ·
        refine ⟨1608684816901468874893721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072456544600979249929147 1608684816901468874893721)
        ·
          refine ⟨1206513612676101656170291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1608684816901468874893721 1206513612676101656170291)
          ·
            refine ⟨1809770419014152484255437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206513612676101656170291 1809770419014152484255437)
            ·
              refine ⟨678663907130307181595789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1809770419014152484255437 678663907130307181595789)
              ·
                refine ⟨254498965173865193098421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 678663907130307181595789 254498965173865193098421)
                ·
                  refine ⟨23859277985049861852977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 254498965173865193098421 23859277985049861852977)
                  ·
                    rfl

theorem cell21_104548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_104548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104548 prefixEnd_104548 := by exact prefixLift 104548
  have htrace : WordTrace (prefixWord ++ tailWord_104548) baseStart_104548 baseEnd_104548 := by
    simpa [prefixWord, tailWord_104548, baseEnd_104548] using wordTrace_append hprefix tailTrace_104548
  have hstable : (prefixWord ++ tailWord_104548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104548).length < 2 ^ (prefixWord ++ tailWord_104548).sum := by decide
  have hdescent : baseEnd_104548 < baseStart_104548 := by decide
  rcases family_descends (prefixWord ++ tailWord_104548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104599 : List Nat := [1, 1, 3, 3, 4, 1, 3, 2, 3]
def baseStart_104599 : Nat := 118140960795 + 104599 * 2 ^ 59
def prefixEnd_104599 : Nat := 4983230072969 + 3 ^ 40 * 104599 * 2
def baseEnd_104599 : Nat := 23870916879885106502873

theorem tailTrace_104599 : CollatzResearch.WordTrace tailWord_104599 prefixEnd_104599 23870916879885106502873 := by
  unfold tailWord_104599
  simp only [CollatzResearch.WordTrace]
  refine ⟨3815038948063161932076851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2543359298708774621384567 3815038948063161932076851)
  ·
    refine ⟨5722558422094742898115277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3815038948063161932076851 5722558422094742898115277)
    ·
      refine ⟨2145959408285528586793229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5722558422094742898115277 2145959408285528586793229)
      ·
        refine ⟨804734778107073220047461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2145959408285528586793229 804734778107073220047461)
        ·
          refine ⟨150887770895076228758899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 804734778107073220047461 150887770895076228758899)
          ·
            refine ⟨226331656342614343138349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150887770895076228758899 226331656342614343138349)
            ·
              refine ⟨84874371128480378676881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226331656342614343138349 84874371128480378676881)
              ·
                refine ⟨63655778346360284007661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84874371128480378676881 63655778346360284007661)
                ·
                  refine ⟨23870916879885106502873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63655778346360284007661 23870916879885106502873)
                  ·
                    rfl

theorem cell21_104599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 3].length) (baseStart_104599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104599 prefixEnd_104599 := by exact prefixLift 104599
  have htrace : WordTrace (prefixWord ++ tailWord_104599) baseStart_104599 baseEnd_104599 := by
    simpa [prefixWord, tailWord_104599, baseEnd_104599] using wordTrace_append hprefix tailTrace_104599
  have hstable : (prefixWord ++ tailWord_104599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104599).length < 2 ^ (prefixWord ++ tailWord_104599).sum := by decide
  have hdescent : baseEnd_104599 < baseStart_104599 := by decide
  rcases family_descends (prefixWord ++ tailWord_104599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104610 : List Nat := [3, 3, 1, 3, 1, 1, 1, 8]
def baseStart_104610 : Nat := 118140960795 + 104610 * 2 ^ 59
def prefixEnd_104610 : Nat := 4983230072969 + 3 ^ 40 * 104610 * 2
def baseEnd_104610 : Nat := 7957809076583843939839

theorem tailTrace_104610 : CollatzResearch.WordTrace tailWord_104610 prefixEnd_104610 7957809076583843939839 := by
  unfold tailWord_104610
  simp only [CollatzResearch.WordTrace]
  refine ⟨953860037755827702681821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2543626767348873873818189 953860037755827702681821)
  ·
    refine ⟨357697514158435388505683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 953860037755827702681821 357697514158435388505683)
    ·
      refine ⟨536546271237653082758525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357697514158435388505683 536546271237653082758525)
      ·
        refine ⟨201204851714119906034447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 536546271237653082758525 201204851714119906034447)
        ·
          refine ⟨301807277571179859051671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201204851714119906034447 301807277571179859051671)
          ·
            refine ⟨452710916356769788577507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301807277571179859051671 452710916356769788577507)
            ·
              refine ⟨679066374535154682866261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452710916356769788577507 679066374535154682866261)
              ·
                refine ⟨7957809076583843939839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 679066374535154682866261 7957809076583843939839)
                ·
                  rfl

theorem cell21_104610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_104610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104610 prefixEnd_104610 := by exact prefixLift 104610
  have htrace : WordTrace (prefixWord ++ tailWord_104610) baseStart_104610 baseEnd_104610 := by
    simpa [prefixWord, tailWord_104610, baseEnd_104610] using wordTrace_append hprefix tailTrace_104610
  have hstable : (prefixWord ++ tailWord_104610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104610).length < 2 ^ (prefixWord ++ tailWord_104610).sum := by decide
  have hdescent : baseEnd_104610 < baseStart_104610 := by decide
  rcases family_descends (prefixWord ++ tailWord_104610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104655 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 4]
def baseStart_104655 : Nat := 118140960795 + 104655 * 2 ^ 59
def prefixEnd_104655 : Nat := 4983230072969 + 3 ^ 40 * 104655 * 2
def baseEnd_104655 : Nat := 23883696842841453569425

theorem tailTrace_104655 : CollatzResearch.WordTrace tailWord_104655 prefixEnd_104655 23883696842841453569425 := by
  unfold tailWord_104655
  simp only [CollatzResearch.WordTrace]
  refine ⟨3817081435860283496115419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2544720957240188997410279 3817081435860283496115419)
  ·
    refine ⟨5725622153790425244173129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3817081435860283496115419 5725622153790425244173129)
    ·
      refine ⟨4294216615342818933129847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5725622153790425244173129 4294216615342818933129847)
      ·
        refine ⟨6441324923014228399694771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294216615342818933129847 6441324923014228399694771)
        ·
          refine ⟨9661987384521342599542157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441324923014228399694771 9661987384521342599542157)
          ·
            refine ⟨3623245269195503474828309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9661987384521342599542157 3623245269195503474828309)
            ·
              refine ⟨169839621993539225382577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3623245269195503474828309 169839621993539225382577)
              ·
                refine ⟨127379716495154419036933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169839621993539225382577 127379716495154419036933)
                ·
                  refine ⟨23883696842841453569425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127379716495154419036933 23883696842841453569425)
                  ·
                    rfl

theorem cell21_104655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 4].length) (baseStart_104655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104655 prefixEnd_104655 := by exact prefixLift 104655
  have htrace : WordTrace (prefixWord ++ tailWord_104655) baseStart_104655 baseEnd_104655 := by
    simpa [prefixWord, tailWord_104655, baseEnd_104655] using wordTrace_append hprefix tailTrace_104655
  have hstable : (prefixWord ++ tailWord_104655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104655).length < 2 ^ (prefixWord ++ tailWord_104655).sum := by decide
  have hdescent : baseEnd_104655 < baseStart_104655 := by decide
  rcases family_descends (prefixWord ++ tailWord_104655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104658 : List Nat := [3, 2, 2, 2, 1, 3, 1, 4, 3]
def baseStart_104658 : Nat := 118140960795 + 104658 * 2 ^ 59
def prefixEnd_104658 : Nat := 4983230072969 + 3 ^ 40 * 104658 * 2
def baseEnd_104658 : Nat := 23884381483714115019419

theorem tailTrace_104658 : CollatzResearch.WordTrace tailWord_104658 prefixEnd_104658 23884381483714115019419 := by
  unfold tailWord_104658
  simp only [CollatzResearch.WordTrace]
  refine ⟨954297713712353752118657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2544793903232943338983085 954297713712353752118657)
  ·
    refine ⟨715723285284265314088993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 954297713712353752118657 715723285284265314088993)
    ·
      refine ⟨536792463963198985566745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 715723285284265314088993 536792463963198985566745)
      ·
        refine ⟨402594347972399239175059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536792463963198985566745 402594347972399239175059)
        ·
          refine ⟨603891521958598858762589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402594347972399239175059 603891521958598858762589)
          ·
            refine ⟨226459320734474572035971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 603891521958598858762589 226459320734474572035971)
            ·
              refine ⟨339688981101711858053957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226459320734474572035971 339688981101711858053957)
              ·
                refine ⟨63691683956570973385117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339688981101711858053957 63691683956570973385117)
                ·
                  refine ⟨23884381483714115019419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63691683956570973385117 23884381483714115019419)
                  ·
                    rfl

theorem cell21_104658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_104658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104658 prefixEnd_104658 := by exact prefixLift 104658
  have htrace : WordTrace (prefixWord ++ tailWord_104658) baseStart_104658 baseEnd_104658 := by
    simpa [prefixWord, tailWord_104658, baseEnd_104658] using wordTrace_append hprefix tailTrace_104658
  have hstable : (prefixWord ++ tailWord_104658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104658).length < 2 ^ (prefixWord ++ tailWord_104658).sum := by decide
  have hdescent : baseEnd_104658 < baseStart_104658 := by decide
  rcases family_descends (prefixWord ++ tailWord_104658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104734 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_104734 : Nat := 118140960795 + 104734 * 2 ^ 59
def prefixEnd_104734 : Nat := 4983230072969 + 3 ^ 40 * 104734 * 2
def baseEnd_104734 : Nat := 23901725719154871752597

theorem tailTrace_104734 : CollatzResearch.WordTrace tailWord_104734 prefixEnd_104734 23901725719154871752597 := by
  unfold tailWord_104734
  simp only [CollatzResearch.WordTrace]
  refine ⟨477495350321759998530157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2546641868382719992160837 477495350321759998530157)
  ·
    refine ⟨179060756370659999448809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 477495350321759998530157 179060756370659999448809)
    ·
      refine ⟨134295567277994999586607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179060756370659999448809 134295567277994999586607)
      ·
        refine ⟨201443350916992499379911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134295567277994999586607 201443350916992499379911)
        ·
          refine ⟨302165026375488749069867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201443350916992499379911 302165026375488749069867)
          ·
            refine ⟨453247539563233123604801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302165026375488749069867 453247539563233123604801)
            ·
              refine ⟨339935654672424842703601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453247539563233123604801 339935654672424842703601)
              ·
                refine ⟨254951741004318632027701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339935654672424842703601 254951741004318632027701)
                ·
                  refine ⟨23901725719154871752597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 254951741004318632027701 23901725719154871752597)
                  ·
                    rfl

theorem cell21_104734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_104734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104734 prefixEnd_104734 := by exact prefixLift 104734
  have htrace : WordTrace (prefixWord ++ tailWord_104734) baseStart_104734 baseEnd_104734 := by
    simpa [prefixWord, tailWord_104734, baseEnd_104734] using wordTrace_append hprefix tailTrace_104734
  have hstable : (prefixWord ++ tailWord_104734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104734).length < 2 ^ (prefixWord ++ tailWord_104734).sum := by decide
  have hdescent : baseEnd_104734 < baseStart_104734 := by decide
  rcases family_descends (prefixWord ++ tailWord_104734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104759 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 7]
def baseStart_104759 : Nat := 118140960795 + 104759 * 2 ^ 59
def prefixEnd_104759 : Nat := 4983230072969 + 3 ^ 40 * 104759 * 2
def baseEnd_104759 : Nat := 23907431059760383835879

theorem tailTrace_104759 : CollatzResearch.WordTrace tailWord_104759 prefixEnd_104759 23907431059760383835879 := by
  unfold tailWord_104759
  simp only [CollatzResearch.WordTrace]
  refine ⟨3820874627483509257901331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2547249751655672838600887 3820874627483509257901331)
  ·
    refine ⟨5731311941225263886851997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3820874627483509257901331 5731311941225263886851997)
    ·
      refine ⟨2149241977959473957569499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5731311941225263886851997 2149241977959473957569499)
      ·
        refine ⟨3223862966939210936354249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2149241977959473957569499 3223862966939210936354249)
        ·
          refine ⟨2417897225204408202265687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3223862966939210936354249 2417897225204408202265687)
          ·
            refine ⟨3626845837806612303398531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417897225204408202265687 3626845837806612303398531)
            ·
              refine ⟨5440268756709918455097797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3626845837806612303398531 5440268756709918455097797)
              ·
                refine ⟨1020050391883109710330837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5440268756709918455097797 1020050391883109710330837)
                ·
                  refine ⟨23907431059760383835879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1020050391883109710330837 23907431059760383835879)
                  ·
                    rfl

theorem cell21_104759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_104759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104759 prefixEnd_104759 := by exact prefixLift 104759
  have htrace : WordTrace (prefixWord ++ tailWord_104759) baseStart_104759 baseEnd_104759 := by
    simpa [prefixWord, tailWord_104759, baseEnd_104759] using wordTrace_append hprefix tailTrace_104759
  have hstable : (prefixWord ++ tailWord_104759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104759).length < 2 ^ (prefixWord ++ tailWord_104759).sum := by decide
  have hdescent : baseEnd_104759 < baseStart_104759 := by decide
  rcases family_descends (prefixWord ++ tailWord_104759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104776 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 5]
def baseStart_104776 : Nat := 118140960795 + 104776 * 2 ^ 59
def prefixEnd_104776 : Nat := 4983230072969 + 3 ^ 40 * 104776 * 2
def baseEnd_104776 : Nat := 23911310691372132052511

theorem tailTrace_104776 : CollatzResearch.WordTrace tailWord_104776 prefixEnd_104776 23911310691372132052511 := by
  unfold tailWord_104776
  simp only [CollatzResearch.WordTrace]
  refine ⟨1910747334210960580635091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2547663112281280774180121 1910747334210960580635091)
  ·
    refine ⟨2866121001316440870952637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1910747334210960580635091 2866121001316440870952637)
    ·
      refine ⟨1074795375493665326607239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2866121001316440870952637 1074795375493665326607239)
      ·
        refine ⟨1612193063240497989910859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074795375493665326607239 1612193063240497989910859)
        ·
          refine ⟨2418289594860746984866289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612193063240497989910859 2418289594860746984866289)
          ·
            refine ⟨1813717196145560238649717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2418289594860746984866289 1813717196145560238649717)
            ·
              refine ⟨170035987138646272373411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1813717196145560238649717 170035987138646272373411)
              ·
                refine ⟨255053980707969408560117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170035987138646272373411 255053980707969408560117)
                ·
                  refine ⟨23911310691372132052511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255053980707969408560117 23911310691372132052511)
                  ·
                    rfl

theorem cell21_104776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_104776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104776 prefixEnd_104776 := by exact prefixLift 104776
  have htrace : WordTrace (prefixWord ++ tailWord_104776) baseStart_104776 baseEnd_104776 := by
    simpa [prefixWord, tailWord_104776, baseEnd_104776] using wordTrace_append hprefix tailTrace_104776
  have hstable : (prefixWord ++ tailWord_104776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104776).length < 2 ^ (prefixWord ++ tailWord_104776).sum := by decide
  have hdescent : baseEnd_104776 < baseStart_104776 := by decide
  rcases family_descends (prefixWord ++ tailWord_104776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104821 : List Nat := [1, 3, 4, 1, 2, 10]
def baseStart_104821 : Nat := 118140960795 + 104821 * 2 ^ 59
def prefixEnd_104821 : Nat := 4983230072969 + 3 ^ 40 * 104821 * 2
def baseEnd_104821 : Nat := 885984455720816807497

theorem tailTrace_104821 : CollatzResearch.WordTrace tailWord_104821 prefixEnd_104821 885984455720816807497 := by
  unfold tailWord_104821
  simp only [CollatzResearch.WordTrace]
  refine ⟨3823135953258893846658317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2548757302172595897772211 3823135953258893846658317)
  ·
    refine ⟨1433675982472085192496869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3823135953258893846658317 1433675982472085192496869)
    ·
      refine ⟨268814246713515973593163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1433675982472085192496869 268814246713515973593163)
      ·
        refine ⟨403221370070273960389745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268814246713515973593163 403221370070273960389745)
        ·
          refine ⟨302416027552705470292309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403221370070273960389745 302416027552705470292309)
          ·
            refine ⟨885984455720816807497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 302416027552705470292309 885984455720816807497)
            ·
              rfl

theorem cell21_104821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 10].length) (baseStart_104821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104821 prefixEnd_104821 := by exact prefixLift 104821
  have htrace : WordTrace (prefixWord ++ tailWord_104821) baseStart_104821 baseEnd_104821 := by
    simpa [prefixWord, tailWord_104821, baseEnd_104821] using wordTrace_append hprefix tailTrace_104821
  have hstable : (prefixWord ++ tailWord_104821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104821).length < 2 ^ (prefixWord ++ tailWord_104821).sum := by decide
  have hdescent : baseEnd_104821 < baseStart_104821 := by decide
  rcases family_descends (prefixWord ++ tailWord_104821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104869 : List Nat := [1, 3, 1, 2, 1, 1, 6, 3, 3]
def baseStart_104869 : Nat := 118140960795 + 104869 * 2 ^ 59
def prefixEnd_104869 : Nat := 4983230072969 + 3 ^ 40 * 104869 * 2
def baseEnd_104869 : Nat := 23932534558424637002321

theorem tailTrace_104869 : CollatzResearch.WordTrace tailWord_104869 prefixEnd_104869 23932534558424637002321 := by
  unfold tailWord_104869
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824886657084998044405661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2549924438056665362937107 3824886657084998044405661)
  ·
    refine ⟨1434332496406874266652123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3824886657084998044405661 1434332496406874266652123)
    ·
      refine ⟨2151498744610311399978185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1434332496406874266652123 2151498744610311399978185)
      ·
        refine ⟨1613624058457733549983639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2151498744610311399978185 1613624058457733549983639)
        ·
          refine ⟨2420436087686600324975459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613624058457733549983639 2420436087686600324975459)
          ·
            refine ⟨3630654131529900487463189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420436087686600324975459 3630654131529900487463189)
            ·
              refine ⟨170186912415464085349837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3630654131529900487463189 170186912415464085349837)
              ·
                refine ⟨63820092155799032006189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170186912415464085349837 63820092155799032006189)
                ·
                  refine ⟨23932534558424637002321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63820092155799032006189 23932534558424637002321)
                  ·
                    rfl

theorem cell21_104869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_104869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104869 prefixEnd_104869 := by exact prefixLift 104869
  have htrace : WordTrace (prefixWord ++ tailWord_104869) baseStart_104869 baseEnd_104869 := by
    simpa [prefixWord, tailWord_104869, baseEnd_104869] using wordTrace_append hprefix tailTrace_104869
  have hstable : (prefixWord ++ tailWord_104869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104869).length < 2 ^ (prefixWord ++ tailWord_104869).sum := by decide
  have hdescent : baseEnd_104869 < baseStart_104869 := by decide
  rcases family_descends (prefixWord ++ tailWord_104869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104990 : List Nat := [4, 3, 3, 11]
def baseStart_104990 : Nat := 118140960795 + 104990 * 2 ^ 59
def prefixEnd_104990 : Nat := 4983230072969 + 3 ^ 40 * 104990 * 2
def baseEnd_104990 : Nat := 98601433773478664549

theorem tailTrace_104990 : CollatzResearch.WordTrace tailWord_104990 prefixEnd_104990 98601433773478664549 := by
  unfold tailWord_104990
  simp only [CollatzResearch.WordTrace]
  refine ⟨478662486205829463695053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2552866593097757139706949 478662486205829463695053)
  ·
    refine ⟨179498432327186048885645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 478662486205829463695053 179498432327186048885645)
    ·
      refine ⟨67311912122694768332117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179498432327186048885645 67311912122694768332117)
      ·
        refine ⟨98601433773478664549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 67311912122694768332117 98601433773478664549)
        ·
          rfl

theorem cell21_104990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 11].length) (baseStart_104990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104990 prefixEnd_104990 := by exact prefixLift 104990
  have htrace : WordTrace (prefixWord ++ tailWord_104990) baseStart_104990 baseEnd_104990 := by
    simpa [prefixWord, tailWord_104990, baseEnd_104990] using wordTrace_append hprefix tailTrace_104990
  have hstable : (prefixWord ++ tailWord_104990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104990).length < 2 ^ (prefixWord ++ tailWord_104990).sum := by decide
  have hdescent : baseEnd_104990 < baseStart_104990 := by decide
  rcases family_descends (prefixWord ++ tailWord_104990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104996 : List Nat := [2, 3, 1, 5, 1, 2, 2, 2, 3]
def baseStart_104996 : Nat := 118140960795 + 104996 * 2 ^ 59
def prefixEnd_104996 : Nat := 4983230072969 + 3 ^ 40 * 104996 * 2
def baseEnd_104996 : Nat := 23961517688700638385395

theorem tailTrace_104996 : CollatzResearch.WordTrace tailWord_104996 prefixEnd_104996 23961517688700638385395 := by
  unfold tailWord_104996
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914759363812449367139421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2553012485083265822852561 1914759363812449367139421)
  ·
    refine ⟨718034761429668512677283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1914759363812449367139421 718034761429668512677283)
    ·
      refine ⟨1077052142144502769015925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 718034761429668512677283 1077052142144502769015925)
      ·
        refine ⟨100973638326047134595243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1077052142144502769015925 100973638326047134595243)
        ·
          refine ⟨151460457489070701892865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100973638326047134595243 151460457489070701892865)
          ·
            refine ⟨113595343116803026419649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151460457489070701892865 113595343116803026419649)
            ·
              refine ⟨85196507337602269814737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113595343116803026419649 85196507337602269814737)
              ·
                refine ⟨63897380503201702361053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85196507337602269814737 63897380503201702361053)
                ·
                  refine ⟨23961517688700638385395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63897380503201702361053 23961517688700638385395)
                  ·
                    rfl

theorem cell21_104996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_104996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_104996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_104996 prefixEnd_104996 := by exact prefixLift 104996
  have htrace : WordTrace (prefixWord ++ tailWord_104996) baseStart_104996 baseEnd_104996 := by
    simpa [prefixWord, tailWord_104996, baseEnd_104996] using wordTrace_append hprefix tailTrace_104996
  have hstable : (prefixWord ++ tailWord_104996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104996).length < 2 ^ (prefixWord ++ tailWord_104996).sum := by decide
  have hdescent : baseEnd_104996 < baseStart_104996 := by decide
  rcases family_descends (prefixWord ++ tailWord_104996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105032 : List Nat := [2, 1, 3, 1, 1, 1, 1, 11]
def baseStart_105032 : Nat := 118140960795 + 105032 * 2 ^ 59
def prefixEnd_105032 : Nat := 4983230072969 + 3 ^ 40 * 105032 * 2
def baseEnd_105032 : Nat := 7989911126390858595107

theorem tailTrace_105032 : CollatzResearch.WordTrace tailWord_105032 prefixEnd_105032 7989911126390858595107 := by
  unfold tailWord_105032
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915415877747238441294675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2553887836996317921726233 1915415877747238441294675)
  ·
    refine ⟨2873123816620857661942013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1915415877747238441294675 2873123816620857661942013)
    ·
      refine ⟨1077421431232821623228255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2873123816620857661942013 1077421431232821623228255)
      ·
        refine ⟨1616132146849232434842383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077421431232821623228255 1616132146849232434842383)
        ·
          refine ⟨2424198220273848652263575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616132146849232434842383 2424198220273848652263575)
          ·
            refine ⟨3636297330410772978395363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424198220273848652263575 3636297330410772978395363)
            ·
              refine ⟨5454445995616159467593045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3636297330410772978395363 5454445995616159467593045)
              ·
                refine ⟨7989911126390858595107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 5454445995616159467593045 7989911126390858595107)
                ·
                  rfl

theorem cell21_105032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_105032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105032 prefixEnd_105032 := by exact prefixLift 105032
  have htrace : WordTrace (prefixWord ++ tailWord_105032) baseStart_105032 baseEnd_105032 := by
    simpa [prefixWord, tailWord_105032, baseEnd_105032] using wordTrace_append hprefix tailTrace_105032
  have hstable : (prefixWord ++ tailWord_105032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105032).length < 2 ^ (prefixWord ++ tailWord_105032).sum := by decide
  have hdescent : baseEnd_105032 < baseStart_105032 := by decide
  rcases family_descends (prefixWord ++ tailWord_105032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105114 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_105114 : Nat := 118140960795 + 105114 * 2 ^ 59
def prefixEnd_105114 : Nat := 4983230072969 + 3 ^ 40 * 105114 * 2
def baseEnd_105114 : Nat := 23988446896358655418487

theorem tailTrace_105114 : CollatzResearch.WordTrace tailWord_105114 prefixEnd_105114 23988446896358655418487 := by
  unfold tailWord_105114
  simp only [CollatzResearch.WordTrace]
  refine ⟨958455635299351221768599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2555881694131603258049597 958455635299351221768599)
  ·
    refine ⟨1437683452949026832652899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 958455635299351221768599 1437683452949026832652899)
    ·
      refine ⟨2156525179423540248979349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437683452949026832652899 2156525179423540248979349)
      ·
        refine ⟨101087117785478449170907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2156525179423540248979349 101087117785478449170907)
        ·
          refine ⟨151630676678217673756361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101087117785478449170907 151630676678217673756361)
          ·
            refine ⟨113723007508663255317271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151630676678217673756361 113723007508663255317271)
            ·
              refine ⟨170584511262994882975907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113723007508663255317271 170584511262994882975907)
              ·
                refine ⟨255876766894492324463861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170584511262994882975907 255876766894492324463861)
                ·
                  refine ⟨23988446896358655418487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255876766894492324463861 23988446896358655418487)
                  ·
                    rfl

theorem cell21_105114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_105114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105114 prefixEnd_105114 := by exact prefixLift 105114
  have htrace : WordTrace (prefixWord ++ tailWord_105114) baseStart_105114 baseEnd_105114 := by
    simpa [prefixWord, tailWord_105114, baseEnd_105114] using wordTrace_append hprefix tailTrace_105114
  have hstable : (prefixWord ++ tailWord_105114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105114).length < 2 ^ (prefixWord ++ tailWord_105114).sum := by decide
  have hdescent : baseEnd_105114 < baseStart_105114 := by decide
  rcases family_descends (prefixWord ++ tailWord_105114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105165 : List Nat := [1, 6, 2, 1, 3, 1, 2, 2, 3]
def baseStart_105165 : Nat := 118140960795 + 105165 * 2 ^ 59
def prefixEnd_105165 : Nat := 4983230072969 + 3 ^ 40 * 105165 * 2
def baseEnd_105165 : Nat := 24000085791193900068383

theorem tailTrace_105165 : CollatzResearch.WordTrace tailWord_105165 prefixEnd_105165 24000085791193900068383 := by
  unfold tailWord_105165
  simp only [CollatzResearch.WordTrace]
  refine ⟨3835682664012640597180949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2557121776008427064787299 3835682664012640597180949)
  ·
    refine ⟨179797624875592527992857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3835682664012640597180949 179797624875592527992857)
    ·
      refine ⟨134848218656694395994643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179797624875592527992857 134848218656694395994643)
      ·
        refine ⟨202272327985041593991965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134848218656694395994643 202272327985041593991965)
        ·
          refine ⟨75852122994390597746987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202272327985041593991965 75852122994390597746987)
          ·
            refine ⟨113778184491585896620481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75852122994390597746987 113778184491585896620481)
            ·
              refine ⟨85333638368689422465361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113778184491585896620481 85333638368689422465361)
              ·
                refine ⟨64000228776517066849021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85333638368689422465361 64000228776517066849021)
                ·
                  refine ⟨24000085791193900068383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64000228776517066849021 24000085791193900068383)
                  ·
                    rfl

theorem cell21_105165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_105165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105165 prefixEnd_105165 := by exact prefixLift 105165
  have htrace : WordTrace (prefixWord ++ tailWord_105165) baseStart_105165 baseEnd_105165 := by
    simpa [prefixWord, tailWord_105165, baseEnd_105165] using wordTrace_append hprefix tailTrace_105165
  have hstable : (prefixWord ++ tailWord_105165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105165).length < 2 ^ (prefixWord ++ tailWord_105165).sum := by decide
  have hdescent : baseEnd_105165 < baseStart_105165 := by decide
  rcases family_descends (prefixWord ++ tailWord_105165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105187 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 4]
def baseStart_105187 : Nat := 118140960795 + 105187 * 2 ^ 59
def prefixEnd_105187 : Nat := 4983230072969 + 3 ^ 40 * 105187 * 2
def baseEnd_105187 : Nat := 24005106490926750701671

theorem tailTrace_105187 : CollatzResearch.WordTrace tailWord_105187 prefixEnd_105187 24005106490926750701671 := by
  unfold tailWord_105187
  simp only [CollatzResearch.WordTrace]
  refine ⟨3836485069932938354481815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2557656713288625569654543 3836485069932938354481815)
  ·
    refine ⟨5754727604899407531722723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3836485069932938354481815 5754727604899407531722723)
    ·
      refine ⟨8632091407349111297584085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5754727604899407531722723 8632091407349111297584085)
      ·
        refine ⟨202314642359744796037127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8632091407349111297584085 202314642359744796037127)
        ·
          refine ⟨303471963539617194055691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202314642359744796037127 303471963539617194055691)
          ·
            refine ⟨455207945309425791083537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303471963539617194055691 455207945309425791083537)
            ·
              refine ⟨341405958982069343312653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455207945309425791083537 341405958982069343312653)
              ·
                refine ⟨128027234618276003742245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341405958982069343312653 128027234618276003742245)
                ·
                  refine ⟨24005106490926750701671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128027234618276003742245 24005106490926750701671)
                  ·
                    rfl

theorem cell21_105187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 4].length) (baseStart_105187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105187 prefixEnd_105187 := by exact prefixLift 105187
  have htrace : WordTrace (prefixWord ++ tailWord_105187) baseStart_105187 baseEnd_105187 := by
    simpa [prefixWord, tailWord_105187, baseEnd_105187] using wordTrace_append hprefix tailTrace_105187
  have hstable : (prefixWord ++ tailWord_105187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105187).length < 2 ^ (prefixWord ++ tailWord_105187).sum := by decide
  have hdescent : baseEnd_105187 < baseStart_105187 := by decide
  rcases family_descends (prefixWord ++ tailWord_105187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105201 : List Nat := [1, 2, 2, 2, 2, 2, 5, 5]
def baseStart_105201 : Nat := 118140960795 + 105201 * 2 ^ 59
def prefixEnd_105201 : Nat := 4983230072969 + 3 ^ 40 * 105201 * 2
def baseEnd_105201 : Nat := 8002767160555279156103

theorem tailTrace_105201 : CollatzResearch.WordTrace tailWord_105201 prefixEnd_105201 8002767160555279156103 := by
  unfold tailWord_105201
  simp only [CollatzResearch.WordTrace]
  refine ⟨3836995691882218745491457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2557997127921479163660971 3836995691882218745491457)
  ·
    refine ⟨2877746768911664059118593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3836995691882218745491457 2877746768911664059118593)
    ·
      refine ⟨2158310076683748044338945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2877746768911664059118593 2158310076683748044338945)
      ·
        refine ⟨1618732557512811033254209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2158310076683748044338945 1618732557512811033254209)
        ·
          refine ⟨1214049418134608274940657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1618732557512811033254209 1214049418134608274940657)
          ·
            refine ⟨910537063600956206205493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1214049418134608274940657 910537063600956206205493)
            ·
              refine ⟨85362849712589644331765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 910537063600956206205493 85362849712589644331765)
              ·
                refine ⟨8002767160555279156103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85362849712589644331765 8002767160555279156103)
                ·
                  rfl

theorem cell21_105201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 5].length) (baseStart_105201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105201 prefixEnd_105201 := by exact prefixLift 105201
  have htrace : WordTrace (prefixWord ++ tailWord_105201) baseStart_105201 baseEnd_105201 := by
    simpa [prefixWord, tailWord_105201, baseEnd_105201] using wordTrace_append hprefix tailTrace_105201
  have hstable : (prefixWord ++ tailWord_105201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105201).length < 2 ^ (prefixWord ++ tailWord_105201).sum := by decide
  have hdescent : baseEnd_105201 < baseStart_105201 := by decide
  rcases family_descends (prefixWord ++ tailWord_105201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105260 : List Nat := [2, 2, 1, 1, 1, 4, 3, 7]
def baseStart_105260 : Nat := 118140960795 + 105260 * 2 ^ 59
def prefixEnd_105260 : Nat := 4983230072969 + 3 ^ 40 * 105260 * 2
def baseEnd_105260 : Nat := 8007255361831615328285

theorem tailTrace_105260 : CollatzResearch.WordTrace tailWord_105260 prefixEnd_105260 8007255361831615328285 := by
  unfold tailWord_105260
  simp only [CollatzResearch.WordTrace]
  refine ⟨1919573799334235910944617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2559431732445647881259489 1919573799334235910944617)
  ·
    refine ⟨1439680349500676933208463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1919573799334235910944617 1439680349500676933208463)
    ·
      refine ⟨2159520524251015399812695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1439680349500676933208463 2159520524251015399812695)
      ·
        refine ⟨3239280786376523099719043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2159520524251015399812695 3239280786376523099719043)
        ·
          refine ⟨4858921179564784649578565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3239280786376523099719043 4858921179564784649578565)
          ·
            refine ⟨911047721168397121795981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4858921179564784649578565 911047721168397121795981)
            ·
              refine ⟨341642895438148920673493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 911047721168397121795981 341642895438148920673493)
              ·
                refine ⟨8007255361831615328285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 341642895438148920673493 8007255361831615328285)
                ·
                  rfl

theorem cell21_105260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_105260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105260 prefixEnd_105260 := by exact prefixLift 105260
  have htrace : WordTrace (prefixWord ++ tailWord_105260) baseStart_105260 baseEnd_105260 := by
    simpa [prefixWord, tailWord_105260, baseEnd_105260] using wordTrace_append hprefix tailTrace_105260
  have hstable : (prefixWord ++ tailWord_105260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105260).length < 2 ^ (prefixWord ++ tailWord_105260).sum := by decide
  have hdescent : baseEnd_105260 < baseStart_105260 := by decide
  rcases family_descends (prefixWord ++ tailWord_105260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105297 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 4]
def baseStart_105297 : Nat := 118140960795 + 105297 * 2 ^ 59
def prefixEnd_105297 : Nat := 4983230072969 + 3 ^ 40 * 105297 * 2
def baseEnd_105297 : Nat := 24030209989591003868113

theorem tailTrace_105297 : CollatzResearch.WordTrace tailWord_105297 prefixEnd_105297 24030209989591003868113 := by
  unfold tailWord_105297
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840497099534427140986145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2560331399689618093990763 3840497099534427140986145)
  ·
    refine ⟨2880372824650820355739609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3840497099534427140986145 2880372824650820355739609)
    ·
      refine ⟨2160279618488115266804707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2880372824650820355739609 2160279618488115266804707)
      ·
        refine ⟨3240419427732172900207061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2160279618488115266804707 3240419427732172900207061)
        ·
          refine ⟨75947330337472802348603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3240419427732172900207061 75947330337472802348603)
          ·
            refine ⟨113920995506209203522905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75947330337472802348603 113920995506209203522905)
            ·
              refine ⟨85440746629656902642179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113920995506209203522905 85440746629656902642179)
              ·
                refine ⟨128161119944485353963269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85440746629656902642179 128161119944485353963269)
                ·
                  refine ⟨24030209989591003868113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128161119944485353963269 24030209989591003868113)
                  ·
                    rfl

theorem cell21_105297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 4].length) (baseStart_105297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105297 prefixEnd_105297 := by exact prefixLift 105297
  have htrace : WordTrace (prefixWord ++ tailWord_105297) baseStart_105297 baseEnd_105297 := by
    simpa [prefixWord, tailWord_105297, baseEnd_105297] using wordTrace_append hprefix tailTrace_105297
  have hstable : (prefixWord ++ tailWord_105297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105297).length < 2 ^ (prefixWord ++ tailWord_105297).sum := by decide
  have hdescent : baseEnd_105297 < baseStart_105297 := by decide
  rcases family_descends (prefixWord ++ tailWord_105297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105353 : List Nat := [1, 2, 1, 1, 5, 4, 1, 6]
def baseStart_105353 : Nat := 118140960795 + 105353 * 2 ^ 59
def prefixEnd_105353 : Nat := 4983230072969 + 3 ^ 40 * 105353 * 2
def baseEnd_105353 : Nat := 8014329984182450311555

theorem tailTrace_105353 : CollatzResearch.WordTrace tailWord_105353 prefixEnd_105353 8014329984182450311555 := by
  unfold tailWord_105353
  simp only [CollatzResearch.WordTrace]
  refine ⟨3842539587331548705024713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2561693058221032470016475 3842539587331548705024713)
  ·
    refine ⟨2881904690498661528768535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3842539587331548705024713 2881904690498661528768535)
    ·
      refine ⟨4322857035747992293152803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2881904690498661528768535 4322857035747992293152803)
      ·
        refine ⟨6484285553621988439729205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4322857035747992293152803 6484285553621988439729205)
        ·
          refine ⟨607901770652061416224613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6484285553621988439729205 607901770652061416224613)
          ·
            refine ⟨113981581997261515542115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 607901770652061416224613 113981581997261515542115)
            ·
              refine ⟨170972372995892273313173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113981581997261515542115 170972372995892273313173)
              ·
                refine ⟨8014329984182450311555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170972372995892273313173 8014329984182450311555)
                ·
                  rfl

theorem cell21_105353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 6].length) (baseStart_105353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105353 prefixEnd_105353 := by exact prefixLift 105353
  have htrace : WordTrace (prefixWord ++ tailWord_105353) baseStart_105353 baseEnd_105353 := by
    simpa [prefixWord, tailWord_105353, baseEnd_105353] using wordTrace_append hprefix tailTrace_105353
  have hstable : (prefixWord ++ tailWord_105353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105353).length < 2 ^ (prefixWord ++ tailWord_105353).sum := by decide
  have hdescent : baseEnd_105353 < baseStart_105353 := by decide
  rcases family_descends (prefixWord ++ tailWord_105353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105367 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 5]
def baseStart_105367 : Nat := 118140960795 + 105367 * 2 ^ 59
def prefixEnd_105367 : Nat := 4983230072969 + 3 ^ 40 * 105367 * 2
def baseEnd_105367 : Nat := 24046184943286437701303

theorem tailTrace_105367 : CollatzResearch.WordTrace tailWord_105367 prefixEnd_105367 24046184943286437701303 := by
  unfold tailWord_105367
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843050209280829096034355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2562033472853886064022903 3843050209280829096034355)
  ·
    refine ⟨5764575313921243644051533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3843050209280829096034355 5764575313921243644051533)
    ·
      refine ⟨2161715742720466366519325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5764575313921243644051533 2161715742720466366519325)
      ·
        refine ⟨810643403520174887444747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2161715742720466366519325 810643403520174887444747)
        ·
          refine ⟨1215965105280262331167121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810643403520174887444747 1215965105280262331167121)
          ·
            refine ⟨911973828960196748375341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215965105280262331167121 911973828960196748375341)
            ·
              refine ⟨341990185860073780640753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 911973828960196748375341 341990185860073780640753)
              ·
                refine ⟨256492639395055335480565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341990185860073780640753 256492639395055335480565)
                ·
                  refine ⟨24046184943286437701303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 256492639395055335480565 24046184943286437701303)
                  ·
                    rfl

theorem cell21_105367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_105367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105367 prefixEnd_105367 := by exact prefixLift 105367
  have htrace : WordTrace (prefixWord ++ tailWord_105367) baseStart_105367 baseEnd_105367 := by
    simpa [prefixWord, tailWord_105367, baseEnd_105367] using wordTrace_append hprefix tailTrace_105367
  have hstable : (prefixWord ++ tailWord_105367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105367).length < 2 ^ (prefixWord ++ tailWord_105367).sum := by decide
  have hdescent : baseEnd_105367 < baseStart_105367 := by decide
  rcases family_descends (prefixWord ++ tailWord_105367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105370 : List Nat := [3, 1, 1, 4, 3, 1, 3, 5]
def baseStart_105370 : Nat := 118140960795 + 105370 * 2 ^ 59
def prefixEnd_105370 : Nat := 4983230072969 + 3 ^ 40 * 105370 * 2
def baseEnd_105370 : Nat := 8015623194719699717099

theorem tailTrace_105370 : CollatzResearch.WordTrace tailWord_105370 prefixEnd_105370 8015623194719699717099 := by
  unfold tailWord_105370
  simp only [CollatzResearch.WordTrace]
  refine ⟨960789907067490152098391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2562106418846640405595709 960789907067490152098391)
  ·
    refine ⟨1441184860601235228147587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 960789907067490152098391 1441184860601235228147587)
    ·
      refine ⟨2161777290901852842221381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1441184860601235228147587 2161777290901852842221381)
      ·
        refine ⟨405333242044097407916509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2161777290901852842221381 405333242044097407916509)
        ·
          refine ⟨151999965766536527968691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405333242044097407916509 151999965766536527968691)
          ·
            refine ⟨227999948649804791953037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151999965766536527968691 227999948649804791953037)
            ·
              refine ⟨85499980743676796982389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227999948649804791953037 85499980743676796982389)
              ·
                refine ⟨8015623194719699717099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85499980743676796982389 8015623194719699717099)
                ·
                  rfl

theorem cell21_105370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_105370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105370 prefixEnd_105370 := by exact prefixLift 105370
  have htrace : WordTrace (prefixWord ++ tailWord_105370) baseStart_105370 baseEnd_105370 := by
    simpa [prefixWord, tailWord_105370, baseEnd_105370] using wordTrace_append hprefix tailTrace_105370
  have hstable : (prefixWord ++ tailWord_105370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105370).length < 2 ^ (prefixWord ++ tailWord_105370).sum := by decide
  have hdescent : baseEnd_105370 < baseStart_105370 := by decide
  rcases family_descends (prefixWord ++ tailWord_105370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105421 : List Nat := [1, 6, 3, 1, 1, 2, 2, 5]
def baseStart_105421 : Nat := 118140960795 + 105421 * 2 ^ 59
def prefixEnd_105421 : Nat := 4983230072969 + 3 ^ 40 * 105421 * 2
def baseEnd_105421 : Nat := 8019502826331447933731

theorem tailTrace_105421 : CollatzResearch.WordTrace tailWord_105421 prefixEnd_105421 8019502826331447933731 := by
  unfold tailWord_105421
  simp only [CollatzResearch.WordTrace]
  refine ⟨3845019751085196318500117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2563346500723464212333411 3845019751085196318500117)
  ·
    refine ⟨180235300832118577429693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3845019751085196318500117 180235300832118577429693)
    ·
      refine ⟨67588237812044466536135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180235300832118577429693 67588237812044466536135)
      ·
        refine ⟨101382356718066699804203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67588237812044466536135 101382356718066699804203)
        ·
          refine ⟨152073535077100049706305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101382356718066699804203 152073535077100049706305)
          ·
            refine ⟨114055151307825037279729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152073535077100049706305 114055151307825037279729)
            ·
              refine ⟨85541363480868777959797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114055151307825037279729 85541363480868777959797)
              ·
                refine ⟨8019502826331447933731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85541363480868777959797 8019502826331447933731)
                ·
                  rfl

theorem cell21_105421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 5].length) (baseStart_105421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105421 prefixEnd_105421 := by exact prefixLift 105421
  have htrace : WordTrace (prefixWord ++ tailWord_105421) baseStart_105421 baseEnd_105421 := by
    simpa [prefixWord, tailWord_105421, baseEnd_105421] using wordTrace_append hprefix tailTrace_105421
  have hstable : (prefixWord ++ tailWord_105421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105421).length < 2 ^ (prefixWord ++ tailWord_105421).sum := by decide
  have hdescent : baseEnd_105421 < baseStart_105421 := by decide
  rcases family_descends (prefixWord ++ tailWord_105421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105429 : List Nat := [1, 3, 2, 3, 3, 1, 1, 7]
def baseStart_105429 : Nat := 118140960795 + 105429 * 2 ^ 59
def prefixEnd_105429 : Nat := 4983230072969 + 3 ^ 40 * 105429 * 2
def baseEnd_105429 : Nat := 8020111395996035889281

theorem tailTrace_105429 : CollatzResearch.WordTrace tailWord_105429 prefixEnd_105429 8020111395996035889281 := by
  unfold tailWord_105429
  simp only [CollatzResearch.WordTrace]
  refine ⟨3845311535056213684791341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2563541023370809123194227 3845311535056213684791341)
  ·
    refine ⟨1441991825646080131796753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3845311535056213684791341 1441991825646080131796753)
    ·
      refine ⟨1081493869234560098847565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1441991825646080131796753 1081493869234560098847565)
      ·
        refine ⟨405560200962960037067837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1081493869234560098847565 405560200962960037067837)
        ·
          refine ⟨152085075361110013900439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405560200962960037067837 152085075361110013900439)
          ·
            refine ⟨228127613041665020850659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152085075361110013900439 228127613041665020850659)
            ·
              refine ⟨342191419562497531275989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228127613041665020850659 342191419562497531275989)
              ·
                refine ⟨8020111395996035889281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 342191419562497531275989 8020111395996035889281)
                ·
                  rfl

theorem cell21_105429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 7].length) (baseStart_105429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105429 prefixEnd_105429 := by exact prefixLift 105429
  have htrace : WordTrace (prefixWord ++ tailWord_105429) baseStart_105429 baseEnd_105429 := by
    simpa [prefixWord, tailWord_105429, baseEnd_105429] using wordTrace_append hprefix tailTrace_105429
  have hstable : (prefixWord ++ tailWord_105429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105429).length < 2 ^ (prefixWord ++ tailWord_105429).sum := by decide
  have hdescent : baseEnd_105429 < baseStart_105429 := by decide
  rcases family_descends (prefixWord ++ tailWord_105429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105511 : List Nat := [1, 1, 7, 1, 1, 3, 2, 2, 3]
def baseStart_105511 : Nat := 118140960795 + 105511 * 2 ^ 59
def prefixEnd_105511 : Nat := 4983230072969 + 3 ^ 40 * 105511 * 2
def baseEnd_105511 : Nat := 24079047705174187301009

theorem tailTrace_105511 : CollatzResearch.WordTrace tailWord_105511 prefixEnd_105511 24079047705174187301009 := by
  unfold tailWord_105511
  simp only [CollatzResearch.WordTrace]
  refine ⟨3848302320759141689276387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2565534880506094459517591 3848302320759141689276387)
  ·
    refine ⟨5772453481138712533914581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3848302320759141689276387 5772453481138712533914581)
    ·
      refine ⟨135291878464188575013623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5772453481138712533914581 135291878464188575013623)
      ·
        refine ⟨202937817696282862520435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135291878464188575013623 202937817696282862520435)
        ·
          refine ⟨304406726544424293780653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202937817696282862520435 304406726544424293780653)
          ·
            refine ⟨114152522454159110167745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304406726544424293780653 114152522454159110167745)
            ·
              refine ⟨85614391840619332625809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114152522454159110167745 85614391840619332625809)
              ·
                refine ⟨64210793880464499469357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85614391840619332625809 64210793880464499469357)
                ·
                  refine ⟨24079047705174187301009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64210793880464499469357 24079047705174187301009)
                  ·
                    rfl

theorem cell21_105511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 3].length) (baseStart_105511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105511 prefixEnd_105511 := by exact prefixLift 105511
  have htrace : WordTrace (prefixWord ++ tailWord_105511) baseStart_105511 baseEnd_105511 := by
    simpa [prefixWord, tailWord_105511, baseEnd_105511] using wordTrace_append hprefix tailTrace_105511
  have hstable : (prefixWord ++ tailWord_105511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105511).length < 2 ^ (prefixWord ++ tailWord_105511).sum := by decide
  have hdescent : baseEnd_105511 < baseStart_105511 := by decide
  rcases family_descends (prefixWord ++ tailWord_105511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105564 : List Nat := [2, 2, 4, 1, 1, 1, 10]
def baseStart_105564 : Nat := 118140960795 + 105564 * 2 ^ 59
def prefixEnd_105564 : Nat := 4983230072969 + 3 ^ 40 * 105564 * 2
def baseEnd_105564 : Nat := 2676793669695319213063

theorem tailTrace_105564 : CollatzResearch.WordTrace tailWord_105564 prefixEnd_105564 2676793669695319213063 := by
  unfold tailWord_105564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1925117694783565870477873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2566823593044754493970497 1925117694783565870477873)
  ·
    refine ⟨1443838271087674402858405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1925117694783565870477873 1443838271087674402858405)
    ·
      refine ⟨270719675828938950535951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1443838271087674402858405 270719675828938950535951)
      ·
        refine ⟨406079513743408425803927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270719675828938950535951 406079513743408425803927)
        ·
          refine ⟨609119270615112638705891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406079513743408425803927 609119270615112638705891)
          ·
            refine ⟨913678905922668958058837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609119270615112638705891 913678905922668958058837)
            ·
              refine ⟨2676793669695319213063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 913678905922668958058837 2676793669695319213063)
              ·
                rfl

theorem cell21_105564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 10].length) (baseStart_105564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105564 prefixEnd_105564 := by exact prefixLift 105564
  have htrace : WordTrace (prefixWord ++ tailWord_105564) baseStart_105564 baseEnd_105564 := by
    simpa [prefixWord, tailWord_105564, baseEnd_105564] using wordTrace_append hprefix tailTrace_105564
  have hstable : (prefixWord ++ tailWord_105564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105564).length < 2 ^ (prefixWord ++ tailWord_105564).sum := by decide
  have hdescent : baseEnd_105564 < baseStart_105564 := by decide
  rcases family_descends (prefixWord ++ tailWord_105564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105609 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 6]
def baseStart_105609 : Nat := 118140960795 + 105609 * 2 ^ 59
def prefixEnd_105609 : Nat := 4983230072969 + 3 ^ 40 * 105609 * 2
def baseEnd_105609 : Nat := 24101412640347794667475

theorem tailTrace_105609 : CollatzResearch.WordTrace tailWord_105609 prefixEnd_105609 24101412640347794667475 := by
  unfold tailWord_105609
  simp only [CollatzResearch.WordTrace]
  refine ⟨3851876674404104426343881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2567917782936069617562587 3851876674404104426343881)
  ·
    refine ⟨2888907505803078319757911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3851876674404104426343881 2888907505803078319757911)
    ·
      refine ⟨4333361258704617479636867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2888907505803078319757911 4333361258704617479636867)
      ·
        refine ⟨6500041888056926219455301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4333361258704617479636867 6500041888056926219455301)
        ·
          refine ⟨1218757854010673666147869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6500041888056926219455301 1218757854010673666147869)
          ·
            refine ⟨457034195254002624805451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1218757854010673666147869 457034195254002624805451)
            ·
              refine ⟨685551292881003937208177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457034195254002624805451 685551292881003937208177)
              ·
                refine ⟨514163469660752952906133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 685551292881003937208177 514163469660752952906133)
                ·
                  refine ⟨24101412640347794667475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 514163469660752952906133 24101412640347794667475)
                  ·
                    rfl

theorem cell21_105609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_105609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105609 prefixEnd_105609 := by exact prefixLift 105609
  have htrace : WordTrace (prefixWord ++ tailWord_105609) baseStart_105609 baseEnd_105609 := by
    simpa [prefixWord, tailWord_105609, baseEnd_105609] using wordTrace_append hprefix tailTrace_105609
  have hstable : (prefixWord ++ tailWord_105609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105609).length < 2 ^ (prefixWord ++ tailWord_105609).sum := by decide
  have hdescent : baseEnd_105609 < baseStart_105609 := by decide
  rcases family_descends (prefixWord ++ tailWord_105609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105626 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_105626 : Nat := 118140960795 + 105626 * 2 ^ 59
def prefixEnd_105626 : Nat := 4983230072969 + 3 ^ 40 * 105626 * 2
def baseEnd_105626 : Nat := 24105292271959542884107

theorem tailTrace_105626 : CollatzResearch.WordTrace tailWord_105626 prefixEnd_105626 24105292271959542884107 := by
  unfold tailWord_105626
  simp only [CollatzResearch.WordTrace]
  refine ⟨963124178835629082428183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2568331143561677553141821 963124178835629082428183)
  ·
    refine ⟨1444686268253443623642275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 963124178835629082428183 1444686268253443623642275)
    ·
      refine ⟨2167029402380165435463413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444686268253443623642275 2167029402380165435463413)
      ·
        refine ⟨203159006473140509574695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2167029402380165435463413 203159006473140509574695)
        ·
          refine ⟨304738509709710764362043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203159006473140509574695 304738509709710764362043)
          ·
            refine ⟨457107764564566146543065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304738509709710764362043 457107764564566146543065)
            ·
              refine ⟨342830823423424609907299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457107764564566146543065 342830823423424609907299)
              ·
                refine ⟨514246235135136914860949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342830823423424609907299 514246235135136914860949)
                ·
                  refine ⟨24105292271959542884107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 514246235135136914860949 24105292271959542884107)
                  ·
                    rfl

theorem cell21_105626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_105626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105626 prefixEnd_105626 := by exact prefixLift 105626
  have htrace : WordTrace (prefixWord ++ tailWord_105626) baseStart_105626 baseEnd_105626 := by
    simpa [prefixWord, tailWord_105626, baseEnd_105626] using wordTrace_append hprefix tailTrace_105626
  have hstable : (prefixWord ++ tailWord_105626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105626).length < 2 ^ (prefixWord ++ tailWord_105626).sum := by decide
  have hdescent : baseEnd_105626 < baseStart_105626 := by decide
  rcases family_descends (prefixWord ++ tailWord_105626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105629 : List Nat := [1, 4, 2, 1, 1, 2, 5, 2, 3]
def baseStart_105629 : Nat := 118140960795 + 105629 * 2 ^ 59
def prefixEnd_105629 : Nat := 4983230072969 + 3 ^ 40 * 105629 * 2
def baseEnd_105629 : Nat := 24105976912832204334101

theorem tailTrace_105629 : CollatzResearch.WordTrace tailWord_105629 prefixEnd_105629 24105976912832204334101 := by
  unfold tailWord_105629
  simp only [CollatzResearch.WordTrace]
  refine ⟨3852606134331647842071941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2568404089554431894714627 3852606134331647842071941)
  ·
    refine ⟨722363650187183970388489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3852606134331647842071941 722363650187183970388489)
    ·
      refine ⟨541772737640387977791367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 722363650187183970388489 541772737640387977791367)
      ·
        refine ⟨812659106460581966687051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541772737640387977791367 812659106460581966687051)
        ·
          refine ⟨1218988659690872950030577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812659106460581966687051 1218988659690872950030577)
          ·
            refine ⟨914241494768154712522933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218988659690872950030577 914241494768154712522933)
            ·
              refine ⟨85710140134514504299025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 914241494768154712522933 85710140134514504299025)
              ·
                refine ⟨64282605100885878224269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85710140134514504299025 64282605100885878224269)
                ·
                  refine ⟨24105976912832204334101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64282605100885878224269 24105976912832204334101)
                  ·
                    rfl

theorem cell21_105629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_105629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105629 prefixEnd_105629 := by exact prefixLift 105629
  have htrace : WordTrace (prefixWord ++ tailWord_105629) baseStart_105629 baseEnd_105629 := by
    simpa [prefixWord, tailWord_105629, baseEnd_105629] using wordTrace_append hprefix tailTrace_105629
  have hstable : (prefixWord ++ tailWord_105629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105629).length < 2 ^ (prefixWord ++ tailWord_105629).sum := by decide
  have hdescent : baseEnd_105629 < baseStart_105629 := by decide
  rcases family_descends (prefixWord ++ tailWord_105629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105677 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 4]
def baseStart_105677 : Nat := 118140960795 + 105677 * 2 ^ 59
def prefixEnd_105677 : Nat := 4983230072969 + 3 ^ 40 * 105677 * 2
def baseEnd_105677 : Nat := 24116931166794787534003

theorem tailTrace_105677 : CollatzResearch.WordTrace tailWord_105677 prefixEnd_105677 24116931166794787534003 := by
  unfold tailWord_105677
  simp only [CollatzResearch.WordTrace]
  refine ⟨3854356838157752039819285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2569571225438501359879523 3854356838157752039819285)
  ·
    refine ⟨180672976788644626866529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3854356838157752039819285 180672976788644626866529)
    ·
      refine ⟨135504732591483470149897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180672976788644626866529 135504732591483470149897)
      ·
        refine ⟨101628549443612602612423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135504732591483470149897 101628549443612602612423)
        ·
          refine ⟨152442824165418903918635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101628549443612602612423 152442824165418903918635)
          ·
            refine ⟨228664236248128355877953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152442824165418903918635 228664236248128355877953)
            ·
              refine ⟨171498177186096266908465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228664236248128355877953 171498177186096266908465)
              ·
                refine ⟨128623632889572200181349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171498177186096266908465 128623632889572200181349)
                ·
                  refine ⟨24116931166794787534003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128623632889572200181349 24116931166794787534003)
                  ·
                    rfl

theorem cell21_105677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_105677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105677 prefixEnd_105677 := by exact prefixLift 105677
  have htrace : WordTrace (prefixWord ++ tailWord_105677) baseStart_105677 baseEnd_105677 := by
    simpa [prefixWord, tailWord_105677, baseEnd_105677] using wordTrace_append hprefix tailTrace_105677
  have hstable : (prefixWord ++ tailWord_105677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105677).length < 2 ^ (prefixWord ++ tailWord_105677).sum := by decide
  have hdescent : baseEnd_105677 < baseStart_105677 := by decide
  rcases family_descends (prefixWord ++ tailWord_105677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105736 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 4]
def baseStart_105736 : Nat := 118140960795 + 105736 * 2 ^ 59
def prefixEnd_105736 : Nat := 4983230072969 + 3 ^ 40 * 105736 * 2
def baseEnd_105736 : Nat := 24130395770623796050549

theorem tailTrace_105736 : CollatzResearch.WordTrace tailWord_105736 prefixEnd_105736 24130395770623796050549 := by
  unfold tailWord_105736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928254372472002558108531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2571005829962670077478041 1928254372472002558108531)
  ·
    refine ⟨2892381558708003837162797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1928254372472002558108531 2892381558708003837162797)
    ·
      refine ⟨1084643084515501438936049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2892381558708003837162797 1084643084515501438936049)
      ·
        refine ⟨813482313386626079202037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1084643084515501438936049 813482313386626079202037)
        ·
          refine ⟨76263966879996194925191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 813482313386626079202037 76263966879996194925191)
          ·
            refine ⟨114395950319994292387787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76263966879996194925191 114395950319994292387787)
            ·
              refine ⟨171593925479991438581681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114395950319994292387787 171593925479991438581681)
              ·
                refine ⟨128695444109993578936261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171593925479991438581681 128695444109993578936261)
                ·
                  refine ⟨24130395770623796050549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128695444109993578936261 24130395770623796050549)
                  ·
                    rfl

theorem cell21_105736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 4].length) (baseStart_105736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105736 prefixEnd_105736 := by exact prefixLift 105736
  have htrace : WordTrace (prefixWord ++ tailWord_105736) baseStart_105736 baseEnd_105736 := by
    simpa [prefixWord, tailWord_105736, baseEnd_105736] using wordTrace_append hprefix tailTrace_105736
  have hstable : (prefixWord ++ tailWord_105736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105736).length < 2 ^ (prefixWord ++ tailWord_105736).sum := by decide
  have hdescent : baseEnd_105736 < baseStart_105736 := by decide
  rcases family_descends (prefixWord ++ tailWord_105736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105781 : List Nat := [1, 3, 3, 1, 2, 4, 1, 3, 3]
def baseStart_105781 : Nat := 118140960795 + 105781 * 2 ^ 59
def prefixEnd_105781 : Nat := 4983230072969 + 3 ^ 40 * 105781 * 2
def baseEnd_105781 : Nat := 24140665383713717800457

theorem tailTrace_105781 : CollatzResearch.WordTrace tailWord_105781 prefixEnd_105781 24140665383713717800457 := by
  unfold tailWord_105781
  simp only [CollatzResearch.WordTrace]
  refine ⟨3858150029780977801605197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2572100019853985201070131 3858150029780977801605197)
  ·
    refine ⟨1446806261167866675601949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3858150029780977801605197 1446806261167866675601949)
    ·
      refine ⟨542552347937950003350731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1446806261167866675601949 542552347937950003350731)
      ·
        refine ⟨813828521906925005026097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542552347937950003350731 813828521906925005026097)
        ·
          refine ⟨610371391430193753769573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813828521906925005026097 610371391430193753769573)
          ·
            refine ⟨114444635893161328831795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 610371391430193753769573 114444635893161328831795)
            ·
              refine ⟨171666953839741993247693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114444635893161328831795 171666953839741993247693)
              ·
                refine ⟨64375107689903247467885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171666953839741993247693 64375107689903247467885)
                ·
                  refine ⟨24140665383713717800457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64375107689903247467885 24140665383713717800457)
                  ·
                    rfl

theorem cell21_105781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_105781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105781 prefixEnd_105781 := by exact prefixLift 105781
  have htrace : WordTrace (prefixWord ++ tailWord_105781) baseStart_105781 baseEnd_105781 := by
    simpa [prefixWord, tailWord_105781, baseEnd_105781] using wordTrace_append hprefix tailTrace_105781
  have hstable : (prefixWord ++ tailWord_105781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105781).length < 2 ^ (prefixWord ++ tailWord_105781).sum := by decide
  have hdescent : baseEnd_105781 < baseStart_105781 := by decide
  rcases family_descends (prefixWord ++ tailWord_105781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105857 : List Nat := [1, 2, 4, 3, 2, 1, 1, 4, 3]
def baseStart_105857 : Nat := 118140960795 + 105857 * 2 ^ 59
def prefixEnd_105857 : Nat := 4983230072969 + 3 ^ 40 * 105857 * 2
def baseEnd_105857 : Nat := 24158009619154474533635

theorem tailTrace_105857 : CollatzResearch.WordTrace tailWord_105857 prefixEnd_105857 24158009619154474533635 := by
  unfold tailWord_105857
  simp only [CollatzResearch.WordTrace]
  refine ⟨3860921977505642781371825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2573947985003761854247883 3860921977505642781371825)
  ·
    refine ⟨2895691483129232086028869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3860921977505642781371825 2895691483129232086028869)
    ·
      refine ⟨542942153086731016130413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2895691483129232086028869 542942153086731016130413)
      ·
        refine ⟨203603307407524131048905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542942153086731016130413 203603307407524131048905)
        ·
          refine ⟨152702480555643098286679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203603307407524131048905 152702480555643098286679)
          ·
            refine ⟨229053720833464647430019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152702480555643098286679 229053720833464647430019)
            ·
              refine ⟨343580581250196971145029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229053720833464647430019 343580581250196971145029)
              ·
                refine ⟨64421358984411932089693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343580581250196971145029 64421358984411932089693)
                ·
                  refine ⟨24158009619154474533635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64421358984411932089693 24158009619154474533635)
                  ·
                    rfl

theorem cell21_105857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 3].length) (baseStart_105857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105857 prefixEnd_105857 := by exact prefixLift 105857
  have htrace : WordTrace (prefixWord ++ tailWord_105857) baseStart_105857 baseEnd_105857 := by
    simpa [prefixWord, tailWord_105857, baseEnd_105857] using wordTrace_append hprefix tailTrace_105857
  have hstable : (prefixWord ++ tailWord_105857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105857).length < 2 ^ (prefixWord ++ tailWord_105857).sum := by decide
  have hdescent : baseEnd_105857 < baseStart_105857 := by decide
  rcases family_descends (prefixWord ++ tailWord_105857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105885 : List Nat := [1, 4, 2, 1, 3, 2, 3, 5]
def baseStart_105885 : Nat := 118140960795 + 105885 * 2 ^ 59
def prefixEnd_105885 : Nat := 4983230072969 + 3 ^ 40 * 105885 * 2
def baseEnd_105885 : Nat := 8054799866877549355637

theorem tailTrace_105885 : CollatzResearch.WordTrace tailWord_105885 prefixEnd_105885 8054799866877549355637 := by
  unfold tailWord_105885
  simp only [CollatzResearch.WordTrace]
  refine ⟨3861943221404203563391109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2574628814269469042260739 3861943221404203563391109)
  ·
    refine ⟨724114354013288168135833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3861943221404203563391109 724114354013288168135833)
    ·
      refine ⟨543085765509966126101875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 724114354013288168135833 543085765509966126101875)
      ·
        refine ⟨814628648264949189152813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543085765509966126101875 814628648264949189152813)
        ·
          refine ⟨305485743099355945932305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814628648264949189152813 305485743099355945932305)
          ·
            refine ⟨229114307324516959449229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305485743099355945932305 229114307324516959449229)
            ·
              refine ⟨85917865246693859793461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229114307324516959449229 85917865246693859793461)
              ·
                refine ⟨8054799866877549355637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85917865246693859793461 8054799866877549355637)
                ·
                  rfl

theorem cell21_105885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 5].length) (baseStart_105885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105885 prefixEnd_105885 := by exact prefixLift 105885
  have htrace : WordTrace (prefixWord ++ tailWord_105885) baseStart_105885 baseEnd_105885 := by
    simpa [prefixWord, tailWord_105885, baseEnd_105885] using wordTrace_append hprefix tailTrace_105885
  have hstable : (prefixWord ++ tailWord_105885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105885).length < 2 ^ (prefixWord ++ tailWord_105885).sum := by decide
  have hdescent : baseEnd_105885 < baseStart_105885 := by decide
  rcases family_descends (prefixWord ++ tailWord_105885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105916 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 5]
def baseStart_105916 : Nat := 118140960795 + 105916 * 2 ^ 59
def prefixEnd_105916 : Nat := 4983230072969 + 3 ^ 40 * 105916 * 2
def baseEnd_105916 : Nat := 24171474222983483050181

theorem tailTrace_105916 : CollatzResearch.WordTrace tailWord_105916 prefixEnd_105916 24171474222983483050181 := by
  unfold tailWord_105916
  simp only [CollatzResearch.WordTrace]
  refine ⟨1931536942145947928884801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2575382589527930571846401 1931536942145947928884801)
  ·
    refine ⟨1448652706609460946663601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1931536942145947928884801 1448652706609460946663601)
    ·
      refine ⟨1086489529957095709997701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1448652706609460946663601 1086489529957095709997701)
      ·
        refine ⟨203716786866955445624569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1086489529957095709997701 203716786866955445624569)
        ·
          refine ⟨152787590150216584218427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203716786866955445624569 152787590150216584218427)
          ·
            refine ⟨229181385225324876327641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152787590150216584218427 229181385225324876327641)
            ·
              refine ⟨171886038918993657245731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229181385225324876327641 171886038918993657245731)
              ·
                refine ⟨257829058378490485868597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171886038918993657245731 257829058378490485868597)
                ·
                  refine ⟨24171474222983483050181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257829058378490485868597 24171474222983483050181)
                  ·
                    rfl

theorem cell21_105916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_105916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105916 prefixEnd_105916 := by exact prefixLift 105916
  have htrace : WordTrace (prefixWord ++ tailWord_105916) baseStart_105916 baseEnd_105916 := by
    simpa [prefixWord, tailWord_105916, baseEnd_105916] using wordTrace_append hprefix tailTrace_105916
  have hstable : (prefixWord ++ tailWord_105916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105916).length < 2 ^ (prefixWord ++ tailWord_105916).sum := by decide
  have hdescent : baseEnd_105916 < baseStart_105916 := by decide
  rcases family_descends (prefixWord ++ tailWord_105916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105927 : List Nat := [1, 1, 4, 1, 1, 3, 2, 8]
def baseStart_105927 : Nat := 118140960795 + 105927 * 2 ^ 59
def prefixEnd_105927 : Nat := 4983230072969 + 3 ^ 40 * 105927 * 2
def baseEnd_105927 : Nat := 8057994857616636122275

theorem tailTrace_105927 : CollatzResearch.WordTrace tailWord_105927 prefixEnd_105927 8057994857616636122275 := by
  unfold tailWord_105927
  simp only [CollatzResearch.WordTrace]
  refine ⟨3863475087252044736420035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2575650058168029824280023 3863475087252044736420035)
  ·
    refine ⟨5795212630878067104630053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3863475087252044736420035 5795212630878067104630053)
    ·
      refine ⟨1086602368289637582118135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5795212630878067104630053 1086602368289637582118135)
      ·
        refine ⟨1629903552434456373177203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086602368289637582118135 1629903552434456373177203)
        ·
          refine ⟨2444855328651684559765805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629903552434456373177203 2444855328651684559765805)
          ·
            refine ⟨916820748244381709912177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2444855328651684559765805 916820748244381709912177)
            ·
              refine ⟨687615561183286282434133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 916820748244381709912177 687615561183286282434133)
              ·
                refine ⟨8057994857616636122275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 687615561183286282434133 8057994857616636122275)
                ·
                  rfl

theorem cell21_105927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 8].length) (baseStart_105927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105927 prefixEnd_105927 := by exact prefixLift 105927
  have htrace : WordTrace (prefixWord ++ tailWord_105927) baseStart_105927 baseEnd_105927 := by
    simpa [prefixWord, tailWord_105927, baseEnd_105927] using wordTrace_append hprefix tailTrace_105927
  have hstable : (prefixWord ++ tailWord_105927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105927).length < 2 ^ (prefixWord ++ tailWord_105927).sum := by decide
  have hdescent : baseEnd_105927 < baseStart_105927 := by decide
  rcases family_descends (prefixWord ++ tailWord_105927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105944 : List Nat := [2, 1, 2, 2, 2, 1, 6, 5]
def baseStart_105944 : Nat := 118140960795 + 105944 * 2 ^ 59
def prefixEnd_105944 : Nat := 4983230072969 + 3 ^ 40 * 105944 * 2
def baseEnd_105944 : Nat := 8059288068153885527819

theorem tailTrace_105944 : CollatzResearch.WordTrace tailWord_105944 prefixEnd_105944 8059288068153885527819 := by
  unfold tailWord_105944
  simp only [CollatzResearch.WordTrace]
  refine ⟨1932047564095228319894443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2576063418793637759859257 1932047564095228319894443)
  ·
    refine ⟨2898071346142842479841665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1932047564095228319894443 2898071346142842479841665)
    ·
      refine ⟨2173553509607131859881249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2898071346142842479841665 2173553509607131859881249)
      ·
        refine ⟨1630165132205348894910937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2173553509607131859881249 1630165132205348894910937)
        ·
          refine ⟨1222623849154011671183203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1630165132205348894910937 1222623849154011671183203)
          ·
            refine ⟨1833935773731017506774805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222623849154011671183203 1833935773731017506774805)
            ·
              refine ⟨85965739393641445630069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1833935773731017506774805 85965739393641445630069)
              ·
                refine ⟨8059288068153885527819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85965739393641445630069 8059288068153885527819)
                ·
                  rfl

theorem cell21_105944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_105944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_105944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_105944 prefixEnd_105944 := by exact prefixLift 105944
  have htrace : WordTrace (prefixWord ++ tailWord_105944) baseStart_105944 baseEnd_105944 := by
    simpa [prefixWord, tailWord_105944, baseEnd_105944] using wordTrace_append hprefix tailTrace_105944
  have hstable : (prefixWord ++ tailWord_105944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105944).length < 2 ^ (prefixWord ++ tailWord_105944).sum := by decide
  have hdescent : baseEnd_105944 < baseStart_105944 := by decide
  rcases family_descends (prefixWord ++ tailWord_105944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106003 : List Nat := [1, 1, 1, 2, 1, 6, 2, 7]
def baseStart_106003 : Nat := 118140960795 + 106003 * 2 ^ 59
def prefixEnd_106003 : Nat := 4983230072969 + 3 ^ 40 * 106003 * 2
def baseEnd_106003 : Nat := 8063776269430221700001

theorem tailTrace_106003 : CollatzResearch.WordTrace tailWord_106003 prefixEnd_106003 8063776269430221700001 := by
  unfold tailWord_106003
  simp only [CollatzResearch.WordTrace]
  refine ⟨3866247034976709716186663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2577498023317806477457775 3866247034976709716186663)
  ·
    refine ⟨5799370552465064574279995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3866247034976709716186663 5799370552465064574279995)
    ·
      refine ⟨8699055828697596861419993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5799370552465064574279995 8699055828697596861419993)
      ·
        refine ⟨6524291871523197646064995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8699055828697596861419993 6524291871523197646064995)
        ·
          refine ⟨9786437807284796469097493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6524291871523197646064995 9786437807284796469097493)
          ·
            refine ⟨458739272216474834488945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9786437807284796469097493 458739272216474834488945)
            ·
              refine ⟨344054454162356125866709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458739272216474834488945 344054454162356125866709)
              ·
                refine ⟨8063776269430221700001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 344054454162356125866709 8063776269430221700001)
                ·
                  rfl

theorem cell21_106003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 7].length) (baseStart_106003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106003 prefixEnd_106003 := by exact prefixLift 106003
  have htrace : WordTrace (prefixWord ++ tailWord_106003) baseStart_106003 baseEnd_106003 := by
    simpa [prefixWord, tailWord_106003, baseEnd_106003] using wordTrace_append hprefix tailTrace_106003
  have hstable : (prefixWord ++ tailWord_106003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106003).length < 2 ^ (prefixWord ++ tailWord_106003).sum := by decide
  have hdescent : baseEnd_106003 < baseStart_106003 := by decide
  rcases family_descends (prefixWord ++ tailWord_106003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106034 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_106034 : Nat := 118140960795 + 106034 * 2 ^ 59
def prefixEnd_106034 : Nat := 4983230072969 + 3 ^ 40 * 106034 * 2
def baseEnd_106034 : Nat := 24198403430641500083273

theorem tailTrace_106034 : CollatzResearch.WordTrace tailWord_106034 prefixEnd_106034 24198403430641500083273 := by
  unfold tailWord_106034
  simp only [CollatzResearch.WordTrace]
  refine ⟨966844424466100502641289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2578251798576268007043437 966844424466100502641289)
  ·
    refine ⟨725133318349575376980967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 966844424466100502641289 725133318349575376980967)
    ·
      refine ⟨1087699977524363065471451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 725133318349575376980967 1087699977524363065471451)
      ·
        refine ⟨1631549966286544598207177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087699977524363065471451 1631549966286544598207177)
        ·
          refine ⟨1223662474714908448655383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1631549966286544598207177 1223662474714908448655383)
          ·
            refine ⟨1835493712072362672983075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223662474714908448655383 1835493712072362672983075)
            ·
              refine ⟨2753240568108544009474613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835493712072362672983075 2753240568108544009474613)
              ·
                refine ⟨258116303260176000888245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2753240568108544009474613 258116303260176000888245)
                ·
                  refine ⟨24198403430641500083273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 258116303260176000888245 24198403430641500083273)
                  ·
                    rfl

theorem cell21_106034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_106034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106034 prefixEnd_106034 := by exact prefixLift 106034
  have htrace : WordTrace (prefixWord ++ tailWord_106034) baseStart_106034 baseEnd_106034 := by
    simpa [prefixWord, tailWord_106034, baseEnd_106034] using wordTrace_append hprefix tailTrace_106034
  have hstable : (prefixWord ++ tailWord_106034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106034).length < 2 ^ (prefixWord ++ tailWord_106034).sum := by decide
  have hdescent : baseEnd_106034 < baseStart_106034 := by decide
  rcases family_descends (prefixWord ++ tailWord_106034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106048 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_106048 : Nat := 118140960795 + 106048 * 2 ^ 59
def prefixEnd_106048 : Nat := 4983230072969 + 3 ^ 40 * 106048 * 2
def baseEnd_106048 : Nat := 24201598421380586849911

theorem tailTrace_106048 : CollatzResearch.WordTrace tailWord_106048 prefixEnd_106048 24201598421380586849911 := by
  unfold tailWord_106048
  simp only [CollatzResearch.WordTrace]
  refine ⟨1933944159906841200787399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2578592213209121601049865 1933944159906841200787399)
  ·
    refine ⟨2900916239860261801181099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1933944159906841200787399 2900916239860261801181099)
    ·
      refine ⟨4351374359790392701771649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2900916239860261801181099 4351374359790392701771649)
      ·
        refine ⟨3263530769842794526328737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4351374359790392701771649 3263530769842794526328737)
        ·
          refine ⟨2447648077382095894746553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3263530769842794526328737 2447648077382095894746553)
          ·
            refine ⟨1835736058036571921059915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2447648077382095894746553 1835736058036571921059915)
            ·
              refine ⟨2753604087054857881589873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835736058036571921059915 2753604087054857881589873)
              ·
                refine ⟨2065203065291143411192405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2753604087054857881589873 2065203065291143411192405)
                ·
                  refine ⟨24201598421380586849911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2065203065291143411192405 24201598421380586849911)
                  ·
                    rfl

theorem cell21_106048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_106048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106048 prefixEnd_106048 := by exact prefixLift 106048
  have htrace : WordTrace (prefixWord ++ tailWord_106048) baseStart_106048 baseEnd_106048 := by
    simpa [prefixWord, tailWord_106048, baseEnd_106048] using wordTrace_append hprefix tailTrace_106048
  have hstable : (prefixWord ++ tailWord_106048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106048).length < 2 ^ (prefixWord ++ tailWord_106048).sum := by decide
  have hdescent : baseEnd_106048 < baseStart_106048 := by decide
  rcases family_descends (prefixWord ++ tailWord_106048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106068 : List Nat := [2, 4, 1, 1, 1, 2, 4, 3, 3]
def baseStart_106068 : Nat := 118140960795 + 106068 * 2 ^ 59
def prefixEnd_106068 : Nat := 4983230072969 + 3 ^ 40 * 106068 * 2
def baseEnd_106068 : Nat := 24206162693864996516537

theorem tailTrace_106068 : CollatzResearch.WordTrace tailWord_106068 prefixEnd_106068 24206162693864996516537 := by
  unfold tailWord_106068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1934308889870612908651429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2579078519827483878201905 1934308889870612908651429)
  ·
    refine ⟨362682916850739920372143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1934308889870612908651429 362682916850739920372143)
    ·
      refine ⟨544024375276109880558215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362682916850739920372143 544024375276109880558215)
      ·
        refine ⟨816036562914164820837323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544024375276109880558215 816036562914164820837323)
        ·
          refine ⟨1224054844371247231255985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816036562914164820837323 1224054844371247231255985)
          ·
            refine ⟨918041133278435423441989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1224054844371247231255985 918041133278435423441989)
            ·
              refine ⟨172132712489706641895373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 918041133278435423441989 172132712489706641895373)
              ·
                refine ⟨64549767183639990710765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172132712489706641895373 64549767183639990710765)
                ·
                  refine ⟨24206162693864996516537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64549767183639990710765 24206162693864996516537)
                  ·
                    rfl

theorem cell21_106068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_106068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106068 prefixEnd_106068 := by exact prefixLift 106068
  have htrace : WordTrace (prefixWord ++ tailWord_106068) baseStart_106068 baseEnd_106068 := by
    simpa [prefixWord, tailWord_106068, baseEnd_106068] using wordTrace_append hprefix tailTrace_106068
  have hstable : (prefixWord ++ tailWord_106068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106068).length < 2 ^ (prefixWord ++ tailWord_106068).sum := by decide
  have hdescent : baseEnd_106068 < baseStart_106068 := by decide
  rcases family_descends (prefixWord ++ tailWord_106068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106113 : List Nat := [1, 2, 4, 2, 1, 4, 2, 5]
def baseStart_106113 : Nat := 118140960795 + 106113 * 2 ^ 59
def prefixEnd_106113 : Nat := 4983230072969 + 3 ^ 40 * 106113 * 2
def baseEnd_106113 : Nat := 8072144102318306088815

theorem tailTrace_106113 : CollatzResearch.WordTrace tailWord_106113 prefixEnd_106113 8072144102318306088815 := by
  unfold tailWord_106113
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870259064578198502690993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2580172709718799001793995 3870259064578198502690993)
  ·
    refine ⟨2902694298433648877018245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3870259064578198502690993 2902694298433648877018245)
    ·
      refine ⟨544255180956309164440921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2902694298433648877018245 544255180956309164440921)
      ·
        refine ⟨408191385717231873330691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544255180956309164440921 408191385717231873330691)
        ·
          refine ⟨612287078575847809996037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408191385717231873330691 612287078575847809996037)
          ·
            refine ⟨114803827232971464374257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 612287078575847809996037 114803827232971464374257)
            ·
              refine ⟨86102870424728598280693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114803827232971464374257 86102870424728598280693)
              ·
                refine ⟨8072144102318306088815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86102870424728598280693 8072144102318306088815)
                ·
                  rfl

theorem cell21_106113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 5].length) (baseStart_106113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106113 prefixEnd_106113 := by exact prefixLift 106113
  have htrace : WordTrace (prefixWord ++ tailWord_106113) baseStart_106113 baseEnd_106113 := by
    simpa [prefixWord, tailWord_106113, baseEnd_106113] using wordTrace_append hprefix tailTrace_106113
  have hstable : (prefixWord ++ tailWord_106113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106113).length < 2 ^ (prefixWord ++ tailWord_106113).sum := by decide
  have hdescent : baseEnd_106113 < baseStart_106113 := by decide
  rcases family_descends (prefixWord ++ tailWord_106113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106124 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_106124 : Nat := 118140960795 + 106124 * 2 ^ 59
def prefixEnd_106124 : Nat := 4983230072969 + 3 ^ 40 * 106124 * 2
def baseEnd_106124 : Nat := 24218942656821343583089

theorem tailTrace_106124 : CollatzResearch.WordTrace tailWord_106124 prefixEnd_106124 24218942656821343583089 := by
  unfold tailWord_106124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935330133769173690670713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2580440178358898254227617 1935330133769173690670713)
  ·
    refine ⟨1451497600326880268003035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1935330133769173690670713 1451497600326880268003035)
    ·
      refine ⟨2177246400490320402004553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1451497600326880268003035 2177246400490320402004553)
      ·
        refine ⟨1632934800367740301503415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2177246400490320402004553 1632934800367740301503415)
        ·
          refine ⟨2449402200551610452255123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632934800367740301503415 2449402200551610452255123)
          ·
            refine ⟨3674103300827415678382685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449402200551610452255123 3674103300827415678382685)
            ·
              refine ⟨1377788737810280879393507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3674103300827415678382685 1377788737810280879393507)
              ·
                refine ⟨2066683106715421319090261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377788737810280879393507 2066683106715421319090261)
                ·
                  refine ⟨24218942656821343583089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2066683106715421319090261 24218942656821343583089)
                  ·
                    rfl

theorem cell21_106124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_106124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106124 prefixEnd_106124 := by exact prefixLift 106124
  have htrace : WordTrace (prefixWord ++ tailWord_106124) baseStart_106124 baseEnd_106124 := by
    simpa [prefixWord, tailWord_106124, baseEnd_106124] using wordTrace_append hprefix tailTrace_106124
  have hstable : (prefixWord ++ tailWord_106124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106124).length < 2 ^ (prefixWord ++ tailWord_106124).sum := by decide
  have hdescent : baseEnd_106124 < baseStart_106124 := by decide
  rcases family_descends (prefixWord ++ tailWord_106124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106141 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 4]
def baseStart_106141 : Nat := 118140960795 + 106141 * 2 ^ 59
def prefixEnd_106141 : Nat := 4983230072969 + 3 ^ 40 * 106141 * 2
def baseEnd_106141 : Nat := 24222822288433091799721

theorem tailTrace_106141 : CollatzResearch.WordTrace tailWord_106141 prefixEnd_106141 24222822288433091799721 := by
  unfold tailWord_106141
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871280308476759284710277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2580853538984506189806851 3871280308476759284710277)
  ·
    refine ⟨725865057839392365883177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3871280308476759284710277 725865057839392365883177)
    ·
      refine ⟨544398793379544274412383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 725865057839392365883177 544398793379544274412383)
      ·
        refine ⟨816598190069316411618575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544398793379544274412383 816598190069316411618575)
        ·
          refine ⟨1224897285103974617427863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816598190069316411618575 1224897285103974617427863)
          ·
            refine ⟨1837345927655961926141795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224897285103974617427863 1837345927655961926141795)
            ·
              refine ⟨2756018891483942889212693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837345927655961926141795 2756018891483942889212693)
              ·
                refine ⟨129188385538309822931845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2756018891483942889212693 129188385538309822931845)
                ·
                  refine ⟨24222822288433091799721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129188385538309822931845 24222822288433091799721)
                  ·
                    rfl

theorem cell21_106141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_106141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106141 prefixEnd_106141 := by exact prefixLift 106141
  have htrace : WordTrace (prefixWord ++ tailWord_106141) baseStart_106141 baseEnd_106141 := by
    simpa [prefixWord, tailWord_106141, baseEnd_106141] using wordTrace_append hprefix tailTrace_106141
  have hstable : (prefixWord ++ tailWord_106141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106141).length < 2 ^ (prefixWord ++ tailWord_106141).sum := by decide
  have hdescent : baseEnd_106141 < baseStart_106141 := by decide
  rcases family_descends (prefixWord ++ tailWord_106141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106296 : List Nat := [2, 1, 2, 1, 3, 5, 1, 3, 3]
def baseStart_106296 : Nat := 118140960795 + 106296 * 2 ^ 59
def prefixEnd_106296 : Nat := 4983230072969 + 3 ^ 40 * 106296 * 2
def baseEnd_106296 : Nat := 24258195400187266716071

theorem tailTrace_106296 : CollatzResearch.WordTrace tailWord_106296 prefixEnd_106296 24258195400187266716071 := by
  unfold tailWord_106296
  simp only [CollatzResearch.WordTrace]
  refine ⟨1938466811457610378301371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2584622415276813837735161 1938466811457610378301371)
  ·
    refine ⟨2907700217186415567452057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1938466811457610378301371 2907700217186415567452057)
    ·
      refine ⟨2180775162889811675589043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2907700217186415567452057 2180775162889811675589043)
      ·
        refine ⟨3271162744334717513383565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2180775162889811675589043 3271162744334717513383565)
        ·
          refine ⟨1226686029125519067518837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3271162744334717513383565 1226686029125519067518837)
          ·
            refine ⟨115001815230517412579891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1226686029125519067518837 115001815230517412579891)
            ·
              refine ⟨172502722845776118869837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115001815230517412579891 172502722845776118869837)
              ·
                refine ⟨64688521067166044576189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172502722845776118869837 64688521067166044576189)
                ·
                  refine ⟨24258195400187266716071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64688521067166044576189 24258195400187266716071)
                  ·
                    rfl

theorem cell21_106296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 3].length) (baseStart_106296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106296 prefixEnd_106296 := by exact prefixLift 106296
  have htrace : WordTrace (prefixWord ++ tailWord_106296) baseStart_106296 baseEnd_106296 := by
    simpa [prefixWord, tailWord_106296, baseEnd_106296] using wordTrace_append hprefix tailTrace_106296
  have hstable : (prefixWord ++ tailWord_106296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106296).length < 2 ^ (prefixWord ++ tailWord_106296).sum := by decide
  have hdescent : baseEnd_106296 < baseStart_106296 := by decide
  rcases family_descends (prefixWord ++ tailWord_106296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106307 : List Nat := [1, 1, 1, 3, 1, 7, 7]
def baseStart_106307 : Nat := 118140960795 + 106307 * 2 ^ 59
def prefixEnd_106307 : Nat := 4983230072969 + 3 ^ 40 * 106307 * 2
def baseEnd_106307 : Nat := 2695633972228188003635

theorem tailTrace_106307 : CollatzResearch.WordTrace tailWord_106307 prefixEnd_106307 2695633972228188003635 := by
  unfold tailWord_106307
  simp only [CollatzResearch.WordTrace]
  refine ⟨3877334825875369635253175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2584889883916913090168783 3877334825875369635253175)
  ·
    refine ⟨5816002238813054452879763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3877334825875369635253175 5816002238813054452879763)
    ·
      refine ⟨8724003358219581679319645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5816002238813054452879763 8724003358219581679319645)
      ·
        refine ⟨3271501259332343129744867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8724003358219581679319645 3271501259332343129744867)
        ·
          refine ⟨4907251888998514694617301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271501259332343129744867 4907251888998514694617301)
          ·
            refine ⟨115013716148402688155093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4907251888998514694617301 115013716148402688155093)
            ·
              refine ⟨2695633972228188003635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 115013716148402688155093 2695633972228188003635)
              ·
                rfl

theorem cell21_106307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 7].length) (baseStart_106307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106307 prefixEnd_106307 := by exact prefixLift 106307
  have htrace : WordTrace (prefixWord ++ tailWord_106307) baseStart_106307 baseEnd_106307 := by
    simpa [prefixWord, tailWord_106307, baseEnd_106307] using wordTrace_append hprefix tailTrace_106307
  have hstable : (prefixWord ++ tailWord_106307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106307).length < 2 ^ (prefixWord ++ tailWord_106307).sum := by decide
  have hdescent : baseEnd_106307 < baseStart_106307 := by decide
  rcases family_descends (prefixWord ++ tailWord_106307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106324 : List Nat := [2, 4, 1, 1, 3, 2, 2, 6]
def baseStart_106324 : Nat := 118140960795 + 106324 * 2 ^ 59
def prefixEnd_106324 : Nat := 4983230072969 + 3 ^ 40 * 106324 * 2
def baseEnd_106324 : Nat := 8088195127221813416449

theorem tailTrace_106324 : CollatzResearch.WordTrace tailWord_106324 prefixEnd_106324 8088195127221813416449 := by
  unfold tailWord_106324
  simp only [CollatzResearch.WordTrace]
  refine ⟨1938977433406890769311013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2585303244542521025748017 1938977433406890769311013)
  ·
    refine ⟨363558268763792019245815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1938977433406890769311013 363558268763792019245815)
    ·
      refine ⟨545337403145688028868723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363558268763792019245815 545337403145688028868723)
      ·
        refine ⟨818006104718532043303085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545337403145688028868723 818006104718532043303085)
        ·
          refine ⟨306752289269449516238657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 818006104718532043303085 306752289269449516238657)
          ·
            refine ⟨230064216952087137178993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306752289269449516238657 230064216952087137178993)
            ·
              refine ⟨172548162714065352884245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230064216952087137178993 172548162714065352884245)
              ·
                refine ⟨8088195127221813416449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172548162714065352884245 8088195127221813416449)
                ·
                  rfl

theorem cell21_106324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_106324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106324 prefixEnd_106324 := by exact prefixLift 106324
  have htrace : WordTrace (prefixWord ++ tailWord_106324) baseStart_106324 baseEnd_106324 := by
    simpa [prefixWord, tailWord_106324, baseEnd_106324] using wordTrace_append hprefix tailTrace_106324
  have hstable : (prefixWord ++ tailWord_106324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106324).length < 2 ^ (prefixWord ++ tailWord_106324).sum := by decide
  have hdescent : baseEnd_106324 < baseStart_106324 := by decide
  rcases family_descends (prefixWord ++ tailWord_106324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106327 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 4]
def baseStart_106327 : Nat := 118140960795 + 106327 * 2 ^ 59
def prefixEnd_106327 : Nat := 4983230072969 + 3 ^ 40 * 106327 * 2
def baseEnd_106327 : Nat := 24265270022538101699341

theorem tailTrace_106327 : CollatzResearch.WordTrace tailWord_106327 prefixEnd_106327 24265270022538101699341 := by
  unfold tailWord_106327
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878064285802913050981235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2585376190535275367320823 3878064285802913050981235)
  ·
    refine ⟨5817096428704369576471853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3878064285802913050981235 5817096428704369576471853)
    ·
      refine ⟨2181411160764138591176945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5817096428704369576471853 2181411160764138591176945)
      ·
        refine ⟨1636058370573103943382709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2181411160764138591176945 1636058370573103943382709)
        ·
          refine ⟨153380472241228494692129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1636058370573103943382709 153380472241228494692129)
          ·
            refine ⟨115035354180921371019097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153380472241228494692129 115035354180921371019097)
            ·
              refine ⟨86276515635691028264323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115035354180921371019097 86276515635691028264323)
              ·
                refine ⟨129414773453536542396485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86276515635691028264323 129414773453536542396485)
                ·
                  refine ⟨24265270022538101699341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129414773453536542396485 24265270022538101699341)
                  ·
                    rfl

theorem cell21_106327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 4].length) (baseStart_106327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106327 prefixEnd_106327 := by exact prefixLift 106327
  have htrace : WordTrace (prefixWord ++ tailWord_106327) baseStart_106327 baseEnd_106327 := by
    simpa [prefixWord, tailWord_106327, baseEnd_106327] using wordTrace_append hprefix tailTrace_106327
  have hstable : (prefixWord ++ tailWord_106327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106327).length < 2 ^ (prefixWord ++ tailWord_106327).sum := by decide
  have hdescent : baseEnd_106327 < baseStart_106327 := by decide
  rcases family_descends (prefixWord ++ tailWord_106327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106372 : List Nat := [2, 3, 2, 1, 1, 1, 6, 2, 3]
def baseStart_106372 : Nat := 118140960795 + 106372 * 2 ^ 59
def prefixEnd_106372 : Nat := 4983230072969 + 3 ^ 40 * 106372 * 2
def baseEnd_106372 : Nat := 24275539635628023449249

theorem tailTrace_106372 : CollatzResearch.WordTrace tailWord_106372 prefixEnd_106372 24275539635628023449249 := by
  unfold tailWord_106372
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939852785319942868184685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2586470380426590490912913 1939852785319942868184685)
  ·
    refine ⟨727444794494978575569257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1939852785319942868184685 727444794494978575569257)
    ·
      refine ⟨545583595871233931676943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 727444794494978575569257 545583595871233931676943)
      ·
        refine ⟨818375393806850897515415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545583595871233931676943 818375393806850897515415)
        ·
          refine ⟨1227563090710276346273123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818375393806850897515415 1227563090710276346273123)
          ·
            refine ⟨1841344636065414519409685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227563090710276346273123 1841344636065414519409685)
            ·
              refine ⟨86313029815566305597329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1841344636065414519409685 86313029815566305597329)
              ·
                refine ⟨64734772361674729197997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86313029815566305597329 64734772361674729197997)
                ·
                  refine ⟨24275539635628023449249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64734772361674729197997 24275539635628023449249)
                  ·
                    rfl

theorem cell21_106372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_106372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106372 prefixEnd_106372 := by exact prefixLift 106372
  have htrace : WordTrace (prefixWord ++ tailWord_106372) baseStart_106372 baseEnd_106372 := by
    simpa [prefixWord, tailWord_106372, baseEnd_106372] using wordTrace_append hprefix tailTrace_106372
  have hstable : (prefixWord ++ tailWord_106372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106372).length < 2 ^ (prefixWord ++ tailWord_106372).sum := by decide
  have hdescent : baseEnd_106372 < baseStart_106372 := by decide
  rcases family_descends (prefixWord ++ tailWord_106372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106386 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_106386 : Nat := 118140960795 + 106386 * 2 ^ 59
def prefixEnd_106386 : Nat := 4983230072969 + 3 ^ 40 * 106386 * 2
def baseEnd_106386 : Nat := 24278734626367110215887

theorem tailTrace_106386 : CollatzResearch.WordTrace tailWord_106386 prefixEnd_106386 24278734626367110215887 := by
  unfold tailWord_106386
  simp only [CollatzResearch.WordTrace]
  refine ⟨970054048147291531844753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2586810795059444084919341 970054048147291531844753)
  ·
    refine ⟨727540536110468648883565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 970054048147291531844753 727540536110468648883565)
    ·
      refine ⟨272827701041425743331337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 727540536110468648883565 272827701041425743331337)
      ·
        refine ⟨204620775781069307498503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272827701041425743331337 204620775781069307498503)
        ·
          refine ⟨306931163671603961247755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204620775781069307498503 306931163671603961247755)
          ·
            refine ⟨460396745507405941871633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306931163671603961247755 460396745507405941871633)
            ·
              refine ⟨345297559130554456403725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460396745507405941871633 345297559130554456403725)
              ·
                refine ⟨129486584673957921151397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345297559130554456403725 129486584673957921151397)
                ·
                  refine ⟨24278734626367110215887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129486584673957921151397 24278734626367110215887)
                  ·
                    rfl

theorem cell21_106386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_106386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106386 prefixEnd_106386 := by exact prefixLift 106386
  have htrace : WordTrace (prefixWord ++ tailWord_106386) baseStart_106386 baseEnd_106386 := by
    simpa [prefixWord, tailWord_106386, baseEnd_106386] using wordTrace_append hprefix tailTrace_106386
  have hstable : (prefixWord ++ tailWord_106386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106386).length < 2 ^ (prefixWord ++ tailWord_106386).sum := by decide
  have hdescent : baseEnd_106386 < baseStart_106386 := by decide
  rcases family_descends (prefixWord ++ tailWord_106386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106420 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 4]
def baseStart_106420 : Nat := 118140960795 + 106420 * 2 ^ 59
def prefixEnd_106420 : Nat := 4983230072969 + 3 ^ 40 * 106420 * 2
def baseEnd_106420 : Nat := 24286493889590606649151

theorem tailTrace_106420 : CollatzResearch.WordTrace tailWord_106420 prefixEnd_106420 24286493889590606649151 := by
  unfold tailWord_106420
  simp only [CollatzResearch.WordTrace]
  refine ⟨1940728137232994967058357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2587637516310659956077809 1940728137232994967058357)
  ·
    refine ⟨181943262865593278161721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1940728137232994967058357 181943262865593278161721)
    ·
      refine ⟨136457447149194958621291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181943262865593278161721 136457447149194958621291)
      ·
        refine ⟨204686170723792437931937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136457447149194958621291 204686170723792437931937)
        ·
          refine ⟨153514628042844328448953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204686170723792437931937 153514628042844328448953)
          ·
            refine ⟨115135971032133246336715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153514628042844328448953 115135971032133246336715)
            ·
              refine ⟨172703956548199869505073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115135971032133246336715 172703956548199869505073)
              ·
                refine ⟨129527967411149902128805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172703956548199869505073 129527967411149902128805)
                ·
                  refine ⟨24286493889590606649151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129527967411149902128805 24286493889590606649151)
                  ·
                    rfl

theorem cell21_106420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_106420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106420 prefixEnd_106420 := by exact prefixLift 106420
  have htrace : WordTrace (prefixWord ++ tailWord_106420) baseStart_106420 baseEnd_106420 := by
    simpa [prefixWord, tailWord_106420, baseEnd_106420] using wordTrace_append hprefix tailTrace_106420
  have hstable : (prefixWord ++ tailWord_106420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106420).length < 2 ^ (prefixWord ++ tailWord_106420).sum := by decide
  have hdescent : baseEnd_106420 < baseStart_106420 := by decide
  rcases family_descends (prefixWord ++ tailWord_106420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106535 : List Nat := [1, 1, 7, 1, 11]
def baseStart_106535 : Nat := 118140960795 + 106535 * 2 ^ 59
def prefixEnd_106535 : Nat := 4983230072969 + 3 ^ 40 * 106535 * 2
def baseEnd_106535 : Nat := 300157264893530397929

theorem tailTrace_106535 : CollatzResearch.WordTrace tailWord_106535 prefixEnd_106535 300157264893530397929 := by
  unfold tailWord_106535
  simp only [CollatzResearch.WordTrace]
  refine ⟨3885650669049364574553059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2590433779366243049702039 3885650669049364574553059)
  ·
    refine ⟨5828476003574046861829589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3885650669049364574553059 5828476003574046861829589)
    ·
      refine ⟨136604906333766723324131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5828476003574046861829589 136604906333766723324131)
      ·
        refine ⟨204907359500650084986197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136604906333766723324131 204907359500650084986197)
        ·
          refine ⟨300157264893530397929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 204907359500650084986197 300157264893530397929)
          ·
            rfl

theorem cell21_106535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 11].length) (baseStart_106535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106535 prefixEnd_106535 := by exact prefixLift 106535
  have htrace : WordTrace (prefixWord ++ tailWord_106535) baseStart_106535 baseEnd_106535 := by
    simpa [prefixWord, tailWord_106535, baseEnd_106535] using wordTrace_append hprefix tailTrace_106535
  have hstable : (prefixWord ++ tailWord_106535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106535).length < 2 ^ (prefixWord ++ tailWord_106535).sum := by decide
  have hdescent : baseEnd_106535 < baseStart_106535 := by decide
  rcases family_descends (prefixWord ++ tailWord_106535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106538 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_106538 : Nat := 118140960795 + 106538 * 2 ^ 59
def prefixEnd_106538 : Nat := 4983230072969 + 3 ^ 40 * 106538 * 2
def baseEnd_106538 : Nat := 24313423097248623682243

theorem tailTrace_106538 : CollatzResearch.WordTrace tailWord_106538 prefixEnd_106538 24313423097248623682243 := by
  unfold tailWord_106538
  simp only [CollatzResearch.WordTrace]
  refine ⟨971440022009624021728067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2590506725358997391274845 971440022009624021728067)
  ·
    refine ⟨1457160033014436032592101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 971440022009624021728067 1457160033014436032592101)
    ·
      refine ⟨273217506190206756111019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1457160033014436032592101 273217506190206756111019)
      ·
        refine ⟨409826259285310134166529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273217506190206756111019 409826259285310134166529)
        ·
          refine ⟨307369694463982600624897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409826259285310134166529 307369694463982600624897)
          ·
            refine ⟨230527270847986950468673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307369694463982600624897 230527270847986950468673)
            ·
              refine ⟨172895453135990212851505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230527270847986950468673 172895453135990212851505)
              ·
                refine ⟨129671589851992659638629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172895453135990212851505 129671589851992659638629)
                ·
                  refine ⟨24313423097248623682243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129671589851992659638629 24313423097248623682243)
                  ·
                    rfl

theorem cell21_106538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_106538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106538 prefixEnd_106538 := by exact prefixLift 106538
  have htrace : WordTrace (prefixWord ++ tailWord_106538) baseStart_106538 baseEnd_106538 := by
    simpa [prefixWord, tailWord_106538, baseEnd_106538] using wordTrace_append hprefix tailTrace_106538
  have hstable : (prefixWord ++ tailWord_106538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106538).length < 2 ^ (prefixWord ++ tailWord_106538).sum := by decide
  have hdescent : baseEnd_106538 < baseStart_106538 := by decide
  rcases family_descends (prefixWord ++ tailWord_106538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106552 : List Nat := [2, 1, 2, 1, 6, 2, 1, 6]
def baseStart_106552 : Nat := 118140960795 + 106552 * 2 ^ 59
def prefixEnd_106552 : Nat := 4983230072969 + 3 ^ 40 * 106552 * 2
def baseEnd_106552 : Nat := 8105539362662570149627

theorem tailTrace_106552 : CollatzResearch.WordTrace tailWord_106552 prefixEnd_106552 8105539362662570149627 := by
  unfold tailWord_106552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943135354993888238960955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2590847139991850985281273 1943135354993888238960955)
  ·
    refine ⟨2914703032490832358441433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1943135354993888238960955 2914703032490832358441433)
    ·
      refine ⟨2186027274368124268831075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2914703032490832358441433 2186027274368124268831075)
      ·
        refine ⟨3279040911552186403246613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186027274368124268831075 3279040911552186403246613)
        ·
          refine ⟨153705042729008737652185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3279040911552186403246613 153705042729008737652185)
          ·
            refine ⟨115278782046756553239139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153705042729008737652185 115278782046756553239139)
            ·
              refine ⟨172918173070134829858709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115278782046756553239139 172918173070134829858709)
              ·
                refine ⟨8105539362662570149627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172918173070134829858709 8105539362662570149627)
                ·
                  rfl

theorem cell21_106552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_106552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106552 prefixEnd_106552 := by exact prefixLift 106552
  have htrace : WordTrace (prefixWord ++ tailWord_106552) baseStart_106552 baseEnd_106552 := by
    simpa [prefixWord, tailWord_106552, baseEnd_106552] using wordTrace_append hprefix tailTrace_106552
  have hstable : (prefixWord ++ tailWord_106552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106552).length < 2 ^ (prefixWord ++ tailWord_106552).sum := by decide
  have hdescent : baseEnd_106552 < baseStart_106552 := by decide
  rcases family_descends (prefixWord ++ tailWord_106552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106580 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_106580 : Nat := 118140960795 + 106580 * 2 ^ 59
def prefixEnd_106580 : Nat := 4983230072969 + 3 ^ 40 * 106580 * 2
def baseEnd_106580 : Nat := 24323008069465883982157

theorem tailTrace_106580 : CollatzResearch.WordTrace tailWord_106580 prefixEnd_106580 24323008069465883982157 := by
  unfold tailWord_106580
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943645976943168629970597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2591527969257558173294129 1943645976943168629970597)
  ·
    refine ⟨364433620676844118119487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1943645976943168629970597 364433620676844118119487)
    ·
      refine ⟨546650431015266177179231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364433620676844118119487 546650431015266177179231)
      ·
        refine ⟨819975646522899265768847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546650431015266177179231 819975646522899265768847)
        ·
          refine ⟨1229963469784348898653271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819975646522899265768847 1229963469784348898653271)
          ·
            refine ⟨1844945204676523347979907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229963469784348898653271 1844945204676523347979907)
            ·
              refine ⟨2767417807014785021969861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844945204676523347979907 2767417807014785021969861)
              ·
                refine ⟨518890838815272191619349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2767417807014785021969861 518890838815272191619349)
                ·
                  refine ⟨24323008069465883982157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 518890838815272191619349 24323008069465883982157)
                  ·
                    rfl

theorem cell21_106580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_106580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106580 prefixEnd_106580 := by exact prefixLift 106580
  have htrace : WordTrace (prefixWord ++ tailWord_106580) baseStart_106580 baseEnd_106580 := by
    simpa [prefixWord, tailWord_106580, baseEnd_106580] using wordTrace_append hprefix tailTrace_106580
  have hstable : (prefixWord ++ tailWord_106580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106580).length < 2 ^ (prefixWord ++ tailWord_106580).sum := by decide
  have hdescent : baseEnd_106580 < baseStart_106580 := by decide
  rcases family_descends (prefixWord ++ tailWord_106580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106597 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 4]
def baseStart_106597 : Nat := 118140960795 + 106597 * 2 ^ 59
def prefixEnd_106597 : Nat := 4983230072969 + 3 ^ 40 * 106597 * 2
def baseEnd_106597 : Nat := 24326887701077632198789

theorem tailTrace_106597 : CollatzResearch.WordTrace tailWord_106597 prefixEnd_106597 24326887701077632198789 := by
  unfold tailWord_106597
  simp only [CollatzResearch.WordTrace]
  refine ⟨3887911994824749163310045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2591941329883166108873363 3887911994824749163310045)
  ·
    refine ⟨1457966998059280936241267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3887911994824749163310045 1457966998059280936241267)
    ·
      refine ⟨2186950497088921404361901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1457966998059280936241267 2186950497088921404361901)
      ·
        refine ⟨820106436408345526635713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2186950497088921404361901 820106436408345526635713)
        ·
          refine ⟨615079827306259144976785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820106436408345526635713 615079827306259144976785)
          ·
            refine ⟨461309870479694358732589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615079827306259144976785 461309870479694358732589)
            ·
              refine ⟨172991201429885384524721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461309870479694358732589 172991201429885384524721)
              ·
                refine ⟨129743401072414038393541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172991201429885384524721 129743401072414038393541)
                ·
                  refine ⟨24326887701077632198789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129743401072414038393541 24326887701077632198789)
                  ·
                    rfl

theorem cell21_106597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_106597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106597 prefixEnd_106597 := by exact prefixLift 106597
  have htrace : WordTrace (prefixWord ++ tailWord_106597) baseStart_106597 baseEnd_106597 := by
    simpa [prefixWord, tailWord_106597, baseEnd_106597] using wordTrace_append hprefix tailTrace_106597
  have hstable : (prefixWord ++ tailWord_106597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106597).length < 2 ^ (prefixWord ++ tailWord_106597).sum := by decide
  have hdescent : baseEnd_106597 < baseStart_106597 := by decide
  rcases family_descends (prefixWord ++ tailWord_106597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106656 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_106656 : Nat := 118140960795 + 106656 * 2 ^ 59
def prefixEnd_106656 : Nat := 4983230072969 + 3 ^ 40 * 106656 * 2
def baseEnd_106656 : Nat := 24340352304906640715335

theorem tailTrace_106656 : CollatzResearch.WordTrace tailWord_106656 prefixEnd_106656 24340352304906640715335 := by
  unfold tailWord_106656
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945031950805501119853911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2593375934407334826471881 1945031950805501119853911)
  ·
    refine ⟨2917547926208251679780867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1945031950805501119853911 2917547926208251679780867)
    ·
      refine ⟨4376321889312377519671301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2917547926208251679780867 4376321889312377519671301)
      ·
        refine ⟨820560354246070784938369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4376321889312377519671301 820560354246070784938369)
        ·
          refine ⟨615420265684553088703777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820560354246070784938369 615420265684553088703777)
          ·
            refine ⟨461565199263414816527833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615420265684553088703777 461565199263414816527833)
            ·
              refine ⟨346173899447561112395875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461565199263414816527833 346173899447561112395875)
              ·
                refine ⟨519260849171341668593813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346173899447561112395875 519260849171341668593813)
                ·
                  refine ⟨24340352304906640715335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 519260849171341668593813 24340352304906640715335)
                  ·
                    rfl

theorem cell21_106656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_106656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106656 prefixEnd_106656 := by exact prefixLift 106656
  have htrace : WordTrace (prefixWord ++ tailWord_106656) baseStart_106656 baseEnd_106656 := by
    simpa [prefixWord, tailWord_106656, baseEnd_106656] using wordTrace_append hprefix tailTrace_106656
  have hstable : (prefixWord ++ tailWord_106656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106656).length < 2 ^ (prefixWord ++ tailWord_106656).sum := by decide
  have hdescent : baseEnd_106656 < baseStart_106656 := by decide
  rcases family_descends (prefixWord ++ tailWord_106656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106710 : List Nat := [5, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_106710 : Nat := 118140960795 + 106710 * 2 ^ 59
def prefixEnd_106710 : Nat := 4983230072969 + 3 ^ 40 * 106710 * 2
def baseEnd_106710 : Nat := 24352675840614546815225

theorem tailTrace_106710 : CollatzResearch.WordTrace tailWord_106710 prefixEnd_106710 24352675840614546815225 := by
  unfold tailWord_106710
  simp only [CollatzResearch.WordTrace]
  refine ⟨243252090213460591385849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2594688962276912974782389 243252090213460591385849)
  ·
    refine ⟨182439067660095443539387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243252090213460591385849 182439067660095443539387)
    ·
      refine ⟨273658601490143165309081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182439067660095443539387 273658601490143165309081)
      ·
        refine ⟨205243951117607373981811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273658601490143165309081 205243951117607373981811)
        ·
          refine ⟨307865926676411060972717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205243951117607373981811 307865926676411060972717)
          ·
            refine ⟨115449722503654147864769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307865926676411060972717 115449722503654147864769)
            ·
              refine ⟨86587291877740610898577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115449722503654147864769 86587291877740610898577)
              ·
                refine ⟨64940468908305458173933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86587291877740610898577 64940468908305458173933)
                ·
                  refine ⟨24352675840614546815225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64940468908305458173933 24352675840614546815225)
                  ·
                    rfl

theorem cell21_106710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_106710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106710 prefixEnd_106710 := by exact prefixLift 106710
  have htrace : WordTrace (prefixWord ++ tailWord_106710) baseStart_106710 baseEnd_106710 := by
    simpa [prefixWord, tailWord_106710, baseEnd_106710] using wordTrace_append hprefix tailTrace_106710
  have hstable : (prefixWord ++ tailWord_106710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106710).length < 2 ^ (prefixWord ++ tailWord_106710).sum := by decide
  have hdescent : baseEnd_106710 < baseStart_106710 := by decide
  rcases family_descends (prefixWord ++ tailWord_106710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106732 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 4]
def baseStart_106732 : Nat := 118140960795 + 106732 * 2 ^ 59
def prefixEnd_106732 : Nat := 4983230072969 + 3 ^ 40 * 106732 * 2
def baseEnd_106732 : Nat := 24357696540347397448513

theorem tailTrace_106732 : CollatzResearch.WordTrace tailWord_106732 prefixEnd_106732 24357696540347397448513 := by
  unfold tailWord_106732
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946417924667833609737225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2595223899557111479649633 1946417924667833609737225)
  ·
    refine ⟨1459813443500875207302919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1946417924667833609737225 1459813443500875207302919)
    ·
      refine ⟨2189720165251312810954379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459813443500875207302919 2189720165251312810954379)
      ·
        refine ⟨3284580247876969216431569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189720165251312810954379 3284580247876969216431569)
        ·
          refine ⟨2463435185907726912323677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3284580247876969216431569 2463435185907726912323677)
          ·
            refine ⟨923788194715397592121379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2463435185907726912323677 923788194715397592121379)
            ·
              refine ⟨1385682292073096388182069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923788194715397592121379 1385682292073096388182069)
              ·
                refine ⟨129907714881852786392069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1385682292073096388182069 129907714881852786392069)
                ·
                  refine ⟨24357696540347397448513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129907714881852786392069 24357696540347397448513)
                  ·
                    rfl

theorem cell21_106732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_106732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106732 prefixEnd_106732 := by exact prefixLift 106732
  have htrace : WordTrace (prefixWord ++ tailWord_106732) baseStart_106732 baseEnd_106732 := by
    simpa [prefixWord, tailWord_106732, baseEnd_106732] using wordTrace_append hprefix tailTrace_106732
  have hstable : (prefixWord ++ tailWord_106732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106732).length < 2 ^ (prefixWord ++ tailWord_106732).sum := by decide
  have hdescent : baseEnd_106732 < baseStart_106732 := by decide
  rcases family_descends (prefixWord ++ tailWord_106732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106915 : List Nat := [1, 1, 1, 4, 1, 5, 3, 5]
def baseStart_106915 : Nat := 118140960795 + 106915 * 2 ^ 59
def prefixEnd_106915 : Nat := 4983230072969 + 3 ^ 40 * 106915 * 2
def baseEnd_106915 : Nat := 8133153211193248632713

theorem tailTrace_106915 : CollatzResearch.WordTrace tailWord_106915 prefixEnd_106915 8133153211193248632713 := by
  unfold tailWord_106915
  simp only [CollatzResearch.WordTrace]
  refine ⟨3899510407672689473386199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2599673605115126315590799 3899510407672689473386199)
  ·
    refine ⟨5849265611509034210079299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3899510407672689473386199 5849265611509034210079299)
    ·
      refine ⟨8773898417263551315118949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5849265611509034210079299 8773898417263551315118949)
      ·
        refine ⟨1645105953236915871584803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8773898417263551315118949 1645105953236915871584803)
        ·
          refine ⟨2467658929855373807377205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1645105953236915871584803 2467658929855373807377205)
          ·
            refine ⟨231343024673941294441613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2467658929855373807377205 231343024673941294441613)
            ·
              refine ⟨86753634252727985415605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231343024673941294441613 86753634252727985415605)
              ·
                refine ⟨8133153211193248632713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86753634252727985415605 8133153211193248632713)
                ·
                  rfl

theorem cell21_106915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 5].length) (baseStart_106915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106915 prefixEnd_106915 := by exact prefixLift 106915
  have htrace : WordTrace (prefixWord ++ tailWord_106915) baseStart_106915 baseEnd_106915 := by
    simpa [prefixWord, tailWord_106915, baseEnd_106915] using wordTrace_append hprefix tailTrace_106915
  have hstable : (prefixWord ++ tailWord_106915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106915).length < 2 ^ (prefixWord ++ tailWord_106915).sum := by decide
  have hdescent : baseEnd_106915 < baseStart_106915 := by decide
  rcases family_descends (prefixWord ++ tailWord_106915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106997 : List Nat := [1, 3, 5, 1, 2, 1, 3, 2, 3]
def baseStart_106997 : Nat := 118140960795 + 106997 * 2 ^ 59
def prefixEnd_106997 : Nat := 4983230072969 + 3 ^ 40 * 106997 * 2
def baseEnd_106997 : Nat := 24418173150765825531305

theorem tailTrace_106997 : CollatzResearch.WordTrace tailWord_106997 prefixEnd_106997 24418173150765825531305 := by
  unfold tailWord_106997
  simp only [CollatzResearch.WordTrace]
  refine ⟨3902501193375617477871245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2601667462250411651914163 3902501193375617477871245)
  ·
    refine ⟨1463437947515856554201717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3902501193375617477871245 1463437947515856554201717)
    ·
      refine ⟨137197307579611551956411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1463437947515856554201717 137197307579611551956411)
      ·
        refine ⟨205795961369417327934617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137197307579611551956411 205795961369417327934617)
        ·
          refine ⟨154346971027062995950963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205795961369417327934617 154346971027062995950963)
          ·
            refine ⟨231520456540594493926445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154346971027062995950963 231520456540594493926445)
            ·
              refine ⟨86820171202722935222417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231520456540594493926445 86820171202722935222417)
              ·
                refine ⟨65115128402042201416813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86820171202722935222417 65115128402042201416813)
                ·
                  refine ⟨24418173150765825531305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65115128402042201416813 24418173150765825531305)
                  ·
                    rfl

theorem cell21_106997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_106997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_106997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_106997 prefixEnd_106997 := by exact prefixLift 106997
  have htrace : WordTrace (prefixWord ++ tailWord_106997) baseStart_106997 baseEnd_106997 := by
    simpa [prefixWord, tailWord_106997, baseEnd_106997] using wordTrace_append hprefix tailTrace_106997
  have hstable : (prefixWord ++ tailWord_106997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106997).length < 2 ^ (prefixWord ++ tailWord_106997).sum := by decide
  have hdescent : baseEnd_106997 < baseStart_106997 := by decide
  rcases family_descends (prefixWord ++ tailWord_106997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107050 : List Nat := [3, 1, 4, 1, 1, 11]
def baseStart_107050 : Nat := 118140960795 + 107050 * 2 ^ 59
def prefixEnd_107050 : Nat := 4983230072969 + 3 ^ 40 * 107050 * 2
def baseEnd_107050 : Nat := 904824758253685598069

theorem tailTrace_107050 : CollatzResearch.WordTrace tailWord_107050 prefixEnd_107050 904824758253685598069 := by
  unfold tailWord_107050
  simp only [CollatzResearch.WordTrace]
  refine ⟨976108565545901882387651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2602956174789071686367069 976108565545901882387651)
  ·
    refine ⟨1464162848318852823581477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 976108565545901882387651 1464162848318852823581477)
    ·
      refine ⟨274530534059784904421527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1464162848318852823581477 274530534059784904421527)
      ·
        refine ⟨411795801089677356632291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274530534059784904421527 411795801089677356632291)
        ·
          refine ⟨617693701634516034948437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411795801089677356632291 617693701634516034948437)
          ·
            refine ⟨904824758253685598069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 617693701634516034948437 904824758253685598069)
            ·
              rfl

theorem cell21_107050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 11].length) (baseStart_107050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107050 prefixEnd_107050 := by exact prefixLift 107050
  have htrace : WordTrace (prefixWord ++ tailWord_107050) baseStart_107050 baseEnd_107050 := by
    simpa [prefixWord, tailWord_107050, baseEnd_107050] using wordTrace_append hprefix tailTrace_107050
  have hstable : (prefixWord ++ tailWord_107050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107050).length < 2 ^ (prefixWord ++ tailWord_107050).sum := by decide
  have hdescent : baseEnd_107050 < baseStart_107050 := by decide
  rcases family_descends (prefixWord ++ tailWord_107050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107095 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 6]
def baseStart_107095 : Nat := 118140960795 + 107095 * 2 ^ 59
def prefixEnd_107095 : Nat := 4983230072969 + 3 ^ 40 * 107095 * 2
def baseEnd_107095 : Nat := 24440538085939432897771

theorem tailTrace_107095 : CollatzResearch.WordTrace tailWord_107095 prefixEnd_107095 24440538085939432897771 := by
  unfold tailWord_107095
  simp only [CollatzResearch.WordTrace]
  refine ⟨3906075547020580214938739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2604050364680386809959159 3906075547020580214938739)
  ·
    refine ⟨5859113320530870322408109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3906075547020580214938739 5859113320530870322408109)
    ·
      refine ⟨2197167495199076370903041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5859113320530870322408109 2197167495199076370903041)
      ·
        refine ⟨1647875621399307278177281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2197167495199076370903041 1647875621399307278177281)
        ·
          refine ⟨1235906716049480458632961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1647875621399307278177281 1235906716049480458632961)
          ·
            refine ⟨926930037037110343974721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235906716049480458632961 926930037037110343974721)
            ·
              refine ⟨695197527777832757981041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926930037037110343974721 695197527777832757981041)
              ·
                refine ⟨521398145833374568485781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695197527777832757981041 521398145833374568485781)
                ·
                  refine ⟨24440538085939432897771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 521398145833374568485781 24440538085939432897771)
                  ·
                    rfl

theorem cell21_107095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_107095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107095 prefixEnd_107095 := by exact prefixLift 107095
  have htrace : WordTrace (prefixWord ++ tailWord_107095) baseStart_107095 baseEnd_107095 := by
    simpa [prefixWord, tailWord_107095, baseEnd_107095] using wordTrace_append hprefix tailTrace_107095
  have hstable : (prefixWord ++ tailWord_107095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107095).length < 2 ^ (prefixWord ++ tailWord_107095).sum := by decide
  have hdescent : baseEnd_107095 < baseStart_107095 := by decide
  rcases family_descends (prefixWord ++ tailWord_107095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107129 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 4]
def baseStart_107129 : Nat := 118140960795 + 107129 * 2 ^ 59
def prefixEnd_107129 : Nat := 4983230072969 + 3 ^ 40 * 107129 * 2
def baseEnd_107129 : Nat := 24448297349162929331035

theorem tailTrace_107129 : CollatzResearch.WordTrace tailWord_107129 prefixEnd_107129 24448297349162929331035 := by
  unfold tailWord_107129
  simp only [CollatzResearch.WordTrace]
  refine ⟨3907315628897404021676441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2604877085931602681117627 3907315628897404021676441)
  ·
    refine ⟨2930486721673053016257331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3907315628897404021676441 2930486721673053016257331)
    ·
      refine ⟨4395730082509579524385997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2930486721673053016257331 4395730082509579524385997)
      ·
        refine ⟨1648398780941092321644749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4395730082509579524385997 1648398780941092321644749)
        ·
          refine ⟨618149542852909620616781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1648398780941092321644749 618149542852909620616781)
          ·
            refine ⟨231806078569841107731293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 618149542852909620616781 231806078569841107731293)
            ·
              refine ⟨86927279463690415399235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231806078569841107731293 86927279463690415399235)
              ·
                refine ⟨130390919195535623098853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86927279463690415399235 130390919195535623098853)
                ·
                  refine ⟨24448297349162929331035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130390919195535623098853 24448297349162929331035)
                  ·
                    rfl

theorem cell21_107129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_107129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107129 prefixEnd_107129 := by exact prefixLift 107129
  have htrace : WordTrace (prefixWord ++ tailWord_107129) baseStart_107129 baseEnd_107129 := by
    simpa [prefixWord, tailWord_107129, baseEnd_107129] using wordTrace_append hprefix tailTrace_107129
  have hstable : (prefixWord ++ tailWord_107129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107129).length < 2 ^ (prefixWord ++ tailWord_107129).sum := by decide
  have hdescent : baseEnd_107129 < baseStart_107129 := by decide
  rcases family_descends (prefixWord ++ tailWord_107129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107337 : List Nat := [1, 2, 1, 1, 2, 5, 9]
def baseStart_107337 : Nat := 118140960795 + 107337 * 2 ^ 59
def prefixEnd_107337 : Nat := 4983230072969 + 3 ^ 40 * 107337 * 2
def baseEnd_107337 : Nat := 2721751753666754429327

theorem tailTrace_107337 : CollatzResearch.WordTrace tailWord_107337 prefixEnd_107337 2721751753666754429327 := by
  unfold tailWord_107337
  simp only [CollatzResearch.WordTrace]
  refine ⟨3914902012143855545248265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2609934674762570363498843 3914902012143855545248265)
  ·
    refine ⟨2936176509107891658936199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3914902012143855545248265 2936176509107891658936199)
    ·
      refine ⟨4404264763661837488404299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2936176509107891658936199 4404264763661837488404299)
      ·
        refine ⟨6606397145492756232606449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4404264763661837488404299 6606397145492756232606449)
        ·
          refine ⟨4954797859119567174454837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6606397145492756232606449 4954797859119567174454837)
          ·
            refine ⟨464512299292459422605141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4954797859119567174454837 464512299292459422605141)
            ·
              refine ⟨2721751753666754429327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 464512299292459422605141 2721751753666754429327)
              ·
                rfl

theorem cell21_107337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 9].length) (baseStart_107337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107337 prefixEnd_107337 := by exact prefixLift 107337
  have htrace : WordTrace (prefixWord ++ tailWord_107337) baseStart_107337 baseEnd_107337 := by
    simpa [prefixWord, tailWord_107337, baseEnd_107337] using wordTrace_append hprefix tailTrace_107337
  have hstable : (prefixWord ++ tailWord_107337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107337).length < 2 ^ (prefixWord ++ tailWord_107337).sum := by decide
  have hdescent : baseEnd_107337 < baseStart_107337 := by decide
  rcases family_descends (prefixWord ++ tailWord_107337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107354 : List Nat := [3, 1, 1, 2, 1, 5, 2, 6]
def baseStart_107354 : Nat := 118140960795 + 107354 * 2 ^ 59
def prefixEnd_107354 : Nat := 4983230072969 + 3 ^ 40 * 107354 * 2
def baseEnd_107354 : Nat := 8166548471537512693525

theorem tailTrace_107354 : CollatzResearch.WordTrace tailWord_107354 prefixEnd_107354 8166548471537512693525 := by
  unfold tailWord_107354
  simp only [CollatzResearch.WordTrace]
  refine ⟨978880513270566862154279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2610348035388178299078077 978880513270566862154279)
  ·
    refine ⟨1468320769905850293231419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 978880513270566862154279 1468320769905850293231419)
    ·
      refine ⟨2202481154858775439847129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1468320769905850293231419 2202481154858775439847129)
      ·
        refine ⟨1651860866144081579885347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2202481154858775439847129 1651860866144081579885347)
        ·
          refine ⟨2477791299216122369828021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1651860866144081579885347 2477791299216122369828021)
          ·
            refine ⟨232292934301511472171377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2477791299216122369828021 232292934301511472171377)
            ·
              refine ⟨174219700726133604128533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232292934301511472171377 174219700726133604128533)
              ·
                refine ⟨8166548471537512693525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174219700726133604128533 8166548471537512693525)
                ·
                  rfl

theorem cell21_107354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_107354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107354 prefixEnd_107354 := by exact prefixLift 107354
  have htrace : WordTrace (prefixWord ++ tailWord_107354) baseStart_107354 baseEnd_107354 := by
    simpa [prefixWord, tailWord_107354, baseEnd_107354] using wordTrace_append hprefix tailTrace_107354
  have hstable : (prefixWord ++ tailWord_107354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107354).length < 2 ^ (prefixWord ++ tailWord_107354).sum := by decide
  have hdescent : baseEnd_107354 < baseStart_107354 := by decide
  rcases family_descends (prefixWord ++ tailWord_107354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107394 : List Nat := [3, 4, 2, 2, 1, 2, 2, 2, 3]
def baseStart_107394 : Nat := 118140960795 + 107394 * 2 ^ 59
def prefixEnd_107394 : Nat := 4983230072969 + 3 ^ 40 * 107394 * 2
def baseEnd_107394 : Nat := 24508773959581357413827

theorem tailTrace_107394 : CollatzResearch.WordTrace tailWord_107394 prefixEnd_107394 24508773959581357413827 := by
  unfold tailWord_107394
  simp only [CollatzResearch.WordTrace]
  refine ⟨979245243234338570018309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2611320648624902853382157 979245243234338570018309)
  ·
    refine ⟨183608483106438481878433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 979245243234338570018309 183608483106438481878433)
    ·
      refine ⟨137706362329828861408825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183608483106438481878433 137706362329828861408825)
      ·
        refine ⟨103279771747371646056619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137706362329828861408825 103279771747371646056619)
        ·
          refine ⟨154919657621057469084929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103279771747371646056619 154919657621057469084929)
          ·
            refine ⟨116189743215793101813697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154919657621057469084929 116189743215793101813697)
            ·
              refine ⟨87142307411844826360273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116189743215793101813697 87142307411844826360273)
              ·
                refine ⟨65356730558883619770205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87142307411844826360273 65356730558883619770205)
                ·
                  refine ⟨24508773959581357413827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65356730558883619770205 24508773959581357413827)
                  ·
                    rfl

theorem cell21_107394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_107394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107394 prefixEnd_107394 := by exact prefixLift 107394
  have htrace : WordTrace (prefixWord ++ tailWord_107394) baseStart_107394 baseEnd_107394 := by
    simpa [prefixWord, tailWord_107394, baseEnd_107394] using wordTrace_append hprefix tailTrace_107394
  have hstable : (prefixWord ++ tailWord_107394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107394).length < 2 ^ (prefixWord ++ tailWord_107394).sum := by decide
  have hdescent : baseEnd_107394 < baseStart_107394 := by decide
  rcases family_descends (prefixWord ++ tailWord_107394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107478 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_107478 : Nat := 118140960795 + 107478 * 2 ^ 59
def prefixEnd_107478 : Nat := 4983230072969 + 3 ^ 40 * 107478 * 2
def baseEnd_107478 : Nat := 24527943904015878013655

theorem tailTrace_107478 : CollatzResearch.WordTrace tailWord_107478 prefixEnd_107478 24527943904015878013655 := by
  unfold tailWord_107478
  simp only [CollatzResearch.WordTrace]
  refine ⟨245002794039564789133193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2613363136422024417420725 245002794039564789133193)
  ·
    refine ⟨183752095529673591849895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245002794039564789133193 183752095529673591849895)
    ·
      refine ⟨275628143294510387774843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183752095529673591849895 275628143294510387774843)
      ·
        refine ⟨413442214941765581662265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275628143294510387774843 413442214941765581662265)
        ·
          refine ⟨310081661206324186246699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413442214941765581662265 310081661206324186246699)
          ·
            refine ⟨465122491809486279370049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310081661206324186246699 465122491809486279370049)
            ·
              refine ⟨348841868857114709527537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465122491809486279370049 348841868857114709527537)
              ·
                refine ⟨261631401642836032145653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348841868857114709527537 261631401642836032145653)
                ·
                  refine ⟨24527943904015878013655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 261631401642836032145653 24527943904015878013655)
                  ·
                    rfl

theorem cell21_107478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_107478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107478 prefixEnd_107478 := by exact prefixLift 107478
  have htrace : WordTrace (prefixWord ++ tailWord_107478) baseStart_107478 baseEnd_107478 := by
    simpa [prefixWord, tailWord_107478, baseEnd_107478] using wordTrace_append hprefix tailTrace_107478
  have hstable : (prefixWord ++ tailWord_107478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107478).length < 2 ^ (prefixWord ++ tailWord_107478).sum := by decide
  have hdescent : baseEnd_107478 < baseStart_107478 := by decide
  rcases family_descends (prefixWord ++ tailWord_107478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107495 : List Nat := [1, 1, 5, 2, 2, 3, 1, 3, 3]
def baseStart_107495 : Nat := 118140960795 + 107495 * 2 ^ 59
def prefixEnd_107495 : Nat := 4983230072969 + 3 ^ 40 * 107495 * 2
def baseEnd_107495 : Nat := 24531823535627626230287

theorem tailTrace_107495 : CollatzResearch.WordTrace tailWord_107495 prefixEnd_107495 24531823535627626230287 := by
  unfold tailWord_107495
  simp only [CollatzResearch.WordTrace]
  refine ⟨3920664745571448529499939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2613776497047632352999959 3920664745571448529499939)
  ·
    refine ⟨5880997118357172794249909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3920664745571448529499939 5880997118357172794249909)
    ·
      refine ⟨551343479845984949460929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5880997118357172794249909 551343479845984949460929)
      ·
        refine ⟨413507609884488712095697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551343479845984949460929 413507609884488712095697)
        ·
          refine ⟨310130707413366534071773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413507609884488712095697 310130707413366534071773)
          ·
            refine ⟨116299015280012450276915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310130707413366534071773 116299015280012450276915)
            ·
              refine ⟨174448522920018675415373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116299015280012450276915 174448522920018675415373)
              ·
                refine ⟨65418196095007003280765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174448522920018675415373 65418196095007003280765)
                ·
                  refine ⟨24531823535627626230287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65418196095007003280765 24531823535627626230287)
                  ·
                    rfl

theorem cell21_107495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 3].length) (baseStart_107495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107495 prefixEnd_107495 := by exact prefixLift 107495
  have htrace : WordTrace (prefixWord ++ tailWord_107495) baseStart_107495 baseEnd_107495 := by
    simpa [prefixWord, tailWord_107495, baseEnd_107495] using wordTrace_append hprefix tailTrace_107495
  have hstable : (prefixWord ++ tailWord_107495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107495).length < 2 ^ (prefixWord ++ tailWord_107495).sum := by decide
  have hdescent : baseEnd_107495 < baseStart_107495 := by decide
  rcases family_descends (prefixWord ++ tailWord_107495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107630 : List Nat := [4, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_107630 : Nat := 118140960795 + 107630 * 2 ^ 59
def prefixEnd_107630 : Nat := 4983230072969 + 3 ^ 40 * 107630 * 2
def baseEnd_107630 : Nat := 24562632374897391480011

theorem tailTrace_107630 : CollatzResearch.WordTrace tailWord_107630 prefixEnd_107630 24562632374897391480011 := by
  unfold tailWord_107630
  simp only [CollatzResearch.WordTrace]
  refine ⟨490698575010295823208043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2617059066721577723776229 490698575010295823208043)
  ·
    refine ⟨736047862515443734812065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 490698575010295823208043 736047862515443734812065)
    ·
      refine ⟨552035896886582801109049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 736047862515443734812065 552035896886582801109049)
      ·
        refine ⟨414026922664937100831787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552035896886582801109049 414026922664937100831787)
        ·
          refine ⟨621040383997405651247681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414026922664937100831787 621040383997405651247681)
          ·
            refine ⟨465780287998054238435761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621040383997405651247681 465780287998054238435761)
            ·
              refine ⟨349335215998540678826821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465780287998054238435761 349335215998540678826821)
              ·
                refine ⟨65500352999726377280029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 349335215998540678826821 65500352999726377280029)
                ·
                  refine ⟨24562632374897391480011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65500352999726377280029 24562632374897391480011)
                  ·
                    rfl

theorem cell21_107630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_107630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107630 prefixEnd_107630 := by exact prefixLift 107630
  have htrace : WordTrace (prefixWord ++ tailWord_107630) baseStart_107630 baseEnd_107630 := by
    simpa [prefixWord, tailWord_107630, baseEnd_107630] using wordTrace_append hprefix tailTrace_107630
  have hstable : (prefixWord ++ tailWord_107630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107630).length < 2 ^ (prefixWord ++ tailWord_107630).sum := by decide
  have hdescent : baseEnd_107630 < baseStart_107630 := by decide
  rcases family_descends (prefixWord ++ tailWord_107630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107644 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 4]
def baseStart_107644 : Nat := 118140960795 + 107644 * 2 ^ 59
def prefixEnd_107644 : Nat := 4983230072969 + 3 ^ 40 * 107644 * 2
def baseEnd_107644 : Nat := 24565827365636478246649

theorem tailTrace_107644 : CollatzResearch.WordTrace tailWord_107644 prefixEnd_107644 24565827365636478246649 := by
  unfold tailWord_107644
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963049611015823488336993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2617399481354431317782657 1963049611015823488336993)
  ·
    refine ⟨1472287208261867616252745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1963049611015823488336993 1472287208261867616252745)
    ·
      refine ⟨1104215406196400712189559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1472287208261867616252745 1104215406196400712189559)
      ·
        refine ⟨1656323109294601068284339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104215406196400712189559 1656323109294601068284339)
        ·
          refine ⟨2484484663941901602426509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656323109294601068284339 2484484663941901602426509)
          ·
            refine ⟨931681748978213100909941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2484484663941901602426509 931681748978213100909941)
            ·
              refine ⟨87345163966707478210307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 931681748978213100909941 87345163966707478210307)
              ·
                refine ⟨131017745950061217315461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87345163966707478210307 131017745950061217315461)
                ·
                  refine ⟨24565827365636478246649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131017745950061217315461 24565827365636478246649)
                  ·
                    rfl

theorem cell21_107644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_107644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107644 prefixEnd_107644 := by exact prefixLift 107644
  have htrace : WordTrace (prefixWord ++ tailWord_107644) baseStart_107644 baseEnd_107644 := by
    simpa [prefixWord, tailWord_107644, baseEnd_107644] using wordTrace_append hprefix tailTrace_107644
  have hstable : (prefixWord ++ tailWord_107644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107644).length < 2 ^ (prefixWord ++ tailWord_107644).sum := by decide
  have hdescent : baseEnd_107644 < baseStart_107644 := by decide
  rcases family_descends (prefixWord ++ tailWord_107644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107703 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 4]
def baseStart_107703 : Nat := 118140960795 + 107703 * 2 ^ 59
def prefixEnd_107703 : Nat := 4983230072969 + 3 ^ 40 * 107703 * 2
def baseEnd_107703 : Nat := 24579291969465486763195

theorem tailTrace_107703 : CollatzResearch.WordTrace tailWord_107703 prefixEnd_107703 24579291969465486763195 := by
  unfold tailWord_107703
  simp only [CollatzResearch.WordTrace]
  refine ⟨3928251128817900053071763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2618834085878600035381175 3928251128817900053071763)
  ·
    refine ⟨5892376693226850079607645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3928251128817900053071763 5892376693226850079607645)
    ·
      refine ⟨2209641259960068779852867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5892376693226850079607645 2209641259960068779852867)
      ·
        refine ⟨3314461889940103169779301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209641259960068779852867 3314461889940103169779301)
        ·
          refine ⟨621461604363769344333619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3314461889940103169779301 621461604363769344333619)
          ·
            refine ⟨932192406545654016500429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621461604363769344333619 932192406545654016500429)
            ·
              refine ⟨349572152454620256187661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 932192406545654016500429 349572152454620256187661)
              ·
                refine ⟨131089557170482596070373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349572152454620256187661 131089557170482596070373)
                ·
                  refine ⟨24579291969465486763195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131089557170482596070373 24579291969465486763195)
                  ·
                    rfl

theorem cell21_107703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 4].length) (baseStart_107703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107703 prefixEnd_107703 := by exact prefixLift 107703
  have htrace : WordTrace (prefixWord ++ tailWord_107703) baseStart_107703 baseEnd_107703 := by
    simpa [prefixWord, tailWord_107703, baseEnd_107703] using wordTrace_append hprefix tailTrace_107703
  have hstable : (prefixWord ++ tailWord_107703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107703).length < 2 ^ (prefixWord ++ tailWord_107703).sum := by decide
  have hdescent : baseEnd_107703 < baseStart_107703 := by decide
  rcases family_descends (prefixWord ++ tailWord_107703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107731 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 7]
def baseStart_107731 : Nat := 118140960795 + 107731 * 2 ^ 59
def prefixEnd_107731 : Nat := 4983230072969 + 3 ^ 40 * 107731 * 2
def baseEnd_107731 : Nat := 24585681950943660296471

theorem tailTrace_107731 : CollatzResearch.WordTrace tailWord_107731 prefixEnd_107731 24585681950943660296471 := by
  unfold tailWord_107731
  simp only [CollatzResearch.WordTrace]
  refine ⟨3929272372716460835091047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2619514915144307223394031 3929272372716460835091047)
  ·
    refine ⟨5893908559074691252636571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3929272372716460835091047 5893908559074691252636571)
    ·
      refine ⟨8840862838612036878954857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5893908559074691252636571 8840862838612036878954857)
      ·
        refine ⟨6630647128959027659216143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8840862838612036878954857 6630647128959027659216143)
        ·
          refine ⟨9945970693438541488824215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6630647128959027659216143 9945970693438541488824215)
          ·
            refine ⟨14918956040157812233236323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9945970693438541488824215 14918956040157812233236323)
            ·
              refine ⟨22378434060236718349854485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14918956040157812233236323 22378434060236718349854485)
              ·
                refine ⟨1048989096573596172649429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22378434060236718349854485 1048989096573596172649429)
                ·
                  refine ⟨24585681950943660296471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1048989096573596172649429 24585681950943660296471)
                  ·
                    rfl

theorem cell21_107731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_107731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107731 prefixEnd_107731 := by exact prefixLift 107731
  have htrace : WordTrace (prefixWord ++ tailWord_107731) baseStart_107731 baseEnd_107731 := by
    simpa [prefixWord, tailWord_107731, baseEnd_107731] using wordTrace_append hprefix tailTrace_107731
  have hstable : (prefixWord ++ tailWord_107731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107731).length < 2 ^ (prefixWord ++ tailWord_107731).sum := by decide
  have hdescent : baseEnd_107731 < baseStart_107731 := by decide
  rcases family_descends (prefixWord ++ tailWord_107731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107734 : List Nat := [5, 2, 1, 2, 11]
def baseStart_107734 : Nat := 118140960795 + 107734 * 2 ^ 59
def prefixEnd_107734 : Nat := 4983230072969 + 3 ^ 40 * 107734 * 2
def baseEnd_107734 : Nat := 303535390022423725265

theorem tailTrace_107734 : CollatzResearch.WordTrace tailWord_107734 prefixEnd_107734 303535390022423725265 := by
  unfold tailWord_107734
  simp only [CollatzResearch.WordTrace]
  refine ⟨245586361981599521715641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2619587861137061564966837 245586361981599521715641)
  ·
    refine ⟨184189771486199641286731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245586361981599521715641 184189771486199641286731)
    ·
      refine ⟨276284657229299461930097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184189771486199641286731 276284657229299461930097)
      ·
        refine ⟨207213492921974596447573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276284657229299461930097 207213492921974596447573)
        ·
          refine ⟨303535390022423725265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 207213492921974596447573 303535390022423725265)
          ·
            rfl

theorem cell21_107734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 11].length) (baseStart_107734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107734 prefixEnd_107734 := by exact prefixLift 107734
  have htrace : WordTrace (prefixWord ++ tailWord_107734) baseStart_107734 baseEnd_107734 := by
    simpa [prefixWord, tailWord_107734, baseEnd_107734] using wordTrace_append hprefix tailTrace_107734
  have hstable : (prefixWord ++ tailWord_107734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107734).length < 2 ^ (prefixWord ++ tailWord_107734).sum := by decide
  have hdescent : baseEnd_107734 < baseStart_107734 := by decide
  rcases family_descends (prefixWord ++ tailWord_107734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107751 : List Nat := [1, 1, 5, 3, 2, 2, 1, 6]
def baseStart_107751 : Nat := 118140960795 + 107751 * 2 ^ 59
def prefixEnd_107751 : Nat := 4983230072969 + 3 ^ 40 * 107751 * 2
def baseEnd_107751 : Nat := 8196748741142689987699

theorem tailTrace_107751 : CollatzResearch.WordTrace tailWord_107751 prefixEnd_107751 8196748741142689987699 := by
  unfold tailWord_107751
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930001832644004250819107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2620001221762669500546071 3930001832644004250819107)
  ·
    refine ⟨5895002748966006376228661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3930001832644004250819107 5895002748966006376228661)
    ·
      refine ⟨552656507715563097771437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5895002748966006376228661 552656507715563097771437)
      ·
        refine ⟨207246190393336161664289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 552656507715563097771437 207246190393336161664289)
        ·
          refine ⟨155434642795002121248217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207246190393336161664289 155434642795002121248217)
          ·
            refine ⟨116575982096251590936163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155434642795002121248217 116575982096251590936163)
            ·
              refine ⟨174863973144377386404245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116575982096251590936163 174863973144377386404245)
              ·
                refine ⟨8196748741142689987699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174863973144377386404245 8196748741142689987699)
                ·
                  rfl

theorem cell21_107751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 6].length) (baseStart_107751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107751 prefixEnd_107751 := by exact prefixLift 107751
  have htrace : WordTrace (prefixWord ++ tailWord_107751) baseStart_107751 baseEnd_107751 := by
    simpa [prefixWord, tailWord_107751, baseEnd_107751] using wordTrace_append hprefix tailTrace_107751
  have hstable : (prefixWord ++ tailWord_107751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107751).length < 2 ^ (prefixWord ++ tailWord_107751).sum := by decide
  have hdescent : baseEnd_107751 < baseStart_107751 := by decide
  rcases family_descends (prefixWord ++ tailWord_107751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107872 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 4]
def baseStart_107872 : Nat := 118140960795 + 107872 * 2 ^ 59
def prefixEnd_107872 : Nat := 4983230072969 + 3 ^ 40 * 107872 * 2
def baseEnd_107872 : Nat := 24617860071958748446183

theorem tailTrace_107872 : CollatzResearch.WordTrace tailWord_107872 prefixEnd_107872 24617860071958748446183 := by
  unfold tailWord_107872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967207532602820957986935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2622943376803761277315913 1967207532602820957986935)
  ·
    refine ⟨2950811298904231436980403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1967207532602820957986935 2950811298904231436980403)
    ·
      refine ⟨4426216948356347155470605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2950811298904231436980403 4426216948356347155470605)
      ·
        refine ⟨1659831355633630183301477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4426216948356347155470605 1659831355633630183301477)
        ·
          refine ⟨311218379181305659369027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1659831355633630183301477 311218379181305659369027)
          ·
            refine ⟨466827568771958489053541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311218379181305659369027 466827568771958489053541)
            ·
              refine ⟨87530169144742216697539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 466827568771958489053541 87530169144742216697539)
              ·
                refine ⟨131295253717113325046309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87530169144742216697539 131295253717113325046309)
                ·
                  refine ⟨24617860071958748446183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131295253717113325046309 24617860071958748446183)
                  ·
                    rfl

theorem cell21_107872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_107872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107872 prefixEnd_107872 := by exact prefixLift 107872
  have htrace : WordTrace (prefixWord ++ tailWord_107872) baseStart_107872 baseEnd_107872 := by
    simpa [prefixWord, tailWord_107872, baseEnd_107872] using wordTrace_append hprefix tailTrace_107872
  have hstable : (prefixWord ++ tailWord_107872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107872).length < 2 ^ (prefixWord ++ tailWord_107872).sum := by decide
  have hdescent : baseEnd_107872 < baseStart_107872 := by decide
  rcases family_descends (prefixWord ++ tailWord_107872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107934 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_107934 : Nat := 118140960795 + 107934 * 2 ^ 59
def prefixEnd_107934 : Nat := 4983230072969 + 3 ^ 40 * 107934 * 2
def baseEnd_107934 : Nat := 24632009316660418412723

theorem tailTrace_107934 : CollatzResearch.WordTrace tailWord_107934 prefixEnd_107934 24632009316660418412723 := by
  unfold tailWord_107934
  simp only [CollatzResearch.WordTrace]
  refine ⟨492084548872628313091357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2624450927320684336487237 492084548872628313091357)
  ·
    refine ⟨184531705827235617409259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 492084548872628313091357 184531705827235617409259)
    ·
      refine ⟨276797558740853426113889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184531705827235617409259 276797558740853426113889)
      ·
        refine ⟨207598169055640069585417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276797558740853426113889 207598169055640069585417)
        ·
          refine ⟨155698626791730052189063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207598169055640069585417 155698626791730052189063)
          ·
            refine ⟨233547940187595078283595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155698626791730052189063 233547940187595078283595)
            ·
              refine ⟨350321910281392617425393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233547940187595078283595 350321910281392617425393)
              ·
                refine ⟨262741432711044463069045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350321910281392617425393 262741432711044463069045)
                ·
                  refine ⟨24632009316660418412723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 262741432711044463069045 24632009316660418412723)
                  ·
                    rfl

theorem cell21_107934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_107934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107934 prefixEnd_107934 := by exact prefixLift 107934
  have htrace : WordTrace (prefixWord ++ tailWord_107934) baseStart_107934 baseEnd_107934 := by
    simpa [prefixWord, tailWord_107934, baseEnd_107934] using wordTrace_append hprefix tailTrace_107934
  have hstable : (prefixWord ++ tailWord_107934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107934).length < 2 ^ (prefixWord ++ tailWord_107934).sum := by decide
  have hdescent : baseEnd_107934 < baseStart_107934 := by decide
  rcases family_descends (prefixWord ++ tailWord_107934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107959 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 7]
def baseStart_107959 : Nat := 118140960795 + 107959 * 2 ^ 59
def prefixEnd_107959 : Nat := 4983230072969 + 3 ^ 40 * 107959 * 2
def baseEnd_107959 : Nat := 24637714657265930496005

theorem tailTrace_107959 : CollatzResearch.WordTrace tailWord_107959 prefixEnd_107959 24637714657265930496005 := by
  unfold tailWord_107959
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937588215890455774390931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2625058810593637182927287 3937588215890455774390931)
  ·
    refine ⟨5906382323835683661586397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3937588215890455774390931 5906382323835683661586397)
    ·
      refine ⟨2214893371438381373094899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5906382323835683661586397 2214893371438381373094899)
      ·
        refine ⟨3322340057157572059642349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2214893371438381373094899 3322340057157572059642349)
        ·
          refine ⟨1245877521434089522365881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3322340057157572059642349 1245877521434089522365881)
          ·
            refine ⟨934408141075567141774411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1245877521434089522365881 934408141075567141774411)
            ·
              refine ⟨1401612211613350712661617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934408141075567141774411 1401612211613350712661617)
              ·
                refine ⟨1051209158710013034496213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401612211613350712661617 1051209158710013034496213)
                ·
                  refine ⟨24637714657265930496005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1051209158710013034496213 24637714657265930496005)
                  ·
                    rfl

theorem cell21_107959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_107959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107959 prefixEnd_107959 := by exact prefixLift 107959
  have htrace : WordTrace (prefixWord ++ tailWord_107959) baseStart_107959 baseEnd_107959 := by
    simpa [prefixWord, tailWord_107959, baseEnd_107959] using wordTrace_append hprefix tailTrace_107959
  have hstable : (prefixWord ++ tailWord_107959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107959).length < 2 ^ (prefixWord ++ tailWord_107959).sum := by decide
  have hdescent : baseEnd_107959 < baseStart_107959 := by decide
  rcases family_descends (prefixWord ++ tailWord_107959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107976 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 5]
def baseStart_107976 : Nat := 118140960795 + 107976 * 2 ^ 59
def prefixEnd_107976 : Nat := 4983230072969 + 3 ^ 40 * 107976 * 2
def baseEnd_107976 : Nat := 24641594288877678712637

theorem tailTrace_107976 : CollatzResearch.WordTrace tailWord_107976 prefixEnd_107976 24641594288877678712637 := by
  unfold tailWord_107976
  simp only [CollatzResearch.WordTrace]
  refine ⟨1969104128414433838879891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2625472171219245118506521 1969104128414433838879891)
  ·
    refine ⟨2953656192621650758319837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1969104128414433838879891 2953656192621650758319837)
    ·
      refine ⟨1107621072233119034369939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2953656192621650758319837 1107621072233119034369939)
      ·
        refine ⟨1661431608349678551554909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107621072233119034369939 1661431608349678551554909)
        ·
          refine ⟨623036853131129456833091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1661431608349678551554909 623036853131129456833091)
          ·
            refine ⟨934555279696694185249637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623036853131129456833091 934555279696694185249637)
            ·
              refine ⟨175229114943130159734307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 934555279696694185249637 175229114943130159734307)
              ·
                refine ⟨262843672414695239601461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175229114943130159734307 262843672414695239601461)
                ·
                  refine ⟨24641594288877678712637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 262843672414695239601461 24641594288877678712637)
                  ·
                    rfl

theorem cell21_107976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_107976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_107976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_107976 prefixEnd_107976 := by exact prefixLift 107976
  have htrace : WordTrace (prefixWord ++ tailWord_107976) baseStart_107976 baseEnd_107976 := by
    simpa [prefixWord, tailWord_107976, baseEnd_107976] using wordTrace_append hprefix tailTrace_107976
  have hstable : (prefixWord ++ tailWord_107976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107976).length < 2 ^ (prefixWord ++ tailWord_107976).sum := by decide
  have hdescent : baseEnd_107976 < baseStart_107976 := by decide
  rcases family_descends (prefixWord ++ tailWord_107976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108035 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 5]
def baseStart_108035 : Nat := 118140960795 + 108035 * 2 ^ 59
def prefixEnd_108035 : Nat := 4983230072969 + 3 ^ 40 * 108035 * 2
def baseEnd_108035 : Nat := 24655058892706687229183

theorem tailTrace_108035 : CollatzResearch.WordTrace tailWord_108035 prefixEnd_108035 24655058892706687229183 := by
  unfold tailWord_108035
  simp only [CollatzResearch.WordTrace]
  refine ⟨3940360163615120754157559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2626906775743413836105039 3940360163615120754157559)
  ·
    refine ⟨5910540245422681131236339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3940360163615120754157559 5910540245422681131236339)
    ·
      refine ⟨8865810368134021696854509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5910540245422681131236339 8865810368134021696854509)
      ·
        refine ⟨3324678888050258136320441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8865810368134021696854509 3324678888050258136320441)
        ·
          refine ⟨2493509166037693602240331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3324678888050258136320441 2493509166037693602240331)
          ·
            refine ⟨3740263749056540403360497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493509166037693602240331 3740263749056540403360497)
            ·
              refine ⟨2805197811792405302520373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3740263749056540403360497 2805197811792405302520373)
              ·
                refine ⟨262987294855537997111285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2805197811792405302520373 262987294855537997111285)
                ·
                  refine ⟨24655058892706687229183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 262987294855537997111285 24655058892706687229183)
                  ·
                    rfl

theorem cell21_108035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_108035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108035 prefixEnd_108035 := by exact prefixLift 108035
  have htrace : WordTrace (prefixWord ++ tailWord_108035) baseStart_108035 baseEnd_108035 := by
    simpa [prefixWord, tailWord_108035, baseEnd_108035] using wordTrace_append hprefix tailTrace_108035
  have hstable : (prefixWord ++ tailWord_108035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108035).length < 2 ^ (prefixWord ++ tailWord_108035).sum := by decide
  have hdescent : baseEnd_108035 < baseStart_108035 := by decide
  rcases family_descends (prefixWord ++ tailWord_108035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108066 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_108066 : Nat := 118140960795 + 108066 * 2 ^ 59
def prefixEnd_108066 : Nat := 4983230072969 + 3 ^ 40 * 108066 * 2
def baseEnd_108066 : Nat := 24662133515057522212453

theorem tailTrace_108066 : CollatzResearch.WordTrace tailWord_108066 prefixEnd_108066 24662133515057522212453 := by
  unfold tailWord_108066
  simp only [CollatzResearch.WordTrace]
  refine ⟨985372706625703262134013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2627660551001875365690701 985372706625703262134013)
  ·
    refine ⟨369514764984638723300255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 985372706625703262134013 369514764984638723300255)
    ·
      refine ⟨554272147476958084950383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369514764984638723300255 554272147476958084950383)
      ·
        refine ⟨831408221215437127425575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554272147476958084950383 831408221215437127425575)
        ·
          refine ⟨1247112331823155691138363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831408221215437127425575 1247112331823155691138363)
          ·
            refine ⟨1870668497734733536707545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247112331823155691138363 1870668497734733536707545)
            ·
              refine ⟨1403001373301050152530659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870668497734733536707545 1403001373301050152530659)
              ·
                refine ⟨2104502059951575228795989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403001373301050152530659 2104502059951575228795989)
                ·
                  refine ⟨24662133515057522212453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2104502059951575228795989 24662133515057522212453)
                  ·
                    rfl

theorem cell21_108066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_108066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108066 prefixEnd_108066 := by exact prefixLift 108066
  have htrace : WordTrace (prefixWord ++ tailWord_108066) baseStart_108066 baseEnd_108066 := by
    simpa [prefixWord, tailWord_108066, baseEnd_108066] using wordTrace_append hprefix tailTrace_108066
  have hstable : (prefixWord ++ tailWord_108066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108066).length < 2 ^ (prefixWord ++ tailWord_108066).sum := by decide
  have hdescent : baseEnd_108066 < baseStart_108066 := by decide
  rcases family_descends (prefixWord ++ tailWord_108066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108083 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 4]
def baseStart_108083 : Nat := 118140960795 + 108083 * 2 ^ 59
def prefixEnd_108083 : Nat := 4983230072969 + 3 ^ 40 * 108083 * 2
def baseEnd_108083 : Nat := 24666013146669270429085

theorem tailTrace_108083 : CollatzResearch.WordTrace tailWord_108083 prefixEnd_108083 24666013146669270429085 := by
  unfold tailWord_108083
  simp only [CollatzResearch.WordTrace]
  refine ⟨3942110867441224951904903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2628073911627483301269935 3942110867441224951904903)
  ·
    refine ⟨5913166301161837427857355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3942110867441224951904903 5913166301161837427857355)
    ·
      refine ⟨8869749451742756141786033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5913166301161837427857355 8869749451742756141786033)
      ·
        refine ⟨6652312088807067106339525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8869749451742756141786033 6652312088807067106339525)
        ·
          refine ⟨1247308516651325082438661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6652312088807067106339525 1247308516651325082438661)
          ·
            refine ⟨233870346872123452957249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1247308516651325082438661 233870346872123452957249)
            ·
              refine ⟨175402760154092589717937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233870346872123452957249 175402760154092589717937)
              ·
                refine ⟨131552070115569442288453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175402760154092589717937 131552070115569442288453)
                ·
                  refine ⟨24666013146669270429085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131552070115569442288453 24666013146669270429085)
                  ·
                    rfl

theorem cell21_108083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 4].length) (baseStart_108083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108083 prefixEnd_108083 := by exact prefixLift 108083
  have htrace : WordTrace (prefixWord ++ tailWord_108083) baseStart_108083 baseEnd_108083 := by
    simpa [prefixWord, tailWord_108083, baseEnd_108083] using wordTrace_append hprefix tailTrace_108083
  have hstable : (prefixWord ++ tailWord_108083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108083).length < 2 ^ (prefixWord ++ tailWord_108083).sum := by decide
  have hdescent : baseEnd_108083 < baseStart_108083 := by decide
  rcases family_descends (prefixWord ++ tailWord_108083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
