import V185TrunkScan21Chunk049

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_604108 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 5]
def baseStart_604108 : Nat := 118140960795 + 604108 * 2 ^ 59
def prefixEnd_604108 : Nat := 4983230072969 + 3 ^ 40 * 604108 * 2
def baseEnd_604108 : Nat := 137865676100634514831895

theorem tailTrace_604108 : CollatzResearch.WordTrace tailWord_604108 prefixEnd_604108 137865676100634514831895 := by
  unfold tailWord_604108
  simp only [CollatzResearch.WordTrace]
  refine ⟨11016814447713682138726489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14689085930284909518301985 11016814447713682138726489)
  ·
    refine ⟨8262610835785261604044867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11016814447713682138726489 8262610835785261604044867)
    ·
      refine ⟨12393916253677892406067301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8262610835785261604044867 12393916253677892406067301)
      ·
        refine ⟨2323859297564604826137619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12393916253677892406067301 2323859297564604826137619)
        ·
          refine ⟨3485788946346907239206429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2323859297564604826137619 3485788946346907239206429)
          ·
            refine ⟨1307170854880090214702411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3485788946346907239206429 1307170854880090214702411)
            ·
              refine ⟨1960756282320135322053617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307170854880090214702411 1960756282320135322053617)
              ·
                refine ⟨1470567211740101491540213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1960756282320135322053617 1470567211740101491540213)
                ·
                  refine ⟨137865676100634514831895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1470567211740101491540213 137865676100634514831895)
                  ·
                    rfl

theorem cell21_604108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_604108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604108 prefixEnd_604108 := by exact prefixLift 604108
  have htrace : WordTrace (prefixWord ++ tailWord_604108) baseStart_604108 baseEnd_604108 := by
    simpa [prefixWord, tailWord_604108, baseEnd_604108] using wordTrace_append hprefix tailTrace_604108
  have hstable : (prefixWord ++ tailWord_604108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604108).length < 2 ^ (prefixWord ++ tailWord_604108).sum := by decide
  have hdescent : baseEnd_604108 < baseStart_604108 := by decide
  rcases family_descends (prefixWord ++ tailWord_604108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604215 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 4]
def baseStart_604215 : Nat := 118140960795 + 604215 * 2 ^ 59
def prefixEnd_604215 : Nat := 4983230072969 + 3 ^ 40 * 604215 * 2
def baseEnd_604215 : Nat := 137890094958426106548343

theorem tailTrace_604215 : CollatzResearch.WordTrace tailWord_604215 prefixEnd_604215 137890094958426106548343 := by
  unfold tailWord_604215
  simp only [CollatzResearch.WordTrace]
  refine ⟨22037531506039721551598099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14691687670693147701065399 22037531506039721551598099)
  ·
    refine ⟨33056297259059582327397149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22037531506039721551598099 33056297259059582327397149)
    ·
      refine ⟨12396111472147343372773931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33056297259059582327397149 12396111472147343372773931)
      ·
        refine ⟨18594167208221015059160897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12396111472147343372773931 18594167208221015059160897)
        ·
          refine ⟨13945625406165761294370673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18594167208221015059160897 13945625406165761294370673)
          ·
            refine ⟨10459219054624320970778005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13945625406165761294370673 10459219054624320970778005)
            ·
              refine ⟨490275893185515045505219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10459219054624320970778005 490275893185515045505219)
              ·
                refine ⟨735413839778272568257829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490275893185515045505219 735413839778272568257829)
                ·
                  refine ⟨137890094958426106548343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 735413839778272568257829 137890094958426106548343)
                  ·
                    rfl

theorem cell21_604215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 4].length) (baseStart_604215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604215 prefixEnd_604215 := by exact prefixLift 604215
  have htrace : WordTrace (prefixWord ++ tailWord_604215) baseStart_604215 baseEnd_604215 := by
    simpa [prefixWord, tailWord_604215, baseEnd_604215] using wordTrace_append hprefix tailTrace_604215
  have hstable : (prefixWord ++ tailWord_604215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604215).length < 2 ^ (prefixWord ++ tailWord_604215).sum := by decide
  have hdescent : baseEnd_604215 < baseStart_604215 := by decide
  rcases family_descends (prefixWord ++ tailWord_604215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604246 : List Nat := [5, 2, 2, 1, 1, 10]
def baseStart_604246 : Nat := 118140960795 + 604246 * 2 ^ 59
def prefixEnd_604246 : Nat := 4983230072969 + 3 ^ 40 * 604246 * 2
def baseEnd_604246 : Nat := 5107302577065812649319

theorem tailTrace_604246 : CollatzResearch.WordTrace tailWord_604246 prefixEnd_604246 5107302577065812649319 := by
  unfold tailWord_604246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377416385557963365373537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14692441445951609230651061 1377416385557963365373537)
  ·
    refine ⟨1033062289168472524030153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1377416385557963365373537 1033062289168472524030153)
    ·
      refine ⟨774796716876354393022615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1033062289168472524030153 774796716876354393022615)
      ·
        refine ⟨1162195075314531589533923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774796716876354393022615 1162195075314531589533923)
        ·
          refine ⟨1743292612971797384300885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162195075314531589533923 1743292612971797384300885)
          ·
            refine ⟨5107302577065812649319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1743292612971797384300885 5107302577065812649319)
            ·
              rfl

theorem cell21_604246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 10].length) (baseStart_604246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604246 prefixEnd_604246 := by exact prefixLift 604246
  have htrace : WordTrace (prefixWord ++ tailWord_604246) baseStart_604246 baseEnd_604246 := by
    simpa [prefixWord, tailWord_604246, baseEnd_604246] using wordTrace_append hprefix tailTrace_604246
  have hstable : (prefixWord ++ tailWord_604246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604246).length < 2 ^ (prefixWord ++ tailWord_604246).sum := by decide
  have hdescent : baseEnd_604246 < baseStart_604246 := by decide
  rcases family_descends (prefixWord ++ tailWord_604246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604308 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 6]
def baseStart_604308 : Nat := 118140960795 + 604308 * 2 ^ 59
def prefixEnd_604308 : Nat := 4983230072969 + 3 ^ 40 * 604308 * 2
def baseEnd_604308 : Nat := 137911318825478611498153

theorem tailTrace_604308 : CollatzResearch.WordTrace tailWord_604308 prefixEnd_604308 137911318825478611498153 := by
  unfold tailWord_604308
  simp only [CollatzResearch.WordTrace]
  refine ⟨11020461747351399217366789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14693948996468532289822385 11020461747351399217366789)
  ·
    refine ⟨2066336577628387353256273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11020461747351399217366789 2066336577628387353256273)
    ·
      refine ⟨1549752433221290514942205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2066336577628387353256273 1549752433221290514942205)
      ·
        refine ⟨581157162457983943103327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1549752433221290514942205 581157162457983943103327)
        ·
          refine ⟨871735743686975914654991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581157162457983943103327 871735743686975914654991)
          ·
            refine ⟨1307603615530463871982487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871735743686975914654991 1307603615530463871982487)
            ·
              refine ⟨1961405423295695807973731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307603615530463871982487 1961405423295695807973731)
              ·
                refine ⟨2942108134943543711960597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961405423295695807973731 2942108134943543711960597)
                ·
                  refine ⟨137911318825478611498153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2942108134943543711960597 137911318825478611498153)
                  ·
                    rfl

theorem cell21_604308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_604308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604308 prefixEnd_604308 := by exact prefixLift 604308
  have htrace : WordTrace (prefixWord ++ tailWord_604308) baseStart_604308 baseEnd_604308 := by
    simpa [prefixWord, tailWord_604308, baseEnd_604308] using wordTrace_append hprefix tailTrace_604308
  have hstable : (prefixWord ++ tailWord_604308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604308).length < 2 ^ (prefixWord ++ tailWord_604308).sum := by decide
  have hdescent : baseEnd_604308 < baseStart_604308 := by decide
  rcases family_descends (prefixWord ++ tailWord_604308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604370 : List Nat := [3, 2, 2, 2, 1, 3, 3, 2, 3]
def baseStart_604370 : Nat := 118140960795 + 604370 * 2 ^ 59
def prefixEnd_604370 : Nat := 4983230072969 + 3 ^ 40 * 604370 * 2
def baseEnd_604370 : Nat := 137925468070180281464693

theorem tailTrace_604370 : CollatzResearch.WordTrace tailWord_604370 prefixEnd_604370 137925468070180281464693 := by
  unfold tailWord_604370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5510796205119545755872641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14695456546985455348993709 5510796205119545755872641)
  ·
    refine ⟨4133097153839659316904481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5510796205119545755872641 4133097153839659316904481)
    ·
      refine ⟨3099822865379744487678361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4133097153839659316904481 3099822865379744487678361)
      ·
        refine ⟨2324867149034808365758771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3099822865379744487678361 2324867149034808365758771)
        ·
          refine ⟨3487300723552212548638157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324867149034808365758771 3487300723552212548638157)
          ·
            refine ⟨1307737771332079705739309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3487300723552212548638157 1307737771332079705739309)
            ·
              refine ⟨490401664249529889652241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1307737771332079705739309 490401664249529889652241)
              ·
                refine ⟨367801248187147417239181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490401664249529889652241 367801248187147417239181)
                ·
                  refine ⟨137925468070180281464693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367801248187147417239181 137925468070180281464693)
                  ·
                    rfl

theorem cell21_604370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_604370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604370 prefixEnd_604370 := by exact prefixLift 604370
  have htrace : WordTrace (prefixWord ++ tailWord_604370) baseStart_604370 baseEnd_604370 := by
    simpa [prefixWord, tailWord_604370, baseEnd_604370] using wordTrace_append hprefix tailTrace_604370
  have hstable : (prefixWord ++ tailWord_604370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604370).length < 2 ^ (prefixWord ++ tailWord_604370).sum := by decide
  have hdescent : baseEnd_604370 < baseStart_604370 := by decide
  rcases family_descends (prefixWord ++ tailWord_604370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604381 : List Nat := [1, 4, 3, 2, 1, 1, 1, 8]
def baseStart_604381 : Nat := 118140960795 + 604381 * 2 ^ 59
def prefixEnd_604381 : Nat := 4983230072969 + 3 ^ 40 * 604381 * 2
def baseEnd_604381 : Nat := 45975992806682235593779

theorem tailTrace_604381 : CollatzResearch.WordTrace tailWord_604381 prefixEnd_604381 45975992806682235593779 := by
  unfold tailWord_604381
  simp only [CollatzResearch.WordTrace]
  refine ⟨22043586023438331902140997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14695724015625554601427331 22043586023438331902140997)
  ·
    refine ⟨4133172379394687231651437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22043586023438331902140997 4133172379394687231651437)
    ·
      refine ⟨1549939642273007711869289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4133172379394687231651437 1549939642273007711869289)
      ·
        refine ⟨1162454731704755783901967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1549939642273007711869289 1162454731704755783901967)
        ·
          refine ⟨1743682097557133675852951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162454731704755783901967 1743682097557133675852951)
          ·
            refine ⟨2615523146335700513779427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743682097557133675852951 2615523146335700513779427)
            ·
              refine ⟨3923284719503550770669141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615523146335700513779427 3923284719503550770669141)
              ·
                refine ⟨45975992806682235593779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3923284719503550770669141 45975992806682235593779)
                ·
                  rfl

theorem cell21_604381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 8].length) (baseStart_604381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604381 prefixEnd_604381 := by exact prefixLift 604381
  have htrace : WordTrace (prefixWord ++ tailWord_604381) baseStart_604381 baseEnd_604381 := by
    simpa [prefixWord, tailWord_604381, baseEnd_604381] using wordTrace_append hprefix tailTrace_604381
  have hstable : (prefixWord ++ tailWord_604381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604381).length < 2 ^ (prefixWord ++ tailWord_604381).sum := by decide
  have hdescent : baseEnd_604381 < baseStart_604381 := by decide
  rcases family_descends (prefixWord ++ tailWord_604381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604409 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 6]
def baseStart_604409 : Nat := 118140960795 + 604409 * 2 ^ 59
def prefixEnd_604409 : Nat := 4983230072969 + 3 ^ 40 * 604409 * 2
def baseEnd_604409 : Nat := 137934368401524880314613

theorem tailTrace_604409 : CollatzResearch.WordTrace tailWord_604409 prefixEnd_604409 137934368401524880314613 := by
  unfold tailWord_604409
  simp only [CollatzResearch.WordTrace]
  refine ⟨22044607267336892684160281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14696404844891261789440187 22044607267336892684160281)
  ·
    refine ⟨16533455450502669513120211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22044607267336892684160281 16533455450502669513120211)
    ·
      refine ⟨24800183175754004269680317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16533455450502669513120211 24800183175754004269680317)
      ·
        refine ⟨9300068690907751601130119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24800183175754004269680317 9300068690907751601130119)
        ·
          refine ⟨13950103036361627401695179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9300068690907751601130119 13950103036361627401695179)
          ·
            refine ⟨20925154554542441102542769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13950103036361627401695179 20925154554542441102542769)
            ·
              refine ⟨15693865915906830826907077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20925154554542441102542769 15693865915906830826907077)
              ·
                refine ⟨2942599859232530780045077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15693865915906830826907077 2942599859232530780045077)
                ·
                  refine ⟨137934368401524880314613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2942599859232530780045077 137934368401524880314613)
                  ·
                    rfl

theorem cell21_604409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_604409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604409 prefixEnd_604409 := by exact prefixLift 604409
  have htrace : WordTrace (prefixWord ++ tailWord_604409) baseStart_604409 baseEnd_604409 := by
    simpa [prefixWord, tailWord_604409, baseEnd_604409] using wordTrace_append hprefix tailTrace_604409
  have hstable : (prefixWord ++ tailWord_604409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604409).length < 2 ^ (prefixWord ++ tailWord_604409).sum := by decide
  have hdescent : baseEnd_604409 < baseStart_604409 := by decide
  rcases family_descends (prefixWord ++ tailWord_604409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604426 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_604426 : Nat := 118140960795 + 604426 * 2 ^ 59
def prefixEnd_604426 : Nat := 4983230072969 + 3 ^ 40 * 604426 * 2
def baseEnd_604426 : Nat := 137938248033136628531245

theorem tailTrace_604426 : CollatzResearch.WordTrace tailWord_604426 prefixEnd_604426 137938248033136628531245 := by
  unfold tailWord_604426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5511306827068826146882283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14696818205516869725019421 5511306827068826146882283)
  ·
    refine ⟨8266960240603239220323425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5511306827068826146882283 8266960240603239220323425)
    ·
      refine ⟨6200220180452429415242569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8266960240603239220323425 6200220180452429415242569)
      ·
        refine ⟨4650165135339322061431927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6200220180452429415242569 4650165135339322061431927)
        ·
          refine ⟨6975247703008983092147891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4650165135339322061431927 6975247703008983092147891)
          ·
            refine ⟨10462871554513474638221837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6975247703008983092147891 10462871554513474638221837)
            ·
              refine ⟨3923576832942552989333189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10462871554513474638221837 3923576832942552989333189)
              ·
                refine ⟨735670656176728685499973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3923576832942552989333189 735670656176728685499973)
                ·
                  refine ⟨137938248033136628531245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 735670656176728685499973 137938248033136628531245)
                  ·
                    rfl

theorem cell21_604426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_604426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604426 prefixEnd_604426 := by exact prefixLift 604426
  have htrace : WordTrace (prefixWord ++ tailWord_604426) baseStart_604426 baseEnd_604426 := by
    simpa [prefixWord, tailWord_604426, baseEnd_604426] using wordTrace_append hprefix tailTrace_604426
  have hstable : (prefixWord ++ tailWord_604426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604426).length < 2 ^ (prefixWord ++ tailWord_604426).sum := by decide
  have hdescent : baseEnd_604426 < baseStart_604426 := by decide
  rcases family_descends (prefixWord ++ tailWord_604426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604488 : List Nat := [2, 1, 3, 1, 1, 2, 4, 4, 3]
def baseStart_604488 : Nat := 118140960795 + 604488 * 2 ^ 59
def prefixEnd_604488 : Nat := 4983230072969 + 3 ^ 40 * 604488 * 2
def baseEnd_604488 : Nat := 137952397277838298497785

theorem tailTrace_604488 : CollatzResearch.WordTrace tailWord_604488 prefixEnd_604488 137952397277838298497785 := by
  unfold tailWord_604488
  simp only [CollatzResearch.WordTrace]
  refine ⟨11023744317025344588143059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14698325756033792784190745 11023744317025344588143059)
  ·
    refine ⟨16535616475538016882214589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11023744317025344588143059 16535616475538016882214589)
    ·
      refine ⟨6200856178326756330830471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16535616475538016882214589 6200856178326756330830471)
      ·
        refine ⟨9301284267490134496245707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6200856178326756330830471 9301284267490134496245707)
        ·
          refine ⟨13951926401235201744368561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9301284267490134496245707 13951926401235201744368561)
          ·
            refine ⟨10463944800926401308276421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13951926401235201744368561 10463944800926401308276421)
            ·
              refine ⟨1961989650173700245301829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10463944800926401308276421 1961989650173700245301829)
              ·
                refine ⟨367873059407568795994093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1961989650173700245301829 367873059407568795994093)
                ·
                  refine ⟨137952397277838298497785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367873059407568795994093 137952397277838298497785)
                  ·
                    rfl

theorem cell21_604488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 3].length) (baseStart_604488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604488 prefixEnd_604488 := by exact prefixLift 604488
  have htrace : WordTrace (prefixWord ++ tailWord_604488) baseStart_604488 baseEnd_604488 := by
    simpa [prefixWord, tailWord_604488, baseEnd_604488] using wordTrace_append hprefix tailTrace_604488
  have hstable : (prefixWord ++ tailWord_604488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604488).length < 2 ^ (prefixWord ++ tailWord_604488).sum := by decide
  have hdescent : baseEnd_604488 < baseStart_604488 := by decide
  rcases family_descends (prefixWord ++ tailWord_604488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604508 : List Nat := [2, 2, 4, 3, 2, 1, 2, 5]
def baseStart_604508 : Nat := 118140960795 + 604508 * 2 ^ 59
def prefixEnd_604508 : Nat := 4983230072969 + 3 ^ 40 * 604508 * 2
def baseEnd_604508 : Nat := 45985653850107569388137

theorem tailTrace_604508 : CollatzResearch.WordTrace tailWord_604508 prefixEnd_604508 45985653850107569388137 := by
  unfold tailWord_604508
  simp only [CollatzResearch.WordTrace]
  refine ⟨11024109046989116296007089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14698812062652155061342785 11024109046989116296007089)
  ·
    refine ⟨8268081785241837222005317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11024109046989116296007089 8268081785241837222005317)
    ·
      refine ⟨1550265334732844479125997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8268081785241837222005317 1550265334732844479125997)
      ·
        refine ⟨581349500524816679672249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1550265334732844479125997 581349500524816679672249)
        ·
          refine ⟨436012125393612509754187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581349500524816679672249 436012125393612509754187)
          ·
            refine ⟨654018188090418764631281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436012125393612509754187 654018188090418764631281)
            ·
              refine ⟨490513641067814073473461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654018188090418764631281 490513641067814073473461)
              ·
                refine ⟨45985653850107569388137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 490513641067814073473461 45985653850107569388137)
                ·
                  rfl

theorem cell21_604508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 5].length) (baseStart_604508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604508 prefixEnd_604508 := by exact prefixLift 604508
  have htrace : WordTrace (prefixWord ++ tailWord_604508) baseStart_604508 baseEnd_604508 := by
    simpa [prefixWord, tailWord_604508, baseEnd_604508] using wordTrace_append hprefix tailTrace_604508
  have hstable : (prefixWord ++ tailWord_604508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604508).length < 2 ^ (prefixWord ++ tailWord_604508).sum := by decide
  have hdescent : baseEnd_604508 < baseStart_604508 := by decide
  rcases family_descends (prefixWord ++ tailWord_604508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604516 : List Nat := [2, 3, 1, 1, 3, 1, 3, 7]
def baseStart_604516 : Nat := 118140960795 + 604516 * 2 ^ 59
def prefixEnd_604516 : Nat := 4983230072969 + 3 ^ 40 * 604516 * 2
def baseEnd_604516 : Nat := 45986262419772157343687

theorem tailTrace_604516 : CollatzResearch.WordTrace tailWord_604516 prefixEnd_604516 45986262419772157343687 := by
  unfold tailWord_604516
  simp only [CollatzResearch.WordTrace]
  refine ⟨11024254938974624979152701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14699006585299499972203601 11024254938974624979152701)
  ·
    refine ⟨4134095602115484367182263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11024254938974624979152701 4134095602115484367182263)
    ·
      refine ⟨6201143403173226550773395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4134095602115484367182263 6201143403173226550773395)
      ·
        refine ⟨9301715104759839826160093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6201143403173226550773395 9301715104759839826160093)
        ·
          refine ⟨3488143164284939934810035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9301715104759839826160093 3488143164284939934810035)
          ·
            refine ⟨5232214746427409902215053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3488143164284939934810035 5232214746427409902215053)
            ·
              refine ⟨1962080529910278713330645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5232214746427409902215053 1962080529910278713330645)
              ·
                refine ⟨45986262419772157343687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1962080529910278713330645 45986262419772157343687)
                ·
                  rfl

theorem cell21_604516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_604516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604516 prefixEnd_604516 := by exact prefixLift 604516
  have htrace : WordTrace (prefixWord ++ tailWord_604516) baseStart_604516 baseEnd_604516 := by
    simpa [prefixWord, tailWord_604516, baseEnd_604516] using wordTrace_append hprefix tailTrace_604516
  have hstable : (prefixWord ++ tailWord_604516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604516).length < 2 ^ (prefixWord ++ tailWord_604516).sum := by decide
  have hdescent : baseEnd_604516 < baseStart_604516 := by decide
  rcases family_descends (prefixWord ++ tailWord_604516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604522 : List Nat := [3, 1, 3, 3, 1, 3, 1, 3, 3]
def baseStart_604522 : Nat := 118140960795 + 604522 * 2 ^ 59
def prefixEnd_604522 : Nat := 4983230072969 + 3 ^ 40 * 604522 * 2
def baseEnd_604522 : Nat := 137960156541061794931049

theorem tailTrace_604522 : CollatzResearch.WordTrace tailWord_604522 prefixEnd_604522 137960156541061794931049 := by
  unfold tailWord_604522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5512182178981878245755955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14699152477285008655349213 5512182178981878245755955)
  ·
    refine ⟨8268273268472817368633933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5512182178981878245755955 8268273268472817368633933)
    ·
      refine ⟨3100602475677306513237725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8268273268472817368633933 3100602475677306513237725)
      ·
        refine ⟨1162725928378989942464147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3100602475677306513237725 1162725928378989942464147)
        ·
          refine ⟨1744088892568484913696221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162725928378989942464147 1744088892568484913696221)
          ·
            refine ⟨654033334713181842636083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1744088892568484913696221 654033334713181842636083)
            ·
              refine ⟨981050002069772763954125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654033334713181842636083 981050002069772763954125)
              ·
                refine ⟨367893750776164786482797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 981050002069772763954125 367893750776164786482797)
                ·
                  refine ⟨137960156541061794931049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367893750776164786482797 137960156541061794931049)
                  ·
                    rfl

theorem cell21_604522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_604522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604522 prefixEnd_604522 := by exact prefixLift 604522
  have htrace : WordTrace (prefixWord ++ tailWord_604522) baseStart_604522 baseEnd_604522 := by
    simpa [prefixWord, tailWord_604522, baseEnd_604522] using wordTrace_append hprefix tailTrace_604522
  have hstable : (prefixWord ++ tailWord_604522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604522).length < 2 ^ (prefixWord ++ tailWord_604522).sum := by decide
  have hdescent : baseEnd_604522 < baseStart_604522 := by decide
  rcases family_descends (prefixWord ++ tailWord_604522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604533 : List Nat := [1, 3, 4, 1, 2, 3, 7]
def baseStart_604533 : Nat := 118140960795 + 604533 * 2 ^ 59
def prefixEnd_604533 : Nat := 4983230072969 + 3 ^ 40 * 604533 * 2
def baseEnd_604533 : Nat := 15329185210103135583077

theorem tailTrace_604533 : CollatzResearch.WordTrace tailWord_604533 prefixEnd_604533 15329185210103135583077 := by
  unfold tailWord_604533
  simp only [CollatzResearch.WordTrace]
  refine ⟨22049129918887661861674253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14699419945925107907782835 22049129918887661861674253)
  ·
    refine ⟨8268423719582873198127845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22049129918887661861674253 8268423719582873198127845)
    ·
      refine ⟨1550329447421788724648971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8268423719582873198127845 1550329447421788724648971)
      ·
        refine ⟨2325494171132683086973457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550329447421788724648971 2325494171132683086973457)
        ·
          refine ⟨1744120628349512315230093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2325494171132683086973457 1744120628349512315230093)
          ·
            refine ⟨654045235631067118211285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1744120628349512315230093 654045235631067118211285)
            ·
              refine ⟨15329185210103135583077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 654045235631067118211285 15329185210103135583077)
              ·
                rfl

theorem cell21_604533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 7].length) (baseStart_604533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604533 prefixEnd_604533 := by exact prefixLift 604533
  have htrace : WordTrace (prefixWord ++ tailWord_604533) baseStart_604533 baseEnd_604533 := by
    simpa [prefixWord, tailWord_604533, baseEnd_604533] using wordTrace_append hprefix tailTrace_604533
  have hstable : (prefixWord ++ tailWord_604533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604533).length < 2 ^ (prefixWord ++ tailWord_604533).sum := by decide
  have hdescent : baseEnd_604533 < baseStart_604533 := by decide
  rcases family_descends (prefixWord ++ tailWord_604533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604640 : List Nat := [2, 1, 1, 3, 1, 1, 6, 3, 3]
def baseStart_604640 : Nat := 118140960795 + 604640 * 2 ^ 59
def prefixEnd_604640 : Nat := 4983230072969 + 3 ^ 40 * 604640 * 2
def baseEnd_604640 : Nat := 137987085748719811964141

theorem tailTrace_604640 : CollatzResearch.WordTrace tailWord_604640 prefixEnd_604640 137987085748719811964141 := by
  unfold tailWord_604640
  simp only [CollatzResearch.WordTrace]
  refine ⟨11026516264750009567909687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14702021686333346090546249 11026516264750009567909687)
  ·
    refine ⟨16539774397125014351864531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11026516264750009567909687 16539774397125014351864531)
    ·
      refine ⟨24809661595687521527796797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16539774397125014351864531 24809661595687521527796797)
      ·
        refine ⟨9303623098382820572923799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24809661595687521527796797 9303623098382820572923799)
        ·
          refine ⟨13955434647574230859385699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9303623098382820572923799 13955434647574230859385699)
          ·
            refine ⟨20933151971361346289078549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13955434647574230859385699 20933151971361346289078549)
            ·
              refine ⟨981241498657563107300557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20933151971361346289078549 981241498657563107300557)
              ·
                refine ⟨367965561996586165237709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 981241498657563107300557 367965561996586165237709)
                ·
                  refine ⟨137987085748719811964141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367965561996586165237709 137987085748719811964141)
                  ·
                    rfl

theorem cell21_604640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 3].length) (baseStart_604640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604640 prefixEnd_604640 := by exact prefixLift 604640
  have htrace : WordTrace (prefixWord ++ tailWord_604640) baseStart_604640 baseEnd_604640 := by
    simpa [prefixWord, tailWord_604640, baseEnd_604640] using wordTrace_append hprefix tailTrace_604640
  have hstable : (prefixWord ++ tailWord_604640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604640).length < 2 ^ (prefixWord ++ tailWord_604640).sum := by decide
  have hdescent : baseEnd_604640 < baseStart_604640 := by decide
  rcases family_descends (prefixWord ++ tailWord_604640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604651 : List Nat := [1, 1, 1, 1, 2, 3, 12]
def baseStart_604651 : Nat := 118140960795 + 604651 * 2 ^ 59
def prefixEnd_604651 : Nat := 4983230072969 + 3 ^ 40 * 604651 * 2
def baseEnd_604651 : Nat := 15332177344287359697865

theorem tailTrace_604651 : CollatzResearch.WordTrace tailWord_604651 prefixEnd_604651 15332177344287359697865 := by
  unfold tailWord_604651
  simp only [CollatzResearch.WordTrace]
  refine ⟨22053433732460168014469807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14702289154973445342979871 22053433732460168014469807)
  ·
    refine ⟨33080150598690252021704711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22053433732460168014469807 33080150598690252021704711)
    ·
      refine ⟨49620225898035378032557067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33080150598690252021704711 49620225898035378032557067)
      ·
        refine ⟨74430338847053067048835601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49620225898035378032557067 74430338847053067048835601)
        ·
          refine ⟨55822754135289800286626701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74430338847053067048835601 55822754135289800286626701)
          ·
            refine ⟨20933532800733675107485013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55822754135289800286626701 20933532800733675107485013)
            ·
              refine ⟨15332177344287359697865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 20933532800733675107485013 15332177344287359697865)
              ·
                rfl

theorem cell21_604651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 12].length) (baseStart_604651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604651 prefixEnd_604651 := by exact prefixLift 604651
  have htrace : WordTrace (prefixWord ++ tailWord_604651) baseStart_604651 baseEnd_604651 := by
    simpa [prefixWord, tailWord_604651, baseEnd_604651] using wordTrace_append hprefix tailTrace_604651
  have hstable : (prefixWord ++ tailWord_604651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604651).length < 2 ^ (prefixWord ++ tailWord_604651).sum := by decide
  have hdescent : baseEnd_604651 < baseStart_604651 := by decide
  rcases family_descends (prefixWord ++ tailWord_604651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604654 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_604654 : Nat := 118140960795 + 604654 * 2 ^ 59
def prefixEnd_604654 : Nat := 4983230072969 + 3 ^ 40 * 604654 * 2
def baseEnd_604654 : Nat := 137990280739458898730779

theorem tailTrace_604654 : CollatzResearch.WordTrace tailWord_604654 prefixEnd_604654 137990280739458898730779 := by
  unfold tailWord_604654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2756692893931162440853627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14702362100966199684552677 2756692893931162440853627)
  ·
    refine ⟨4135039340896743661280441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2756692893931162440853627 4135039340896743661280441)
    ·
      refine ⟨3101279505672557745960331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4135039340896743661280441 3101279505672557745960331)
      ·
        refine ⟨4651919258508836618940497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101279505672557745960331 4651919258508836618940497)
        ·
          refine ⟨3488939443881627464205373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4651919258508836618940497 3488939443881627464205373)
          ·
            refine ⟨1308352291455610299077015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3488939443881627464205373 1308352291455610299077015)
            ·
              refine ⟨1962528437183415448615523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308352291455610299077015 1962528437183415448615523)
              ·
                refine ⟨2943792655775123172923285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962528437183415448615523 2943792655775123172923285)
                ·
                  refine ⟨137990280739458898730779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2943792655775123172923285 137990280739458898730779)
                  ·
                    rfl

theorem cell21_604654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_604654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604654 prefixEnd_604654 := by exact prefixLift 604654
  have htrace : WordTrace (prefixWord ++ tailWord_604654) baseStart_604654 baseEnd_604654 := by
    simpa [prefixWord, tailWord_604654, baseEnd_604654] using wordTrace_append hprefix tailTrace_604654
  have hstable : (prefixWord ++ tailWord_604654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604654).length < 2 ^ (prefixWord ++ tailWord_604654).sum := by decide
  have hdescent : baseEnd_604654 < baseStart_604654 := by decide
  rcases family_descends (prefixWord ++ tailWord_604654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604730 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_604730 : Nat := 118140960795 + 604730 * 2 ^ 59
def prefixEnd_604730 : Nat := 4983230072969 + 3 ^ 40 * 604730 * 2
def baseEnd_604730 : Nat := 138007624974899655463957

theorem tailTrace_604730 : CollatzResearch.WordTrace tailWord_604730 prefixEnd_604730 138007624974899655463957 := by
  unfold tailWord_604730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5514078774793491126648911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14704210066115976337730429 5514078774793491126648911)
  ·
    refine ⟨8271118162190236689973367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5514078774793491126648911 8271118162190236689973367)
    ·
      refine ⟨12406677243285355034960051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8271118162190236689973367 12406677243285355034960051)
      ·
        refine ⟨18610015864928032552440077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12406677243285355034960051 18610015864928032552440077)
        ·
          refine ⟨6978755949348012207165029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18610015864928032552440077 6978755949348012207165029)
          ·
            refine ⟨1308516740502752288843443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6978755949348012207165029 1308516740502752288843443)
            ·
              refine ⟨1962775110754128433265165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308516740502752288843443 1962775110754128433265165)
              ·
                refine ⟨736040666532798162474437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1962775110754128433265165 736040666532798162474437)
                ·
                  refine ⟨138007624974899655463957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 736040666532798162474437 138007624974899655463957)
                  ·
                    rfl

theorem cell21_604730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_604730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604730 prefixEnd_604730 := by exact prefixLift 604730
  have htrace : WordTrace (prefixWord ++ tailWord_604730) baseStart_604730 baseEnd_604730 := by
    simpa [prefixWord, tailWord_604730, baseEnd_604730] using wordTrace_append hprefix tailTrace_604730
  have hstable : (prefixWord ++ tailWord_604730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604730).length < 2 ^ (prefixWord ++ tailWord_604730).sum := by decide
  have hdescent : baseEnd_604730 < baseStart_604730 := by decide
  rcases family_descends (prefixWord ++ tailWord_604730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604803 : List Nat := [1, 1, 1, 3, 3, 1, 2, 9]
def baseStart_604803 : Nat := 118140960795 + 604803 * 2 ^ 59
def prefixEnd_604803 : Nat := 4983230072969 + 3 ^ 40 * 604803 * 2
def baseEnd_604803 : Nat := 46008094856489250249047

theorem tailTrace_604803 : CollatzResearch.WordTrace tailWord_604803 prefixEnd_604803 46008094856489250249047 := by
  unfold tailWord_604803
  simp only [CollatzResearch.WordTrace]
  refine ⟨22058977627909497974003063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14705985085272998649335375 22058977627909497974003063)
  ·
    refine ⟨33088466441864246961004595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22058977627909497974003063 33088466441864246961004595)
    ·
      refine ⟨49632699662796370441506893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33088466441864246961004595 49632699662796370441506893)
      ·
        refine ⟨18612262373548638915565085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49632699662796370441506893 18612262373548638915565085)
        ·
          refine ⟨6979598390080739593336907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18612262373548638915565085 6979598390080739593336907)
          ·
            refine ⟨10469397585121109390005361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6979598390080739593336907 10469397585121109390005361)
            ·
              refine ⟨7852048188840832042504021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10469397585121109390005361 7852048188840832042504021)
              ·
                refine ⟨46008094856489250249047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7852048188840832042504021 46008094856489250249047)
                ·
                  rfl

theorem cell21_604803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 9].length) (baseStart_604803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604803 prefixEnd_604803 := by exact prefixLift 604803
  have htrace : WordTrace (prefixWord ++ tailWord_604803) baseStart_604803 baseEnd_604803 := by
    simpa [prefixWord, tailWord_604803, baseEnd_604803] using wordTrace_append hprefix tailTrace_604803
  have hstable : (prefixWord ++ tailWord_604803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604803).length < 2 ^ (prefixWord ++ tailWord_604803).sum := by decide
  have hdescent : baseEnd_604803 < baseStart_604803 := by decide
  rcases family_descends (prefixWord ++ tailWord_604803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604854 : List Nat := [5, 1, 3, 1, 2, 1, 1, 7]
def baseStart_604854 : Nat := 118140960795 + 604854 * 2 ^ 59
def prefixEnd_604854 : Nat := 4983230072969 + 3 ^ 40 * 604854 * 2
def baseEnd_604854 : Nat := 46011974488100998465679

theorem tailTrace_604854 : CollatzResearch.WordTrace tailWord_604854 prefixEnd_604854 46011974488100998465679 := by
  unfold tailWord_604854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1378802359420295855256851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14707225167149822456073077 1378802359420295855256851)
  ·
    refine ⟨2068203539130443782885277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1378802359420295855256851 2068203539130443782885277)
    ·
      refine ⟨775576327173916418581979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2068203539130443782885277 775576327173916418581979)
      ·
        refine ⟨1163364490760874627872969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775576327173916418581979 1163364490760874627872969)
        ·
          refine ⟨872523368070655970904727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1163364490760874627872969 872523368070655970904727)
          ·
            refine ⟨1308785052105983956357091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872523368070655970904727 1308785052105983956357091)
            ·
              refine ⟨1963177578158975934535637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308785052105983956357091 1963177578158975934535637)
              ·
                refine ⟨46011974488100998465679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1963177578158975934535637 46011974488100998465679)
                ·
                  rfl

theorem cell21_604854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_604854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604854 prefixEnd_604854 := by exact prefixLift 604854
  have htrace : WordTrace (prefixWord ++ tailWord_604854) baseStart_604854 baseEnd_604854 := by
    simpa [prefixWord, tailWord_604854, baseEnd_604854] using wordTrace_append hprefix tailTrace_604854
  have hstable : (prefixWord ++ tailWord_604854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604854).length < 2 ^ (prefixWord ++ tailWord_604854).sum := by decide
  have hdescent : baseEnd_604854 < baseStart_604854 := by decide
  rcases family_descends (prefixWord ++ tailWord_604854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604885 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 5]
def baseStart_604885 : Nat := 118140960795 + 604885 * 2 ^ 59
def prefixEnd_604885 : Nat := 4983230072969 + 3 ^ 40 * 604885 * 2
def baseEnd_604885 : Nat := 138042998086653830380307

theorem tailTrace_604885 : CollatzResearch.WordTrace tailWord_604885 prefixEnd_604885 138042998086653830380307 := by
  unfold tailWord_604885
  simp only [CollatzResearch.WordTrace]
  refine ⟨22061968413612425978488109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14707978942408283985658739 22061968413612425978488109)
  ·
    refine ⟨8273238155104659741933041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22061968413612425978488109 8273238155104659741933041)
    ·
      refine ⟨6204928616328494806449781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8273238155104659741933041 6204928616328494806449781)
      ·
        refine ⟨581712057780796388104667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6204928616328494806449781 581712057780796388104667)
        ·
          refine ⟨872568086671194582157001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581712057780796388104667 872568086671194582157001)
          ·
            refine ⟨654426065003395936617751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 872568086671194582157001 654426065003395936617751)
            ·
              refine ⟨981639097505093904926627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654426065003395936617751 981639097505093904926627)
              ·
                refine ⟨1472458646257640857389941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981639097505093904926627 1472458646257640857389941)
                ·
                  refine ⟨138042998086653830380307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1472458646257640857389941 138042998086653830380307)
                  ·
                    rfl

theorem cell21_604885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_604885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604885 prefixEnd_604885 := by exact prefixLift 604885
  have htrace : WordTrace (prefixWord ++ tailWord_604885) baseStart_604885 baseEnd_604885 := by
    simpa [prefixWord, tailWord_604885, baseEnd_604885] using wordTrace_append hprefix tailTrace_604885
  have hstable : (prefixWord ++ tailWord_604885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604885).length < 2 ^ (prefixWord ++ tailWord_604885).sum := by decide
  have hdescent : baseEnd_604885 < baseStart_604885 := by decide
  rcases family_descends (prefixWord ++ tailWord_604885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604899 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 4]
def baseStart_604899 : Nat := 118140960795 + 604899 * 2 ^ 59
def prefixEnd_604899 : Nat := 4983230072969 + 3 ^ 40 * 604899 * 2
def baseEnd_604899 : Nat := 138046193077392917146945

theorem tailTrace_604899 : CollatzResearch.WordTrace tailWord_604899 prefixEnd_604899 138046193077392917146945 := by
  unfold tailWord_604899
  simp only [CollatzResearch.WordTrace]
  refine ⟨22062479035561706369497751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14708319357041137579665167 22062479035561706369497751)
  ·
    refine ⟨33093718553342559554246627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22062479035561706369497751 33093718553342559554246627)
    ·
      refine ⟨49640577830013839331369941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33093718553342559554246627 49640577830013839331369941)
      ·
        refine ⟨1163451042890949359328983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 49640577830013839331369941 1163451042890949359328983)
        ·
          refine ⟨1745176564336424038993475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1163451042890949359328983 1745176564336424038993475)
          ·
            refine ⟨2617764846504636058490213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1745176564336424038993475 2617764846504636058490213)
            ·
              refine ⟨490830908719619260966915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2617764846504636058490213 490830908719619260966915)
              ·
                refine ⟨736246363079428891450373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490830908719619260966915 736246363079428891450373)
                ·
                  refine ⟨138046193077392917146945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 736246363079428891450373 138046193077392917146945)
                  ·
                    rfl

theorem cell21_604899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 4].length) (baseStart_604899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604899 prefixEnd_604899 := by exact prefixLift 604899
  have htrace : WordTrace (prefixWord ++ tailWord_604899) baseStart_604899 baseEnd_604899 := by
    simpa [prefixWord, tailWord_604899, baseEnd_604899] using wordTrace_append hprefix tailTrace_604899
  have hstable : (prefixWord ++ tailWord_604899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604899).length < 2 ^ (prefixWord ++ tailWord_604899).sum := by decide
  have hdescent : baseEnd_604899 < baseStart_604899 := by decide
  rcases family_descends (prefixWord ++ tailWord_604899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604927 : List Nat := [1, 1, 2, 2, 1, 3, 1, 7, 3]
def baseStart_604927 : Nat := 118140960795 + 604927 * 2 ^ 59
def prefixEnd_604927 : Nat := 4983230072969 + 3 ^ 40 * 604927 * 2
def baseEnd_604927 : Nat := 138052583058871090680221

theorem tailTrace_604927 : CollatzResearch.WordTrace tailWord_604927 prefixEnd_604927 138052583058871090680221 := by
  unfold tailWord_604927
  simp only [CollatzResearch.WordTrace]
  refine ⟨22063500279460267151517035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14709000186306844767678023 22063500279460267151517035)
  ·
    refine ⟨33095250419190400727275553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22063500279460267151517035 33095250419190400727275553)
    ·
      refine ⟨24821437814392800545456665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33095250419190400727275553 24821437814392800545456665)
      ·
        refine ⟨18616078360794600409092499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24821437814392800545456665 18616078360794600409092499)
        ·
          refine ⟨27924117541191900613638749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18616078360794600409092499 27924117541191900613638749)
          ·
            refine ⟨10471544077946962730114531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27924117541191900613638749 10471544077946962730114531)
            ·
              refine ⟨15707316116920444095171797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10471544077946962730114531 15707316116920444095171797)
              ·
                refine ⟨368140221490322908480589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15707316116920444095171797 368140221490322908480589)
                ·
                  refine ⟨138052583058871090680221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368140221490322908480589 138052583058871090680221)
                  ·
                    rfl

theorem cell21_604927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 3].length) (baseStart_604927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604927 prefixEnd_604927 := by exact prefixLift 604927
  have htrace : WordTrace (prefixWord ++ tailWord_604927) baseStart_604927 baseEnd_604927 := by
    simpa [prefixWord, tailWord_604927, baseEnd_604927] using wordTrace_append hprefix tailTrace_604927
  have hstable : (prefixWord ++ tailWord_604927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604927).length < 2 ^ (prefixWord ++ tailWord_604927).sum := by decide
  have hdescent : baseEnd_604927 < baseStart_604927 := by decide
  rcases family_descends (prefixWord ++ tailWord_604927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_604972 : List Nat := [2, 2, 1, 1, 1, 4, 5, 5]
def baseStart_604972 : Nat := 118140960795 + 604972 * 2 ^ 59
def prefixEnd_604972 : Nat := 4983230072969 + 3 ^ 40 * 604972 * 2
def baseEnd_604972 : Nat := 46020950890653670810043

theorem tailTrace_604972 : CollatzResearch.WordTrace tailWord_604972 prefixEnd_604972 46020950890653670810043 := by
  unfold tailWord_604972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11032570782148619918452585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14710094376198159891270113 11032570782148619918452585)
  ·
    refine ⟨8274428086611464938839439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11032570782148619918452585 8274428086611464938839439)
    ·
      refine ⟨12411642129917197408259159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8274428086611464938839439 12411642129917197408259159)
      ·
        refine ⟨18617463194875796112388739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12411642129917197408259159 18617463194875796112388739)
        ·
          refine ⟨27926194792313694168583109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18617463194875796112388739 27926194792313694168583109)
          ·
            refine ⟨5236161523558817656609333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27926194792313694168583109 5236161523558817656609333)
            ·
              refine ⟨490890142833639155307125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5236161523558817656609333 490890142833639155307125)
              ·
                refine ⟨46020950890653670810043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 490890142833639155307125 46020950890653670810043)
                ·
                  rfl

theorem cell21_604972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_604972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_604972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_604972 prefixEnd_604972 := by exact prefixLift 604972
  have htrace : WordTrace (prefixWord ++ tailWord_604972) baseStart_604972 baseEnd_604972 := by
    simpa [prefixWord, tailWord_604972, baseEnd_604972] using wordTrace_append hprefix tailTrace_604972
  have hstable : (prefixWord ++ tailWord_604972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_604972).length < 2 ^ (prefixWord ++ tailWord_604972).sum := by decide
  have hdescent : baseEnd_604972 < baseStart_604972 := by decide
  rcases family_descends (prefixWord ++ tailWord_604972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605054 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_605054 : Nat := 118140960795 + 605054 * 2 ^ 59
def prefixEnd_605054 : Nat := 4983230072969 + 3 ^ 40 * 605054 * 2
def baseEnd_605054 : Nat := 138081566189147092063295

theorem tailTrace_605054 : CollatzResearch.WordTrace tailWord_605054 prefixEnd_605054 138081566189147092063295 := by
  unfold tailWord_605054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2758516543750020980173777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14712088233333445227593477 2758516543750020980173777)
  ·
    refine ⟨2068887407812515735130333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2758516543750020980173777 2068887407812515735130333)
    ·
      refine ⟨775832777929693400673875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2068887407812515735130333 775832777929693400673875)
      ·
        refine ⟨1163749166894540101010813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775832777929693400673875 1163749166894540101010813)
        ·
          refine ⟨436405937585452537879055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1163749166894540101010813 436405937585452537879055)
          ·
            refine ⟨654608906378178806818583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436405937585452537879055 654608906378178806818583)
            ·
              refine ⟨981913359567268210227875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654608906378178806818583 981913359567268210227875)
              ·
                refine ⟨1472870039350902315341813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981913359567268210227875 1472870039350902315341813)
                ·
                  refine ⟨138081566189147092063295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1472870039350902315341813 138081566189147092063295)
                  ·
                    rfl

theorem cell21_605054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_605054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605054 prefixEnd_605054 := by exact prefixLift 605054
  have htrace : WordTrace (prefixWord ++ tailWord_605054) baseStart_605054 baseEnd_605054 := by
    simpa [prefixWord, tailWord_605054, baseEnd_605054] using wordTrace_append hprefix tailTrace_605054
  have hstable : (prefixWord ++ tailWord_605054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605054).length < 2 ^ (prefixWord ++ tailWord_605054).sum := by decide
  have hdescent : baseEnd_605054 < baseStart_605054 := by decide
  rcases family_descends (prefixWord ++ tailWord_605054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605113 : List Nat := [1, 2, 1, 4, 2, 4, 2, 2, 3]
def baseStart_605113 : Nat := 118140960795 + 605113 * 2 ^ 59
def prefixEnd_605113 : Nat := 4983230072969 + 3 ^ 40 * 605113 * 2
def baseEnd_605113 : Nat := 138095030792976100579841

theorem tailTrace_605113 : CollatzResearch.WordTrace tailWord_605113 prefixEnd_605113 138095030792976100579841 := by
  unfold tailWord_605113
  simp only [CollatzResearch.WordTrace]
  refine ⟨22070284256786420917787993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14713522837857613945191995 22070284256786420917787993)
  ·
    refine ⟨16552713192589815688340995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22070284256786420917787993 16552713192589815688340995)
    ·
      refine ⟨24829069788884723532511493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16552713192589815688340995 24829069788884723532511493)
      ·
        refine ⟨4655450585415885662345905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24829069788884723532511493 4655450585415885662345905)
        ·
          refine ⟨3491587939061914246759429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4655450585415885662345905 3491587939061914246759429)
          ·
            refine ⟨654672738574108921267393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3491587939061914246759429 654672738574108921267393)
            ·
              refine ⟨491004553930581690950545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654672738574108921267393 491004553930581690950545)
              ·
                refine ⟨368253415447936268212909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491004553930581690950545 368253415447936268212909)
                ·
                  refine ⟨138095030792976100579841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368253415447936268212909 138095030792976100579841)
                  ·
                    rfl

theorem cell21_605113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 3].length) (baseStart_605113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605113 prefixEnd_605113 := by exact prefixLift 605113
  have htrace : WordTrace (prefixWord ++ tailWord_605113) baseStart_605113 baseEnd_605113 := by
    simpa [prefixWord, tailWord_605113, baseEnd_605113] using wordTrace_append hprefix tailTrace_605113
  have hstable : (prefixWord ++ tailWord_605113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605113).length < 2 ^ (prefixWord ++ tailWord_605113).sum := by decide
  have hdescent : baseEnd_605113 < baseStart_605113 := by decide
  rcases family_descends (prefixWord ++ tailWord_605113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605141 : List Nat := [1, 3, 2, 3, 3, 1, 3, 5]
def baseStart_605141 : Nat := 118140960795 + 605141 * 2 ^ 59
def prefixEnd_605141 : Nat := 4983230072969 + 3 ^ 40 * 605141 * 2
def baseEnd_605141 : Nat := 46033806924818091371039

theorem tailTrace_605141 : CollatzResearch.WordTrace tailWord_605141 prefixEnd_605141 46033806924818091371039 := by
  unfold tailWord_605141
  simp only [CollatzResearch.WordTrace]
  refine ⟨22071305500684981699807277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14714203667123321133204851 22071305500684981699807277)
  ·
    refine ⟨8276739562756868137427729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22071305500684981699807277 8276739562756868137427729)
    ·
      refine ⟨6207554672067651103070797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8276739562756868137427729 6207554672067651103070797)
      ·
        refine ⟨2327833002025369163651549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6207554672067651103070797 2327833002025369163651549)
        ·
          refine ⟨872937375759513436369331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2327833002025369163651549 872937375759513436369331)
          ·
            refine ⟨1309406063639270154553997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872937375759513436369331 1309406063639270154553997)
            ·
              refine ⟨491027273864726307957749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1309406063639270154553997 491027273864726307957749)
              ·
                refine ⟨46033806924818091371039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 491027273864726307957749 46033806924818091371039)
                ·
                  rfl

theorem cell21_605141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 5].length) (baseStart_605141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605141 prefixEnd_605141 := by exact prefixLift 605141
  have htrace : WordTrace (prefixWord ++ tailWord_605141) baseStart_605141 baseEnd_605141 := by
    simpa [prefixWord, tailWord_605141, baseEnd_605141] using wordTrace_append hprefix tailTrace_605141
  have hstable : (prefixWord ++ tailWord_605141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605141).length < 2 ^ (prefixWord ++ tailWord_605141).sum := by decide
  have hdescent : baseEnd_605141 < baseStart_605141 := by decide
  rcases family_descends (prefixWord ++ tailWord_605141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605169 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 6]
def baseStart_605169 : Nat := 118140960795 + 605169 * 2 ^ 59
def prefixEnd_605169 : Nat := 4983230072969 + 3 ^ 40 * 605169 * 2
def baseEnd_605169 : Nat := 138107810755932447646393

theorem tailTrace_605169 : CollatzResearch.WordTrace tailWord_605169 prefixEnd_605169 138107810755932447646393 := by
  unfold tailWord_605169
  simp only [CollatzResearch.WordTrace]
  refine ⟨22072326744583542481826561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14714884496389028321217707 22072326744583542481826561)
  ·
    refine ⟨16554245058437656861369921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22072326744583542481826561 16554245058437656861369921)
    ·
      refine ⟨12415683793828242646027441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16554245058437656861369921 12415683793828242646027441)
      ·
        refine ⟨9311762845371181984520581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12415683793828242646027441 9311762845371181984520581)
        ·
          refine ⟨1745955533507096622097609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9311762845371181984520581 1745955533507096622097609)
          ·
            refine ⟨1309466650130322466573207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1745955533507096622097609 1309466650130322466573207)
            ·
              refine ⟨1964199975195483699859811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1309466650130322466573207 1964199975195483699859811)
              ·
                refine ⟨2946299962793225549789717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964199975195483699859811 2946299962793225549789717)
                ·
                  refine ⟨138107810755932447646393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2946299962793225549789717 138107810755932447646393)
                  ·
                    rfl

theorem cell21_605169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_605169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605169 prefixEnd_605169 := by exact prefixLift 605169
  have htrace : WordTrace (prefixWord ++ tailWord_605169) baseStart_605169 baseEnd_605169 := by
    simpa [prefixWord, tailWord_605169, baseEnd_605169] using wordTrace_append hprefix tailTrace_605169
  have hstable : (prefixWord ++ tailWord_605169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605169).length < 2 ^ (prefixWord ++ tailWord_605169).sum := by decide
  have hdescent : baseEnd_605169 < baseStart_605169 := by decide
  rcases family_descends (prefixWord ++ tailWord_605169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605228 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_605228 : Nat := 118140960795 + 605228 * 2 ^ 59
def prefixEnd_605228 : Nat := 4983230072969 + 3 ^ 40 * 605228 * 2
def baseEnd_605228 : Nat := 138121275359761456162939

theorem tailTrace_605228 : CollatzResearch.WordTrace tailWord_605228 prefixEnd_605228 138121275359761456162939 := by
  unfold tailWord_605228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11037239325684897779112169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14716319100913197038816225 11037239325684897779112169)
  ·
    refine ⟨8277929494263673334334127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11037239325684897779112169 8277929494263673334334127)
    ·
      refine ⟨12416894241395510001501191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8277929494263673334334127 12416894241395510001501191)
      ·
        refine ⟨18625341362093265002251787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12416894241395510001501191 18625341362093265002251787)
        ·
          refine ⟨27938012043139897503377681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18625341362093265002251787 27938012043139897503377681)
          ·
            refine ⟨20953509032354923127533261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27938012043139897503377681 20953509032354923127533261)
            ·
              refine ⟨7857565887133096172824973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20953509032354923127533261 7857565887133096172824973)
              ·
                refine ⟨2946587207674911064809365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7857565887133096172824973 2946587207674911064809365)
                ·
                  refine ⟨138121275359761456162939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2946587207674911064809365 138121275359761456162939)
                  ·
                    rfl

theorem cell21_605228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_605228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605228 prefixEnd_605228 := by exact prefixLift 605228
  have htrace : WordTrace (prefixWord ++ tailWord_605228) baseStart_605228 baseEnd_605228 := by
    simpa [prefixWord, tailWord_605228, baseEnd_605228] using wordTrace_append hprefix tailTrace_605228
  have hstable : (prefixWord ++ tailWord_605228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605228).length < 2 ^ (prefixWord ++ tailWord_605228).sum := by decide
  have hdescent : baseEnd_605228 < baseStart_605228 := by decide
  rcases family_descends (prefixWord ++ tailWord_605228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605273 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 9]
def baseStart_605273 : Nat := 118140960795 + 605273 * 2 ^ 59
def prefixEnd_605273 : Nat := 4983230072969 + 3 ^ 40 * 605273 * 2
def baseEnd_605273 : Nat := 138131544972851377912847

theorem tailTrace_605273 : CollatzResearch.WordTrace tailWord_605273 prefixEnd_605273 138131544972851377912847 := by
  unfold tailWord_605273
  simp only [CollatzResearch.WordTrace]
  refine ⟨22076119936206768243612473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14717413290804512162408315 22076119936206768243612473)
  ·
    refine ⟨16557089952155076182709355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22076119936206768243612473 16557089952155076182709355)
    ·
      refine ⟨24835634928232614274064033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16557089952155076182709355 24835634928232614274064033)
      ·
        refine ⟨18626726196174460705548025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24835634928232614274064033 18626726196174460705548025)
        ·
          refine ⟨13970044647130845529161019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18626726196174460705548025 13970044647130845529161019)
          ·
            refine ⟨20955066970696268293741529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13970044647130845529161019 20955066970696268293741529)
            ·
              refine ⟨15716300228022201220306147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20955066970696268293741529 15716300228022201220306147)
              ·
                refine ⟨23574450342033301830459221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15716300228022201220306147 23574450342033301830459221)
                ·
                  refine ⟨138131544972851377912847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23574450342033301830459221 138131544972851377912847)
                  ·
                    rfl

theorem cell21_605273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_605273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605273 prefixEnd_605273 := by exact prefixLift 605273
  have htrace : WordTrace (prefixWord ++ tailWord_605273) baseStart_605273 baseEnd_605273 := by
    simpa [prefixWord, tailWord_605273, baseEnd_605273] using wordTrace_append hprefix tailTrace_605273
  have hstable : (prefixWord ++ tailWord_605273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605273).length < 2 ^ (prefixWord ++ tailWord_605273).sum := by decide
  have hdescent : baseEnd_605273 < baseStart_605273 := by decide
  rcases family_descends (prefixWord ++ tailWord_605273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605282 : List Nat := [3, 3, 2, 2, 1, 3, 2, 2, 3]
def baseStart_605282 : Nat := 118140960795 + 605282 * 2 ^ 59
def prefixEnd_605282 : Nat := 4983230072969 + 3 ^ 40 * 605282 * 2
def baseEnd_605282 : Nat := 138133598895469362262829

theorem tailTrace_605282 : CollatzResearch.WordTrace tailWord_605282 prefixEnd_605282 138133598895469362262829 := by
  unfold tailWord_605282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5519112048293540695172525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14717632128782775187126733 5519112048293540695172525)
  ·
    refine ⟨2069667018110077760689697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5519112048293540695172525 2069667018110077760689697)
    ·
      refine ⟨1552250263582558320517273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2069667018110077760689697 1552250263582558320517273)
      ·
        refine ⟨1164187697686918740387955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1552250263582558320517273 1164187697686918740387955)
        ·
          refine ⟨1746281546530378110581933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164187697686918740387955 1746281546530378110581933)
          ·
            refine ⟨654855579948891791468225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1746281546530378110581933 654855579948891791468225)
            ·
              refine ⟨491141684961668843601169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654855579948891791468225 491141684961668843601169)
              ·
                refine ⟨368356263721251632700877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491141684961668843601169 368356263721251632700877)
                ·
                  refine ⟨138133598895469362262829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368356263721251632700877 138133598895469362262829)
                  ·
                    rfl

theorem cell21_605282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_605282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605282 prefixEnd_605282 := by exact prefixLift 605282
  have htrace : WordTrace (prefixWord ++ tailWord_605282) baseStart_605282 baseEnd_605282 := by
    simpa [prefixWord, tailWord_605282, baseEnd_605282] using wordTrace_append hprefix tailTrace_605282
  have hstable : (prefixWord ++ tailWord_605282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605282).length < 2 ^ (prefixWord ++ tailWord_605282).sum := by decide
  have hdescent : baseEnd_605282 < baseStart_605282 := by decide
  rcases family_descends (prefixWord ++ tailWord_605282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605335 : List Nat := [1, 1, 3, 3, 3, 2, 8]
def baseStart_605335 : Nat := 118140960795 + 605335 * 2 ^ 59
def prefixEnd_605335 : Nat := 4983230072969 + 3 ^ 40 * 605335 * 2
def baseEnd_605335 : Nat := 15349521579728116431043

theorem tailTrace_605335 : CollatzResearch.WordTrace tailWord_605335 prefixEnd_605335 15349521579728116431043 := by
  unfold tailWord_605335
  simp only [CollatzResearch.WordTrace]
  refine ⟨22078381261982152832369459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14718920841321435221579639 22078381261982152832369459)
  ·
    refine ⟨33117571892973229248554189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22078381261982152832369459 33117571892973229248554189)
    ·
      refine ⟨12419089459864960968207821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33117571892973229248554189 12419089459864960968207821)
      ·
        refine ⟨4657158547449360363077933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12419089459864960968207821 4657158547449360363077933)
        ·
          refine ⟨1746434455293510136154225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4657158547449360363077933 1746434455293510136154225)
          ·
            refine ⟨1309825841470132602115669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1746434455293510136154225 1309825841470132602115669)
            ·
              refine ⟨15349521579728116431043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1309825841470132602115669 15349521579728116431043)
              ·
                rfl

theorem cell21_605335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 8].length) (baseStart_605335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605335 prefixEnd_605335 := by exact prefixLift 605335
  have htrace : WordTrace (prefixWord ++ tailWord_605335) baseStart_605335 baseEnd_605335 := by
    simpa [prefixWord, tailWord_605335, baseEnd_605335] using wordTrace_append hprefix tailTrace_605335
  have hstable : (prefixWord ++ tailWord_605335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605335).length < 2 ^ (prefixWord ++ tailWord_605335).sum := by decide
  have hdescent : baseEnd_605335 < baseStart_605335 := by decide
  rcases family_descends (prefixWord ++ tailWord_605335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605338 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_605338 : Nat := 118140960795 + 605338 * 2 ^ 59
def prefixEnd_605338 : Nat := 4983230072969 + 3 ^ 40 * 605338 * 2
def baseEnd_605338 : Nat := 138146378858425709329381

theorem tailTrace_605338 : CollatzResearch.WordTrace tailWord_605338 prefixEnd_605338 138146378858425709329381 := by
  unfold tailWord_605338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5519622670242821086182167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14718993787314189563152445 5519622670242821086182167)
  ·
    refine ⟨8279434005364231629273251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5519622670242821086182167 8279434005364231629273251)
    ·
      refine ⟨12419151008046347443909877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8279434005364231629273251 12419151008046347443909877)
      ·
        refine ⟨1164295407004345072866551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12419151008046347443909877 1164295407004345072866551)
        ·
          refine ⟨1746443110506517609299827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164295407004345072866551 1746443110506517609299827)
          ·
            refine ⟨2619664665759776413949741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746443110506517609299827 2619664665759776413949741)
            ·
              refine ⟨982374249659916155231153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2619664665759776413949741 982374249659916155231153)
              ·
                refine ⟨736780687244937116423365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982374249659916155231153 736780687244937116423365)
                ·
                  refine ⟨138146378858425709329381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 736780687244937116423365 138146378858425709329381)
                  ·
                    rfl

theorem cell21_605338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_605338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605338 prefixEnd_605338 := by exact prefixLift 605338
  have htrace : WordTrace (prefixWord ++ tailWord_605338) baseStart_605338 baseEnd_605338 := by
    simpa [prefixWord, tailWord_605338, baseEnd_605338] using wordTrace_append hprefix tailTrace_605338
  have hstable : (prefixWord ++ tailWord_605338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605338).length < 2 ^ (prefixWord ++ tailWord_605338).sum := by decide
  have hdescent : baseEnd_605338 < baseStart_605338 := by decide
  rcases family_descends (prefixWord ++ tailWord_605338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605397 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 6]
def baseStart_605397 : Nat := 118140960795 + 605397 * 2 ^ 59
def prefixEnd_605397 : Nat := 4983230072969 + 3 ^ 40 * 605397 * 2
def baseEnd_605397 : Nat := 138159843462254717845927

theorem tailTrace_605397 : CollatzResearch.WordTrace tailWord_605397 prefixEnd_605397 138159843462254717845927 := by
  unfold tailWord_605397
  simp only [CollatzResearch.WordTrace]
  refine ⟨22080642587757537421126445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14720428391838358280750963 22080642587757537421126445)
  ·
    refine ⟨8280240970409076532922417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22080642587757537421126445 8280240970409076532922417)
    ·
      refine ⟨6210180727806807399691813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8280240970409076532922417 6210180727806807399691813)
      ·
        refine ⟨1164408886463776387442215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6210180727806807399691813 1164408886463776387442215)
        ·
          refine ⟨1746613329695664581163323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164408886463776387442215 1746613329695664581163323)
          ·
            refine ⟨2619919994543496871744985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746613329695664581163323 2619919994543496871744985)
            ·
              refine ⟨1964939995907622653808739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2619919994543496871744985 1964939995907622653808739)
              ·
                refine ⟨2947409993861433980713109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964939995907622653808739 2947409993861433980713109)
                ·
                  refine ⟨138159843462254717845927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2947409993861433980713109 138159843462254717845927)
                  ·
                    rfl

theorem cell21_605397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_605397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605397 prefixEnd_605397 := by exact prefixLift 605397
  have htrace : WordTrace (prefixWord ++ tailWord_605397) baseStart_605397 baseEnd_605397 := by
    simpa [prefixWord, tailWord_605397, baseEnd_605397] using wordTrace_append hprefix tailTrace_605397
  have hstable : (prefixWord ++ tailWord_605397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605397).length < 2 ^ (prefixWord ++ tailWord_605397).sum := by decide
  have hdescent : baseEnd_605397 < baseStart_605397 := by decide
  rcases family_descends (prefixWord ++ tailWord_605397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605400 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 5]
def baseStart_605400 : Nat := 118140960795 + 605400 * 2 ^ 59
def prefixEnd_605400 : Nat := 4983230072969 + 3 ^ 40 * 605400 * 2
def baseEnd_605400 : Nat := 138160528103127379295921

theorem tailTrace_605400 : CollatzResearch.WordTrace tailWord_605400 prefixEnd_605400 138160528103127379295921 := by
  unfold tailWord_605400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11040376003373334466742827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14720501337831112622323769 11040376003373334466742827)
  ·
    refine ⟨16560564005060001700114241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11040376003373334466742827 16560564005060001700114241)
    ·
      refine ⟨12420423003795001275085681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16560564005060001700114241 12420423003795001275085681)
      ·
        refine ⟨9315317252846250956314261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12420423003795001275085681 9315317252846250956314261)
        ·
          refine ⟨436655496227168013577231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9315317252846250956314261 436655496227168013577231)
          ·
            refine ⟨654983244340752020365847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436655496227168013577231 654983244340752020365847)
            ·
              refine ⟨982474866511128030548771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654983244340752020365847 982474866511128030548771)
              ·
                refine ⟨1473712299766692045823157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982474866511128030548771 1473712299766692045823157)
                ·
                  refine ⟨138160528103127379295921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1473712299766692045823157 138160528103127379295921)
                  ·
                    rfl

theorem cell21_605400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 5].length) (baseStart_605400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605400 prefixEnd_605400 := by exact prefixLift 605400
  have htrace : WordTrace (prefixWord ++ tailWord_605400) baseStart_605400 baseEnd_605400 := by
    simpa [prefixWord, tailWord_605400, baseEnd_605400] using wordTrace_append hprefix tailTrace_605400
  have hstable : (prefixWord ++ tailWord_605400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605400).length < 2 ^ (prefixWord ++ tailWord_605400).sum := by decide
  have hdescent : baseEnd_605400 < baseStart_605400 := by decide
  rcases family_descends (prefixWord ++ tailWord_605400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605425 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 7]
def baseStart_605425 : Nat := 118140960795 + 605425 * 2 ^ 59
def prefixEnd_605425 : Nat := 4983230072969 + 3 ^ 40 * 605425 * 2
def baseEnd_605425 : Nat := 138166233443732891379203

theorem tailTrace_605425 : CollatzResearch.WordTrace tailWord_605425 prefixEnd_605425 138166233443732891379203 := by
  unfold tailWord_605425
  simp only [CollatzResearch.WordTrace]
  refine ⟨22081663831656098203145729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14721109221104065468763819 22081663831656098203145729)
  ·
    refine ⟨16561247873742073652359297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22081663831656098203145729 16561247873742073652359297)
    ·
      refine ⟨12420935905306555239269473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16561247873742073652359297 12420935905306555239269473)
      ·
        refine ⟨9315701928979916429452105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12420935905306555239269473 9315701928979916429452105)
        ·
          refine ⟨6986776446734937322089079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9315701928979916429452105 6986776446734937322089079)
          ·
            refine ⟨10480164670102405983133619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6986776446734937322089079 10480164670102405983133619)
            ·
              refine ⟨15720247005153608974700429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10480164670102405983133619 15720247005153608974700429)
              ·
                refine ⟨5895092626932603365512661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15720247005153608974700429 5895092626932603365512661)
                ·
                  refine ⟨138166233443732891379203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5895092626932603365512661 138166233443732891379203)
                  ·
                    rfl

theorem cell21_605425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_605425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605425 prefixEnd_605425 := by exact prefixLift 605425
  have htrace : WordTrace (prefixWord ++ tailWord_605425) baseStart_605425 baseEnd_605425 := by
    simpa [prefixWord, tailWord_605425, baseEnd_605425] using wordTrace_append hprefix tailTrace_605425
  have hstable : (prefixWord ++ tailWord_605425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605425).length < 2 ^ (prefixWord ++ tailWord_605425).sum := by decide
  have hdescent : baseEnd_605425 < baseStart_605425 := by decide
  rcases family_descends (prefixWord ++ tailWord_605425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605518 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_605518 : Nat := 118140960795 + 605518 * 2 ^ 59
def prefixEnd_605518 : Nat := 4983230072969 + 3 ^ 40 * 605518 * 2
def baseEnd_605518 : Nat := 138187457310785396329013

theorem tailTrace_605518 : CollatzResearch.WordTrace tailWord_605518 prefixEnd_605518 138187457310785396329013 := by
  unfold tailWord_605518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2760631977539896885785151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14723370546879450057520805 2760631977539896885785151)
  ·
    refine ⟨4140947966309845328677727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2760631977539896885785151 4140947966309845328677727)
    ·
      refine ⟨6211421949464767993016591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4140947966309845328677727 6211421949464767993016591)
      ·
        refine ⟨9317132924197151989524887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6211421949464767993016591 9317132924197151989524887)
        ·
          refine ⟨13975699386295727984287331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9317132924197151989524887 13975699386295727984287331)
          ·
            refine ⟨20963549079443591976430997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13975699386295727984287331 20963549079443591976430997)
            ·
              refine ⟨982666363098918373895203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20963549079443591976430997 982666363098918373895203)
              ·
                refine ⟨1473999544648377560842805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982666363098918373895203 1473999544648377560842805)
                ·
                  refine ⟨138187457310785396329013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1473999544648377560842805 138187457310785396329013)
                  ·
                    rfl

theorem cell21_605518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_605518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605518 prefixEnd_605518 := by exact prefixLift 605518
  have htrace : WordTrace (prefixWord ++ tailWord_605518) baseStart_605518 baseEnd_605518 := by
    simpa [prefixWord, tailWord_605518, baseEnd_605518] using wordTrace_append hprefix tailTrace_605518
  have hstable : (prefixWord ++ tailWord_605518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605518).length < 2 ^ (prefixWord ++ tailWord_605518).sum := by decide
  have hdescent : baseEnd_605518 < baseStart_605518 := by decide
  rcases family_descends (prefixWord ++ tailWord_605518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605569 : List Nat := [1, 2, 4, 3, 2, 1, 3, 2, 3]
def baseStart_605569 : Nat := 118140960795 + 605569 * 2 ^ 59
def prefixEnd_605569 : Nat := 4983230072969 + 3 ^ 40 * 605569 * 2
def baseEnd_605569 : Nat := 138199096205620640978909

theorem tailTrace_605569 : CollatzResearch.WordTrace tailWord_605569 prefixEnd_605569 138199096205620640978909 := by
  unfold tailWord_605569
  simp only [CollatzResearch.WordTrace]
  refine ⟨22086915943134410796387761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14724610628756273864258507 22086915943134410796387761)
  ·
    refine ⟨16565186957350808097290821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22086915943134410796387761 16565186957350808097290821)
    ·
      refine ⟨3105972554503276518242029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16565186957350808097290821 3105972554503276518242029)
      ·
        refine ⟨1164739707938728694340761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3105972554503276518242029 1164739707938728694340761)
        ·
          refine ⟨873554780954046520755571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1164739707938728694340761 873554780954046520755571)
          ·
            refine ⟨1310332171431069781133357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873554780954046520755571 1310332171431069781133357)
            ·
              refine ⟨491374564286651167925009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1310332171431069781133357 491374564286651167925009)
              ·
                refine ⟨368530923214988375943757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491374564286651167925009 368530923214988375943757)
                ·
                  refine ⟨138199096205620640978909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368530923214988375943757 138199096205620640978909)
                  ·
                    rfl

theorem cell21_605569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 3].length) (baseStart_605569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605569 prefixEnd_605569 := by exact prefixLift 605569
  have htrace : WordTrace (prefixWord ++ tailWord_605569) baseStart_605569 baseEnd_605569 := by
    simpa [prefixWord, tailWord_605569, baseEnd_605569] using wordTrace_append hprefix tailTrace_605569
  have hstable : (prefixWord ++ tailWord_605569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605569).length < 2 ^ (prefixWord ++ tailWord_605569).sum := by decide
  have hdescent : baseEnd_605569 < baseStart_605569 := by decide
  rcases family_descends (prefixWord ++ tailWord_605569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605628 : List Nat := [2, 2, 2, 4, 2, 1, 1, 4, 3]
def baseStart_605628 : Nat := 118140960795 + 605628 * 2 ^ 59
def prefixEnd_605628 : Nat := 4983230072969 + 3 ^ 40 * 605628 * 2
def baseEnd_605628 : Nat := 138212560809449649495455

theorem tailTrace_605628 : CollatzResearch.WordTrace tailWord_605628 prefixEnd_605628 138212560809449649495455 := by
  unfold tailWord_605628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11044533924960331936392769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14726045233280442581857025 11044533924960331936392769)
  ·
    refine ⟨8283400443720248952294577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11044533924960331936392769 8283400443720248952294577)
    ·
      refine ⟨6212550332790186714220933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8283400443720248952294577 6212550332790186714220933)
      ·
        refine ⟨1164853187398160008916425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6212550332790186714220933 1164853187398160008916425)
        ·
          refine ⟨873639890548620006687319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1164853187398160008916425 873639890548620006687319)
          ·
            refine ⟨1310459835822930010030979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873639890548620006687319 1310459835822930010030979)
            ·
              refine ⟨1965689753734395015046469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310459835822930010030979 1965689753734395015046469)
              ·
                refine ⟨368566828825199065321213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1965689753734395015046469 368566828825199065321213)
                ·
                  refine ⟨138212560809449649495455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368566828825199065321213 138212560809449649495455)
                  ·
                    rfl

theorem cell21_605628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_605628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605628 prefixEnd_605628 := by exact prefixLift 605628
  have htrace : WordTrace (prefixWord ++ tailWord_605628) baseStart_605628 baseEnd_605628 := by
    simpa [prefixWord, tailWord_605628, baseEnd_605628] using wordTrace_append hprefix tailTrace_605628
  have hstable : (prefixWord ++ tailWord_605628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605628).length < 2 ^ (prefixWord ++ tailWord_605628).sum := by decide
  have hdescent : baseEnd_605628 < baseStart_605628 := by decide
  rcases family_descends (prefixWord ++ tailWord_605628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605715 : List Nat := [1, 1, 1, 2, 1, 6, 4, 5]
def baseStart_605715 : Nat := 118140960795 + 605715 * 2 ^ 59
def prefixEnd_605715 : Nat := 4983230072969 + 3 ^ 40 * 605715 * 2
def baseEnd_605715 : Nat := 46077471798252277181759

theorem tailTrace_605715 : CollatzResearch.WordTrace tailWord_605715 prefixEnd_605715 46077471798252277181759 := by
  unfold tailWord_605715
  simp only [CollatzResearch.WordTrace]
  refine ⟨22092241000605477731202599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14728160667070318487468399 22092241000605477731202599)
  ·
    refine ⟨33138361500908216596803899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22092241000605477731202599 33138361500908216596803899)
    ·
      refine ⟨49707542251362324895205849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33138361500908216596803899 49707542251362324895205849)
      ·
        refine ⟨37280656688521743671404387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49707542251362324895205849 37280656688521743671404387)
        ·
          refine ⟨55920985032782615507106581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37280656688521743671404387 55920985032782615507106581)
          ·
            refine ⟨2621296173411685101895621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55920985032782615507106581 2621296173411685101895621)
            ·
              refine ⟨491493032514690956605429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2621296173411685101895621 491493032514690956605429)
              ·
                refine ⟨46077471798252277181759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 491493032514690956605429 46077471798252277181759)
                ·
                  rfl

theorem cell21_605715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 5].length) (baseStart_605715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605715 prefixEnd_605715 := by exact prefixLift 605715
  have htrace : WordTrace (prefixWord ++ tailWord_605715) baseStart_605715 baseEnd_605715 := by
    simpa [prefixWord, tailWord_605715, baseEnd_605715] using wordTrace_append hprefix tailTrace_605715
  have hstable : (prefixWord ++ tailWord_605715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605715).length < 2 ^ (prefixWord ++ tailWord_605715).sum := by decide
  have hdescent : baseEnd_605715 < baseStart_605715 := by decide
  rcases family_descends (prefixWord ++ tailWord_605715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605881 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 5]
def baseStart_605881 : Nat := 118140960795 + 605881 * 2 ^ 59
def prefixEnd_605881 : Nat := 4983230072969 + 3 ^ 40 * 605881 * 2
def baseEnd_605881 : Nat := 138270298856377431778271

theorem tailTrace_605881 : CollatzResearch.WordTrace tailWord_605881 prefixEnd_605881 138270298856377431778271 := by
  unfold tailWord_605881
  simp only [CollatzResearch.WordTrace]
  refine ⟨22098295518004088081745497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14732197012002725387830331 22098295518004088081745497)
  ·
    refine ⟨16573721638503066061309123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22098295518004088081745497 16573721638503066061309123)
    ·
      refine ⟨24860582457754599091963685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16573721638503066061309123 24860582457754599091963685)
      ·
        refine ⟨4661359210828987329743191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24860582457754599091963685 4661359210828987329743191)
        ·
          refine ⟨6992038816243480994614787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4661359210828987329743191 6992038816243480994614787)
          ·
            refine ⟨10488058224365221491922181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6992038816243480994614787 10488058224365221491922181)
            ·
              refine ⟨1966510917068479029735409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10488058224365221491922181 1966510917068479029735409)
              ·
                refine ⟨1474883187801359272301557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1966510917068479029735409 1474883187801359272301557)
                ·
                  refine ⟨138270298856377431778271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1474883187801359272301557 138270298856377431778271)
                  ·
                    rfl

theorem cell21_605881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_605881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605881 prefixEnd_605881 := by exact prefixLift 605881
  have htrace : WordTrace (prefixWord ++ tailWord_605881) baseStart_605881 baseEnd_605881 := by
    simpa [prefixWord, tailWord_605881, baseEnd_605881] using wordTrace_append hprefix tailTrace_605881
  have hstable : (prefixWord ++ tailWord_605881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605881).length < 2 ^ (prefixWord ++ tailWord_605881).sum := by decide
  have hdescent : baseEnd_605881 < baseStart_605881 := by decide
  rcases family_descends (prefixWord ++ tailWord_605881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605884 : List Nat := [2, 2, 2, 3, 1, 4, 2, 5]
def baseStart_605884 : Nat := 118140960795 + 605884 * 2 ^ 59
def prefixEnd_605884 : Nat := 4983230072969 + 3 ^ 40 * 605884 * 2
def baseEnd_605884 : Nat := 46090327832416697742755

theorem tailTrace_605884 : CollatzResearch.WordTrace tailWord_605884 prefixEnd_605884 46090327832416697742755 := by
  unfold tailWord_605884
  simp only [CollatzResearch.WordTrace]
  refine ⟨11049202468496609797052353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14732269957995479729403137 11049202468496609797052353)
  ·
    refine ⟨8286901851372457347789265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11049202468496609797052353 8286901851372457347789265)
    ·
      refine ⟨6215176388529343010841949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8286901851372457347789265 6215176388529343010841949)
      ·
        refine ⟨2330691145698503629065731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6215176388529343010841949 2330691145698503629065731)
        ·
          refine ⟨3496036718547755443598597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2330691145698503629065731 3496036718547755443598597)
          ·
            refine ⟨655506884727704145674737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3496036718547755443598597 655506884727704145674737)
            ·
              refine ⟨491630163545778109256053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655506884727704145674737 491630163545778109256053)
              ·
                refine ⟨46090327832416697742755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 491630163545778109256053 46090327832416697742755)
                ·
                  rfl

theorem cell21_605884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_605884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605884 prefixEnd_605884 := by exact prefixLift 605884
  have htrace : WordTrace (prefixWord ++ tailWord_605884) baseStart_605884 baseEnd_605884 := by
    simpa [prefixWord, tailWord_605884, baseEnd_605884] using wordTrace_append hprefix tailTrace_605884
  have hstable : (prefixWord ++ tailWord_605884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605884).length < 2 ^ (prefixWord ++ tailWord_605884).sum := by decide
  have hdescent : baseEnd_605884 < baseStart_605884 := by decide
  rcases family_descends (prefixWord ++ tailWord_605884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605895 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 8]
def baseStart_605895 : Nat := 118140960795 + 605895 * 2 ^ 59
def prefixEnd_605895 : Nat := 4983230072969 + 3 ^ 40 * 605895 * 2
def baseEnd_605895 : Nat := 138273493847116518544909

theorem tailTrace_605895 : CollatzResearch.WordTrace tailWord_605895 prefixEnd_605895 138273493847116518544909 := by
  unfold tailWord_605895
  simp only [CollatzResearch.WordTrace]
  refine ⟨22098806139953368472755139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14732537426635578981836759 22098806139953368472755139)
  ·
    refine ⟨33148209209930052709132709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22098806139953368472755139 33148209209930052709132709)
    ·
      refine ⟨6215289226861884882962383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33148209209930052709132709 6215289226861884882962383)
      ·
        refine ⟨9322933840292827324443575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6215289226861884882962383 9322933840292827324443575)
        ·
          refine ⟨13984400760439240986665363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9322933840292827324443575 13984400760439240986665363)
          ·
            refine ⟨20976601140658861479998045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13984400760439240986665363 20976601140658861479998045)
            ·
              refine ⟨7866225427747073054999267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20976601140658861479998045 7866225427747073054999267)
              ·
                refine ⟨11799338141620609582498901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7866225427747073054999267 11799338141620609582498901)
                ·
                  refine ⟨138273493847116518544909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11799338141620609582498901 138273493847116518544909)
                  ·
                    rfl

theorem cell21_605895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_605895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605895 prefixEnd_605895 := by exact prefixLift 605895
  have htrace : WordTrace (prefixWord ++ tailWord_605895) baseStart_605895 baseEnd_605895 := by
    simpa [prefixWord, tailWord_605895, baseEnd_605895] using wordTrace_append hprefix tailTrace_605895
  have hstable : (prefixWord ++ tailWord_605895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605895).length < 2 ^ (prefixWord ++ tailWord_605895).sum := by decide
  have hdescent : baseEnd_605895 < baseStart_605895 := by decide
  rcases family_descends (prefixWord ++ tailWord_605895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_605912 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 4]
def baseStart_605912 : Nat := 118140960795 + 605912 * 2 ^ 59
def prefixEnd_605912 : Nat := 4983230072969 + 3 ^ 40 * 605912 * 2
def baseEnd_605912 : Nat := 138277373478728266761541

theorem tailTrace_605912 : CollatzResearch.WordTrace tailWord_605912 prefixEnd_605912 138277373478728266761541 := by
  unfold tailWord_605912
  simp only [CollatzResearch.WordTrace]
  refine ⟨11049713090445890188061995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14732950787261186917415993 11049713090445890188061995)
  ·
    refine ⟨16574569635668835282092993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11049713090445890188061995 16574569635668835282092993)
    ·
      refine ⟨12430927226751626461569745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16574569635668835282092993 12430927226751626461569745)
      ·
        refine ⟨9323195420063719846177309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12430927226751626461569745 9323195420063719846177309)
        ·
          refine ⟨3496198282523894942316491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9323195420063719846177309 3496198282523894942316491)
          ·
            refine ⟨5244297423785842413474737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3496198282523894942316491 5244297423785842413474737)
            ·
              refine ⟨3933223067839381810106053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5244297423785842413474737 3933223067839381810106053)
              ·
                refine ⟨737479325219884089394885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3933223067839381810106053 737479325219884089394885)
                ·
                  refine ⟨138277373478728266761541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 737479325219884089394885 138277373478728266761541)
                  ·
                    rfl

theorem cell21_605912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_605912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_605912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_605912 prefixEnd_605912 := by exact prefixLift 605912
  have htrace : WordTrace (prefixWord ++ tailWord_605912) baseStart_605912 baseEnd_605912 := by
    simpa [prefixWord, tailWord_605912, baseEnd_605912] using wordTrace_append hprefix tailTrace_605912
  have hstable : (prefixWord ++ tailWord_605912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_605912).length < 2 ^ (prefixWord ++ tailWord_605912).sum := by decide
  have hdescent : baseEnd_605912 < baseStart_605912 := by decide
  rcases family_descends (prefixWord ++ tailWord_605912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606022 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_606022 : Nat := 118140960795 + 606022 * 2 ^ 59
def prefixEnd_606022 : Nat := 4983230072969 + 3 ^ 40 * 606022 * 2
def baseEnd_606022 : Nat := 138302476977392519927983

theorem tailTrace_606022 : CollatzResearch.WordTrace tailWord_606022 prefixEnd_606022 138302476977392519927983 := by
  unfold tailWord_606022
  simp only [CollatzResearch.WordTrace]
  refine ⟨690732444077914661332135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14735625473662179441752213 690732444077914661332135)
  ·
    refine ⟨1036098666116871991998203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 690732444077914661332135 1036098666116871991998203)
    ·
      refine ⟨1554147999175307987997305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1036098666116871991998203 1554147999175307987997305)
      ·
        refine ⟨1165610999381480990997979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1554147999175307987997305 1165610999381480990997979)
        ·
          refine ⟨1748416499072221486496969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165610999381480990997979 1748416499072221486496969)
          ·
            refine ⟨1311312374304166114872727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1748416499072221486496969 1311312374304166114872727)
            ·
              refine ⟨1966968561456249172309091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311312374304166114872727 1966968561456249172309091)
              ·
                refine ⟨2950452842184373758463637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1966968561456249172309091 2950452842184373758463637)
                ·
                  refine ⟨138302476977392519927983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2950452842184373758463637 138302476977392519927983)
                  ·
                    rfl

theorem cell21_606022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_606022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606022 prefixEnd_606022 := by exact prefixLift 606022
  have htrace : WordTrace (prefixWord ++ tailWord_606022) baseStart_606022 baseEnd_606022 := by
    simpa [prefixWord, tailWord_606022, baseEnd_606022] using wordTrace_append hprefix tailTrace_606022
  have hstable : (prefixWord ++ tailWord_606022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606022).length < 2 ^ (prefixWord ++ tailWord_606022).sum := by decide
  have hdescent : baseEnd_606022 < baseStart_606022 := by decide
  rcases family_descends (prefixWord ++ tailWord_606022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606033 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 5]
def baseStart_606033 : Nat := 118140960795 + 606033 * 2 ^ 59
def prefixEnd_606033 : Nat := 4983230072969 + 3 ^ 40 * 606033 * 2
def baseEnd_606033 : Nat := 138304987327258945244627

theorem tailTrace_606033 : CollatzResearch.WordTrace tailWord_606033 prefixEnd_606033 138304987327258945244627 := by
  unfold tailWord_606033
  simp only [CollatzResearch.WordTrace]
  refine ⟨22103839413453418041278753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14735892942302278694185835 22103839413453418041278753)
  ·
    refine ⟨16577879560090063530959065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22103839413453418041278753 16577879560090063530959065)
    ·
      refine ⟨12433409670067547648219299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16577879560090063530959065 12433409670067547648219299)
      ·
        refine ⟨18650114505101321472328949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12433409670067547648219299 18650114505101321472328949)
        ·
          refine ⟨1748448234853248888030839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18650114505101321472328949 1748448234853248888030839)
          ·
            refine ⟨2622672352279873332046259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748448234853248888030839 2622672352279873332046259)
            ·
              refine ⟨3934008528419809998069389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622672352279873332046259 3934008528419809998069389)
              ·
                refine ⟨1475253198157428749276021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3934008528419809998069389 1475253198157428749276021)
                ·
                  refine ⟨138304987327258945244627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1475253198157428749276021 138304987327258945244627)
                  ·
                    rfl

theorem cell21_606033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_606033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606033 prefixEnd_606033 := by exact prefixLift 606033
  have htrace : WordTrace (prefixWord ++ tailWord_606033) baseStart_606033 baseEnd_606033 := by
    simpa [prefixWord, tailWord_606033, baseEnd_606033] using wordTrace_append hprefix tailTrace_606033
  have hstable : (prefixWord ++ tailWord_606033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606033).length < 2 ^ (prefixWord ++ tailWord_606033).sum := by decide
  have hdescent : baseEnd_606033 < baseStart_606033 := by decide
  rcases family_descends (prefixWord ++ tailWord_606033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606050 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_606050 : Nat := 118140960795 + 606050 * 2 ^ 59
def prefixEnd_606050 : Nat := 4983230072969 + 3 ^ 40 * 606050 * 2
def baseEnd_606050 : Nat := 138308866958870693461259

theorem tailTrace_606050 : CollatzResearch.WordTrace tailWord_606050 prefixEnd_606050 138308866958870693461259 := by
  unfold tailWord_606050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5526114863597957486161901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14736306302927886629765069 5526114863597957486161901)
  ·
    refine ⟨2072293073849234057310713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5526114863597957486161901 2072293073849234057310713)
    ·
      refine ⟨1554219805386925542983035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2072293073849234057310713 1554219805386925542983035)
      ·
        refine ⟨2331329708080388314474553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554219805386925542983035 2331329708080388314474553)
        ·
          refine ⟨1748497281060291235855915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2331329708080388314474553 1748497281060291235855915)
          ·
            refine ⟨2622745921590436853783873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748497281060291235855915 2622745921590436853783873)
            ·
              refine ⟨1967059441192827640337905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2622745921590436853783873 1967059441192827640337905)
              ·
                refine ⟨1475294580894620730253429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1967059441192827640337905 1475294580894620730253429)
                ·
                  refine ⟨138308866958870693461259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1475294580894620730253429 138308866958870693461259)
                  ·
                    rfl

theorem cell21_606050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_606050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606050 prefixEnd_606050 := by exact prefixLift 606050
  have htrace : WordTrace (prefixWord ++ tailWord_606050) baseStart_606050 baseEnd_606050 := by
    simpa [prefixWord, tailWord_606050, baseEnd_606050] using wordTrace_append hprefix tailTrace_606050
  have hstable : (prefixWord ++ tailWord_606050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606050).length < 2 ^ (prefixWord ++ tailWord_606050).sum := by decide
  have hdescent : baseEnd_606050 < baseStart_606050 := by decide
  rcases family_descends (prefixWord ++ tailWord_606050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606098 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_606098 : Nat := 118140960795 + 606098 * 2 ^ 59
def prefixEnd_606098 : Nat := 4983230072969 + 3 ^ 40 * 606098 * 2
def baseEnd_606098 : Nat := 138319821212833276661161

theorem tailTrace_606098 : CollatzResearch.WordTrace tailWord_606098 prefixEnd_606098 138319821212833276661161 := by
  unfold tailWord_606098
  simp only [CollatzResearch.WordTrace]
  refine ⟨5526552539554483535598737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14737473438811956094929965 5526552539554483535598737)
  ·
    refine ⟨4144914404665862651699053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5526552539554483535598737 4144914404665862651699053)
    ·
      refine ⟨1554342901749698494387145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4144914404665862651699053 1554342901749698494387145)
      ·
        refine ⟨1165757176312273870790359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1554342901749698494387145 1165757176312273870790359)
        ·
          refine ⟨1748635764468410806185539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165757176312273870790359 1748635764468410806185539)
          ·
            refine ⟨2622953646702616209278309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748635764468410806185539 2622953646702616209278309)
            ·
              refine ⟨491803808756740539239683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2622953646702616209278309 491803808756740539239683)
              ·
                refine ⟨737705713135110808859525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491803808756740539239683 737705713135110808859525)
                ·
                  refine ⟨138319821212833276661161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 737705713135110808859525 138319821212833276661161)
                  ·
                    rfl

theorem cell21_606098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_606098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606098 prefixEnd_606098 := by exact prefixLift 606098
  have htrace : WordTrace (prefixWord ++ tailWord_606098) baseStart_606098 baseEnd_606098 := by
    simpa [prefixWord, tailWord_606098, baseEnd_606098] using wordTrace_append hprefix tailTrace_606098
  have hstable : (prefixWord ++ tailWord_606098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606098).length < 2 ^ (prefixWord ++ tailWord_606098).sum := by decide
  have hdescent : baseEnd_606098 < baseStart_606098 := by decide
  rcases family_descends (prefixWord ++ tailWord_606098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606154 : List Nat := [3, 1, 2, 1, 2, 1, 5, 6]
def baseStart_606154 : Nat := 118140960795 + 606154 * 2 ^ 59
def prefixEnd_606154 : Nat := 4983230072969 + 3 ^ 40 * 606154 * 2
def baseEnd_606154 : Nat := 46110867058596541242571

theorem tailTrace_606154 : CollatzResearch.WordTrace tailWord_606154 prefixEnd_606154 46110867058596541242571 := by
  unfold tailWord_606154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5527063161503763926608379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14738835097343370470955677 5527063161503763926608379)
  ·
    refine ⟨8290594742255645889912569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5527063161503763926608379 8290594742255645889912569)
    ·
      refine ⟨6217946056691734417434427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8290594742255645889912569 6217946056691734417434427)
      ·
        refine ⟨9326919085037601626151641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6217946056691734417434427 9326919085037601626151641)
        ·
          refine ⟨6995189313778201219613731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9326919085037601626151641 6995189313778201219613731)
          ·
            refine ⟨10492783970667301829420597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6995189313778201219613731 10492783970667301829420597)
            ·
              refine ⟨983698497250059546508181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10492783970667301829420597 983698497250059546508181)
              ·
                refine ⟨46110867058596541242571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 983698497250059546508181 46110867058596541242571)
                ·
                  rfl

theorem cell21_606154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_606154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606154 prefixEnd_606154 := by exact prefixLift 606154
  have htrace : WordTrace (prefixWord ++ tailWord_606154) baseStart_606154 baseEnd_606154 := by
    simpa [prefixWord, tailWord_606154, baseEnd_606154] using wordTrace_append hprefix tailTrace_606154
  have hstable : (prefixWord ++ tailWord_606154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606154).length < 2 ^ (prefixWord ++ tailWord_606154).sum := by decide
  have hdescent : baseEnd_606154 < baseStart_606154 := by decide
  rcases family_descends (prefixWord ++ tailWord_606154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606261 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 5]
def baseStart_606261 : Nat := 118140960795 + 606261 * 2 ^ 59
def prefixEnd_606261 : Nat := 4983230072969 + 3 ^ 40 * 606261 * 2
def baseEnd_606261 : Nat := 138357020033581215444161

theorem tailTrace_606261 : CollatzResearch.WordTrace tailWord_606261 prefixEnd_606261 138357020033581215444161 := by
  unfold tailWord_606261
  simp only [CollatzResearch.WordTrace]
  refine ⟨22112155256627412980578637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14741436837751608653719091 22112155256627412980578637)
  ·
    refine ⟨8292058221235279867716989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22112155256627412980578637 8292058221235279867716989)
    ·
      refine ⟨3109521832963229950393871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8292058221235279867716989 3109521832963229950393871)
      ·
        refine ⟨4664282749444844925590807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3109521832963229950393871 4664282749444844925590807)
        ·
          refine ⟨6996424124167267388386211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664282749444844925590807 6996424124167267388386211)
          ·
            refine ⟨10494636186250901082579317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996424124167267388386211 10494636186250901082579317)
            ·
              refine ⟨983872142461021976491811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10494636186250901082579317 983872142461021976491811)
              ·
                refine ⟨1475808213691532964737717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983872142461021976491811 1475808213691532964737717)
                ·
                  refine ⟨138357020033581215444161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1475808213691532964737717 138357020033581215444161)
                  ·
                    rfl

theorem cell21_606261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_606261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606261 prefixEnd_606261 := by exact prefixLift 606261
  have htrace : WordTrace (prefixWord ++ tailWord_606261) baseStart_606261 baseEnd_606261 := by
    simpa [prefixWord, tailWord_606261, baseEnd_606261] using wordTrace_append hprefix tailTrace_606261
  have hstable : (prefixWord ++ tailWord_606261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606261).length < 2 ^ (prefixWord ++ tailWord_606261).sum := by decide
  have hdescent : baseEnd_606261 < baseStart_606261 := by decide
  rcases family_descends (prefixWord ++ tailWord_606261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606278 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_606278 : Nat := 118140960795 + 606278 * 2 ^ 59
def prefixEnd_606278 : Nat := 4983230072969 + 3 ^ 40 * 606278 * 2
def baseEnd_606278 : Nat := 138360899665192963660793

theorem tailTrace_606278 : CollatzResearch.WordTrace tailWord_606278 prefixEnd_606278 138360899665192963660793 := by
  unfold tailWord_606278
  simp only [CollatzResearch.WordTrace]
  refine ⟨691024228048932027623359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14741850198377216589298325 691024228048932027623359)
  ·
    refine ⟨1036536342073398041435039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 691024228048932027623359 1036536342073398041435039)
    ·
      refine ⟨1554804513110097062152559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1036536342073398041435039 1554804513110097062152559)
      ·
        refine ⟨2332206769665145593228839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554804513110097062152559 2332206769665145593228839)
        ·
          refine ⟨3498310154497718389843259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332206769665145593228839 3498310154497718389843259)
          ·
            refine ⟨5247465231746577584764889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3498310154497718389843259 5247465231746577584764889)
            ·
              refine ⟨3935598923809933188573667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5247465231746577584764889 3935598923809933188573667)
              ·
                refine ⟨5903398385714899782860501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935598923809933188573667 5903398385714899782860501)
                ·
                  refine ⟨138360899665192963660793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5903398385714899782860501 138360899665192963660793)
                  ·
                    rfl

theorem cell21_606278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_606278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606278 prefixEnd_606278 := by exact prefixLift 606278
  have htrace : WordTrace (prefixWord ++ tailWord_606278) baseStart_606278 baseEnd_606278 := by
    simpa [prefixWord, tailWord_606278, baseEnd_606278] using wordTrace_append hprefix tailTrace_606278
  have hstable : (prefixWord ++ tailWord_606278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606278).length < 2 ^ (prefixWord ++ tailWord_606278).sum := by decide
  have hdescent : baseEnd_606278 < baseStart_606278 := by decide
  rcases family_descends (prefixWord ++ tailWord_606278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606306 : List Nat := [3, 3, 2, 2, 11]
def baseStart_606306 : Nat := 118140960795 + 606306 * 2 ^ 59
def prefixEnd_606306 : Nat := 4983230072969 + 3 ^ 40 * 606306 * 2
def baseEnd_606306 : Nat := 1708238143786063422149

theorem tailTrace_606306 : CollatzResearch.WordTrace tailWord_606306 prefixEnd_606306 1708238143786063422149 := by
  unfold tailWord_606306
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528449135366096416491693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14742531027642923777311181 5528449135366096416491693)
  ·
    refine ⟨2073168425762286156184385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5528449135366096416491693 2073168425762286156184385)
    ·
      refine ⟨1554876319321714617138289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2073168425762286156184385 1554876319321714617138289)
      ·
        refine ⟨1166157239491285962853717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1554876319321714617138289 1166157239491285962853717)
        ·
          refine ⟨1708238143786063422149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1166157239491285962853717 1708238143786063422149)
          ·
            rfl

theorem cell21_606306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 11].length) (baseStart_606306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606306 prefixEnd_606306 := by exact prefixLift 606306
  have htrace : WordTrace (prefixWord ++ tailWord_606306) baseStart_606306 baseEnd_606306 := by
    simpa [prefixWord, tailWord_606306, baseEnd_606306] using wordTrace_append hprefix tailTrace_606306
  have hstable : (prefixWord ++ tailWord_606306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606306).length < 2 ^ (prefixWord ++ tailWord_606306).sum := by decide
  have hdescent : baseEnd_606306 < baseStart_606306 := by decide
  rcases family_descends (prefixWord ++ tailWord_606306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606368 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 4]
def baseStart_606368 : Nat := 118140960795 + 606368 * 2 ^ 59
def prefixEnd_606368 : Nat := 4983230072969 + 3 ^ 40 * 606368 * 2
def baseEnd_606368 : Nat := 138381438891372807160609

theorem tailTrace_606368 : CollatzResearch.WordTrace tailWord_606368 prefixEnd_606368 138381438891372807160609 := by
  unfold tailWord_606368
  simp only [CollatzResearch.WordTrace]
  refine ⟨11058028933619885127361879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14744038578159846836482505 11058028933619885127361879)
  ·
    refine ⟨16587043400429827691042819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11058028933619885127361879 16587043400429827691042819)
    ·
      refine ⟨24880565100644741536564229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16587043400429827691042819 24880565100644741536564229)
      ·
        refine ⟨4665105956370889038105793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24880565100644741536564229 4665105956370889038105793)
        ·
          refine ⟨3498829467278166778579345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4665105956370889038105793 3498829467278166778579345)
          ·
            refine ⟨2624122100458625083934509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3498829467278166778579345 2624122100458625083934509)
            ·
              refine ⟨984045787671984406475441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2624122100458625083934509 984045787671984406475441)
              ·
                refine ⟨738034340753988304856581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 984045787671984406475441 738034340753988304856581)
                ·
                  refine ⟨138381438891372807160609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 738034340753988304856581 138381438891372807160609)
                  ·
                    rfl

theorem cell21_606368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_606368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606368 prefixEnd_606368 := by exact prefixLift 606368
  have htrace : WordTrace (prefixWord ++ tailWord_606368) baseStart_606368 baseEnd_606368 := by
    simpa [prefixWord, tailWord_606368, baseEnd_606368] using wordTrace_append hprefix tailTrace_606368
  have hstable : (prefixWord ++ tailWord_606368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606368).length < 2 ^ (prefixWord ++ tailWord_606368).sum := by decide
  have hdescent : baseEnd_606368 < baseStart_606368 := by decide
  rcases family_descends (prefixWord ++ tailWord_606368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606506 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_606506 : Nat := 118140960795 + 606506 * 2 ^ 59
def prefixEnd_606506 : Nat := 4983230072969 + 3 ^ 40 * 606506 * 2
def baseEnd_606506 : Nat := 138412932371515233860327

theorem tailTrace_606506 : CollatzResearch.WordTrace tailWord_606506 prefixEnd_606506 138412932371515233860327 := by
  unfold tailWord_606506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5530272785184954955811843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14747394093826546548831581 5530272785184954955811843)
  ·
    refine ⟨8295409177777432433717765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5530272785184954955811843 8295409177777432433717765)
    ·
      refine ⟨1555389220833268581322081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8295409177777432433717765 1555389220833268581322081)
      ·
        refine ⟨1166541915624951435991561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1555389220833268581322081 1166541915624951435991561)
        ·
          refine ⟨874906436718713576993671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1166541915624951435991561 874906436718713576993671)
          ·
            refine ⟨1312359655078070365490507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874906436718713576993671 1312359655078070365490507)
            ·
              refine ⟨1968539482617105548235761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1312359655078070365490507 1968539482617105548235761)
              ·
                refine ⟨1476404611962829161176821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1968539482617105548235761 1476404611962829161176821)
                ·
                  refine ⟨138412932371515233860327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1476404611962829161176821 138412932371515233860327)
                  ·
                    rfl

theorem cell21_606506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_606506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606506 prefixEnd_606506 := by exact prefixLift 606506
  have htrace : WordTrace (prefixWord ++ tailWord_606506) baseStart_606506 baseEnd_606506 := by
    simpa [prefixWord, tailWord_606506, baseEnd_606506] using wordTrace_append hprefix tailTrace_606506
  have hstable : (prefixWord ++ tailWord_606506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606506).length < 2 ^ (prefixWord ++ tailWord_606506).sum := by decide
  have hdescent : baseEnd_606506 < baseStart_606506 := by decide
  rcases family_descends (prefixWord ++ tailWord_606506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606644 : List Nat := [2, 5, 2, 2, 2, 8]
def baseStart_606644 : Nat := 118140960795 + 606644 * 2 ^ 59
def prefixEnd_606644 : Nat := 4983230072969 + 3 ^ 40 * 606644 * 2
def baseEnd_606644 : Nat := 5127571327839172613335

theorem tailTrace_606644 : CollatzResearch.WordTrace tailWord_606644 prefixEnd_606644 5127571327839172613335 := by
  unfold tailWord_606644
  simp only [CollatzResearch.WordTrace]
  refine ⟨11063062207119934695885493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14750749609493246261180657 11063062207119934695885493)
  ·
    refine ⟨1037162081917493877739265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11063062207119934695885493 1037162081917493877739265)
    ·
      refine ⟨777871561438120408304449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1037162081917493877739265 777871561438120408304449)
      ·
        refine ⟨583403671078590306228337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 777871561438120408304449 583403671078590306228337)
        ·
          refine ⟨437552753308942729671253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583403671078590306228337 437552753308942729671253)
          ·
            refine ⟨5127571327839172613335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 437552753308942729671253 5127571327839172613335)
            ·
              rfl

theorem cell21_606644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 8].length) (baseStart_606644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606644 prefixEnd_606644 := by exact prefixLift 606644
  have htrace : WordTrace (prefixWord ++ tailWord_606644) baseStart_606644 baseEnd_606644 := by
    simpa [prefixWord, tailWord_606644, baseEnd_606644] using wordTrace_append hprefix tailTrace_606644
  have hstable : (prefixWord ++ tailWord_606644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606644).length < 2 ^ (prefixWord ++ tailWord_606644).sum := by decide
  have hdescent : baseEnd_606644 < baseStart_606644 := by decide
  rcases family_descends (prefixWord ++ tailWord_606644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606706 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 4]
def baseStart_606706 : Nat := 118140960795 + 606706 * 2 ^ 59
def prefixEnd_606706 : Nat := 4983230072969 + 3 ^ 40 * 606706 * 2
def baseEnd_606706 : Nat := 138458575096359330526585

theorem tailTrace_606706 : CollatzResearch.WordTrace tailWord_606706 prefixEnd_606706 138458575096359330526585 := by
  unfold tailWord_606706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5532096435003813495131993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14752257160010169320351981 5532096435003813495131993)
  ·
    refine ⟨4149072326252860121348995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5532096435003813495131993 4149072326252860121348995)
    ·
      refine ⟨6223608489379290182023493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4149072326252860121348995 6223608489379290182023493)
      ·
        refine ⟨1166926591758616909129405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6223608489379290182023493 1166926591758616909129405)
        ·
          refine ⟨437597471909481340923527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1166926591758616909129405 437597471909481340923527)
          ·
            refine ⟨656396207864222011385291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437597471909481340923527 656396207864222011385291)
            ·
              refine ⟨984594311796333017077937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656396207864222011385291 984594311796333017077937)
              ·
                refine ⟨738445733847249762808453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 984594311796333017077937 738445733847249762808453)
                ·
                  refine ⟨138458575096359330526585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 738445733847249762808453 138458575096359330526585)
                  ·
                    rfl

theorem cell21_606706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_606706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606706 prefixEnd_606706 := by exact prefixLift 606706
  have htrace : WordTrace (prefixWord ++ tailWord_606706) baseStart_606706 baseEnd_606706 := by
    simpa [prefixWord, tailWord_606706, baseEnd_606706] using wordTrace_append hprefix tailTrace_606706
  have hstable : (prefixWord ++ tailWord_606706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606706).length < 2 ^ (prefixWord ++ tailWord_606706).sum := by decide
  have hdescent : baseEnd_606706 < baseStart_606706 := by decide
  rcases family_descends (prefixWord ++ tailWord_606706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606717 : List Nat := [1, 4, 1, 1, 1, 3, 1, 6, 3]
def baseStart_606717 : Nat := 118140960795 + 606717 * 2 ^ 59
def prefixEnd_606717 : Nat := 4983230072969 + 3 ^ 40 * 606717 * 2
def baseEnd_606717 : Nat := 138461085446225755843229

theorem tailTrace_606717 : CollatzResearch.WordTrace tailWord_606717 prefixEnd_606717 138461085446225755843229 := by
  unfold tailWord_606717
  simp only [CollatzResearch.WordTrace]
  refine ⟨22128786942975402859178405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14752524628650268572785603 22128786942975402859178405)
  ·
    refine ⟨4149147551807888036095951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22128786942975402859178405 4149147551807888036095951)
    ·
      refine ⟨6223721327711832054143927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4149147551807888036095951 6223721327711832054143927)
      ·
        refine ⟨9335581991567748081215891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6223721327711832054143927 9335581991567748081215891)
        ·
          refine ⟨14003372987351622121823837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9335581991567748081215891 14003372987351622121823837)
          ·
            refine ⟨5251264870256858295683939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14003372987351622121823837 5251264870256858295683939)
            ·
              refine ⟨7876897305385287443525909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251264870256858295683939 7876897305385287443525909)
              ·
                refine ⟨369229561189935348915277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7876897305385287443525909 369229561189935348915277)
                ·
                  refine ⟨138461085446225755843229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369229561189935348915277 138461085446225755843229)
                  ·
                    rfl

theorem cell21_606717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_606717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606717 prefixEnd_606717 := by exact prefixLift 606717
  have htrace : WordTrace (prefixWord ++ tailWord_606717) baseStart_606717 baseEnd_606717 := by
    simpa [prefixWord, tailWord_606717, baseEnd_606717] using wordTrace_append hprefix tailTrace_606717
  have hstable : (prefixWord ++ tailWord_606717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606717).length < 2 ^ (prefixWord ++ tailWord_606717).sum := by decide
  have hdescent : baseEnd_606717 < baseStart_606717 := by decide
  rcases family_descends (prefixWord ++ tailWord_606717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606762 : List Nat := [3, 1, 4, 1, 1, 4, 7]
def baseStart_606762 : Nat := 118140960795 + 606762 * 2 ^ 59
def prefixEnd_606762 : Nat := 4983230072969 + 3 ^ 40 * 606762 * 2
def baseEnd_606762 : Nat := 15385706117701741954793

theorem tailTrace_606762 : CollatzResearch.WordTrace tailWord_606762 prefixEnd_606762 15385706117701741954793 := by
  unfold tailWord_606762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5532607056953093886141635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14753618818541583696377693 5532607056953093886141635)
  ·
    refine ⟨8298910585429640829212453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5532607056953093886141635 8298910585429640829212453)
    ·
      refine ⟨1556045734768057655477335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8298910585429640829212453 1556045734768057655477335)
      ·
        refine ⟨2334068602152086483216003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1556045734768057655477335 2334068602152086483216003)
        ·
          refine ⟨3501102903228129724824005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334068602152086483216003 3501102903228129724824005)
          ·
            refine ⟨656456794355274323404501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3501102903228129724824005 656456794355274323404501)
            ·
              refine ⟨15385706117701741954793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 656456794355274323404501 15385706117701741954793)
              ·
                rfl

theorem cell21_606762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 7].length) (baseStart_606762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606762 prefixEnd_606762 := by exact prefixLift 606762
  have htrace : WordTrace (prefixWord ++ tailWord_606762) baseStart_606762 baseEnd_606762 := by
    simpa [prefixWord, tailWord_606762, baseEnd_606762] using wordTrace_append hprefix tailTrace_606762
  have hstable : (prefixWord ++ tailWord_606762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606762).length < 2 ^ (prefixWord ++ tailWord_606762).sum := by decide
  have hdescent : baseEnd_606762 < baseStart_606762 := by decide
  rcases family_descends (prefixWord ++ tailWord_606762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606821 : List Nat := [1, 3, 1, 3, 4, 9]
def baseStart_606821 : Nat := 118140960795 + 606821 * 2 ^ 59
def prefixEnd_606821 : Nat := 4983230072969 + 3 ^ 40 * 606821 * 2
def baseEnd_606821 : Nat := 5129067394931284670729

theorem tailTrace_606821 : CollatzResearch.WordTrace tailWord_606821 prefixEnd_606821 5129067394931284670729 := by
  unfold tailWord_606821
  simp only [CollatzResearch.WordTrace]
  refine ⟨22132580134598628620964317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14755053423065752413976211 22132580134598628620964317)
  ·
    refine ⟨8299717550474485732861619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22132580134598628620964317 8299717550474485732861619)
    ·
      refine ⟨12449576325711728599292429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8299717550474485732861619 12449576325711728599292429)
      ·
        refine ⟨4668591122141898224734661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12449576325711728599292429 4668591122141898224734661)
        ·
          refine ⟨875360835401605917137749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4668591122141898224734661 875360835401605917137749)
          ·
            refine ⟨5129067394931284670729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 875360835401605917137749 5129067394931284670729)
            ·
              rfl

theorem cell21_606821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 9].length) (baseStart_606821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606821 prefixEnd_606821 := by exact prefixLift 606821
  have htrace : WordTrace (prefixWord ++ tailWord_606821) baseStart_606821 baseEnd_606821 := by
    simpa [prefixWord, tailWord_606821, baseEnd_606821] using wordTrace_append hprefix tailTrace_606821
  have hstable : (prefixWord ++ tailWord_606821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606821).length < 2 ^ (prefixWord ++ tailWord_606821).sum := by decide
  have hdescent : baseEnd_606821 < baseStart_606821 := by decide
  rcases family_descends (prefixWord ++ tailWord_606821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606852 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_606852 : Nat := 118140960795 + 606852 * 2 ^ 59
def prefixEnd_606852 : Nat := 4983230072969 + 3 ^ 40 * 606852 * 2
def baseEnd_606852 : Nat := 138491894285495521092953

theorem tailTrace_606852 : CollatzResearch.WordTrace tailWord_606852 prefixEnd_606852 138491894285495521092953 := by
  unfold tailWord_606852
  simp only [CollatzResearch.WordTrace]
  refine ⟨11066855398743160457671405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14755807198324213943561873 11066855398743160457671405)
  ·
    refine ⟨4150070774528685171626777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11066855398743160457671405 4150070774528685171626777)
    ·
      refine ⟨3112553080896513878720083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4150070774528685171626777 3112553080896513878720083)
      ·
        refine ⟨4668829621344770818080125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3112553080896513878720083 4668829621344770818080125)
        ·
          refine ⟨1750811108004289056780047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4668829621344770818080125 1750811108004289056780047)
          ·
            refine ⟨2626216662006433585170071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1750811108004289056780047 2626216662006433585170071)
            ·
              refine ⟨3939324993009650377755107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626216662006433585170071 3939324993009650377755107)
              ·
                refine ⟨5908987489514475566632661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939324993009650377755107 5908987489514475566632661)
                ·
                  refine ⟨138491894285495521092953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5908987489514475566632661 138491894285495521092953)
                  ·
                    rfl

theorem cell21_606852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_606852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606852 prefixEnd_606852 := by exact prefixLift 606852
  have htrace : WordTrace (prefixWord ++ tailWord_606852) baseStart_606852 baseEnd_606852 := by
    simpa [prefixWord, tailWord_606852, baseEnd_606852] using wordTrace_append hprefix tailTrace_606852
  have hstable : (prefixWord ++ tailWord_606852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606852).length < 2 ^ (prefixWord ++ tailWord_606852).sum := by decide
  have hdescent : baseEnd_606852 < baseStart_606852 := by decide
  rcases family_descends (prefixWord ++ tailWord_606852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606945 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 5]
def baseStart_606945 : Nat := 118140960795 + 606945 * 2 ^ 59
def prefixEnd_606945 : Nat := 4983230072969 + 3 ^ 40 * 606945 * 2
def baseEnd_606945 : Nat := 138513118152548026042763

theorem tailTrace_606945 : CollatzResearch.WordTrace tailWord_606945 prefixEnd_606945 138513118152548026042763 := by
  unfold tailWord_606945
  simp only [CollatzResearch.WordTrace]
  refine ⟨22137102786149397798478289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14758068524099598532318859 22137102786149397798478289)
  ·
    refine ⟨16602827089612048348858717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22137102786149397798478289 16602827089612048348858717)
    ·
      refine ⟨6226060158604518130822019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16602827089612048348858717 6226060158604518130822019)
      ·
        refine ⟨9339090237906777196233029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6226060158604518130822019 9339090237906777196233029)
        ·
          refine ⟨1751079419607520724293693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9339090237906777196233029 1751079419607520724293693)
          ·
            refine ⟨656654782352820271610135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1751079419607520724293693 656654782352820271610135)
            ·
              refine ⟨984982173529230407415203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656654782352820271610135 984982173529230407415203)
              ·
                refine ⟨1477473260293845611122805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984982173529230407415203 1477473260293845611122805)
                ·
                  refine ⟨138513118152548026042763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1477473260293845611122805 138513118152548026042763)
                  ·
                    rfl

theorem cell21_606945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_606945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606945 prefixEnd_606945 := by exact prefixLift 606945
  have htrace : WordTrace (prefixWord ++ tailWord_606945) baseStart_606945 baseEnd_606945 := by
    simpa [prefixWord, tailWord_606945, baseEnd_606945] using wordTrace_append hprefix tailTrace_606945
  have hstable : (prefixWord ++ tailWord_606945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606945).length < 2 ^ (prefixWord ++ tailWord_606945).sum := by decide
  have hdescent : baseEnd_606945 < baseStart_606945 := by decide
  rcases family_descends (prefixWord ++ tailWord_606945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_606959 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 4]
def baseStart_606959 : Nat := 118140960795 + 606959 * 2 ^ 59
def prefixEnd_606959 : Nat := 4983230072969 + 3 ^ 40 * 606959 * 2
def baseEnd_606959 : Nat := 138516313143287112809401

theorem tailTrace_606959 : CollatzResearch.WordTrace tailWord_606959 prefixEnd_606959 138516313143287112809401 := by
  unfold tailWord_606959
  simp only [CollatzResearch.WordTrace]
  refine ⟨22137613408098678189487931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14758408938732452126325287 22137613408098678189487931)
  ·
    refine ⟨33206420112148017284231897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22137613408098678189487931 33206420112148017284231897)
    ·
      refine ⟨24904815084111012963173923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33206420112148017284231897 24904815084111012963173923)
      ·
        refine ⟨37357222626166519444760885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24904815084111012963173923 37357222626166519444760885)
        ·
          refine ⟨3502239621203111197946333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37357222626166519444760885 3502239621203111197946333)
          ·
            refine ⟨1313339857951166699229875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3502239621203111197946333 1313339857951166699229875)
            ·
              refine ⟨1970009786926750048844813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313339857951166699229875 1970009786926750048844813)
              ·
                refine ⟨738753670097531268316805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1970009786926750048844813 738753670097531268316805)
                ·
                  refine ⟨138516313143287112809401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 738753670097531268316805 138516313143287112809401)
                  ·
                    rfl

theorem cell21_606959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 4].length) (baseStart_606959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_606959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_606959 prefixEnd_606959 := by exact prefixLift 606959
  have htrace : WordTrace (prefixWord ++ tailWord_606959) baseStart_606959 baseEnd_606959 := by
    simpa [prefixWord, tailWord_606959, baseEnd_606959] using wordTrace_append hprefix tailTrace_606959
  have hstable : (prefixWord ++ tailWord_606959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_606959).length < 2 ^ (prefixWord ++ tailWord_606959).sum := by decide
  have hdescent : baseEnd_606959 < baseStart_606959 := by decide
  rcases family_descends (prefixWord ++ tailWord_606959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607052 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 4]
def baseStart_607052 : Nat := 118140960795 + 607052 * 2 ^ 59
def prefixEnd_607052 : Nat := 4983230072969 + 3 ^ 40 * 607052 * 2
def baseEnd_607052 : Nat := 138537537010339617759211

theorem tailTrace_607052 : CollatzResearch.WordTrace tailWord_607052 prefixEnd_607052 138537537010339617759211 := by
  unfold tailWord_607052
  simp only [CollatzResearch.WordTrace]
  refine ⟨11070502698380877536311705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14760670264507836715082273 11070502698380877536311705)
  ·
    refine ⟨8302877023785658152233779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11070502698380877536311705 8302877023785658152233779)
    ·
      refine ⟨12454315535678487228350669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8302877023785658152233779 12454315535678487228350669)
      ·
        refine ⟨4670368325879432710631501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12454315535678487228350669 4670368325879432710631501)
        ·
          refine ⟨1751388122204787266486813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4670368325879432710631501 1751388122204787266486813)
          ·
            refine ⟨656770545826795224932555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1751388122204787266486813 656770545826795224932555)
            ·
              refine ⟨985155818740192837398833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656770545826795224932555 985155818740192837398833)
              ·
                refine ⟨738866864055144628049125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985155818740192837398833 738866864055144628049125)
                ·
                  refine ⟨138537537010339617759211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 738866864055144628049125 138537537010339617759211)
                  ·
                    rfl

theorem cell21_607052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_607052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607052 prefixEnd_607052 := by exact prefixLift 607052
  have htrace : WordTrace (prefixWord ++ tailWord_607052) baseStart_607052 baseEnd_607052 := by
    simpa [prefixWord, tailWord_607052, baseEnd_607052] using wordTrace_append hprefix tailTrace_607052
  have hstable : (prefixWord ++ tailWord_607052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607052).length < 2 ^ (prefixWord ++ tailWord_607052).sum := by decide
  have hdescent : baseEnd_607052 < baseStart_607052 := by decide
  rcases family_descends (prefixWord ++ tailWord_607052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607080 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_607080 : Nat := 118140960795 + 607080 * 2 ^ 59
def prefixEnd_607080 : Nat := 4983230072969 + 3 ^ 40 * 607080 * 2
def baseEnd_607080 : Nat := 138543926991817791292487

theorem tailTrace_607080 : CollatzResearch.WordTrace tailWord_607080 prefixEnd_607080 138543926991817791292487 := by
  unfold tailWord_607080
  simp only [CollatzResearch.WordTrace]
  refine ⟨11071013320330157927321347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14761351093773543903095129 11071013320330157927321347)
  ·
    refine ⟨16606519980495236890982021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11071013320330157927321347 16606519980495236890982021)
    ·
      refine ⟨3113722496342856917059129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16606519980495236890982021 3113722496342856917059129)
      ·
        refine ⟨2335291872257142687794347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3113722496342856917059129 2335291872257142687794347)
        ·
          refine ⟨3502937808385714031691521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2335291872257142687794347 3502937808385714031691521)
          ·
            refine ⟨2627203356289285523768641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3502937808385714031691521 2627203356289285523768641)
            ·
              refine ⟨1970402517216964142826481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2627203356289285523768641 1970402517216964142826481)
              ·
                refine ⟨1477801887912723107119861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1970402517216964142826481 1477801887912723107119861)
                ·
                  refine ⟨138543926991817791292487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1477801887912723107119861 138543926991817791292487)
                  ·
                    rfl

theorem cell21_607080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_607080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607080 prefixEnd_607080 := by exact prefixLift 607080
  have htrace : WordTrace (prefixWord ++ tailWord_607080) baseStart_607080 baseEnd_607080 := by
    simpa [prefixWord, tailWord_607080, baseEnd_607080] using wordTrace_append hprefix tailTrace_607080
  have hstable : (prefixWord ++ tailWord_607080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607080).length < 2 ^ (prefixWord ++ tailWord_607080).sum := by decide
  have hdescent : baseEnd_607080 < baseStart_607080 := by decide
  rcases family_descends (prefixWord ++ tailWord_607080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607097 : List Nat := [1, 2, 1, 3, 2, 3, 3, 3, 3]
def baseStart_607097 : Nat := 118140960795 + 607097 * 2 ^ 59
def prefixEnd_607097 : Nat := 4983230072969 + 3 ^ 40 * 607097 * 2
def baseEnd_607097 : Nat := 138547806623429539509119

theorem tailTrace_607097 : CollatzResearch.WordTrace tailWord_607097 prefixEnd_607097 138547806623429539509119 := by
  unfold tailWord_607097
  simp only [CollatzResearch.WordTrace]
  refine ⟨22142646681598727758011545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14761764454399151838674363 22142646681598727758011545)
  ·
    refine ⟨16606985011199045818508659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22142646681598727758011545 16606985011199045818508659)
    ·
      refine ⟨24910477516798568727762989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16606985011199045818508659 24910477516798568727762989)
      ·
        refine ⟨9341429068799463272911121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24910477516798568727762989 9341429068799463272911121)
        ·
          refine ⟨7006071801599597454683341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9341429068799463272911121 7006071801599597454683341)
          ·
            refine ⟨2627276925599849045506253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7006071801599597454683341 2627276925599849045506253)
            ·
              refine ⟨985228847099943392064845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2627276925599849045506253 985228847099943392064845)
              ·
                refine ⟨369460817662478772024317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 985228847099943392064845 369460817662478772024317)
                ·
                  refine ⟨138547806623429539509119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369460817662478772024317 138547806623429539509119)
                  ·
                    rfl

theorem cell21_607097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 3].length) (baseStart_607097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607097 prefixEnd_607097 := by exact prefixLift 607097
  have htrace : WordTrace (prefixWord ++ tailWord_607097) baseStart_607097 baseEnd_607097 := by
    simpa [prefixWord, tailWord_607097, baseEnd_607097] using wordTrace_append hprefix tailTrace_607097
  have hstable : (prefixWord ++ tailWord_607097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607097).length < 2 ^ (prefixWord ++ tailWord_607097).sum := by decide
  have hdescent : baseEnd_607097 < baseStart_607097 := by decide
  rcases family_descends (prefixWord ++ tailWord_607097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607125 : List Nat := [1, 3, 2, 1, 1, 5, 2, 6]
def baseStart_607125 : Nat := 118140960795 + 607125 * 2 ^ 59
def prefixEnd_607125 : Nat := 4983230072969 + 3 ^ 40 * 607125 * 2
def baseEnd_607125 : Nat := 46184732201635904347465

theorem tailTrace_607125 : CollatzResearch.WordTrace tailWord_607125 prefixEnd_607125 46184732201635904347465 := by
  unfold tailWord_607125
  simp only [CollatzResearch.WordTrace]
  refine ⟨22143667925497288540030829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14762445283664859026687219 22143667925497288540030829)
  ·
    refine ⟨8303875472061483202511561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22143667925497288540030829 8303875472061483202511561)
    ·
      refine ⟨6227906604046112401883671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8303875472061483202511561 6227906604046112401883671)
      ·
        refine ⟨9341859906069168602825507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6227906604046112401883671 9341859906069168602825507)
        ·
          refine ⟨14012789859103752904238261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9341859906069168602825507 14012789859103752904238261)
          ·
            refine ⟨1313699049290976834772337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14012789859103752904238261 1313699049290976834772337)
            ·
              refine ⟨985274286968232626079253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1313699049290976834772337 985274286968232626079253)
              ·
                refine ⟨46184732201635904347465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 985274286968232626079253 46184732201635904347465)
                ·
                  rfl

theorem cell21_607125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 6].length) (baseStart_607125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607125 prefixEnd_607125 := by exact prefixLift 607125
  have htrace : WordTrace (prefixWord ++ tailWord_607125) baseStart_607125 baseEnd_607125 := by
    simpa [prefixWord, tailWord_607125, baseEnd_607125] using wordTrace_append hprefix tailTrace_607125
  have hstable : (prefixWord ++ tailWord_607125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607125).length < 2 ^ (prefixWord ++ tailWord_607125).sum := by decide
  have hdescent : baseEnd_607125 < baseStart_607125 := by decide
  rcases family_descends (prefixWord ++ tailWord_607125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607139 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 5]
def baseStart_607139 : Nat := 118140960795 + 607139 * 2 ^ 59
def prefixEnd_607139 : Nat := 4983230072969 + 3 ^ 40 * 607139 * 2
def baseEnd_607139 : Nat := 138557391595646799809033

theorem tailTrace_607139 : CollatzResearch.WordTrace tailWord_607139 prefixEnd_607139 138557391595646799809033 := by
  unfold tailWord_607139
  simp only [CollatzResearch.WordTrace]
  refine ⟨22144178547446568931040471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14762785698297712620693647 22144178547446568931040471)
  ·
    refine ⟨33216267821169853396560707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22144178547446568931040471 33216267821169853396560707)
    ·
      refine ⟨49824401731754780094841061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33216267821169853396560707 49824401731754780094841061)
      ·
        refine ⟨9342075324704021267782699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49824401731754780094841061 9342075324704021267782699)
        ·
          refine ⟨14013112987056031901674049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9342075324704021267782699 14013112987056031901674049)
          ·
            refine ⟨10509834740292023926255537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14013112987056031901674049 10509834740292023926255537)
            ·
              refine ⟨7882376055219017944691653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10509834740292023926255537 7882376055219017944691653)
              ·
                refine ⟨1477945510353565864629685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7882376055219017944691653 1477945510353565864629685)
                ·
                  refine ⟨138557391595646799809033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1477945510353565864629685 138557391595646799809033)
                  ·
                    rfl

theorem cell21_607139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_607139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607139 prefixEnd_607139 := by exact prefixLift 607139
  have htrace : WordTrace (prefixWord ++ tailWord_607139) baseStart_607139 baseEnd_607139 := by
    simpa [prefixWord, tailWord_607139, baseEnd_607139] using wordTrace_append hprefix tailTrace_607139
  have hstable : (prefixWord ++ tailWord_607139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607139).length < 2 ^ (prefixWord ++ tailWord_607139).sum := by decide
  have hdescent : baseEnd_607139 < baseStart_607139 := by decide
  rcases family_descends (prefixWord ++ tailWord_607139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607218 : List Nat := [3, 2, 1, 5, 1, 1, 8]
def baseStart_607218 : Nat := 118140960795 + 607218 * 2 ^ 59
def prefixEnd_607218 : Nat := 4983230072969 + 3 ^ 40 * 607218 * 2
def baseEnd_607218 : Nat := 15397268941328913110245

theorem tailTrace_607218 : CollatzResearch.WordTrace tailWord_607218 prefixEnd_607218 15397268941328913110245 := by
  unfold tailWord_607218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5536764978540091355791577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14764706609440243615444205 5536764978540091355791577)
  ·
    refine ⟨4152573733905068516843683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5536764978540091355791577 4152573733905068516843683)
    ·
      refine ⟨6228860600857602775265525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4152573733905068516843683 6228860600857602775265525)
      ·
        refine ⟨583955681330400260181143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6228860600857602775265525 583955681330400260181143)
        ·
          refine ⟨875933521995600390271715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583955681330400260181143 875933521995600390271715)
          ·
            refine ⟨1313900282993400585407573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875933521995600390271715 1313900282993400585407573)
            ·
              refine ⟨15397268941328913110245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1313900282993400585407573 15397268941328913110245)
              ·
                rfl

theorem cell21_607218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 8].length) (baseStart_607218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607218 prefixEnd_607218 := by exact prefixLift 607218
  have htrace : WordTrace (prefixWord ++ tailWord_607218) baseStart_607218 baseEnd_607218 := by
    simpa [prefixWord, tailWord_607218, baseEnd_607218] using wordTrace_append hprefix tailTrace_607218
  have hstable : (prefixWord ++ tailWord_607218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607218).length < 2 ^ (prefixWord ++ tailWord_607218).sum := by decide
  have hdescent : baseEnd_607218 < baseStart_607218 := by decide
  rcases family_descends (prefixWord ++ tailWord_607218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607266 : List Nat := [3, 3, 1, 1, 1, 5, 1, 3, 3]
def baseStart_607266 : Nat := 118140960795 + 607266 * 2 ^ 59
def prefixEnd_607266 : Nat := 4983230072969 + 3 ^ 40 * 607266 * 2
def baseEnd_607266 : Nat := 138586374725922801192107

theorem tailTrace_607266 : CollatzResearch.WordTrace tailWord_607266 prefixEnd_607266 138586374725922801192107 := by
  unfold tailWord_607266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5537202654496617405228413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14765873745324313080609101 5537202654496617405228413)
  ·
    refine ⟨2076450995436231526960655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5537202654496617405228413 2076450995436231526960655)
    ·
      refine ⟨3114676493154347290440983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2076450995436231526960655 3114676493154347290440983)
      ·
        refine ⟨4672014739731520935661475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3114676493154347290440983 4672014739731520935661475)
        ·
          refine ⟨7008022109597281403492213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4672014739731520935661475 7008022109597281403492213)
          ·
            refine ⟨657002072774745131577395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7008022109597281403492213 657002072774745131577395)
            ·
              refine ⟨985503109162117697366093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657002072774745131577395 985503109162117697366093)
              ·
                refine ⟨369563665935794136512285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 985503109162117697366093 369563665935794136512285)
                ·
                  refine ⟨138586374725922801192107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369563665935794136512285 138586374725922801192107)
                  ·
                    rfl

theorem cell21_607266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_607266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607266 prefixEnd_607266 := by exact prefixLift 607266
  have htrace : WordTrace (prefixWord ++ tailWord_607266) baseStart_607266 baseEnd_607266 := by
    simpa [prefixWord, tailWord_607266, baseEnd_607266] using wordTrace_append hprefix tailTrace_607266
  have hstable : (prefixWord ++ tailWord_607266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607266).length < 2 ^ (prefixWord ++ tailWord_607266).sum := by decide
  have hdescent : baseEnd_607266 < baseStart_607266 := by decide
  rcases family_descends (prefixWord ++ tailWord_607266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607294 : List Nat := [4, 2, 1, 3, 1, 2, 2, 6]
def baseStart_607294 : Nat := 118140960795 + 607294 * 2 ^ 59
def prefixEnd_607294 : Nat := 4983230072969 + 3 ^ 40 * 607294 * 2
def baseEnd_607294 : Nat := 46197588235800324908461

theorem tailTrace_607294 : CollatzResearch.WordTrace tailWord_607294 prefixEnd_607294 46197588235800324908461 := by
  unfold tailWord_607294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768728982735628800366617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14766554574590020268621957 2768728982735628800366617)
  ·
    refine ⟨2076546737051721600274963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2768728982735628800366617 2076546737051721600274963)
    ·
      refine ⟨3114820105577582400412445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2076546737051721600274963 3114820105577582400412445)
      ·
        refine ⟨1168057539591593400154667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3114820105577582400412445 1168057539591593400154667)
        ·
          refine ⟨1752086309387390100232001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168057539591593400154667 1752086309387390100232001)
          ·
            refine ⟨1314064732040542575174001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1752086309387390100232001 1314064732040542575174001)
            ·
              refine ⟨985548549030406931380501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314064732040542575174001 985548549030406931380501)
              ·
                refine ⟨46197588235800324908461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 985548549030406931380501 46197588235800324908461)
                ·
                  rfl

theorem cell21_607294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_607294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607294 prefixEnd_607294 := by exact prefixLift 607294
  have htrace : WordTrace (prefixWord ++ tailWord_607294) baseStart_607294 baseEnd_607294 := by
    simpa [prefixWord, tailWord_607294, baseEnd_607294] using wordTrace_append hprefix tailTrace_607294
  have hstable : (prefixWord ++ tailWord_607294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607294).length < 2 ^ (prefixWord ++ tailWord_607294).sum := by decide
  have hdescent : baseEnd_607294 < baseStart_607294 := by decide
  rcases family_descends (prefixWord ++ tailWord_607294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607297 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 4]
def baseStart_607297 : Nat := 118140960795 + 607297 * 2 ^ 59
def prefixEnd_607297 : Nat := 4983230072969 + 3 ^ 40 * 607297 * 2
def baseEnd_607297 : Nat := 138593449348273636175377

theorem tailTrace_607297 : CollatzResearch.WordTrace tailWord_607297 prefixEnd_607297 138593449348273636175377 := by
  unfold tailWord_607297
  simp only [CollatzResearch.WordTrace]
  refine ⟨22149941280874161915292145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14766627520582774610194763 22149941280874161915292145)
  ·
    refine ⟨16612455960655621436469109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22149941280874161915292145 16612455960655621436469109)
    ·
      refine ⟨1557417746311464509668979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16612455960655621436469109 1557417746311464509668979)
      ·
        refine ⟨2336126619467196764503469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557417746311464509668979 2336126619467196764503469)
        ·
          refine ⟨876047482300198786688801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2336126619467196764503469 876047482300198786688801)
          ·
            refine ⟨657035611725149090016601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 876047482300198786688801 657035611725149090016601)
            ·
              refine ⟨492776708793861817512451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657035611725149090016601 492776708793861817512451)
              ·
                refine ⟨739165063190792726268677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492776708793861817512451 739165063190792726268677)
                ·
                  refine ⟨138593449348273636175377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 739165063190792726268677 138593449348273636175377)
                  ·
                    rfl

theorem cell21_607297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_607297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607297 prefixEnd_607297 := by exact prefixLift 607297
  have htrace : WordTrace (prefixWord ++ tailWord_607297) baseStart_607297 baseEnd_607297 := by
    simpa [prefixWord, tailWord_607297, baseEnd_607297] using wordTrace_append hprefix tailTrace_607297
  have hstable : (prefixWord ++ tailWord_607297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607297).length < 2 ^ (prefixWord ++ tailWord_607297).sum := by decide
  have hdescent : baseEnd_607297 < baseStart_607297 := by decide
  rcases family_descends (prefixWord ++ tailWord_607297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607305 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 8]
def baseStart_607305 : Nat := 118140960795 + 607305 * 2 ^ 59
def prefixEnd_607305 : Nat := 4983230072969 + 3 ^ 40 * 607305 * 2
def baseEnd_607305 : Nat := 138595275057267400042027

theorem tailTrace_607305 : CollatzResearch.WordTrace tailWord_607305 prefixEnd_607305 138595275057267400042027 := by
  unfold tailWord_607305
  simp only [CollatzResearch.WordTrace]
  refine ⟨22150233064845179281583369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14766822043230119521055579 22150233064845179281583369)
  ·
    refine ⟨16612674798633884461187527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22150233064845179281583369 16612674798633884461187527)
    ·
      refine ⟨24919012197950826691781291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16612674798633884461187527 24919012197950826691781291)
      ·
        refine ⟨37378518296926240037671937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24919012197950826691781291 37378518296926240037671937)
        ·
          refine ⟨28033888722694680028253953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37378518296926240037671937 28033888722694680028253953)
          ·
            refine ⟨21025416542021010021190465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28033888722694680028253953 21025416542021010021190465)
            ·
              refine ⟨15769062406515757515892849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21025416542021010021190465 15769062406515757515892849)
              ·
                refine ⟨11826796804886818136919637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15769062406515757515892849 11826796804886818136919637)
                ·
                  refine ⟨138595275057267400042027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11826796804886818136919637 138595275057267400042027)
                  ·
                    rfl

theorem cell21_607305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_607305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607305 prefixEnd_607305 := by exact prefixLift 607305
  have htrace : WordTrace (prefixWord ++ tailWord_607305) baseStart_607305 baseEnd_607305 := by
    simpa [prefixWord, tailWord_607305, baseEnd_607305] using wordTrace_append hprefix tailTrace_607305
  have hstable : (prefixWord ++ tailWord_607305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607305).length < 2 ^ (prefixWord ++ tailWord_607305).sum := by decide
  have hdescent : baseEnd_607305 < baseStart_607305 := by decide
  rcases family_descends (prefixWord ++ tailWord_607305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607342 : List Nat := [4, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_607342 : Nat := 118140960795 + 607342 * 2 ^ 59
def prefixEnd_607342 : Nat := 4983230072969 + 3 ^ 40 * 607342 * 2
def baseEnd_607342 : Nat := 138603718961363557925285

theorem tailTrace_607342 : CollatzResearch.WordTrace tailWord_607342 prefixEnd_607342 138603718961363557925285 := by
  unfold tailWord_607342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768947820713891825085035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14767721710474089733786853 2768947820713891825085035)
  ·
    refine ⟨4153421731070837737627553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2768947820713891825085035 4153421731070837737627553)
    ·
      refine ⟨3115066298303128303220665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4153421731070837737627553 3115066298303128303220665)
      ·
        refine ⟨2336299723727346227415499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3115066298303128303220665 2336299723727346227415499)
        ·
          refine ⟨3504449585591019341123249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336299723727346227415499 3504449585591019341123249)
          ·
            refine ⟨2628337189193264505842437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3504449585591019341123249 2628337189193264505842437)
            ·
              refine ⟨492813222973737094845457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2628337189193264505842437 492813222973737094845457)
              ·
                refine ⟨369609917230302821134093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492813222973737094845457 369609917230302821134093)
                ·
                  refine ⟨138603718961363557925285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369609917230302821134093 138603718961363557925285)
                  ·
                    rfl

theorem cell21_607342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_607342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607342 prefixEnd_607342 := by exact prefixLift 607342
  have htrace : WordTrace (prefixWord ++ tailWord_607342) baseStart_607342 baseEnd_607342 := by
    simpa [prefixWord, tailWord_607342, baseEnd_607342] using wordTrace_append hprefix tailTrace_607342
  have hstable : (prefixWord ++ tailWord_607342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607342).length < 2 ^ (prefixWord ++ tailWord_607342).sum := by decide
  have hdescent : baseEnd_607342 < baseStart_607342 := by decide
  rcases family_descends (prefixWord ++ tailWord_607342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607415 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 4]
def baseStart_607415 : Nat := 118140960795 + 607415 * 2 ^ 59
def prefixEnd_607415 : Nat := 4983230072969 + 3 ^ 40 * 607415 * 2
def baseEnd_607415 : Nat := 138620378555931653208469

theorem tailTrace_607415 : CollatzResearch.WordTrace tailWord_607415 prefixEnd_607415 138620378555931653208469 := by
  unfold tailWord_607415
  simp only [CollatzResearch.WordTrace]
  refine ⟨22154245094446668068087699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14769496729631112045391799 22154245094446668068087699)
  ·
    refine ⟨33231367641670002102131549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22154245094446668068087699 33231367641670002102131549)
    ·
      refine ⟨12461762865626250788299331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33231367641670002102131549 12461762865626250788299331)
      ·
        refine ⟨18692644298439376182448997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12461762865626250788299331 18692644298439376182448997)
        ·
          refine ⟨3504870805957383034209187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18692644298439376182448997 3504870805957383034209187)
          ·
            refine ⟨5257306208936074551313781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3504870805957383034209187 5257306208936074551313781)
            ·
              refine ⟨492872457087756989185667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5257306208936074551313781 492872457087756989185667)
              ·
                refine ⟨739308685631635483778501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492872457087756989185667 739308685631635483778501)
                ·
                  refine ⟨138620378555931653208469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 739308685631635483778501 138620378555931653208469)
                  ·
                    rfl

theorem cell21_607415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 4].length) (baseStart_607415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607415 prefixEnd_607415 := by exact prefixLift 607415
  have htrace : WordTrace (prefixWord ++ tailWord_607415) baseStart_607415 baseEnd_607415 := by
    simpa [prefixWord, tailWord_607415, baseEnd_607415] using wordTrace_append hprefix tailTrace_607415
  have hstable : (prefixWord ++ tailWord_607415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607415).length < 2 ^ (prefixWord ++ tailWord_607415).sum := by decide
  have hdescent : baseEnd_607415 < baseStart_607415 := by decide
  rcases family_descends (prefixWord ++ tailWord_607415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607460 : List Nat := [2, 3, 1, 1, 1, 2, 2, 6, 3]
def baseStart_607460 : Nat := 118140960795 + 607460 * 2 ^ 59
def prefixEnd_607460 : Nat := 4983230072969 + 3 ^ 40 * 607460 * 2
def baseEnd_607460 : Nat := 138630648169021574958377

theorem tailTrace_607460 : CollatzResearch.WordTrace tailWord_607460 prefixEnd_607460 138630648169021574958377 := by
  unfold tailWord_607460
  simp only [CollatzResearch.WordTrace]
  refine ⟨11077943189641820376737917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14770590919522427168983889 11077943189641820376737917)
  ·
    refine ⟨4154228696115682641276719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11077943189641820376737917 4154228696115682641276719)
    ·
      refine ⟨6231343044173523961915079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4154228696115682641276719 6231343044173523961915079)
      ·
        refine ⟨9347014566260285942872619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231343044173523961915079 9347014566260285942872619)
        ·
          refine ⟨14020521849390428914308929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9347014566260285942872619 14020521849390428914308929)
          ·
            refine ⟨10515391387042821685731697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14020521849390428914308929 10515391387042821685731697)
            ·
              refine ⟨7886543540282116264298773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10515391387042821685731697 7886543540282116264298773)
              ·
                refine ⟨369681728450724199889005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7886543540282116264298773 369681728450724199889005)
                ·
                  refine ⟨138630648169021574958377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369681728450724199889005 138630648169021574958377)
                  ·
                    rfl

theorem cell21_607460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_607460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607460 prefixEnd_607460 := by exact prefixLift 607460
  have htrace : WordTrace (prefixWord ++ tailWord_607460) baseStart_607460 baseEnd_607460 := by
    simpa [prefixWord, tailWord_607460, baseEnd_607460] using wordTrace_append hprefix tailTrace_607460
  have hstable : (prefixWord ++ tailWord_607460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607460).length < 2 ^ (prefixWord ++ tailWord_607460).sum := by decide
  have hdescent : baseEnd_607460 < baseStart_607460 := by decide
  rcases family_descends (prefixWord ++ tailWord_607460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607522 : List Nat := [3, 3, 1, 1, 4, 2, 1, 6]
def baseStart_607522 : Nat := 118140960795 + 607522 * 2 ^ 59
def prefixEnd_607522 : Nat := 4983230072969 + 3 ^ 40 * 607522 * 2
def baseEnd_607522 : Nat := 46214932471241081641639

theorem tailTrace_607522 : CollatzResearch.WordTrace tailWord_607522 prefixEnd_607522 46214932471241081641639 := by
  unfold tailWord_607522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5539536926264756335558205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14772098470039350228155213 5539536926264756335558205)
  ·
    refine ⟨2077326347349283625834327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5539536926264756335558205 2077326347349283625834327)
    ·
      refine ⟨3115989521023925438751491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077326347349283625834327 3115989521023925438751491)
      ·
        refine ⟨4673984281535888158127237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115989521023925438751491 4673984281535888158127237)
        ·
          refine ⟨876372052787979029648857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4673984281535888158127237 876372052787979029648857)
          ·
            refine ⟨657279039590984272236643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 876372052787979029648857 657279039590984272236643)
            ·
              refine ⟨985918559386476408354965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657279039590984272236643 985918559386476408354965)
              ·
                refine ⟨46214932471241081641639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 985918559386476408354965 46214932471241081641639)
                ·
                  rfl

theorem cell21_607522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_607522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607522 prefixEnd_607522 := by exact prefixLift 607522
  have htrace : WordTrace (prefixWord ++ tailWord_607522) baseStart_607522 baseEnd_607522 := by
    simpa [prefixWord, tailWord_607522, baseEnd_607522] using wordTrace_append hprefix tailTrace_607522
  have hstable : (prefixWord ++ tailWord_607522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607522).length < 2 ^ (prefixWord ++ tailWord_607522).sum := by decide
  have hdescent : baseEnd_607522 < baseStart_607522 := by decide
  rcases family_descends (prefixWord ++ tailWord_607522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607550 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_607550 : Nat := 118140960795 + 607550 * 2 ^ 59
def prefixEnd_607550 : Nat := 4983230072969 + 3 ^ 40 * 607550 * 2
def baseEnd_607550 : Nat := 138651187395201418458193

theorem tailTrace_607550 : CollatzResearch.WordTrace tailWord_607550 prefixEnd_607550 138651187395201418458193 := by
  unfold tailWord_607550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769896118619698265531513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14772779299305057416168069 2769896118619698265531513)
  ·
    refine ⟨2077422088964773699148635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2769896118619698265531513 2077422088964773699148635)
    ·
      refine ⟨3116133133447160548722953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077422088964773699148635 3116133133447160548722953)
      ·
        refine ⟨2337099850085370411542215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3116133133447160548722953 2337099850085370411542215)
        ·
          refine ⟨3505649775128055617313323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337099850085370411542215 3505649775128055617313323)
          ·
            refine ⟨5258474662692083425969985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505649775128055617313323 5258474662692083425969985)
            ·
              refine ⟨3943855997019062569477489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5258474662692083425969985 3943855997019062569477489)
              ·
                refine ⟨2957891997764296927108117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3943855997019062569477489 2957891997764296927108117)
                ·
                  refine ⟨138651187395201418458193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2957891997764296927108117 138651187395201418458193)
                  ·
                    rfl

theorem cell21_607550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_607550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607550 prefixEnd_607550 := by exact prefixLift 607550
  have htrace : WordTrace (prefixWord ++ tailWord_607550) baseStart_607550 baseEnd_607550 := by
    simpa [prefixWord, tailWord_607550, baseEnd_607550] using wordTrace_append hprefix tailTrace_607550
  have hstable : (prefixWord ++ tailWord_607550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607550).length < 2 ^ (prefixWord ++ tailWord_607550).sum := by decide
  have hdescent : baseEnd_607550 < baseStart_607550 := by decide
  rcases family_descends (prefixWord ++ tailWord_607550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607553 : List Nat := [1, 2, 5, 2, 1, 1, 1, 5, 3]
def baseStart_607553 : Nat := 118140960795 + 607553 * 2 ^ 59
def prefixEnd_607553 : Nat := 4983230072969 + 3 ^ 40 * 607553 * 2
def baseEnd_607553 : Nat := 138651872036074079908187

theorem tailTrace_607553 : CollatzResearch.WordTrace tailWord_607553 prefixEnd_607553 138651872036074079908187 := by
  unfold tailWord_607553
  simp only [CollatzResearch.WordTrace]
  refine ⟨22159278367946717636611313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14772852245297811757740875 22159278367946717636611313)
  ·
    refine ⟨16619458775960038227458485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22159278367946717636611313 16619458775960038227458485)
    ·
      refine ⟨1558074260246253583824233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16619458775960038227458485 1558074260246253583824233)
      ·
        refine ⟨1168555695184690187868175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1558074260246253583824233 1168555695184690187868175)
        ·
          refine ⟨1752833542777035281802263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168555695184690187868175 1752833542777035281802263)
          ·
            refine ⟨2629250314165552922703395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752833542777035281802263 2629250314165552922703395)
            ·
              refine ⟨3943875471248329384055093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629250314165552922703395 3943875471248329384055093)
              ·
                refine ⟨369738325429530879755165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3943875471248329384055093 369738325429530879755165)
                ·
                  refine ⟨138651872036074079908187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369738325429530879755165 138651872036074079908187)
                  ·
                    rfl

theorem cell21_607553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 3].length) (baseStart_607553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607553 prefixEnd_607553 := by exact prefixLift 607553
  have htrace : WordTrace (prefixWord ++ tailWord_607553) baseStart_607553 baseEnd_607553 := by
    simpa [prefixWord, tailWord_607553, baseEnd_607553] using wordTrace_append hprefix tailTrace_607553
  have hstable : (prefixWord ++ tailWord_607553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607553).length < 2 ^ (prefixWord ++ tailWord_607553).sum := by decide
  have hdescent : baseEnd_607553 < baseStart_607553 := by decide
  rcases family_descends (prefixWord ++ tailWord_607553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607564 : List Nat := [2, 2, 1, 3, 2, 3, 8]
def baseStart_607564 : Nat := 118140960795 + 607564 * 2 ^ 59
def prefixEnd_607564 : Nat := 4983230072969 + 3 ^ 40 * 607564 * 2
def baseEnd_607564 : Nat := 15406042487326722802759

theorem tailTrace_607564 : CollatzResearch.WordTrace tailWord_607564 prefixEnd_607564 15406042487326722802759 := by
  unfold tailWord_607564
  simp only [CollatzResearch.WordTrace]
  refine ⟨11079839785453433257630873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14773119713937911010174497 11079839785453433257630873)
  ·
    refine ⟨8309879839090074943223155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11079839785453433257630873 8309879839090074943223155)
    ·
      refine ⟨12464819758635112414834733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8309879839090074943223155 12464819758635112414834733)
      ·
        refine ⟨4674307409488167155563025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12464819758635112414834733 4674307409488167155563025)
        ·
          refine ⟨3505730557116125366672269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4674307409488167155563025 3505730557116125366672269)
          ·
            refine ⟨1314648958918547012502101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3505730557116125366672269 1314648958918547012502101)
            ·
              refine ⟨15406042487326722802759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1314648958918547012502101 15406042487326722802759)
              ·
                rfl

theorem cell21_607564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 8].length) (baseStart_607564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607564 prefixEnd_607564 := by exact prefixLift 607564
  have htrace : WordTrace (prefixWord ++ tailWord_607564) baseStart_607564 baseEnd_607564 := by
    simpa [prefixWord, tailWord_607564, baseEnd_607564] using wordTrace_append hprefix tailTrace_607564
  have hstable : (prefixWord ++ tailWord_607564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607564).length < 2 ^ (prefixWord ++ tailWord_607564).sum := by decide
  have hdescent : baseEnd_607564 < baseStart_607564 := by decide
  rcases family_descends (prefixWord ++ tailWord_607564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607598 : List Nat := [4, 1, 2, 4, 1, 1, 1, 7]
def baseStart_607598 : Nat := 118140960795 + 607598 * 2 ^ 59
def prefixEnd_607598 : Nat := 4983230072969 + 3 ^ 40 * 607598 * 2
def baseEnd_607598 : Nat := 46220713883054667219365

theorem tailTrace_607598 : CollatzResearch.WordTrace tailWord_607598 prefixEnd_607598 46220713883054667219365 := by
  unfold tailWord_607598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770114956597961290249931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14773946435189126881332965 2770114956597961290249931)
  ·
    refine ⟨4155172434896941935374897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2770114956597961290249931 4155172434896941935374897)
    ·
      refine ⟨3116379326172706451531173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4155172434896941935374897 3116379326172706451531173)
      ·
        refine ⟨584321123657382459662095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3116379326172706451531173 584321123657382459662095)
        ·
          refine ⟨876481685486073689493143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584321123657382459662095 876481685486073689493143)
          ·
            refine ⟨1314722528229110534239715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876481685486073689493143 1314722528229110534239715)
            ·
              refine ⟨1972083792343665801359573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314722528229110534239715 1972083792343665801359573)
              ·
                refine ⟨46220713883054667219365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1972083792343665801359573 46220713883054667219365)
                ·
                  rfl

theorem cell21_607598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_607598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607598 prefixEnd_607598 := by exact prefixLift 607598
  have htrace : WordTrace (prefixWord ++ tailWord_607598) baseStart_607598 baseEnd_607598 := by
    simpa [prefixWord, tailWord_607598, baseEnd_607598] using wordTrace_append hprefix tailTrace_607598
  have hstable : (prefixWord ++ tailWord_607598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607598).length < 2 ^ (prefixWord ++ tailWord_607598).sum := by decide
  have hdescent : baseEnd_607598 < baseStart_607598 := by decide
  rcases family_descends (prefixWord ++ tailWord_607598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607609 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 6]
def baseStart_607609 : Nat := 118140960795 + 607609 * 2 ^ 59
def prefixEnd_607609 : Nat := 4983230072969 + 3 ^ 40 * 607609 * 2
def baseEnd_607609 : Nat := 138664651999030426974739

theorem tailTrace_607609 : CollatzResearch.WordTrace tailWord_607609 prefixEnd_607609 138664651999030426974739 := by
  unfold tailWord_607609
  simp only [CollatzResearch.WordTrace]
  refine ⟨22161320855743839200649881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14774213903829226133766587 22161320855743839200649881)
  ·
    refine ⟨16620990641807879400487411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22161320855743839200649881 16620990641807879400487411)
    ·
      refine ⟨24931485962711819100731117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16620990641807879400487411 24931485962711819100731117)
      ·
        refine ⟨9349307236016932162774169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24931485962711819100731117 9349307236016932162774169)
        ·
          refine ⟨7011980427012699122080627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9349307236016932162774169 7011980427012699122080627)
          ·
            refine ⟨10517970640519048683120941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7011980427012699122080627 10517970640519048683120941)
            ·
              refine ⟨3944238990194643256170353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10517970640519048683120941 3944238990194643256170353)
              ·
                refine ⟨2958179242645982442127765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3944238990194643256170353 2958179242645982442127765)
                ·
                  refine ⟨138664651999030426974739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2958179242645982442127765 138664651999030426974739)
                  ·
                    rfl

theorem cell21_607609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_607609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607609 prefixEnd_607609 := by exact prefixLift 607609
  have htrace : WordTrace (prefixWord ++ tailWord_607609) baseStart_607609 baseEnd_607609 := by
    simpa [prefixWord, tailWord_607609, baseEnd_607609] using wordTrace_append hprefix tailTrace_607609
  have hstable : (prefixWord ++ tailWord_607609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607609).length < 2 ^ (prefixWord ++ tailWord_607609).sum := by decide
  have hdescent : baseEnd_607609 < baseStart_607609 := by decide
  rcases family_descends (prefixWord ++ tailWord_607609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607688 : List Nat := [2, 1, 3, 1, 3, 1, 3, 4, 3]
def baseStart_607688 : Nat := 118140960795 + 607688 * 2 ^ 59
def prefixEnd_607688 : Nat := 4983230072969 + 3 ^ 40 * 607688 * 2
def baseEnd_607688 : Nat := 138682680875343845157911

theorem tailTrace_607688 : CollatzResearch.WordTrace tailWord_607688 prefixEnd_607688 138682680875343845157911 := by
  unfold tailWord_607688
  simp only [CollatzResearch.WordTrace]
  refine ⟨11082101111228817846387859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14776134814971757128517145 11082101111228817846387859)
  ·
    refine ⟨16623151666843226769581789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11082101111228817846387859 16623151666843226769581789)
    ·
      refine ⟨6233681875066210038593171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16623151666843226769581789 6233681875066210038593171)
      ·
        refine ⟨9350522812599315057889757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6233681875066210038593171 9350522812599315057889757)
        ·
          refine ⟨3506446054724743146708659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9350522812599315057889757 3506446054724743146708659)
          ·
            refine ⟨5259669082087114720062989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506446054724743146708659 5259669082087114720062989)
            ·
              refine ⟨1972375905782668020023621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5259669082087114720062989 1972375905782668020023621)
              ·
                refine ⟨369820482334250253754429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1972375905782668020023621 369820482334250253754429)
                ·
                  refine ⟨138682680875343845157911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369820482334250253754429 138682680875343845157911)
                  ·
                    rfl

theorem cell21_607688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 3].length) (baseStart_607688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607688 prefixEnd_607688 := by exact prefixLift 607688
  have htrace : WordTrace (prefixWord ++ tailWord_607688) baseStart_607688 baseEnd_607688 := by
    simpa [prefixWord, tailWord_607688, baseEnd_607688] using wordTrace_append hprefix tailTrace_607688
  have hstable : (prefixWord ++ tailWord_607688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607688).length < 2 ^ (prefixWord ++ tailWord_607688).sum := by decide
  have hdescent : baseEnd_607688 < baseStart_607688 := by decide
  rcases family_descends (prefixWord ++ tailWord_607688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607733 : List Nat := [1, 3, 5, 1, 1, 2, 8]
def baseStart_607733 : Nat := 118140960795 + 607733 * 2 ^ 59
def prefixEnd_607733 : Nat := 4983230072969 + 3 ^ 40 * 607733 * 2
def baseEnd_607733 : Nat := 15410327832048196323091

theorem tailTrace_607733 : CollatzResearch.WordTrace tailWord_607733 prefixEnd_607733 15410327832048196323091 := by
  unfold tailWord_607733
  simp only [CollatzResearch.WordTrace]
  refine ⟨22165843507294608378163853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14777229004863072252109235 22165843507294608378163853)
  ·
    refine ⟨8312191315235478141811445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22165843507294608378163853 8312191315235478141811445)
    ·
      refine ⟨779267935803326075794823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8312191315235478141811445 779267935803326075794823)
      ·
        refine ⟨1168901903704989113692235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 779267935803326075794823 1168901903704989113692235)
        ·
          refine ⟨1753352855557483670538353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168901903704989113692235 1753352855557483670538353)
          ·
            refine ⟨1315014641668112752903765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1753352855557483670538353 1315014641668112752903765)
            ·
              refine ⟨15410327832048196323091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1315014641668112752903765 15410327832048196323091)
              ·
                rfl

theorem cell21_607733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 8].length) (baseStart_607733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607733 prefixEnd_607733 := by exact prefixLift 607733
  have htrace : WordTrace (prefixWord ++ tailWord_607733) baseStart_607733 baseEnd_607733 := by
    simpa [prefixWord, tailWord_607733, baseEnd_607733] using wordTrace_append hprefix tailTrace_607733
  have hstable : (prefixWord ++ tailWord_607733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607733).length < 2 ^ (prefixWord ++ tailWord_607733).sum := by decide
  have hdescent : baseEnd_607733 < baseStart_607733 := by decide
  rcases family_descends (prefixWord ++ tailWord_607733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_607798 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_607798 : Nat := 118140960795 + 607798 * 2 ^ 59
def prefixEnd_607798 : Nat := 4983230072969 + 3 ^ 40 * 607798 * 2
def baseEnd_607798 : Nat := 138707784374008098324353

theorem tailTrace_607798 : CollatzResearch.WordTrace tailWord_607798 prefixEnd_607798 138707784374008098324353 := by
  unfold tailWord_607798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385513390753695279955003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14778809501372749652853365 1385513390753695279955003)
  ·
    refine ⟨2078270086130542919932505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1385513390753695279955003 2078270086130542919932505)
    ·
      refine ⟨1558702564597907189949379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2078270086130542919932505 1558702564597907189949379)
      ·
        refine ⟨2338053846896860784924069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558702564597907189949379 2338053846896860784924069)
        ·
          refine ⟨438385096293161397173263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2338053846896860784924069 438385096293161397173263)
          ·
            refine ⟨657577644439742095759895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438385096293161397173263 657577644439742095759895)
            ·
              refine ⟨986366466659613143639843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657577644439742095759895 986366466659613143639843)
              ·
                refine ⟨1479549699989419715459765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986366466659613143639843 1479549699989419715459765)
                ·
                  refine ⟨138707784374008098324353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1479549699989419715459765 138707784374008098324353)
                  ·
                    rfl

theorem cell21_607798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_607798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_607798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_607798 prefixEnd_607798 := by exact prefixLift 607798
  have htrace : WordTrace (prefixWord ++ tailWord_607798) baseStart_607798 baseEnd_607798 := by
    simpa [prefixWord, tailWord_607798, baseEnd_607798] using wordTrace_append hprefix tailTrace_607798
  have hstable : (prefixWord ++ tailWord_607798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_607798).length < 2 ^ (prefixWord ++ tailWord_607798).sum := by decide
  have hdescent : baseEnd_607798 < baseStart_607798 := by decide
  rcases family_descends (prefixWord ++ tailWord_607798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608003 : List Nat := [1, 1, 1, 3, 2, 2, 4, 7]
def baseStart_608003 : Nat := 118140960795 + 608003 * 2 ^ 59
def prefixEnd_608003 : Nat := 4983230072969 + 3 ^ 40 * 608003 * 2
def baseEnd_608003 : Nat := 46251522722324432469089

theorem tailTrace_608003 : CollatzResearch.WordTrace tailWord_608003 prefixEnd_608003 46251522722324432469089 := by
  unfold tailWord_608003
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175691216316444490492663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14783794144210962993661775 22175691216316444490492663)
  ·
    refine ⟨33263536824474666735738995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22175691216316444490492663 33263536824474666735738995)
    ·
      refine ⟨49895305236712000103608493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33263536824474666735738995 49895305236712000103608493)
      ·
        refine ⟨18710739463767000038853185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49895305236712000103608493 18710739463767000038853185)
        ·
          refine ⟨14033054597825250029139889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18710739463767000038853185 14033054597825250029139889)
          ·
            refine ⟨10524790948368937521854917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14033054597825250029139889 10524790948368937521854917)
            ·
              refine ⟨1973398302819175785347797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10524790948368937521854917 1973398302819175785347797)
              ·
                refine ⟨46251522722324432469089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1973398302819175785347797 46251522722324432469089)
                ·
                  rfl

theorem cell21_608003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 7].length) (baseStart_608003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608003 prefixEnd_608003 := by exact prefixLift 608003
  have htrace : WordTrace (prefixWord ++ tailWord_608003) baseStart_608003 baseEnd_608003 := by
    simpa [prefixWord, tailWord_608003, baseEnd_608003] using wordTrace_append hprefix tailTrace_608003
  have hstable : (prefixWord ++ tailWord_608003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608003).length < 2 ^ (prefixWord ++ tailWord_608003).sum := by decide
  have hdescent : baseEnd_608003 < baseStart_608003 := by decide
  rcases family_descends (prefixWord ++ tailWord_608003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608048 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_608048 : Nat := 118140960795 + 608048 * 2 ^ 59
def prefixEnd_608048 : Nat := 4983230072969 + 3 ^ 40 * 608048 * 2
def baseEnd_608048 : Nat := 138764837780063219157175

theorem tailTrace_608048 : CollatzResearch.WordTrace tailWord_608048 prefixEnd_608048 138764837780063219157175 := by
  unfold tailWord_608048
  simp only [CollatzResearch.WordTrace]
  refine ⟨11088666250576708587940399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14784888334102278117253865 11088666250576708587940399)
  ·
    refine ⟨16632999375865062881910599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11088666250576708587940399 16632999375865062881910599)
    ·
      refine ⟨24949499063797594322865899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16632999375865062881910599 24949499063797594322865899)
      ·
        refine ⟨37424248595696391484298849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24949499063797594322865899 37424248595696391484298849)
        ·
          refine ⟨28068186446772293613224137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37424248595696391484298849 28068186446772293613224137)
          ·
            refine ⟨21051139835079220209918103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28068186446772293613224137 21051139835079220209918103)
            ·
              refine ⟨31576709752618830314877155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21051139835079220209918103 31576709752618830314877155)
              ·
                refine ⟨47365064628928245472315733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31576709752618830314877155 47365064628928245472315733)
                ·
                  refine ⟨138764837780063219157175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 47365064628928245472315733 138764837780063219157175)
                  ·
                    rfl

theorem cell21_608048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_608048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608048 prefixEnd_608048 := by exact prefixLift 608048
  have htrace : WordTrace (prefixWord ++ tailWord_608048) baseStart_608048 baseEnd_608048 := by
    simpa [prefixWord, tailWord_608048, baseEnd_608048] using wordTrace_append hprefix tailTrace_608048
  have hstable : (prefixWord ++ tailWord_608048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608048).length < 2 ^ (prefixWord ++ tailWord_608048).sum := by decide
  have hdescent : baseEnd_608048 < baseStart_608048 := by decide
  rcases family_descends (prefixWord ++ tailWord_608048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608051 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 5]
def baseStart_608051 : Nat := 118140960795 + 608051 * 2 ^ 59
def prefixEnd_608051 : Nat := 4983230072969 + 3 ^ 40 * 608051 * 2
def baseEnd_608051 : Nat := 138765522420935880607169

theorem tailTrace_608051 : CollatzResearch.WordTrace tailWord_608051 prefixEnd_608051 138765522420935880607169 := by
  unfold tailWord_608051
  simp only [CollatzResearch.WordTrace]
  refine ⟨22177441920142548688240007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14784961280095032458826671 22177441920142548688240007)
  ·
    refine ⟨33266162880213823032360011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22177441920142548688240007 33266162880213823032360011)
    ·
      refine ⟨49899244320320734548540017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33266162880213823032360011 49899244320320734548540017)
      ·
        refine ⟨37424433240240550911405013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49899244320320734548540017 37424433240240550911405013)
        ·
          refine ⟨877135154068137911986055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 37424433240240550911405013 877135154068137911986055)
          ·
            refine ⟨1315702731102206867979083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877135154068137911986055 1315702731102206867979083)
            ·
              refine ⟨1973554096653310301968625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315702731102206867979083 1973554096653310301968625)
              ·
                refine ⟨1480165572489982726476469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973554096653310301968625 1480165572489982726476469)
                ·
                  refine ⟨138765522420935880607169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1480165572489982726476469 138765522420935880607169)
                  ·
                    rfl

theorem cell21_608051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 5].length) (baseStart_608051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608051 prefixEnd_608051 := by exact prefixLift 608051
  have htrace : WordTrace (prefixWord ++ tailWord_608051) baseStart_608051 baseEnd_608051 := by
    simpa [prefixWord, tailWord_608051, baseEnd_608051] using wordTrace_append hprefix tailTrace_608051
  have hstable : (prefixWord ++ tailWord_608051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608051).length < 2 ^ (prefixWord ++ tailWord_608051).sum := by decide
  have hdescent : baseEnd_608051 < baseStart_608051 := by decide
  rcases family_descends (prefixWord ++ tailWord_608051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608054 : List Nat := [5, 1, 2, 2, 1, 2, 3, 5]
def baseStart_608054 : Nat := 118140960795 + 608054 * 2 ^ 59
def prefixEnd_608054 : Nat := 4983230072969 + 3 ^ 40 * 608054 * 2
def baseEnd_608054 : Nat := 46255402353936180685721

theorem tailTrace_608054 : CollatzResearch.WordTrace tailWord_608054 prefixEnd_608054 46255402353936180685721 := by
  unfold tailWord_608054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1386096958695730012537451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14785034226087786800399477 1386096958695730012537451)
  ·
    refine ⟨2079145438043595018806177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1386096958695730012537451 2079145438043595018806177)
    ·
      refine ⟨1559359078532696264104633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2079145438043595018806177 1559359078532696264104633)
      ·
        refine ⟨1169519308899522198078475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1559359078532696264104633 1169519308899522198078475)
        ·
          refine ⟨1754278963349283297117713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1169519308899522198078475 1754278963349283297117713)
          ·
            refine ⟨1315709222511962472838285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1754278963349283297117713 1315709222511962472838285)
            ·
              refine ⟨493390958441985927314357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1315709222511962472838285 493390958441985927314357)
              ·
                refine ⟨46255402353936180685721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 493390958441985927314357 46255402353936180685721)
                ·
                  rfl

theorem cell21_608054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_608054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608054 prefixEnd_608054 := by exact prefixLift 608054
  have htrace : WordTrace (prefixWord ++ tailWord_608054) baseStart_608054 baseEnd_608054 := by
    simpa [prefixWord, tailWord_608054, baseEnd_608054] using wordTrace_append hprefix tailTrace_608054
  have hstable : (prefixWord ++ tailWord_608054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608054).length < 2 ^ (prefixWord ++ tailWord_608054).sum := by decide
  have hdescent : baseEnd_608054 < baseStart_608054 := by decide
  rcases family_descends (prefixWord ++ tailWord_608054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608082 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_608082 : Nat := 118140960795 + 608082 * 2 ^ 59
def prefixEnd_608082 : Nat := 4983230072969 + 3 ^ 40 * 608082 * 2
def baseEnd_608082 : Nat := 138772597043286715590439

theorem tailTrace_608082 : CollatzResearch.WordTrace tailWord_608082 prefixEnd_608082 138772597043286715590439 := by
  unfold tailWord_608082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5544643145757560245654625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14785715055353493988412333 5544643145757560245654625)
  ·
    refine ⟨4158482359318170184240969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5544643145757560245654625 4158482359318170184240969)
    ·
      refine ⟨3118861769488627638180727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4158482359318170184240969 3118861769488627638180727)
      ·
        refine ⟨4678292654232941457271091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3118861769488627638180727 4678292654232941457271091)
        ·
          refine ⟨7017438981349412185906637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4678292654232941457271091 7017438981349412185906637)
          ·
            refine ⟨2631539618006029569714989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7017438981349412185906637 2631539618006029569714989)
            ·
              refine ⟨986827356752261088643121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2631539618006029569714989 986827356752261088643121)
              ·
                refine ⟨740120517564195816482341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986827356752261088643121 740120517564195816482341)
                ·
                  refine ⟨138772597043286715590439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740120517564195816482341 138772597043286715590439)
                  ·
                    rfl

theorem cell21_608082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_608082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608082 prefixEnd_608082 := by exact prefixLift 608082
  have htrace : WordTrace (prefixWord ++ tailWord_608082) baseStart_608082 baseEnd_608082 := by
    simpa [prefixWord, tailWord_608082, baseEnd_608082] using wordTrace_append hprefix tailTrace_608082
  have hstable : (prefixWord ++ tailWord_608082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608082).length < 2 ^ (prefixWord ++ tailWord_608082).sum := by decide
  have hdescent : baseEnd_608082 < baseStart_608082 := by decide
  rcases family_descends (prefixWord ++ tailWord_608082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608099 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 4]
def baseStart_608099 : Nat := 118140960795 + 608099 * 2 ^ 59
def prefixEnd_608099 : Nat := 4983230072969 + 3 ^ 40 * 608099 * 2
def baseEnd_608099 : Nat := 138776476674898463807071

theorem tailTrace_608099 : CollatzResearch.WordTrace tailWord_608099 prefixEnd_608099 138776476674898463807071 := by
  unfold tailWord_608099
  simp only [CollatzResearch.WordTrace]
  refine ⟨22179192623968652885987351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14786128415979101923991567 22179192623968652885987351)
  ·
    refine ⟨33268788935952979328981027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22179192623968652885987351 33268788935952979328981027)
    ·
      refine ⟨49903183403929468993471541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33268788935952979328981027 49903183403929468993471541)
      ·
        refine ⟨4678423444118387718137957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49903183403929468993471541 4678423444118387718137957)
        ·
          refine ⟨877204395772197697150867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4678423444118387718137957 877204395772197697150867)
          ·
            refine ⟨1315806593658296545726301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877204395772197697150867 1315806593658296545726301)
            ·
              refine ⟨493427472621861204647363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1315806593658296545726301 493427472621861204647363)
              ·
                refine ⟨740141208932791806971045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493427472621861204647363 740141208932791806971045)
                ·
                  refine ⟨138776476674898463807071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740141208932791806971045 138776476674898463807071)
                  ·
                    rfl

theorem cell21_608099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 4].length) (baseStart_608099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608099 prefixEnd_608099 := by exact prefixLift 608099
  have htrace : WordTrace (prefixWord ++ tailWord_608099) baseStart_608099 baseEnd_608099 := by
    simpa [prefixWord, tailWord_608099, baseEnd_608099] using wordTrace_append hprefix tailTrace_608099
  have hstable : (prefixWord ++ tailWord_608099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608099).length < 2 ^ (prefixWord ++ tailWord_608099).sum := by decide
  have hdescent : baseEnd_608099 < baseStart_608099 := by decide
  rcases family_descends (prefixWord ++ tailWord_608099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608150 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_608150 : Nat := 118140960795 + 608150 * 2 ^ 59
def prefixEnd_608150 : Nat := 4983230072969 + 3 ^ 40 * 608150 * 2
def baseEnd_608150 : Nat := 138788115569733708456967

theorem tailTrace_608150 : CollatzResearch.WordTrace tailWord_608150 prefixEnd_608150 138788115569733708456967 := by
  unfold tailWord_608150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1386315796673993037255869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14787368497855925730729269 1386315796673993037255869)
  ·
    refine ⟨519868423752747388970951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1386315796673993037255869 519868423752747388970951)
    ·
      refine ⟨779802635629121083456427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519868423752747388970951 779802635629121083456427)
      ·
        refine ⟨1169703953443681625184641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 779802635629121083456427 1169703953443681625184641)
        ·
          refine ⟨877277965082761218888481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1169703953443681625184641 877277965082761218888481)
          ·
            refine ⟨657958473812070914166361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 877277965082761218888481 657958473812070914166361)
            ·
              refine ⟨493468855359053185624771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657958473812070914166361 493468855359053185624771)
              ·
                refine ⟨740203283038579778437157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493468855359053185624771 740203283038579778437157)
                ·
                  refine ⟨138788115569733708456967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740203283038579778437157 138788115569733708456967)
                  ·
                    rfl

theorem cell21_608150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_608150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608150 prefixEnd_608150 := by exact prefixLift 608150
  have htrace : WordTrace (prefixWord ++ tailWord_608150) baseStart_608150 baseEnd_608150 := by
    simpa [prefixWord, tailWord_608150, baseEnd_608150] using wordTrace_append hprefix tailTrace_608150
  have hstable : (prefixWord ++ tailWord_608150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608150).length < 2 ^ (prefixWord ++ tailWord_608150).sum := by decide
  have hdescent : baseEnd_608150 < baseStart_608150 := by decide
  rcases family_descends (prefixWord ++ tailWord_608150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608203 : List Nat := [1, 1, 1, 1, 3, 4, 3, 4, 3]
def baseStart_608203 : Nat := 118140960795 + 608203 * 2 ^ 59
def prefixEnd_608203 : Nat := 4983230072969 + 3 ^ 40 * 608203 * 2
def baseEnd_608203 : Nat := 138800210891817394073525

theorem tailTrace_608203 : CollatzResearch.WordTrace tailWord_608203 prefixEnd_608203 138800210891817394073525 := by
  unfold tailWord_608203
  simp only [CollatzResearch.WordTrace]
  refine ⟨22182985815591878647773263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14788657210394585765182175 22182985815591878647773263)
  ·
    refine ⟨33274478723387817971659895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22182985815591878647773263 33274478723387817971659895)
    ·
      refine ⟨49911718085081726957489843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33274478723387817971659895 49911718085081726957489843)
      ·
        refine ⟨74867577127622590436234765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49911718085081726957489843 74867577127622590436234765)
        ·
          refine ⟨28075341422858471413588037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74867577127622590436234765 28075341422858471413588037)
          ·
            refine ⟨5264126516785963390047757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28075341422858471413588037 5264126516785963390047757)
            ·
              refine ⟨1974047443794736271267909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5264126516785963390047757 1974047443794736271267909)
              ·
                refine ⟨370133895711513050862733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1974047443794736271267909 370133895711513050862733)
                ·
                  refine ⟨138800210891817394073525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370133895711513050862733 138800210891817394073525)
                  ·
                    rfl

theorem cell21_608203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 3].length) (baseStart_608203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608203 prefixEnd_608203 := by exact prefixLift 608203
  have htrace : WordTrace (prefixWord ++ tailWord_608203) baseStart_608203 baseEnd_608203 := by
    simpa [prefixWord, tailWord_608203, baseEnd_608203] using wordTrace_append hprefix tailTrace_608203
  have hstable : (prefixWord ++ tailWord_608203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608203).length < 2 ^ (prefixWord ++ tailWord_608203).sum := by decide
  have hdescent : baseEnd_608203 < baseStart_608203 := by decide
  rcases family_descends (prefixWord ++ tailWord_608203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608310 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_608310 : Nat := 118140960795 + 608310 * 2 ^ 59
def prefixEnd_608310 : Nat := 4983230072969 + 3 ^ 40 * 608310 * 2
def baseEnd_608310 : Nat := 138824629749608985789973

theorem tailTrace_608310 : CollatzResearch.WordTrace tailWord_608310 prefixEnd_608310 138824629749608985789973 := by
  unfold tailWord_608310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1386680526637764745119899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14791258950802823947945589 1386680526637764745119899)
  ·
    refine ⟨2080020789956647117679849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1386680526637764745119899 2080020789956647117679849)
    ·
      refine ⟨1560015592467485338259887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2080020789956647117679849 1560015592467485338259887)
      ·
        refine ⟨2340023388701228007389831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1560015592467485338259887 2340023388701228007389831)
        ·
          refine ⟨3510035083051842011084747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340023388701228007389831 3510035083051842011084747)
          ·
            refine ⟨5265052624577763016627121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510035083051842011084747 5265052624577763016627121)
            ·
              refine ⟨3948789468433322262470341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5265052624577763016627121 3948789468433322262470341)
              ·
                refine ⟨740398025331247924213189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3948789468433322262470341 740398025331247924213189)
                ·
                  refine ⟨138824629749608985789973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740398025331247924213189 138824629749608985789973)
                  ·
                    rfl

theorem cell21_608310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_608310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608310 prefixEnd_608310 := by exact prefixLift 608310
  have htrace : WordTrace (prefixWord ++ tailWord_608310) baseStart_608310 baseEnd_608310 := by
    simpa [prefixWord, tailWord_608310, baseEnd_608310] using wordTrace_append hprefix tailTrace_608310
  have hstable : (prefixWord ++ tailWord_608310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608310).length < 2 ^ (prefixWord ++ tailWord_608310).sum := by decide
  have hdescent : baseEnd_608310 < baseStart_608310 := by decide
  rcases family_descends (prefixWord ++ tailWord_608310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608313 : List Nat := [1, 2, 1, 5, 3, 1, 3, 2, 3]
def baseStart_608313 : Nat := 118140960795 + 608313 * 2 ^ 59
def prefixEnd_608313 : Nat := 4983230072969 + 3 ^ 40 * 608313 * 2
def baseEnd_608313 : Nat := 138825314390481647239967

theorem tailTrace_608313 : CollatzResearch.WordTrace tailWord_608313 prefixEnd_608313 138825314390481647239967 := by
  unfold tailWord_608313
  simp only [CollatzResearch.WordTrace]
  refine ⟨22186997845193367434277593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14791331896795578289518395 22186997845193367434277593)
  ·
    refine ⟨16640248383895025575708195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22186997845193367434277593 16640248383895025575708195)
    ·
      refine ⟨24960372575842538363562293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16640248383895025575708195 24960372575842538363562293)
      ·
        refine ⟨2340034928985237971583965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24960372575842538363562293 2340034928985237971583965)
        ·
          refine ⟨877513098369464239343987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2340034928985237971583965 877513098369464239343987)
          ·
            refine ⟨1316269647554196359015981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877513098369464239343987 1316269647554196359015981)
            ·
              refine ⟨493601117832823634630993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1316269647554196359015981 493601117832823634630993)
              ·
                refine ⟨370200838374617725973245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493601117832823634630993 370200838374617725973245)
                ·
                  refine ⟨138825314390481647239967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370200838374617725973245 138825314390481647239967)
                  ·
                    rfl

theorem cell21_608313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 3].length) (baseStart_608313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608313 prefixEnd_608313 := by exact prefixLift 608313
  have htrace : WordTrace (prefixWord ++ tailWord_608313) baseStart_608313 baseEnd_608313 := by
    simpa [prefixWord, tailWord_608313, baseEnd_608313] using wordTrace_append hprefix tailTrace_608313
  have hstable : (prefixWord ++ tailWord_608313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608313).length < 2 ^ (prefixWord ++ tailWord_608313).sum := by decide
  have hdescent : baseEnd_608313 < baseStart_608313 := by decide
  rcases family_descends (prefixWord ++ tailWord_608313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608369 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 4]
def baseStart_608369 : Nat := 118140960795 + 608369 * 2 ^ 59
def prefixEnd_608369 : Nat := 4983230072969 + 3 ^ 40 * 608369 * 2
def baseEnd_608369 : Nat := 138838094353437994306519

theorem tailTrace_608369 : CollatzResearch.WordTrace tailWord_608369 prefixEnd_608369 138838094353437994306519 := by
  unfold tailWord_608369
  simp only [CollatzResearch.WordTrace]
  refine ⟨22189040332990488998316161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14792693555326992665544107 22189040332990488998316161)
  ·
    refine ⟨16641780249742866748737121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22189040332990488998316161 16641780249742866748737121)
    ·
      refine ⟨12481335187307150061552841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16641780249742866748737121 12481335187307150061552841)
      ·
        refine ⟨9361001390480362546164631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12481335187307150061552841 9361001390480362546164631)
        ·
          refine ⟨14041502085720543819246947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9361001390480362546164631 14041502085720543819246947)
          ·
            refine ⟨21062253128580815728870421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14041502085720543819246947 21062253128580815728870421)
            ·
              refine ⟨987293115402225737290801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21062253128580815728870421 987293115402225737290801)
              ·
                refine ⟨740469836551669302968101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 987293115402225737290801 740469836551669302968101)
                ·
                  refine ⟨138838094353437994306519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740469836551669302968101 138838094353437994306519)
                  ·
                    rfl

theorem cell21_608369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_608369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608369 prefixEnd_608369 := by exact prefixLift 608369
  have htrace : WordTrace (prefixWord ++ tailWord_608369) baseStart_608369 baseEnd_608369 := by
    simpa [prefixWord, tailWord_608369, baseEnd_608369] using wordTrace_append hprefix tailTrace_608369
  have hstable : (prefixWord ++ tailWord_608369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608369).length < 2 ^ (prefixWord ++ tailWord_608369).sum := by decide
  have hdescent : baseEnd_608369 < baseStart_608369 := by decide
  rcases family_descends (prefixWord ++ tailWord_608369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608473 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 7]
def baseStart_608473 : Nat := 118140960795 + 608473 * 2 ^ 59
def prefixEnd_608473 : Nat := 4983230072969 + 3 ^ 40 * 608473 * 2
def baseEnd_608473 : Nat := 138861828570356924572973

theorem tailTrace_608473 : CollatzResearch.WordTrace tailWord_608473 prefixEnd_608473 138861828570356924572973 := by
  unfold tailWord_608473
  simp only [CollatzResearch.WordTrace]
  refine ⟨22192833524613714760102073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14795222349742476506734715 22192833524613714760102073)
  ·
    refine ⟨16644625143460286070076555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22192833524613714760102073 16644625143460286070076555)
    ·
      refine ⟨24966937715190429105114833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16644625143460286070076555 24966937715190429105114833)
      ·
        refine ⟨18725203286392821828836125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24966937715190429105114833 18725203286392821828836125)
        ·
          refine ⟨7021951232397308185813547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18725203286392821828836125 7021951232397308185813547)
          ·
            refine ⟨10532926848595962278720321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7021951232397308185813547 10532926848595962278720321)
            ·
              refine ⟨7899695136446971709040241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10532926848595962278720321 7899695136446971709040241)
              ·
                refine ⟨5924771352335228781780181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7899695136446971709040241 5924771352335228781780181)
                ·
                  refine ⟨138861828570356924572973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5924771352335228781780181 138861828570356924572973)
                  ·
                    rfl

theorem cell21_608473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_608473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608473 prefixEnd_608473 := by exact prefixLift 608473
  have htrace : WordTrace (prefixWord ++ tailWord_608473) baseStart_608473 baseEnd_608473 := by
    simpa [prefixWord, tailWord_608473, baseEnd_608473] using wordTrace_append hprefix tailTrace_608473
  have hstable : (prefixWord ++ tailWord_608473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608473).length < 2 ^ (prefixWord ++ tailWord_608473).sum := by decide
  have hdescent : baseEnd_608473 < baseStart_608473 := by decide
  rcases family_descends (prefixWord ++ tailWord_608473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608482 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 5]
def baseStart_608482 : Nat := 118140960795 + 608482 * 2 ^ 59
def prefixEnd_608482 : Nat := 4983230072969 + 3 ^ 40 * 608482 * 2
def baseEnd_608482 : Nat := 138863882492974908922955

theorem tailTrace_608482 : CollatzResearch.WordTrace tailWord_608482 prefixEnd_608482 138863882492974908922955 := by
  unfold tailWord_608482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548290445395277324294925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14795441187720739531453133 5548290445395277324294925)
  ·
    refine ⟨2080608917023228996610597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5548290445395277324294925 2080608917023228996610597)
    ·
      refine ⟨390114171941855436864487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2080608917023228996610597 390114171941855436864487)
      ·
        refine ⟨585171257912783155296731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390114171941855436864487 585171257912783155296731)
        ·
          refine ⟨877756886869174732945097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585171257912783155296731 877756886869174732945097)
          ·
            refine ⟨658317665151881049708823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 877756886869174732945097 658317665151881049708823)
            ·
              refine ⟨987476497727821574563235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658317665151881049708823 987476497727821574563235)
              ·
                refine ⟨1481214746591732361844853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987476497727821574563235 1481214746591732361844853)
                ·
                  refine ⟨138863882492974908922955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1481214746591732361844853 138863882492974908922955)
                  ·
                    rfl

theorem cell21_608482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_608482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608482 prefixEnd_608482 := by exact prefixLift 608482
  have htrace : WordTrace (prefixWord ++ tailWord_608482) baseStart_608482 baseEnd_608482 := by
    simpa [prefixWord, tailWord_608482, baseEnd_608482] using wordTrace_append hprefix tailTrace_608482
  have hstable : (prefixWord ++ tailWord_608482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608482).length < 2 ^ (prefixWord ++ tailWord_608482).sum := by decide
  have hdescent : baseEnd_608482 < baseStart_608482 := by decide
  rcases family_descends (prefixWord ++ tailWord_608482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608538 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_608538 : Nat := 118140960795 + 608538 * 2 ^ 59
def prefixEnd_608538 : Nat := 4983230072969 + 3 ^ 40 * 608538 * 2
def baseEnd_608538 : Nat := 138876662455931255989507

theorem tailTrace_608538 : CollatzResearch.WordTrace tailWord_608538 prefixEnd_608538 138876662455931255989507 := by
  unfold tailWord_608538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548801067344557715304567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14796802846252153907478845 5548801067344557715304567)
  ·
    refine ⟨8323201601016836572956851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5548801067344557715304567 8323201601016836572956851)
    ·
      refine ⟨12484802401525254859435277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8323201601016836572956851 12484802401525254859435277)
      ·
        refine ⟨4681800900571970572288229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12484802401525254859435277 4681800900571970572288229)
        ·
          refine ⟨877837668857244482304043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4681800900571970572288229 877837668857244482304043)
          ·
            refine ⟨1316756503285866723456065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877837668857244482304043 1316756503285866723456065)
            ·
              refine ⟨987567377464400042592049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1316756503285866723456065 987567377464400042592049)
              ·
                refine ⟨740675533098300031944037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 987567377464400042592049 740675533098300031944037)
                ·
                  refine ⟨138876662455931255989507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740675533098300031944037 138876662455931255989507)
                  ·
                    rfl

theorem cell21_608538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_608538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608538 prefixEnd_608538 := by exact prefixLift 608538
  have htrace : WordTrace (prefixWord ++ tailWord_608538) baseStart_608538 baseEnd_608538 := by
    simpa [prefixWord, tailWord_608538, baseEnd_608538] using wordTrace_append hprefix tailTrace_608538
  have hstable : (prefixWord ++ tailWord_608538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608538).length < 2 ^ (prefixWord ++ tailWord_608538).sum := by decide
  have hdescent : baseEnd_608538 < baseStart_608538 := by decide
  rcases family_descends (prefixWord ++ tailWord_608538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608583 : List Nat := [1, 1, 4, 1, 2, 2, 4, 3, 3]
def baseStart_608583 : Nat := 118140960795 + 608583 * 2 ^ 59
def prefixEnd_608583 : Nat := 4983230072969 + 3 ^ 40 * 608583 * 2
def baseEnd_608583 : Nat := 138886932069021177739415

theorem tailTrace_608583 : CollatzResearch.WordTrace tailWord_608583 prefixEnd_608583 138886932069021177739415 := by
  unfold tailWord_608583
  simp only [CollatzResearch.WordTrace]
  refine ⟨22196845554215203546606403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14797897036143469031070935 22196845554215203546606403)
  ·
    refine ⟨33295268331322805319909605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22196845554215203546606403 33295268331322805319909605)
    ·
      refine ⟨6242862812123025997483051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33295268331322805319909605 6242862812123025997483051)
      ·
        refine ⟨9364294218184538996224577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6242862812123025997483051 9364294218184538996224577)
        ·
          refine ⟨7023220663638404247168433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9364294218184538996224577 7023220663638404247168433)
          ·
            refine ⟨5267415497728803185376325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7023220663638404247168433 5267415497728803185376325)
            ·
              refine ⟨987640405824150597258061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5267415497728803185376325 987640405824150597258061)
              ·
                refine ⟨370365152184056473971773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 987640405824150597258061 370365152184056473971773)
                ·
                  refine ⟨138886932069021177739415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370365152184056473971773 138886932069021177739415)
                  ·
                    rfl

theorem cell21_608583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 3].length) (baseStart_608583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608583 prefixEnd_608583 := by exact prefixLift 608583
  have htrace : WordTrace (prefixWord ++ tailWord_608583) baseStart_608583 baseEnd_608583 := by
    simpa [prefixWord, tailWord_608583, baseEnd_608583] using wordTrace_append hprefix tailTrace_608583
  have hstable : (prefixWord ++ tailWord_608583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608583).length < 2 ^ (prefixWord ++ tailWord_608583).sum := by decide
  have hdescent : baseEnd_608583 < baseStart_608583 := by decide
  rcases family_descends (prefixWord ++ tailWord_608583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608597 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 6]
def baseStart_608597 : Nat := 118140960795 + 608597 * 2 ^ 59
def prefixEnd_608597 : Nat := 4983230072969 + 3 ^ 40 * 608597 * 2
def baseEnd_608597 : Nat := 138890127059760264506053

theorem tailTrace_608597 : CollatzResearch.WordTrace tailWord_608597 prefixEnd_608597 138890127059760264506053 := by
  unfold tailWord_608597
  simp only [CollatzResearch.WordTrace]
  refine ⟨22197356176164483937616045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14798237450776322625077363 22197356176164483937616045)
  ·
    refine ⟨8324008566061681476606017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22197356176164483937616045 8324008566061681476606017)
    ·
      refine ⟨6243006424546261107454513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8324008566061681476606017 6243006424546261107454513)
      ·
        refine ⟨4682254818409695830590885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6243006424546261107454513 4682254818409695830590885)
        ·
          refine ⟨877922778451817968235791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4682254818409695830590885 877922778451817968235791)
          ·
            refine ⟨1316884167677726952353687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877922778451817968235791 1316884167677726952353687)
            ·
              refine ⟨1975326251516590428530531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316884167677726952353687 1975326251516590428530531)
              ·
                refine ⟨2962989377274885642795797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975326251516590428530531 2962989377274885642795797)
                ·
                  refine ⟨138890127059760264506053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2962989377274885642795797 138890127059760264506053)
                  ·
                    rfl

theorem cell21_608597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_608597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608597 prefixEnd_608597 := by exact prefixLift 608597
  have htrace : WordTrace (prefixWord ++ tailWord_608597) baseStart_608597 baseEnd_608597 := by
    simpa [prefixWord, tailWord_608597, baseEnd_608597] using wordTrace_append hprefix tailTrace_608597
  have hstable : (prefixWord ++ tailWord_608597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608597).length < 2 ^ (prefixWord ++ tailWord_608597).sum := by decide
  have hdescent : baseEnd_608597 < baseStart_608597 := by decide
  rcases family_descends (prefixWord ++ tailWord_608597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608606 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_608606 : Nat := 118140960795 + 608606 * 2 ^ 59
def prefixEnd_608606 : Nat := 4983230072969 + 3 ^ 40 * 608606 * 2
def baseEnd_608606 : Nat := 138892180982378248856035

theorem tailTrace_608606 : CollatzResearch.WordTrace tailWord_608606 prefixEnd_608606 138892180982378248856035 := by
  unfold tailWord_608606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774710554141484809336709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14798456288754585649795781 2774710554141484809336709)
  ·
    refine ⟨520258228901528401750633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2774710554141484809336709 520258228901528401750633)
    ·
      refine ⟨390193671676146301312975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 520258228901528401750633 390193671676146301312975)
      ·
        refine ⟨585290507514219451969463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390193671676146301312975 585290507514219451969463)
        ·
          refine ⟨877935761271329177954195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585290507514219451969463 877935761271329177954195)
          ·
            refine ⟨1316903641906993766931293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877935761271329177954195 1316903641906993766931293)
            ·
              refine ⟨493838865715122662599235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1316903641906993766931293 493838865715122662599235)
              ·
                refine ⟨740758298572683993898853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493838865715122662599235 740758298572683993898853)
                ·
                  refine ⟨138892180982378248856035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740758298572683993898853 138892180982378248856035)
                  ·
                    rfl

theorem cell21_608606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_608606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608606 prefixEnd_608606 := by exact prefixLift 608606
  have htrace : WordTrace (prefixWord ++ tailWord_608606) baseStart_608606 baseEnd_608606 := by
    simpa [prefixWord, tailWord_608606, baseEnd_608606] using wordTrace_append hprefix tailTrace_608606
  have hstable : (prefixWord ++ tailWord_608606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608606).length < 2 ^ (prefixWord ++ tailWord_608606).sum := by decide
  have hdescent : baseEnd_608606 < baseStart_608606 := by decide
  rcases family_descends (prefixWord ++ tailWord_608606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608738 : List Nat := [3, 3, 3, 2, 1, 1, 3, 5]
def baseStart_608738 : Nat := 118140960795 + 608738 * 2 ^ 59
def prefixEnd_608738 : Nat := 4983230072969 + 3 ^ 40 * 608738 * 2
def baseEnd_608738 : Nat := 46307435060258450885255

theorem tailTrace_608738 : CollatzResearch.WordTrace tailWord_608738 prefixEnd_608738 46307435060258450885255 := by
  unfold tailWord_608738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5550624717163416254624717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14801665912435776678999245 5550624717163416254624717)
  ·
    refine ⟨2081484268936281095484269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5550624717163416254624717 2081484268936281095484269)
    ·
      refine ⟨780556600851105410806601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2081484268936281095484269 780556600851105410806601)
      ·
        refine ⟨585417450638329058104951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 780556600851105410806601 585417450638329058104951)
        ·
          refine ⟨878126175957493587157427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585417450638329058104951 878126175957493587157427)
          ·
            refine ⟨1317189263936240380736141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878126175957493587157427 1317189263936240380736141)
            ·
              refine ⟨493945973976090142776053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1317189263936240380736141 493945973976090142776053)
              ·
                refine ⟨46307435060258450885255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 493945973976090142776053 46307435060258450885255)
                ·
                  rfl

theorem cell21_608738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_608738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608738 prefixEnd_608738 := by exact prefixLift 608738
  have htrace : WordTrace (prefixWord ++ tailWord_608738) baseStart_608738 baseEnd_608738 := by
    simpa [prefixWord, tailWord_608738, baseEnd_608738] using wordTrace_append hprefix tailTrace_608738
  have hstable : (prefixWord ++ tailWord_608738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608738).length < 2 ^ (prefixWord ++ tailWord_608738).sum := by decide
  have hdescent : baseEnd_608738 < baseStart_608738 := by decide
  rcases family_descends (prefixWord ++ tailWord_608738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608828 : List Nat := [2, 2, 2, 2, 3, 2, 3, 2, 3]
def baseStart_608828 : Nat := 118140960795 + 608828 * 2 ^ 59
def prefixEnd_608828 : Nat := 4983230072969 + 3 ^ 40 * 608828 * 2
def baseEnd_608828 : Nat := 138942844406955196155581

theorem tailTrace_608828 : CollatzResearch.WordTrace tailWord_608828 prefixEnd_608828 138942844406955196155581 := by
  unfold tailWord_608828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11102890719163805194637569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14803854292218406926183425 11102890719163805194637569)
  ·
    refine ⟨8327168039372853895978177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11102890719163805194637569 8327168039372853895978177)
    ·
      refine ⟨6245376029529640421983633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8327168039372853895978177 6245376029529640421983633)
      ·
        refine ⟨4684032022147230316487725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6245376029529640421983633 4684032022147230316487725)
        ·
          refine ⟨1756512008305211368682897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4684032022147230316487725 1756512008305211368682897)
          ·
            refine ⟨1317384006228908526512173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756512008305211368682897 1317384006228908526512173)
            ·
              refine ⟨494019002335840697442065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1317384006228908526512173 494019002335840697442065)
              ·
                refine ⟨370514251751880523081549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494019002335840697442065 370514251751880523081549)
                ·
                  refine ⟨138942844406955196155581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370514251751880523081549 138942844406955196155581)
                  ·
                    rfl

theorem cell21_608828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_608828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608828 prefixEnd_608828 := by exact prefixLift 608828
  have htrace : WordTrace (prefixWord ++ tailWord_608828) baseStart_608828 baseEnd_608828 := by
    simpa [prefixWord, tailWord_608828, baseEnd_608828] using wordTrace_append hprefix tailTrace_608828
  have hstable : (prefixWord ++ tailWord_608828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608828).length < 2 ^ (prefixWord ++ tailWord_608828).sum := by decide
  have hdescent : baseEnd_608828 < baseStart_608828 := by decide
  rcases family_descends (prefixWord ++ tailWord_608828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608839 : List Nat := [1, 1, 4, 1, 4, 2, 2, 6]
def baseStart_608839 : Nat := 118140960795 + 608839 * 2 ^ 59
def prefixEnd_608839 : Nat := 4983230072969 + 3 ^ 40 * 608839 * 2
def baseEnd_608839 : Nat := 46315118252273873824075

theorem tailTrace_608839 : CollatzResearch.WordTrace tailWord_608839 prefixEnd_608839 46315118252273873824075 := by
  unfold tailWord_608839
  simp only [CollatzResearch.WordTrace]
  refine ⟨22206182641287759267925571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14804121760858506178617047 22206182641287759267925571)
  ·
    refine ⟨33309273961931638901888357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22206182641287759267925571 33309273961931638901888357)
    ·
      refine ⟨6245488867862182294104067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33309273961931638901888357 6245488867862182294104067)
      ·
        refine ⟨9368233301793273441156101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6245488867862182294104067 9368233301793273441156101)
        ·
          refine ⟨1756543744086238770216769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9368233301793273441156101 1756543744086238770216769)
          ·
            refine ⟨1317407808064679077662577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756543744086238770216769 1317407808064679077662577)
            ·
              refine ⟨988055856048509308246933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317407808064679077662577 988055856048509308246933)
              ·
                refine ⟨46315118252273873824075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 988055856048509308246933 46315118252273873824075)
                ·
                  rfl

theorem cell21_608839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 6].length) (baseStart_608839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608839 prefixEnd_608839 := by exact prefixLift 608839
  have htrace : WordTrace (prefixWord ++ tailWord_608839) baseStart_608839 baseEnd_608839 := by
    simpa [prefixWord, tailWord_608839, baseEnd_608839] using wordTrace_append hprefix tailTrace_608839
  have hstable : (prefixWord ++ tailWord_608839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608839).length < 2 ^ (prefixWord ++ tailWord_608839).sum := by decide
  have hdescent : baseEnd_608839 < baseStart_608839 := by decide
  rcases family_descends (prefixWord ++ tailWord_608839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608842 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_608842 : Nat := 118140960795 + 608842 * 2 ^ 59
def prefixEnd_608842 : Nat := 4983230072969 + 3 ^ 40 * 608842 * 2
def baseEnd_608842 : Nat := 138946039397694282922219

theorem tailTrace_608842 : CollatzResearch.WordTrace tailWord_608842 prefixEnd_608842 138946039397694282922219 := by
  unfold tailWord_608842
  simp only [CollatzResearch.WordTrace]
  refine ⟨5551573015069222695071195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14804194706851260520189853 5551573015069222695071195)
  ·
    refine ⟨8327359522603834042606793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5551573015069222695071195 8327359522603834042606793)
    ·
      refine ⟨6245519641952875531955095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8327359522603834042606793 6245519641952875531955095)
      ·
        refine ⟨9368279462929313297932643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6245519641952875531955095 9368279462929313297932643)
        ·
          refine ⟨14052419194393969946898965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9368279462929313297932643 14052419194393969946898965)
          ·
            refine ⟨658707149737217341260889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14052419194393969946898965 658707149737217341260889)
            ·
              refine ⟨494030362302913005945667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658707149737217341260889 494030362302913005945667)
              ·
                refine ⟨741045543454369508918501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494030362302913005945667 741045543454369508918501)
                ·
                  refine ⟨138946039397694282922219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 741045543454369508918501 138946039397694282922219)
                  ·
                    rfl

theorem cell21_608842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_608842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608842 prefixEnd_608842 := by exact prefixLift 608842
  have htrace : WordTrace (prefixWord ++ tailWord_608842) baseStart_608842 baseEnd_608842 := by
    simpa [prefixWord, tailWord_608842, baseEnd_608842] using wordTrace_append hprefix tailTrace_608842
  have hstable : (prefixWord ++ tailWord_608842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608842).length < 2 ^ (prefixWord ++ tailWord_608842).sum := by decide
  have hdescent : baseEnd_608842 < baseStart_608842 := by decide
  rcases family_descends (prefixWord ++ tailWord_608842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608853 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 5]
def baseStart_608853 : Nat := 118140960795 + 608853 * 2 ^ 59
def prefixEnd_608853 : Nat := 4983230072969 + 3 ^ 40 * 608853 * 2
def baseEnd_608853 : Nat := 138948549747560708238863

theorem tailTrace_608853 : CollatzResearch.WordTrace tailWord_608853 prefixEnd_608853 138948549747560708238863 := by
  unfold tailWord_608853
  simp only [CollatzResearch.WordTrace]
  refine ⟨22206693263237039658935213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14804462175491359772623475 22206693263237039658935213)
  ·
    refine ⟨8327509973713889872100705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22206693263237039658935213 8327509973713889872100705)
    ·
      refine ⟨6245632480285417404075529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8327509973713889872100705 6245632480285417404075529)
      ·
        refine ⟨4684224360214063053056647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6245632480285417404075529 4684224360214063053056647)
        ·
          refine ⟨7026336540321094579584971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4684224360214063053056647 7026336540321094579584971)
          ·
            refine ⟨10539504810481641869377457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7026336540321094579584971 10539504810481641869377457)
            ·
              refine ⟨7904628607861231402033093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10539504810481641869377457 7904628607861231402033093)
              ·
                refine ⟨1482117863973980887881205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7904628607861231402033093 1482117863973980887881205)
                ·
                  refine ⟨138948549747560708238863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1482117863973980887881205 138948549747560708238863)
                  ·
                    rfl

theorem cell21_608853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_608853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608853 prefixEnd_608853 := by exact prefixLift 608853
  have htrace : WordTrace (prefixWord ++ tailWord_608853) baseStart_608853 baseEnd_608853 := by
    simpa [prefixWord, tailWord_608853, baseEnd_608853] using wordTrace_append hprefix tailTrace_608853
  have hstable : (prefixWord ++ tailWord_608853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608853).length < 2 ^ (prefixWord ++ tailWord_608853).sum := by decide
  have hdescent : baseEnd_608853 < baseStart_608853 := by decide
  rcases family_descends (prefixWord ++ tailWord_608853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608887 : List Nat := [1, 1, 3, 1, 1, 3, 6, 2, 3]
def baseStart_608887 : Nat := 118140960795 + 608887 * 2 ^ 59
def prefixEnd_608887 : Nat := 4983230072969 + 3 ^ 40 * 608887 * 2
def baseEnd_608887 : Nat := 138956309010784204672127

theorem tailTrace_608887 : CollatzResearch.WordTrace tailWord_608887 prefixEnd_608887 138956309010784204672127 := by
  unfold tailWord_608887
  simp only [CollatzResearch.WordTrace]
  refine ⟨22207933345113863465672915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14805288896742575643781943 22207933345113863465672915)
  ·
    refine ⟨33311900017670795198509373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22207933345113863465672915 33311900017670795198509373)
    ·
      refine ⟨12491962506626548199441015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33311900017670795198509373 12491962506626548199441015)
      ·
        refine ⟨18737943759939822299161523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12491962506626548199441015 18737943759939822299161523)
        ·
          refine ⟨28106915639909733448742285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18737943759939822299161523 28106915639909733448742285)
          ·
            refine ⟨10540093364966150043278357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28106915639909733448742285 10540093364966150043278357)
            ·
              refine ⟨494066876482788283278673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10540093364966150043278357 494066876482788283278673)
              ·
                refine ⟨370550157362091212459005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494066876482788283278673 370550157362091212459005)
                ·
                  refine ⟨138956309010784204672127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370550157362091212459005 138956309010784204672127)
                  ·
                    rfl

theorem cell21_608887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 3].length) (baseStart_608887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608887 prefixEnd_608887 := by exact prefixLift 608887
  have htrace : WordTrace (prefixWord ++ tailWord_608887) baseStart_608887 baseEnd_608887 := by
    simpa [prefixWord, tailWord_608887, baseEnd_608887] using wordTrace_append hprefix tailTrace_608887
  have hstable : (prefixWord ++ tailWord_608887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608887).length < 2 ^ (prefixWord ++ tailWord_608887).sum := by decide
  have hdescent : baseEnd_608887 < baseStart_608887 := by decide
  rcases family_descends (prefixWord ++ tailWord_608887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608935 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 4]
def baseStart_608935 : Nat := 118140960795 + 608935 * 2 ^ 59
def prefixEnd_608935 : Nat := 4983230072969 + 3 ^ 40 * 608935 * 2
def baseEnd_608935 : Nat := 138967263264746787872029

theorem tailTrace_608935 : CollatzResearch.WordTrace tailWord_608935 prefixEnd_608935 138967263264746787872029 := by
  unfold tailWord_608935
  simp only [CollatzResearch.WordTrace]
  refine ⟨22209684048939967663420259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14806456032626645108946839 22209684048939967663420259)
  ·
    refine ⟨33314526073409951495130389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22209684048939967663420259 33314526073409951495130389)
    ·
      refine ⟨1561618409691091476334237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33314526073409951495130389 1561618409691091476334237)
      ·
        refine ⟨585606903634159303625339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1561618409691091476334237 585606903634159303625339)
        ·
          refine ⟨878410355451238955438009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585606903634159303625339 878410355451238955438009)
          ·
            refine ⟨658807766588429216578507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878410355451238955438009 658807766588429216578507)
            ·
              refine ⟨988211649882643824867761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658807766588429216578507 988211649882643824867761)
              ·
                refine ⟨741158737411982868650821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988211649882643824867761 741158737411982868650821)
                ·
                  refine ⟨138967263264746787872029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 741158737411982868650821 138967263264746787872029)
                  ·
                    rfl

theorem cell21_608935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 4].length) (baseStart_608935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_608935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_608935 prefixEnd_608935 := by exact prefixLift 608935
  have htrace : WordTrace (prefixWord ++ tailWord_608935) baseStart_608935 baseEnd_608935 := by
    simpa [prefixWord, tailWord_608935, baseEnd_608935] using wordTrace_append hprefix tailTrace_608935
  have hstable : (prefixWord ++ tailWord_608935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608935).length < 2 ^ (prefixWord ++ tailWord_608935).sum := by decide
  have hdescent : baseEnd_608935 < baseStart_608935 := by decide
  rcases family_descends (prefixWord ++ tailWord_608935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609056 : List Nat := [2, 1, 1, 5, 1, 4, 2, 2, 3]
def baseStart_609056 : Nat := 118140960795 + 609056 * 2 ^ 59
def prefixEnd_609056 : Nat := 4983230072969 + 3 ^ 40 * 609056 * 2
def baseEnd_609056 : Nat := 138994877113277466355115

theorem tailTrace_609056 : CollatzResearch.WordTrace tailWord_609056 prefixEnd_609056 138994877113277466355115 := by
  unfold tailWord_609056
  simp only [CollatzResearch.WordTrace]
  refine ⟨11107048640750802664287511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14809398187667736885716681 11107048640750802664287511)
  ·
    refine ⟨16660572961126203996431267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11107048640750802664287511 16660572961126203996431267)
    ·
      refine ⟨24990859441689305994646901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16660572961126203996431267 24990859441689305994646901)
      ·
        refine ⟨2342893072658372436998147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24990859441689305994646901 2342893072658372436998147)
        ·
          refine ⟨3514339608987558655497221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2342893072658372436998147 3514339608987558655497221)
          ·
            refine ⟨658938676685167247905729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3514339608987558655497221 658938676685167247905729)
            ·
              refine ⟨494204007513875435929297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658938676685167247905729 494204007513875435929297)
              ·
                refine ⟨370653005635406576946973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494204007513875435929297 370653005635406576946973)
                ·
                  refine ⟨138994877113277466355115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370653005635406576946973 138994877113277466355115)
                  ·
                    rfl

theorem cell21_609056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 3].length) (baseStart_609056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609056 prefixEnd_609056 := by exact prefixLift 609056
  have htrace : WordTrace (prefixWord ++ tailWord_609056) baseStart_609056 baseEnd_609056 := by
    simpa [prefixWord, tailWord_609056, baseEnd_609056] using wordTrace_append hprefix tailTrace_609056
  have hstable : (prefixWord ++ tailWord_609056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609056).length < 2 ^ (prefixWord ++ tailWord_609056).sum := by decide
  have hdescent : baseEnd_609056 < baseStart_609056 := by decide
  rcases family_descends (prefixWord ++ tailWord_609056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609095 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 6]
def baseStart_609095 : Nat := 118140960795 + 609095 * 2 ^ 59
def prefixEnd_609095 : Nat := 4983230072969 + 3 ^ 40 * 609095 * 2
def baseEnd_609095 : Nat := 139003777444622065205035

theorem tailTrace_609095 : CollatzResearch.WordTrace tailWord_609095 prefixEnd_609095 139003777444622065205035 := by
  unfold tailWord_609095
  simp only [CollatzResearch.WordTrace]
  refine ⟨22215519728360314989244739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14810346485573543326163159 22215519728360314989244739)
  ·
    refine ⟨33323279592540472483867109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22215519728360314989244739 33323279592540472483867109)
    ·
      refine ⟨6248114923601338590725083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33323279592540472483867109 6248114923601338590725083)
      ·
        refine ⟨9372172385402007886087625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6248114923601338590725083 9372172385402007886087625)
        ·
          refine ⟨7029129289051505914565719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9372172385402007886087625 7029129289051505914565719)
          ·
            refine ⟨10543693933577258871848579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7029129289051505914565719 10543693933577258871848579)
            ·
              refine ⟨15815540900365888307772869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10543693933577258871848579 15815540900365888307772869)
              ·
                refine ⟨2965413918818604057707413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15815540900365888307772869 2965413918818604057707413)
                ·
                  refine ⟨139003777444622065205035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2965413918818604057707413 139003777444622065205035)
                  ·
                    rfl

theorem cell21_609095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_609095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609095 prefixEnd_609095 := by exact prefixLift 609095
  have htrace : WordTrace (prefixWord ++ tailWord_609095) baseStart_609095 baseEnd_609095 := by
    simpa [prefixWord, tailWord_609095, baseEnd_609095] using wordTrace_append hprefix tailTrace_609095
  have hstable : (prefixWord ++ tailWord_609095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609095).length < 2 ^ (prefixWord ++ tailWord_609095).sum := by decide
  have hdescent : baseEnd_609095 < baseStart_609095 := by decide
  rcases family_descends (prefixWord ++ tailWord_609095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609188 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 4]
def baseStart_609188 : Nat := 118140960795 + 609188 * 2 ^ 59
def prefixEnd_609188 : Nat := 4983230072969 + 3 ^ 40 * 609188 * 2
def baseEnd_609188 : Nat := 139025001311674570154845

theorem tailTrace_609188 : CollatzResearch.WordTrace tailWord_609188 prefixEnd_609188 139025001311674570154845 := by
  unfold tailWord_609188
  simp only [CollatzResearch.WordTrace]
  refine ⟨11109455858511695936190109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14812607811348927914920145 11109455858511695936190109)
  ·
    refine ⟨4166045946941885976071291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11109455858511695936190109 4166045946941885976071291)
    ·
      refine ⟨6249068920412828964106937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4166045946941885976071291 6249068920412828964106937)
      ·
        refine ⟨4686801690309621723080203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6249068920412828964106937 4686801690309621723080203)
        ·
          refine ⟨7030202535464432584620305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4686801690309621723080203 7030202535464432584620305)
          ·
            refine ⟨5272651901598324438465229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7030202535464432584620305 5272651901598324438465229)
            ·
              refine ⟨1977244463099371664424461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5272651901598324438465229 1977244463099371664424461)
              ·
                refine ⟨741466673662264374159173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1977244463099371664424461 741466673662264374159173)
                ·
                  refine ⟨139025001311674570154845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 741466673662264374159173 139025001311674570154845)
                  ·
                    rfl

theorem cell21_609188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_609188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609188 prefixEnd_609188 := by exact prefixLift 609188
  have htrace : WordTrace (prefixWord ++ tailWord_609188) baseStart_609188 baseEnd_609188 := by
    simpa [prefixWord, tailWord_609188, baseEnd_609188] using wordTrace_append hprefix tailTrace_609188
  have hstable : (prefixWord ++ tailWord_609188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609188).length < 2 ^ (prefixWord ++ tailWord_609188).sum := by decide
  have hdescent : baseEnd_609188 < baseStart_609188 := by decide
  rcases family_descends (prefixWord ++ tailWord_609188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609250 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_609250 : Nat := 118140960795 + 609250 * 2 ^ 59
def prefixEnd_609250 : Nat := 4983230072969 + 3 ^ 40 * 609250 * 2
def baseEnd_609250 : Nat := 139039150556376240121385

theorem tailTrace_609250 : CollatzResearch.WordTrace tailWord_609250 prefixEnd_609250 139039150556376240121385 := by
  unfold tailWord_609250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5555293260699694115284301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14814115361865850974091469 5555293260699694115284301)
  ·
    refine ⟨2083234972762385293231613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5555293260699694115284301 2083234972762385293231613)
    ·
      refine ⟨781213114785894484961855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2083234972762385293231613 781213114785894484961855)
      ·
        refine ⟨1171819672178841727442783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 781213114785894484961855 1171819672178841727442783)
        ·
          refine ⟨1757729508268262591164175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171819672178841727442783 1757729508268262591164175)
          ·
            refine ⟨2636594262402393886746263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757729508268262591164175 2636594262402393886746263)
            ·
              refine ⟨3954891393603590830119395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2636594262402393886746263 3954891393603590830119395)
              ·
                refine ⟨5932337090405386245179093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954891393603590830119395 5932337090405386245179093)
                ·
                  refine ⟨139039150556376240121385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5932337090405386245179093 139039150556376240121385)
                  ·
                    rfl

theorem cell21_609250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_609250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609250 prefixEnd_609250 := by exact prefixLift 609250
  have htrace : WordTrace (prefixWord ++ tailWord_609250) baseStart_609250 baseEnd_609250 := by
    simpa [prefixWord, tailWord_609250, baseEnd_609250] using wordTrace_append hprefix tailTrace_609250
  have hstable : (prefixWord ++ tailWord_609250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609250).length < 2 ^ (prefixWord ++ tailWord_609250).sum := by decide
  have hdescent : baseEnd_609250 < baseStart_609250 := by decide
  rcases family_descends (prefixWord ++ tailWord_609250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609281 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 4]
def baseStart_609281 : Nat := 118140960795 + 609281 * 2 ^ 59
def prefixEnd_609281 : Nat := 4983230072969 + 3 ^ 40 * 609281 * 2
def baseEnd_609281 : Nat := 139046225178727075104655

theorem tailTrace_609281 : CollatzResearch.WordTrace tailWord_609281 prefixEnd_609281 139046225178727075104655 := by
  unfold tailWord_609281
  simp only [CollatzResearch.WordTrace]
  refine ⟨22222303705686468755515697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14814869137124312503677131 22222303705686468755515697)
  ·
    refine ⟨16666727779264851566636773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22222303705686468755515697 16666727779264851566636773)
    ·
      refine ⟨3125011458612159668744395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16666727779264851566636773 3125011458612159668744395)
      ·
        refine ⟨4687517187918239503116593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125011458612159668744395 4687517187918239503116593)
        ·
          refine ⟨3515637890938679627337445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4687517187918239503116593 3515637890938679627337445)
          ·
            refine ⟨659182104551002430125771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3515637890938679627337445 659182104551002430125771)
            ·
              refine ⟨988773156826503645188657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659182104551002430125771 988773156826503645188657)
              ·
                refine ⟨741579867619877733891493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988773156826503645188657 741579867619877733891493)
                ·
                  refine ⟨139046225178727075104655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 741579867619877733891493 139046225178727075104655)
                  ·
                    rfl

theorem cell21_609281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_609281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609281 prefixEnd_609281 := by exact prefixLift 609281
  have htrace : WordTrace (prefixWord ++ tailWord_609281) baseStart_609281 baseEnd_609281 := by
    simpa [prefixWord, tailWord_609281, baseEnd_609281] using wordTrace_append hprefix tailTrace_609281
  have hstable : (prefixWord ++ tailWord_609281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609281).length < 2 ^ (prefixWord ++ tailWord_609281).sum := by decide
  have hdescent : baseEnd_609281 < baseStart_609281 := by decide
  rcases family_descends (prefixWord ++ tailWord_609281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609357 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 4]
def baseStart_609357 : Nat := 118140960795 + 609357 * 2 ^ 59
def prefixEnd_609357 : Nat := 4983230072969 + 3 ^ 40 * 609357 * 2
def baseEnd_609357 : Nat := 139063569414167831837833

theorem tailTrace_609357 : CollatzResearch.WordTrace tailWord_609357 prefixEnd_609357 139063569414167831837833 := by
  unfold tailWord_609357
  simp only [CollatzResearch.WordTrace]
  refine ⟨22225075653411133735282325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14816717102274089156854883 22225075653411133735282325)
  ·
    refine ⟨1041800421253646893841359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22225075653411133735282325 1041800421253646893841359)
    ·
      refine ⟨1562700631880470340762039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1041800421253646893841359 1562700631880470340762039)
      ·
        refine ⟨2344050947820705511143059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562700631880470340762039 2344050947820705511143059)
        ·
          refine ⟨3516076421731058266714589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2344050947820705511143059 3516076421731058266714589)
          ·
            refine ⟨1318528658149146850017971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3516076421731058266714589 1318528658149146850017971)
            ·
              refine ⟨1977792987223720275026957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318528658149146850017971 1977792987223720275026957)
              ·
                refine ⟨741672370208895103135109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1977792987223720275026957 741672370208895103135109)
                ·
                  refine ⟨139063569414167831837833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 741672370208895103135109 139063569414167831837833)
                  ·
                    rfl

theorem cell21_609357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_609357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609357 prefixEnd_609357 := by exact prefixLift 609357
  have htrace : WordTrace (prefixWord ++ tailWord_609357) baseStart_609357 baseEnd_609357 := by
    simpa [prefixWord, tailWord_609357, baseEnd_609357] using wordTrace_append hprefix tailTrace_609357
  have hstable : (prefixWord ++ tailWord_609357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609357).length < 2 ^ (prefixWord ++ tailWord_609357).sum := by decide
  have hdescent : baseEnd_609357 < baseStart_609357 := by decide
  rcases family_descends (prefixWord ++ tailWord_609357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609368 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_609368 : Nat := 118140960795 + 609368 * 2 ^ 59
def prefixEnd_609368 : Nat := 4983230072969 + 3 ^ 40 * 609368 * 2
def baseEnd_609368 : Nat := 139066079764034257154477

theorem tailTrace_609368 : CollatzResearch.WordTrace tailWord_609368 prefixEnd_609368 139066079764034257154477 := by
  unfold tailWord_609368
  simp only [CollatzResearch.WordTrace]
  refine ⟨11112738428185641306966379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14816984570914188409288505 11112738428185641306966379)
  ·
    refine ⟨16669107642278461960449569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11112738428185641306966379 16669107642278461960449569)
    ·
      refine ⟨12501830731708846470337177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16669107642278461960449569 12501830731708846470337177)
      ·
        refine ⟨9376373048781634852752883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12501830731708846470337177 9376373048781634852752883)
        ·
          refine ⟨14064559573172452279129325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9376373048781634852752883 14064559573172452279129325)
          ·
            refine ⟨5274209839939669604673497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14064559573172452279129325 5274209839939669604673497)
            ·
              refine ⟨3955657379954752203505123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5274209839939669604673497 3955657379954752203505123)
              ·
                refine ⟨5933486069932128305257685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3955657379954752203505123 5933486069932128305257685)
                ·
                  refine ⟨139066079764034257154477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5933486069932128305257685 139066079764034257154477)
                  ·
                    rfl

theorem cell21_609368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_609368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609368 prefixEnd_609368 := by exact prefixLift 609368
  have htrace : WordTrace (prefixWord ++ tailWord_609368) baseStart_609368 baseEnd_609368 := by
    simpa [prefixWord, tailWord_609368, baseEnd_609368] using wordTrace_append hprefix tailTrace_609368
  have hstable : (prefixWord ++ tailWord_609368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609368).length < 2 ^ (prefixWord ++ tailWord_609368).sum := by decide
  have hdescent : baseEnd_609368 < baseStart_609368 := by decide
  rcases family_descends (prefixWord ++ tailWord_609368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609450 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_609450 : Nat := 118140960795 + 609450 * 2 ^ 59
def prefixEnd_609450 : Nat := 4983230072969 + 3 ^ 40 * 609450 * 2
def baseEnd_609450 : Nat := 139084793281220336787643

theorem tailTrace_609450 : CollatzResearch.WordTrace tailWord_609450 prefixEnd_609450 139084793281220336787643 := by
  unfold tailWord_609450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5557116910518552654604451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14818978428049473745611869 5557116910518552654604451)
  ·
    refine ⟨8335675365777828981906677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5557116910518552654604451 8335675365777828981906677)
    ·
      refine ⟨781469565541671467053751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8335675365777828981906677 781469565541671467053751)
      ·
        refine ⟨1172204348312507200580627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 781469565541671467053751 1172204348312507200580627)
        ·
          refine ⟨1758306522468760800870941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172204348312507200580627 1758306522468760800870941)
          ·
            refine ⟨659364945925785300326603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1758306522468760800870941 659364945925785300326603)
            ·
              refine ⟨989047418888677950489905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659364945925785300326603 989047418888677950489905)
              ·
                refine ⟨741785564166508462867429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989047418888677950489905 741785564166508462867429)
                ·
                  refine ⟨139084793281220336787643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 741785564166508462867429 139084793281220336787643)
                  ·
                    rfl

theorem cell21_609450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_609450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609450 prefixEnd_609450 := by exact prefixLift 609450
  have htrace : WordTrace (prefixWord ++ tailWord_609450) baseStart_609450 baseEnd_609450 := by
    simpa [prefixWord, tailWord_609450, baseEnd_609450] using wordTrace_append hprefix tailTrace_609450
  have hstable : (prefixWord ++ tailWord_609450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609450).length < 2 ^ (prefixWord ++ tailWord_609450).sum := by decide
  have hdescent : baseEnd_609450 < baseStart_609450 := by decide
  rcases family_descends (prefixWord ++ tailWord_609450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609571 : List Nat := [1, 1, 1, 4, 2, 5, 2, 2, 3]
def baseStart_609571 : Nat := 118140960795 + 609571 * 2 ^ 59
def prefixEnd_609571 : Nat := 4983230072969 + 3 ^ 40 * 609571 * 2
def baseEnd_609571 : Nat := 139112407129751015270729

theorem tailTrace_609571 : CollatzResearch.WordTrace tailWord_609571 prefixEnd_609571 139112407129751015270729 := by
  unfold tailWord_609571
  simp only [CollatzResearch.WordTrace]
  refine ⟨22232880874635848283572567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14821920583090565522381711 22232880874635848283572567)
  ·
    refine ⟨33349321311953772425358851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22232880874635848283572567 33349321311953772425358851)
    ·
      refine ⟨50023981967930658638038277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33349321311953772425358851 50023981967930658638038277)
      ·
        refine ⟨9379496618986998494632177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50023981967930658638038277 9379496618986998494632177)
        ·
          refine ⟨7034622464240248870974133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9379496618986998494632177 7034622464240248870974133)
          ·
            refine ⟨659495856022523331653825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7034622464240248870974133 659495856022523331653825)
            ·
              refine ⟨494621892016892498740369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659495856022523331653825 494621892016892498740369)
              ·
                refine ⟨370966419012669374055277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494621892016892498740369 370966419012669374055277)
                ·
                  refine ⟨139112407129751015270729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370966419012669374055277 139112407129751015270729)
                  ·
                    rfl

theorem cell21_609571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 3].length) (baseStart_609571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609571 prefixEnd_609571 := by exact prefixLift 609571
  have htrace : WordTrace (prefixWord ++ tailWord_609571) baseStart_609571 baseEnd_609571 := by
    simpa [prefixWord, tailWord_609571, baseEnd_609571] using wordTrace_append hprefix tailTrace_609571
  have hstable : (prefixWord ++ tailWord_609571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609571).length < 2 ^ (prefixWord ++ tailWord_609571).sum := by decide
  have hdescent : baseEnd_609571 < baseStart_609571 := by decide
  rcases family_descends (prefixWord ++ tailWord_609571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609596 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_609596 : Nat := 118140960795 + 609596 * 2 ^ 59
def prefixEnd_609596 : Nat := 4983230072969 + 3 ^ 40 * 609596 * 2
def baseEnd_609596 : Nat := 139118112470356527354011

theorem tailTrace_609596 : CollatzResearch.WordTrace tailWord_609596 prefixEnd_609596 139118112470356527354011 := by
  unfold tailWord_609596
  simp only [CollatzResearch.WordTrace]
  refine ⟨11116896349772638776616321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14822528466363518368821761 11116896349772638776616321)
  ·
    refine ⟨8337672262329479082462241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11116896349772638776616321 8337672262329479082462241)
    ·
      refine ⟨6253254196747109311846681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8337672262329479082462241 6253254196747109311846681)
      ·
        refine ⟨4689940647560331983885011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6253254196747109311846681 4689940647560331983885011)
        ·
          refine ⟨7034910971340497975827517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4689940647560331983885011 7034910971340497975827517)
          ·
            refine ⟨2638091614252686740935319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7034910971340497975827517 2638091614252686740935319)
            ·
              refine ⟨3957137421379030111402979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638091614252686740935319 3957137421379030111402979)
              ·
                refine ⟨5935706132068545167104469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3957137421379030111402979 5935706132068545167104469)
                ·
                  refine ⟨139118112470356527354011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5935706132068545167104469 139118112470356527354011)
                  ·
                    rfl

theorem cell21_609596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_609596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609596 prefixEnd_609596 := by exact prefixLift 609596
  have htrace : WordTrace (prefixWord ++ tailWord_609596) baseStart_609596 baseEnd_609596 := by
    simpa [prefixWord, tailWord_609596, baseEnd_609596] using wordTrace_append hprefix tailTrace_609596
  have hstable : (prefixWord ++ tailWord_609596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609596).length < 2 ^ (prefixWord ++ tailWord_609596).sum := by decide
  have hdescent : baseEnd_609596 < baseStart_609596 := by decide
  rcases family_descends (prefixWord ++ tailWord_609596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609689 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 5]
def baseStart_609689 : Nat := 118140960795 + 609689 * 2 ^ 59
def prefixEnd_609689 : Nat := 4983230072969 + 3 ^ 40 * 609689 * 2
def baseEnd_609689 : Nat := 139139336337409032303821

theorem tailTrace_609689 : CollatzResearch.WordTrace tailWord_609689 prefixEnd_609689 139139336337409032303821 := by
  unfold tailWord_609689
  simp only [CollatzResearch.WordTrace]
  refine ⟨22237184688208354436368121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14824789792138902957578747 22237184688208354436368121)
  ·
    refine ⟨16677888516156265827276091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22237184688208354436368121 16677888516156265827276091)
    ·
      refine ⟨25016832774234398740914137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16677888516156265827276091 25016832774234398740914137)
      ·
        refine ⟨18762624580675799055685603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25016832774234398740914137 18762624580675799055685603)
        ·
          refine ⟨28143936871013698583528405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18762624580675799055685603 28143936871013698583528405)
          ·
            refine ⟨659623520414383560551447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28143936871013698583528405 659623520414383560551447)
            ·
              refine ⟨989435280621575340827171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659623520414383560551447 989435280621575340827171)
              ·
                refine ⟨1484152920932363011240757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989435280621575340827171 1484152920932363011240757)
                ·
                  refine ⟨139139336337409032303821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1484152920932363011240757 139139336337409032303821)
                  ·
                    rfl

theorem cell21_609689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_609689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609689 prefixEnd_609689 := by exact prefixLift 609689
  have htrace : WordTrace (prefixWord ++ tailWord_609689) baseStart_609689 baseEnd_609689 := by
    simpa [prefixWord, tailWord_609689, baseEnd_609689] using wordTrace_append hprefix tailTrace_609689
  have hstable : (prefixWord ++ tailWord_609689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609689).length < 2 ^ (prefixWord ++ tailWord_609689).sum := by decide
  have hdescent : baseEnd_609689 < baseStart_609689 := by decide
  rcases family_descends (prefixWord ++ tailWord_609689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609765 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 5]
def baseStart_609765 : Nat := 118140960795 + 609765 * 2 ^ 59
def prefixEnd_609765 : Nat := 4983230072969 + 3 ^ 40 * 609765 * 2
def baseEnd_609765 : Nat := 139156680572849789036999

theorem tailTrace_609765 : CollatzResearch.WordTrace tailWord_609765 prefixEnd_609765 139156680572849789036999 := by
  unfold tailWord_609765
  simp only [CollatzResearch.WordTrace]
  refine ⟨22239956635933019416134749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14826637757288679610756499 22239956635933019416134749)
  ·
    refine ⟨8339983738474882281050531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22239956635933019416134749 8339983738474882281050531)
    ·
      refine ⟨12509975607712323421575797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8339983738474882281050531 12509975607712323421575797)
      ·
        refine ⟨1172810213223030320772731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12509975607712323421575797 1172810213223030320772731)
        ·
          refine ⟨1759215319834545481159097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172810213223030320772731 1759215319834545481159097)
          ·
            refine ⟨1319411489875909110869323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1759215319834545481159097 1319411489875909110869323)
            ·
              refine ⟨1979117234813863666303985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319411489875909110869323 1979117234813863666303985)
              ·
                refine ⟨1484337926110397749727989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1979117234813863666303985 1484337926110397749727989)
                ·
                  refine ⟨139156680572849789036999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1484337926110397749727989 139156680572849789036999)
                  ·
                    rfl

theorem cell21_609765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_609765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609765 prefixEnd_609765 := by exact prefixLift 609765
  have htrace : WordTrace (prefixWord ++ tailWord_609765) baseStart_609765 baseEnd_609765 := by
    simpa [prefixWord, tailWord_609765, baseEnd_609765] using wordTrace_append hprefix tailTrace_609765
  have hstable : (prefixWord ++ tailWord_609765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609765).length < 2 ^ (prefixWord ++ tailWord_609765).sum := by decide
  have hdescent : baseEnd_609765 < baseStart_609765 := by decide
  rcases family_descends (prefixWord ++ tailWord_609765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609782 : List Nat := [5, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_609782 : Nat := 118140960795 + 609782 * 2 ^ 59
def prefixEnd_609782 : Nat := 4983230072969 + 3 ^ 40 * 609782 * 2
def baseEnd_609782 : Nat := 139160560204461537253631

theorem tailTrace_609782 : CollatzResearch.WordTrace tailWord_609782 prefixEnd_609782 139160560204461537253631 := by
  unfold tailWord_609782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1390036042304464457468975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14827051117914287546335733 1390036042304464457468975)
  ·
    refine ⟨2085054063456696686203463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1390036042304464457468975 2085054063456696686203463)
    ·
      refine ⟨3127581095185045029305195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2085054063456696686203463 3127581095185045029305195)
      ·
        refine ⟨4691371642777567543957793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3127581095185045029305195 4691371642777567543957793)
        ·
          refine ⟨3518528732083175657968345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4691371642777567543957793 3518528732083175657968345)
          ·
            refine ⟨2638896549062381743476259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3518528732083175657968345 2638896549062381743476259)
            ·
              refine ⟨3958344823593572615214389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638896549062381743476259 3958344823593572615214389)
              ·
                refine ⟨371094827211897432676349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3958344823593572615214389 371094827211897432676349)
                ·
                  refine ⟨139160560204461537253631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371094827211897432676349 139160560204461537253631)
                  ·
                    rfl

theorem cell21_609782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_609782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609782 prefixEnd_609782 := by exact prefixLift 609782
  have htrace : WordTrace (prefixWord ++ tailWord_609782) baseStart_609782 baseEnd_609782 := by
    simpa [prefixWord, tailWord_609782, baseEnd_609782] using wordTrace_append hprefix tailTrace_609782
  have hstable : (prefixWord ++ tailWord_609782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609782).length < 2 ^ (prefixWord ++ tailWord_609782).sum := by decide
  have hdescent : baseEnd_609782 < baseStart_609782 := by decide
  rcases family_descends (prefixWord ++ tailWord_609782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609796 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 6]
def baseStart_609796 : Nat := 118140960795 + 609796 * 2 ^ 59
def prefixEnd_609796 : Nat := 4983230072969 + 3 ^ 40 * 609796 * 2
def baseEnd_609796 : Nat := 139163755195200624020269

theorem tailTrace_609796 : CollatzResearch.WordTrace tailWord_609796 prefixEnd_609796 139163755195200624020269 := by
  unfold tailWord_609796
  simp only [CollatzResearch.WordTrace]
  refine ⟨11120543649410355855256621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14827391532547141140342161 11120543649410355855256621)
  ·
    refine ⟨4170203868528883445721233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11120543649410355855256621 4170203868528883445721233)
    ·
      refine ⟨3127652901396662584290925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4170203868528883445721233 3127652901396662584290925)
      ·
        refine ⟨1172869838023748469109097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3127652901396662584290925 1172869838023748469109097)
        ·
          refine ⟨879652378517811351831823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1172869838023748469109097 879652378517811351831823)
          ·
            refine ⟨1319478567776717027747735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879652378517811351831823 1319478567776717027747735)
            ·
              refine ⟨1979217851665075541621603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319478567776717027747735 1979217851665075541621603)
              ·
                refine ⟨2968826777497613312432405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979217851665075541621603 2968826777497613312432405)
                ·
                  refine ⟨139163755195200624020269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2968826777497613312432405 139163755195200624020269)
                  ·
                    rfl

theorem cell21_609796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_609796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609796 prefixEnd_609796 := by exact prefixLift 609796
  have htrace : WordTrace (prefixWord ++ tailWord_609796) baseStart_609796 baseEnd_609796 := by
    simpa [prefixWord, tailWord_609796, baseEnd_609796] using wordTrace_append hprefix tailTrace_609796
  have hstable : (prefixWord ++ tailWord_609796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609796).length < 2 ^ (prefixWord ++ tailWord_609796).sum := by decide
  have hdescent : baseEnd_609796 < baseStart_609796 := by decide
  rcases family_descends (prefixWord ++ tailWord_609796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609827 : List Nat := [1, 1, 1, 4, 5, 2, 2, 5]
def baseStart_609827 : Nat := 118140960795 + 609827 * 2 ^ 59
def prefixEnd_609827 : Nat := 4983230072969 + 3 ^ 40 * 609827 * 2
def baseEnd_609827 : Nat := 46390276605850486334513

theorem tailTrace_609827 : CollatzResearch.WordTrace tailWord_609827 prefixEnd_609827 46390276605850486334513 := by
  unfold tailWord_609827
  simp only [CollatzResearch.WordTrace]
  refine ⟨22242217961708404004891735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14828145307805602669927823 22242217961708404004891735)
  ·
    refine ⟨33363326942562606007337603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22242217961708404004891735 33363326942562606007337603)
    ·
      refine ⟨50044990413843909011006405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33363326942562606007337603 50044990413843909011006405)
      ·
        refine ⟨9383435702595732939563701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50044990413843909011006405 9383435702595732939563701)
        ·
          refine ⟨879697097118349963084097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9383435702595732939563701 879697097118349963084097)
          ·
            refine ⟨659772822838762472313073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 879697097118349963084097 659772822838762472313073)
            ·
              refine ⟨494829617129071854234805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659772822838762472313073 494829617129071854234805)
              ·
                refine ⟨46390276605850486334513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 494829617129071854234805 46390276605850486334513)
                ·
                  rfl

theorem cell21_609827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 5].length) (baseStart_609827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609827 prefixEnd_609827 := by exact prefixLift 609827
  have htrace : WordTrace (prefixWord ++ tailWord_609827) baseStart_609827 baseEnd_609827 := by
    simpa [prefixWord, tailWord_609827, baseEnd_609827] using wordTrace_append hprefix tailTrace_609827
  have hstable : (prefixWord ++ tailWord_609827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609827).length < 2 ^ (prefixWord ++ tailWord_609827).sum := by decide
  have hdescent : baseEnd_609827 < baseStart_609827 := by decide
  rcases family_descends (prefixWord ++ tailWord_609827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609951 : List Nat := [1, 1, 2, 7, 1, 1, 2, 3, 3]
def baseStart_609951 : Nat := 118140960795 + 609951 * 2 ^ 59
def prefixEnd_609951 : Nat := 4983230072969 + 3 ^ 40 * 609951 * 2
def baseEnd_609951 : Nat := 139199128306954798936619

theorem tailTrace_609951 : CollatzResearch.WordTrace tailWord_609951 prefixEnd_609951 139199128306954798936619 := by
  unfold tailWord_609951
  simp only [CollatzResearch.WordTrace]
  refine ⟨22246740613259173182405707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14831160408839448788270471 22246740613259173182405707)
  ·
    refine ⟨33370110919888759773608561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22246740613259173182405707 33370110919888759773608561)
    ·
      refine ⟨25027583189916569830206421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33370110919888759773608561 25027583189916569830206421)
      ·
        refine ⟨586583981013669605395463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 25027583189916569830206421 586583981013669605395463)
        ·
          refine ⟨879875971520504408093195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586583981013669605395463 879875971520504408093195)
          ·
            refine ⟨1319813957280756612139793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879875971520504408093195 1319813957280756612139793)
            ·
              refine ⟨989860467960567459104845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1319813957280756612139793 989860467960567459104845)
              ·
                refine ⟨371197675485212797164317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 989860467960567459104845 371197675485212797164317)
                ·
                  refine ⟨139199128306954798936619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371197675485212797164317 139199128306954798936619)
                  ·
                    rfl

theorem cell21_609951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 3].length) (baseStart_609951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609951 prefixEnd_609951 := by exact prefixLift 609951
  have htrace : WordTrace (prefixWord ++ tailWord_609951) baseStart_609951 baseEnd_609951 := by
    simpa [prefixWord, tailWord_609951, baseEnd_609951] using wordTrace_append hprefix tailTrace_609951
  have hstable : (prefixWord ++ tailWord_609951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609951).length < 2 ^ (prefixWord ++ tailWord_609951).sum := by decide
  have hdescent : baseEnd_609951 < baseStart_609951 := by decide
  rcases family_descends (prefixWord ++ tailWord_609951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609996 : List Nat := [2, 2, 1, 5, 3, 1, 2, 5]
def baseStart_609996 : Nat := 118140960795 + 609996 * 2 ^ 59
def prefixEnd_609996 : Nat := 4983230072969 + 3 ^ 40 * 609996 * 2
def baseEnd_609996 : Nat := 46403132640014906895509

theorem tailTrace_609996 : CollatzResearch.WordTrace tailWord_609996 prefixEnd_609996 46403132640014906895509 := by
  unfold tailWord_609996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11124190949048072933896921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14832254598730763911862561 11124190949048072933896921)
  ·
    refine ⟨8343143211786054700422691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11124190949048072933896921 8343143211786054700422691)
    ·
      refine ⟨12514714817679082050634037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8343143211786054700422691 12514714817679082050634037)
      ·
        refine ⟨1173254514157413942246941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12514714817679082050634037 1173254514157413942246941)
        ·
          refine ⟨439970442809030228342603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1173254514157413942246941 439970442809030228342603)
          ·
            refine ⟨659955664213545342513905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439970442809030228342603 659955664213545342513905)
            ·
              refine ⟨494966748160159006885429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659955664213545342513905 494966748160159006885429)
              ·
                refine ⟨46403132640014906895509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 494966748160159006885429 46403132640014906895509)
                ·
                  rfl

theorem cell21_609996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 5].length) (baseStart_609996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_609996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_609996 prefixEnd_609996 := by exact prefixLift 609996
  have htrace : WordTrace (prefixWord ++ tailWord_609996) baseStart_609996 baseEnd_609996 := by
    simpa [prefixWord, tailWord_609996, baseEnd_609996] using wordTrace_append hprefix tailTrace_609996
  have hstable : (prefixWord ++ tailWord_609996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609996).length < 2 ^ (prefixWord ++ tailWord_609996).sum := by decide
  have hdescent : baseEnd_609996 < baseStart_609996 := by decide
  rcases family_descends (prefixWord ++ tailWord_609996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610010 : List Nat := [3, 1, 1, 2, 2, 5, 1, 3, 3]
def baseStart_610010 : Nat := 118140960795 + 610010 * 2 ^ 59
def prefixEnd_610010 : Nat := 4983230072969 + 3 ^ 40 * 610010 * 2
def baseEnd_610010 : Nat := 139212592910783807453165

theorem tailTrace_610010 : CollatzResearch.WordTrace tailWord_610010 prefixEnd_610010 139212592910783807453165 := by
  unfold tailWord_610010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5562223130011356564700871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14832595013363617505868989 5562223130011356564700871)
  ·
    refine ⟨8343334695017034847051307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5562223130011356564700871 8343334695017034847051307)
    ·
      refine ⟨12515002042525552270576961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8343334695017034847051307 12515002042525552270576961)
      ·
        refine ⟨9386251531894164202932721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12515002042525552270576961 9386251531894164202932721)
        ·
          refine ⟨7039688648920623152199541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9386251531894164202932721 7039688648920623152199541)
          ·
            refine ⟨659970810836308420518707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7039688648920623152199541 659970810836308420518707)
            ·
              refine ⟨989956216254462630778061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659970810836308420518707 989956216254462630778061)
              ·
                refine ⟨371233581095423486541773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 989956216254462630778061 371233581095423486541773)
                ·
                  refine ⟨139212592910783807453165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371233581095423486541773 139212592910783807453165)
                  ·
                    rfl

theorem cell21_610010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_610010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610010 prefixEnd_610010 := by exact prefixLift 610010
  have htrace : WordTrace (prefixWord ++ tailWord_610010) baseStart_610010 baseEnd_610010 := by
    simpa [prefixWord, tailWord_610010, baseEnd_610010] using wordTrace_append hprefix tailTrace_610010
  have hstable : (prefixWord ++ tailWord_610010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610010).length < 2 ^ (prefixWord ++ tailWord_610010).sum := by decide
  have hdescent : baseEnd_610010 < baseStart_610010 := by decide
  rcases family_descends (prefixWord ++ tailWord_610010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610038 : List Nat := [5, 1, 1, 1, 1, 4, 2, 6]
def baseStart_610038 : Nat := 118140960795 + 610038 * 2 ^ 59
def prefixEnd_610038 : Nat := 4983230072969 + 3 ^ 40 * 610038 * 2
def baseEnd_610038 : Nat := 46406327630753993662147

theorem tailTrace_610038 : CollatzResearch.WordTrace tailWord_610038 prefixEnd_610038 46406327630753993662147 := by
  unfold tailWord_610038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1390619610246499190051423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14833275842629324693881845 1390619610246499190051423)
  ·
    refine ⟨2085929415369748785077135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1390619610246499190051423 2085929415369748785077135)
    ·
      refine ⟨3128894123054623177615703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2085929415369748785077135 3128894123054623177615703)
      ·
        refine ⟨4693341184581934766423555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3128894123054623177615703 4693341184581934766423555)
        ·
          refine ⟨7040011776872902149635333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4693341184581934766423555 7040011776872902149635333)
          ·
            refine ⟨1320002208163669153056625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7040011776872902149635333 1320002208163669153056625)
            ·
              refine ⟨990001656122751864792469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320002208163669153056625 990001656122751864792469)
              ·
                refine ⟨46406327630753993662147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 990001656122751864792469 46406327630753993662147)
                ·
                  rfl

theorem cell21_610038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_610038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610038 prefixEnd_610038 := by exact prefixLift 610038
  have htrace : WordTrace (prefixWord ++ tailWord_610038) baseStart_610038 baseEnd_610038 := by
    simpa [prefixWord, tailWord_610038, baseEnd_610038] using wordTrace_append hprefix tailTrace_610038
  have hstable : (prefixWord ++ tailWord_610038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610038).length < 2 ^ (prefixWord ++ tailWord_610038).sum := by decide
  have hdescent : baseEnd_610038 < baseStart_610038 := by decide
  rcases family_descends (prefixWord ++ tailWord_610038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610078 : List Nat := [4, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_610078 : Nat := 118140960795 + 610078 * 2 ^ 59
def prefixEnd_610078 : Nat := 4983230072969 + 3 ^ 40 * 610078 * 2
def baseEnd_610078 : Nat := 139228111437230800319693

theorem tailTrace_610078 : CollatzResearch.WordTrace tailWord_610078 prefixEnd_610078 139228111437230800319693 := by
  unfold tailWord_610078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2781421585474884234034861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14834248455866049248185925 2781421585474884234034861)
  ·
    refine ⟨1043033094553081587763073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2781421585474884234034861 1043033094553081587763073)
    ·
      refine ⟨782274820914811190822305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1043033094553081587763073 782274820914811190822305)
      ·
        refine ⟨586706115686108393116729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 782274820914811190822305 586706115686108393116729)
        ·
          refine ⟨440029586764581294837547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586706115686108393116729 440029586764581294837547)
          ·
            refine ⟨660044380146871942256321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440029586764581294837547 660044380146871942256321)
            ·
              refine ⟨495033285110153956692241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660044380146871942256321 495033285110153956692241)
              ·
                refine ⟨371274963832615467519181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495033285110153956692241 371274963832615467519181)
                ·
                  refine ⟨139228111437230800319693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371274963832615467519181 139228111437230800319693)
                  ·
                    rfl

theorem cell21_610078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_610078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610078 prefixEnd_610078 := by exact prefixLift 610078
  have htrace : WordTrace (prefixWord ++ tailWord_610078) baseStart_610078 baseEnd_610078 := by
    simpa [prefixWord, tailWord_610078, baseEnd_610078] using wordTrace_append hprefix tailTrace_610078
  have hstable : (prefixWord ++ tailWord_610078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610078).length < 2 ^ (prefixWord ++ tailWord_610078).sum := by decide
  have hdescent : baseEnd_610078 < baseStart_610078 := by decide
  rcases family_descends (prefixWord ++ tailWord_610078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610097 : List Nat := [1, 2, 2, 3, 2, 2, 3, 6]
def baseStart_610097 : Nat := 118140960795 + 610097 * 2 ^ 59
def prefixEnd_610097 : Nat := 4983230072969 + 3 ^ 40 * 610097 * 2
def baseEnd_610097 : Nat := 46410815832030329834329

theorem tailTrace_610097 : CollatzResearch.WordTrace tailWord_610097 prefixEnd_610097 46410815832030329834329 := by
  unfold tailWord_610097
  simp only [CollatzResearch.WordTrace]
  refine ⟨22252065670730240117220545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14834710447153493411480363 22252065670730240117220545)
  ·
    refine ⟨16689049253047680087915409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22252065670730240117220545 16689049253047680087915409)
    ·
      refine ⟨12516786939785760065936557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16689049253047680087915409 12516786939785760065936557)
      ·
        refine ⟨4693795102419660024726209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12516786939785760065936557 4693795102419660024726209)
        ·
          refine ⟨3520346326814745018544657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4693795102419660024726209 3520346326814745018544657)
          ·
            refine ⟨2640259745111058763908493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3520346326814745018544657 2640259745111058763908493)
            ·
              refine ⟨990097404416647036465685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2640259745111058763908493 990097404416647036465685)
              ·
                refine ⟨46410815832030329834329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 990097404416647036465685 46410815832030329834329)
                ·
                  rfl

theorem cell21_610097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 6].length) (baseStart_610097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610097 prefixEnd_610097 := by exact prefixLift 610097
  have htrace : WordTrace (prefixWord ++ tailWord_610097) baseStart_610097 baseEnd_610097 := by
    simpa [prefixWord, tailWord_610097, baseEnd_610097] using wordTrace_append hprefix tailTrace_610097
  have hstable : (prefixWord ++ tailWord_610097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610097).length < 2 ^ (prefixWord ++ tailWord_610097).sum := by decide
  have hdescent : baseEnd_610097 < baseStart_610097 := by decide
  rcases family_descends (prefixWord ++ tailWord_610097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610100 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 4]
def baseStart_610100 : Nat := 118140960795 + 610100 * 2 ^ 59
def prefixEnd_610100 : Nat := 4983230072969 + 3 ^ 40 * 610100 * 2
def baseEnd_610100 : Nat := 139233132136963650952981

theorem tailTrace_610100 : CollatzResearch.WordTrace tailWord_610100 prefixEnd_610100 139233132136963650952981 := by
  unfold tailWord_610100
  simp only [CollatzResearch.WordTrace]
  refine ⟨11126087544859685814789877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14834783393146247753053169 11126087544859685814789877)
  ·
    refine ⟨1043070707330595545136551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11126087544859685814789877 1043070707330595545136551)
    ·
      refine ⟨1564606060995893317704827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1043070707330595545136551 1564606060995893317704827)
      ·
        refine ⟨2346909091493839976557241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1564606060995893317704827 2346909091493839976557241)
        ·
          refine ⟨1760181818620379982417931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2346909091493839976557241 1760181818620379982417931)
          ·
            refine ⟨2640272727930569973626897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760181818620379982417931 2640272727930569973626897)
            ·
              refine ⟨1980204545947927480220173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2640272727930569973626897 1980204545947927480220173)
              ·
                refine ⟨742576704730472805082565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1980204545947927480220173 742576704730472805082565)
                ·
                  refine ⟨139233132136963650952981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 742576704730472805082565 139233132136963650952981)
                  ·
                    rfl

theorem cell21_610100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_610100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610100 prefixEnd_610100 := by exact prefixLift 610100
  have htrace : WordTrace (prefixWord ++ tailWord_610100) baseStart_610100 baseEnd_610100 := by
    simpa [prefixWord, tailWord_610100, baseEnd_610100] using wordTrace_append hprefix tailTrace_610100
  have hstable : (prefixWord ++ tailWord_610100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610100).length < 2 ^ (prefixWord ++ tailWord_610100).sum := by decide
  have hdescent : baseEnd_610100 < baseStart_610100 := by decide
  rcases family_descends (prefixWord ++ tailWord_610100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610210 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 4]
def baseStart_610210 : Nat := 118140960795 + 610210 * 2 ^ 59
def prefixEnd_610210 : Nat := 4983230072969 + 3 ^ 40 * 610210 * 2
def baseEnd_610210 : Nat := 139258235635627904119423

theorem tailTrace_610210 : CollatzResearch.WordTrace tailWord_610210 prefixEnd_610210 139258235635627904119423 := by
  unfold tailWord_610210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5564046779830215104021021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14837458079547240277389389 5564046779830215104021021)
  ·
    refine ⟨2086517542436330664007883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5564046779830215104021021 2086517542436330664007883)
    ·
      refine ⟨3129776313654495996011825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2086517542436330664007883 3129776313654495996011825)
      ·
        refine ⟨2347332235240871997008869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3129776313654495996011825 2347332235240871997008869)
        ·
          refine ⟨440124794107663499439163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2347332235240871997008869 440124794107663499439163)
          ·
            refine ⟨660187191161495249158745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440124794107663499439163 660187191161495249158745)
            ·
              refine ⟨495140393371121436869059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660187191161495249158745 495140393371121436869059)
              ·
                refine ⟨742710590056682155303589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495140393371121436869059 742710590056682155303589)
                ·
                  refine ⟨139258235635627904119423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 742710590056682155303589 139258235635627904119423)
                  ·
                    rfl

theorem cell21_610210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_610210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610210 prefixEnd_610210 := by exact prefixLift 610210
  have htrace : WordTrace (prefixWord ++ tailWord_610210) baseStart_610210 baseEnd_610210 := by
    simpa [prefixWord, tailWord_610210, baseEnd_610210] using wordTrace_append hprefix tailTrace_610210
  have hstable : (prefixWord ++ tailWord_610210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610210).length < 2 ^ (prefixWord ++ tailWord_610210).sum := by decide
  have hdescent : baseEnd_610210 < baseStart_610210 := by decide
  rcases family_descends (prefixWord ++ tailWord_610210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610232 : List Nat := [2, 1, 2, 1, 2, 3, 1, 9]
def baseStart_610232 : Nat := 118140960795 + 610232 * 2 ^ 59
def prefixEnd_610232 : Nat := 4983230072969 + 3 ^ 40 * 610232 * 2
def baseEnd_610232 : Nat := 46421085445120251584237

theorem tailTrace_610232 : CollatzResearch.WordTrace tailWord_610232 prefixEnd_610232 46421085445120251584237 := by
  unfold tailWord_610232
  simp only [CollatzResearch.WordTrace]
  refine ⟨11128494762620579086692475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14837993016827438782256633 11128494762620579086692475)
  ·
    refine ⟨16692742143930868630038713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11128494762620579086692475 16692742143930868630038713)
    ·
      refine ⟨12519556607948151472529035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16692742143930868630038713 12519556607948151472529035)
      ·
        refine ⟨18779334911922227208793553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12519556607948151472529035 18779334911922227208793553)
        ·
          refine ⟨14084501183941670406595165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18779334911922227208793553 14084501183941670406595165)
          ·
            refine ⟨5281687943978126402473187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14084501183941670406595165 5281687943978126402473187)
            ·
              refine ⟨7922531915967189603709781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5281687943978126402473187 7922531915967189603709781)
              ·
                refine ⟨46421085445120251584237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7922531915967189603709781 46421085445120251584237)
                ·
                  rfl

theorem cell21_610232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_610232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610232 prefixEnd_610232 := by exact prefixLift 610232
  have htrace : WordTrace (prefixWord ++ tailWord_610232) baseStart_610232 baseEnd_610232 := by
    simpa [prefixWord, tailWord_610232, baseEnd_610232] using wordTrace_append hprefix tailTrace_610232
  have hstable : (prefixWord ++ tailWord_610232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610232).length < 2 ^ (prefixWord ++ tailWord_610232).sum := by decide
  have hdescent : baseEnd_610232 < baseStart_610232 := by decide
  rcases family_descends (prefixWord ++ tailWord_610232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610263 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 5]
def baseStart_610263 : Nat := 118140960795 + 610263 * 2 ^ 59
def prefixEnd_610263 : Nat := 4983230072969 + 3 ^ 40 * 610263 * 2
def baseEnd_610263 : Nat := 139270330957711589735981

theorem tailTrace_610263 : CollatzResearch.WordTrace tailWord_610263 prefixEnd_610263 139270330957711589735981 := by
  unfold tailWord_610263
  simp only [CollatzResearch.WordTrace]
  refine ⟨22258120188128850467763443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14838746792085900311842295 22258120188128850467763443)
  ·
    refine ⟨33387180282193275701645165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22258120188128850467763443 33387180282193275701645165)
    ·
      refine ⟨12520192605822478388116937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33387180282193275701645165 12520192605822478388116937)
      ·
        refine ⟨9390144454366858791087703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12520192605822478388116937 9390144454366858791087703)
        ·
          refine ⟨14085216681550288186631555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9390144454366858791087703 14085216681550288186631555)
          ·
            refine ⟨21127825022325432279947333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14085216681550288186631555 21127825022325432279947333)
            ·
              refine ⟨3961467191686018552490125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21127825022325432279947333 3961467191686018552490125)
              ·
                refine ⟨1485550196882256957183797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3961467191686018552490125 1485550196882256957183797)
                ·
                  refine ⟨139270330957711589735981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1485550196882256957183797 139270330957711589735981)
                  ·
                    rfl

theorem cell21_610263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_610263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610263 prefixEnd_610263 := by exact prefixLift 610263
  have htrace : WordTrace (prefixWord ++ tailWord_610263) baseStart_610263 baseEnd_610263 := by
    simpa [prefixWord, tailWord_610263, baseEnd_610263] using wordTrace_append hprefix tailTrace_610263
  have hstable : (prefixWord ++ tailWord_610263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610263).length < 2 ^ (prefixWord ++ tailWord_610263).sum := by decide
  have hdescent : baseEnd_610263 < baseStart_610263 := by decide
  rcases family_descends (prefixWord ++ tailWord_610263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610266 : List Nat := [3, 1, 1, 2, 5, 2, 1, 6]
def baseStart_610266 : Nat := 118140960795 + 610266 * 2 ^ 59
def prefixEnd_610266 : Nat := 4983230072969 + 3 ^ 40 * 610266 * 2
def baseEnd_610266 : Nat := 46423671866194750395325

theorem tailTrace_610266 : CollatzResearch.WordTrace tailWord_610266 prefixEnd_610266 46423671866194750395325 := by
  unfold tailWord_610266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5564557401779495495030663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14838819738078654653415101 5564557401779495495030663)
  ·
    refine ⟨8346836102669243242545995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5564557401779495495030663 8346836102669243242545995)
    ·
      refine ⟨12520254154003864863818993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8346836102669243242545995 12520254154003864863818993)
      ·
        refine ⟨9390190615502898647864245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12520254154003864863818993 9390190615502898647864245)
        ·
          refine ⟨880330370203396748237273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9390190615502898647864245 880330370203396748237273)
          ·
            refine ⟨660247777652547561177955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 880330370203396748237273 660247777652547561177955)
            ·
              refine ⟨990371666478821341766933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660247777652547561177955 990371666478821341766933)
              ·
                refine ⟨46423671866194750395325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 990371666478821341766933 46423671866194750395325)
                ·
                  rfl

theorem cell21_610266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_610266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610266 prefixEnd_610266 := by exact prefixLift 610266
  have htrace : WordTrace (prefixWord ++ tailWord_610266) baseStart_610266 baseEnd_610266 := by
    simpa [prefixWord, tailWord_610266, baseEnd_610266] using wordTrace_append hprefix tailTrace_610266
  have hstable : (prefixWord ++ tailWord_610266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610266).length < 2 ^ (prefixWord ++ tailWord_610266).sum := by decide
  have hdescent : baseEnd_610266 < baseStart_610266 := by decide
  rcases family_descends (prefixWord ++ tailWord_610266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610297 : List Nat := [1, 2, 1, 3, 1, 5, 2, 3, 3]
def baseStart_610297 : Nat := 118140960795 + 610297 * 2 ^ 59
def prefixEnd_610297 : Nat := 4983230072969 + 3 ^ 40 * 610297 * 2
def baseEnd_610297 : Nat := 139278090220935086169245

theorem tailTrace_610297 : CollatzResearch.WordTrace tailWord_610297 prefixEnd_610297 139278090220935086169245 := by
  unfold tailWord_610297
  simp only [CollatzResearch.WordTrace]
  refine ⟨22259360270005674274501145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14839573513337116183000763 22259360270005674274501145)
  ·
    refine ⟨16694520202504255705875859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22259360270005674274501145 16694520202504255705875859)
    ·
      refine ⟨25041780303756383558813789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16694520202504255705875859 25041780303756383558813789)
      ·
        refine ⟨9390667613908643834555171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25041780303756383558813789 9390667613908643834555171)
        ·
          refine ⟨14086001420862965751832757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9390667613908643834555171 14086001420862965751832757)
          ·
            refine ⟨1320562633205903039234321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14086001420862965751832757 1320562633205903039234321)
            ·
              refine ⟨990421974904427279425741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320562633205903039234321 990421974904427279425741)
              ·
                refine ⟨371408240589160229784653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 990421974904427279425741 371408240589160229784653)
                ·
                  refine ⟨139278090220935086169245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371408240589160229784653 139278090220935086169245)
                  ·
                    rfl

theorem cell21_610297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 3].length) (baseStart_610297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610297 prefixEnd_610297 := by exact prefixLift 610297
  have htrace : WordTrace (prefixWord ++ tailWord_610297) baseStart_610297 baseEnd_610297 := by
    simpa [prefixWord, tailWord_610297, baseEnd_610297] using wordTrace_append hprefix tailTrace_610297
  have hstable : (prefixWord ++ tailWord_610297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610297).length < 2 ^ (prefixWord ++ tailWord_610297).sum := by decide
  have hdescent : baseEnd_610297 < baseStart_610297 := by decide
  rcases family_descends (prefixWord ++ tailWord_610297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610311 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 4]
def baseStart_610311 : Nat := 118140960795 + 610311 * 2 ^ 59
def prefixEnd_610311 : Nat := 4983230072969 + 3 ^ 40 * 610311 * 2
def baseEnd_610311 : Nat := 139281285211674172935883

theorem tailTrace_610311 : CollatzResearch.WordTrace tailWord_610311 prefixEnd_610311 139281285211674172935883 := by
  unfold tailWord_610311
  simp only [CollatzResearch.WordTrace]
  refine ⟨22259870891954954665510787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14839913927969969777007191 22259870891954954665510787)
  ·
    refine ⟨33389806337932431998266181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22259870891954954665510787 33389806337932431998266181)
    ·
      refine ⟨6260588688362330999674909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33389806337932431998266181 6260588688362330999674909)
      ·
        refine ⟨2347720758135874124878091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6260588688362330999674909 2347720758135874124878091)
        ·
          refine ⟨3521581137203811187317137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2347720758135874124878091 3521581137203811187317137)
          ·
            refine ⟨2641185852902858390487853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3521581137203811187317137 2641185852902858390487853)
            ·
              refine ⟨990444694838571896432945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2641185852902858390487853 990444694838571896432945)
              ·
                refine ⟨742833521128928922324709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990444694838571896432945 742833521128928922324709)
                ·
                  refine ⟨139281285211674172935883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 742833521128928922324709 139281285211674172935883)
                  ·
                    rfl

theorem cell21_610311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 4].length) (baseStart_610311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610311 prefixEnd_610311 := by exact prefixLift 610311
  have htrace : WordTrace (prefixWord ++ tailWord_610311) baseStart_610311 baseEnd_610311 := by
    simpa [prefixWord, tailWord_610311, baseEnd_610311] using wordTrace_append hprefix tailTrace_610311
  have hstable : (prefixWord ++ tailWord_610311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610311).length < 2 ^ (prefixWord ++ tailWord_610311).sum := by decide
  have hdescent : baseEnd_610311 < baseStart_610311 := by decide
  rcases family_descends (prefixWord ++ tailWord_610311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610339 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 5]
def baseStart_610339 : Nat := 118140960795 + 610339 * 2 ^ 59
def prefixEnd_610339 : Nat := 4983230072969 + 3 ^ 40 * 610339 * 2
def baseEnd_610339 : Nat := 139287675193152346469159

theorem tailTrace_610339 : CollatzResearch.WordTrace tailWord_610339 prefixEnd_610339 139287675193152346469159 := by
  unfold tailWord_610339
  simp only [CollatzResearch.WordTrace]
  refine ⟨22260892135853515447530071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14840594757235676965020047 22260892135853515447530071)
  ·
    refine ⟨33391338203780273171295107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22260892135853515447530071 33391338203780273171295107)
    ·
      refine ⟨50087007305670409756942661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33391338203780273171295107 50087007305670409756942661)
      ·
        refine ⟨9391313869813201829426749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50087007305670409756942661 9391313869813201829426749)
        ·
          refine ⟨3521742701179950686035031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9391313869813201829426749 3521742701179950686035031)
          ·
            refine ⟨5282614051769926029052547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521742701179950686035031 5282614051769926029052547)
            ·
              refine ⟨7923921077654889043578821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5282614051769926029052547 7923921077654889043578821)
              ·
                refine ⟨1485735202060291695671029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7923921077654889043578821 1485735202060291695671029)
                ·
                  refine ⟨139287675193152346469159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1485735202060291695671029 139287675193152346469159)
                  ·
                    rfl

theorem cell21_610339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_610339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610339 prefixEnd_610339 := by exact prefixLift 610339
  have htrace : WordTrace (prefixWord ++ tailWord_610339) baseStart_610339 baseEnd_610339 := by
    simpa [prefixWord, tailWord_610339, baseEnd_610339] using wordTrace_append hprefix tailTrace_610339
  have hstable : (prefixWord ++ tailWord_610339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610339).length < 2 ^ (prefixWord ++ tailWord_610339).sum := by decide
  have hdescent : baseEnd_610339 < baseStart_610339 := by decide
  rcases family_descends (prefixWord ++ tailWord_610339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610466 : List Nat := [3, 3, 1, 3, 1, 2, 2, 3, 3]
def baseStart_610466 : Nat := 118140960795 + 610466 * 2 ^ 59
def prefixEnd_610466 : Nat := 4983230072969 + 3 ^ 40 * 610466 * 2
def baseEnd_610466 : Nat := 139316658323428347852233

theorem tailTrace_610466 : CollatzResearch.WordTrace tailWord_610466 prefixEnd_610466 139316658323428347852233 := by
  unfold tailWord_610466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5566381051598354034350813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14843682804262277424935501 5566381051598354034350813)
  ·
    refine ⟨2087392894349382762881555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5566381051598354034350813 2087392894349382762881555)
    ·
      refine ⟨3131089341524074144322333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2087392894349382762881555 3131089341524074144322333)
      ·
        refine ⟨1174158503071527804120875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3131089341524074144322333 1174158503071527804120875)
        ·
          refine ⟨1761237754607291706181313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174158503071527804120875 1761237754607291706181313)
          ·
            refine ⟨1320928315955468779635985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1761237754607291706181313 1320928315955468779635985)
            ·
              refine ⟨990696236966601584726989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320928315955468779635985 990696236966601584726989)
              ·
                refine ⟨371511088862475594272621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 990696236966601584726989 371511088862475594272621)
                ·
                  refine ⟨139316658323428347852233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371511088862475594272621 139316658323428347852233)
                  ·
                    rfl

theorem cell21_610466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_610466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610466 prefixEnd_610466 := by exact prefixLift 610466
  have htrace : WordTrace (prefixWord ++ tailWord_610466) baseStart_610466 baseEnd_610466 := by
    simpa [prefixWord, tailWord_610466, baseEnd_610466] using wordTrace_append hprefix tailTrace_610466
  have hstable : (prefixWord ++ tailWord_610466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610466).length < 2 ^ (prefixWord ++ tailWord_610466).sum := by decide
  have hdescent : baseEnd_610466 < baseStart_610466 := by decide
  rcases family_descends (prefixWord ++ tailWord_610466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610477 : List Nat := [1, 5, 2, 1, 2, 2, 8]
def baseStart_610477 : Nat := 118140960795 + 610477 * 2 ^ 59
def prefixEnd_610477 : Nat := 4983230072969 + 3 ^ 40 * 610477 * 2
def baseEnd_610477 : Nat := 15479907630366085907653

theorem tailTrace_610477 : CollatzResearch.WordTrace tailWord_610477 prefixEnd_610477 15479907630366085907653 := by
  unfold tailWord_610477
  simp only [CollatzResearch.WordTrace]
  refine ⟨22265925409353565016053685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14843950272902376677369123 22265925409353565016053685)
  ·
    refine ⟨2087430507126896720255033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22265925409353565016053685 2087430507126896720255033)
    ·
      refine ⟨1565572880345172540191275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2087430507126896720255033 1565572880345172540191275)
      ·
        refine ⟨2348359320517758810286913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565572880345172540191275 2348359320517758810286913)
        ·
          refine ⟨1761269490388319107715185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2348359320517758810286913 1761269490388319107715185)
          ·
            refine ⟨1320952117791239330786389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1761269490388319107715185 1320952117791239330786389)
            ·
              refine ⟨15479907630366085907653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1320952117791239330786389 15479907630366085907653)
              ·
                rfl

theorem cell21_610477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 8].length) (baseStart_610477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610477 prefixEnd_610477 := by exact prefixLift 610477
  have htrace : WordTrace (prefixWord ++ tailWord_610477) baseStart_610477 baseEnd_610477 := by
    simpa [prefixWord, tailWord_610477, baseEnd_610477] using wordTrace_append hprefix tailTrace_610477
  have hstable : (prefixWord ++ tailWord_610477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610477).length < 2 ^ (prefixWord ++ tailWord_610477).sum := by decide
  have hdescent : baseEnd_610477 < baseStart_610477 := by decide
  rcases family_descends (prefixWord ++ tailWord_610477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610491 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 5]
def baseStart_610491 : Nat := 118140960795 + 610491 * 2 ^ 59
def prefixEnd_610491 : Nat := 4983230072969 + 3 ^ 40 * 610491 * 2
def baseEnd_610491 : Nat := 139322363664033859935515

theorem tailTrace_610491 : CollatzResearch.WordTrace tailWord_610491 prefixEnd_610491 139322363664033859935515 := by
  unfold tailWord_610491
  simp only [CollatzResearch.WordTrace]
  refine ⟨22266436031302845407063327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14844290687535230271375551 22266436031302845407063327)
  ·
    refine ⟨33399654046954268110594991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22266436031302845407063327 33399654046954268110594991)
    ·
      refine ⟨50099481070431402165892487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33399654046954268110594991 50099481070431402165892487)
      ·
        refine ⟨75149221605647103248838731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50099481070431402165892487 75149221605647103248838731)
        ·
          refine ⟨112723832408470654873258097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75149221605647103248838731 112723832408470654873258097)
          ·
            refine ⟨84542874306352991154943573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112723832408470654873258097 84542874306352991154943573)
            ·
              refine ⟨990736808277574115096995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 84542874306352991154943573 990736808277574115096995)
              ·
                refine ⟨1486105212416361172645493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990736808277574115096995 1486105212416361172645493)
                ·
                  refine ⟨139322363664033859935515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1486105212416361172645493 139322363664033859935515)
                  ·
                    rfl

theorem cell21_610491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 5].length) (baseStart_610491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610491 prefixEnd_610491 := by exact prefixLift 610491
  have htrace : WordTrace (prefixWord ++ tailWord_610491) baseStart_610491 baseEnd_610491 := by
    simpa [prefixWord, tailWord_610491, baseEnd_610491] using wordTrace_append hprefix tailTrace_610491
  have hstable : (prefixWord ++ tailWord_610491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610491).length < 2 ^ (prefixWord ++ tailWord_610491).sum := by decide
  have hdescent : baseEnd_610491 < baseStart_610491 := by decide
  rcases family_descends (prefixWord ++ tailWord_610491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610497 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 4]
def baseStart_610497 : Nat := 118140960795 + 610497 * 2 ^ 59
def prefixEnd_610497 : Nat := 4983230072969 + 3 ^ 40 * 610497 * 2
def baseEnd_610497 : Nat := 139323732945779182835503

theorem tailTrace_610497 : CollatzResearch.WordTrace tailWord_610497 prefixEnd_610497 139323732945779182835503 := by
  unfold tailWord_610497
  simp only [CollatzResearch.WordTrace]
  refine ⟨22266654869281108431781745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14844436579520738954521163 22266654869281108431781745)
  ·
    refine ⟨16699991151960831323836309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22266654869281108431781745 16699991151960831323836309)
    ·
      refine ⟨782812085248163968304827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16699991151960831323836309 782812085248163968304827)
      ·
        refine ⟨1174218127872245952457241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782812085248163968304827 1174218127872245952457241)
        ·
          refine ⟨880663595904184464342931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1174218127872245952457241 880663595904184464342931)
          ·
            refine ⟨1320995393856276696514397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880663595904184464342931 1320995393856276696514397)
            ·
              refine ⟨495373272696103761192899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1320995393856276696514397 495373272696103761192899)
              ·
                refine ⟨743059909044155641789349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495373272696103761192899 743059909044155641789349)
                ·
                  refine ⟨139323732945779182835503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 743059909044155641789349 139323732945779182835503)
                  ·
                    rfl

theorem cell21_610497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_610497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610497 prefixEnd_610497 := by exact prefixLift 610497
  have htrace : WordTrace (prefixWord ++ tailWord_610497) baseStart_610497 baseEnd_610497 := by
    simpa [prefixWord, tailWord_610497, baseEnd_610497] using wordTrace_append hprefix tailTrace_610497
  have hstable : (prefixWord ++ tailWord_610497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610497).length < 2 ^ (prefixWord ++ tailWord_610497).sum := by decide
  have hdescent : baseEnd_610497 < baseStart_610497 := by decide
  rcases family_descends (prefixWord ++ tailWord_610497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610536 : List Nat := [2, 1, 4, 1, 2, 2, 9]
def baseStart_610536 : Nat := 118140960795 + 610536 * 2 ^ 59
def prefixEnd_610536 : Nat := 4983230072969 + 3 ^ 40 * 610536 * 2
def baseEnd_610536 : Nat := 15481403697458197965047

theorem tailTrace_610536 : CollatzResearch.WordTrace tailWord_610536 prefixEnd_610536 15481403697458197965047 := by
  unfold tailWord_610536
  simp only [CollatzResearch.WordTrace]
  refine ⟨11134038658069909046225731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14845384877426545394967641 11134038658069909046225731)
  ·
    refine ⟨16701057987104863569338597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11134038658069909046225731 16701057987104863569338597)
    ·
      refine ⟨3131448372582161919250987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16701057987104863569338597 3131448372582161919250987)
      ·
        refine ⟨4697172558873242878876481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131448372582161919250987 4697172558873242878876481)
        ·
          refine ⟨3522879419154932159157361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4697172558873242878876481 3522879419154932159157361)
          ·
            refine ⟨2642159564366199119368021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3522879419154932159157361 2642159564366199119368021)
            ·
              refine ⟨15481403697458197965047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2642159564366199119368021 15481403697458197965047)
              ·
                rfl

theorem cell21_610536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 9].length) (baseStart_610536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610536 prefixEnd_610536 := by exact prefixLift 610536
  have htrace : WordTrace (prefixWord ++ tailWord_610536) baseStart_610536 baseEnd_610536 := by
    simpa [prefixWord, tailWord_610536, baseEnd_610536] using wordTrace_append hprefix tailTrace_610536
  have hstable : (prefixWord ++ tailWord_610536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610536).length < 2 ^ (prefixWord ++ tailWord_610536).sum := by decide
  have hdescent : baseEnd_610536 < baseStart_610536 := by decide
  rcases family_descends (prefixWord ++ tailWord_610536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610556 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 4]
def baseStart_610556 : Nat := 118140960795 + 610556 * 2 ^ 59
def prefixEnd_610556 : Nat := 4983230072969 + 3 ^ 40 * 610556 * 2
def baseEnd_610556 : Nat := 139337197549608191352049

theorem tailTrace_610556 : CollatzResearch.WordTrace tailWord_610556 prefixEnd_610556 139337197549608191352049 := by
  unfold tailWord_610556
  simp only [CollatzResearch.WordTrace]
  refine ⟨11134403388033680754089761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14845871184044907672119681 11134403388033680754089761)
  ·
    refine ⟨8350802541025260565567321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11134403388033680754089761 8350802541025260565567321)
    ·
      refine ⟨6263101905768945424175491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8350802541025260565567321 6263101905768945424175491)
      ·
        refine ⟨9394652858653418136263237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6263101905768945424175491 9394652858653418136263237)
        ·
          refine ⟨1761497410997515900549357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9394652858653418136263237 1761497410997515900549357)
          ·
            refine ⟨660561529124068462706009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1761497410997515900549357 660561529124068462706009)
            ·
              refine ⟨495421146843051347029507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660561529124068462706009 495421146843051347029507)
              ·
                refine ⟨743131720264577020544261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495421146843051347029507 743131720264577020544261)
                ·
                  refine ⟨139337197549608191352049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 743131720264577020544261 139337197549608191352049)
                  ·
                    rfl

theorem cell21_610556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_610556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610556 prefixEnd_610556 := by exact prefixLift 610556
  have htrace : WordTrace (prefixWord ++ tailWord_610556) baseStart_610556 baseEnd_610556 := by
    simpa [prefixWord, tailWord_610556, baseEnd_610556] using wordTrace_append hprefix tailTrace_610556
  have hstable : (prefixWord ++ tailWord_610556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610556).length < 2 ^ (prefixWord ++ tailWord_610556).sum := by decide
  have hdescent : baseEnd_610556 < baseStart_610556 := by decide
  rcases family_descends (prefixWord ++ tailWord_610556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610581 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 8]
def baseStart_610581 : Nat := 118140960795 + 610581 * 2 ^ 59
def prefixEnd_610581 : Nat := 4983230072969 + 3 ^ 40 * 610581 * 2
def baseEnd_610581 : Nat := 139342902890213703435331

theorem tailTrace_610581 : CollatzResearch.WordTrace tailWord_610581 prefixEnd_610581 139342902890213703435331 := by
  unfold tailWord_610581
  simp only [CollatzResearch.WordTrace]
  refine ⟨22269718600976790777839597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14846479067317860518559731 22269718600976790777839597)
  ·
    refine ⟨8351144475366296541689849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22269718600976790777839597 8351144475366296541689849)
    ·
      refine ⟨6263358356524722406267387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8351144475366296541689849 6263358356524722406267387)
      ·
        refine ⟨9395037534787083609401081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6263358356524722406267387 9395037534787083609401081)
        ·
          refine ⟨7046278151090312707050811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9395037534787083609401081 7046278151090312707050811)
          ·
            refine ⟨10569417226635469060576217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7046278151090312707050811 10569417226635469060576217)
            ·
              refine ⟨7927062919976601795432163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10569417226635469060576217 7927062919976601795432163)
              ·
                refine ⟨11890594379964902693148245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7927062919976601795432163 11890594379964902693148245)
                ·
                  refine ⟨139342902890213703435331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11890594379964902693148245 139342902890213703435331)
                  ·
                    rfl

theorem cell21_610581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_610581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610581 prefixEnd_610581 := by exact prefixLift 610581
  have htrace : WordTrace (prefixWord ++ tailWord_610581) baseStart_610581 baseEnd_610581 := by
    simpa [prefixWord, tailWord_610581, baseEnd_610581] using wordTrace_append hprefix tailTrace_610581
  have hstable : (prefixWord ++ tailWord_610581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610581).length < 2 ^ (prefixWord ++ tailWord_610581).sum := by decide
  have hdescent : baseEnd_610581 < baseStart_610581 := by decide
  rcases family_descends (prefixWord ++ tailWord_610581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610584 : List Nat := [2, 1, 2, 3, 1, 2, 2, 5, 3]
def baseStart_610584 : Nat := 118140960795 + 610584 * 2 ^ 59
def prefixEnd_610584 : Nat := 4983230072969 + 3 ^ 40 * 610584 * 2
def baseEnd_610584 : Nat := 139343587531086364885325

theorem tailTrace_610584 : CollatzResearch.WordTrace tailWord_610584 prefixEnd_610584 139343587531086364885325 := by
  unfold tailWord_610584
  simp only [CollatzResearch.WordTrace]
  refine ⟨11134914009982961145099403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14846552013310614860132537 11134914009982961145099403)
  ·
    refine ⟨16702371014974441717649105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11134914009982961145099403 16702371014974441717649105)
    ·
      refine ⟨12526778261230831288236829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16702371014974441717649105 12526778261230831288236829)
      ·
        refine ⟨4697541847961561733088811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12526778261230831288236829 4697541847961561733088811)
        ·
          refine ⟨7046312771942342599633217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697541847961561733088811 7046312771942342599633217)
          ·
            refine ⟨5284734578956756949724913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7046312771942342599633217 5284734578956756949724913)
            ·
              refine ⟨3963550934217567712293685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5284734578956756949724913 3963550934217567712293685)
              ·
                refine ⟨371582900082896973027533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3963550934217567712293685 371582900082896973027533)
                ·
                  refine ⟨139343587531086364885325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371582900082896973027533 139343587531086364885325)
                  ·
                    rfl

theorem cell21_610584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 3].length) (baseStart_610584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610584 prefixEnd_610584 := by exact prefixLift 610584
  have htrace : WordTrace (prefixWord ++ tailWord_610584) baseStart_610584 baseEnd_610584 := by
    simpa [prefixWord, tailWord_610584, baseEnd_610584] using wordTrace_append hprefix tailTrace_610584
  have hstable : (prefixWord ++ tailWord_610584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610584).length < 2 ^ (prefixWord ++ tailWord_610584).sum := by decide
  have hdescent : baseEnd_610584 < baseStart_610584 := by decide
  rcases family_descends (prefixWord ++ tailWord_610584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610660 : List Nat := [2, 3, 1, 1, 3, 1, 1, 6, 3]
def baseStart_610660 : Nat := 118140960795 + 610660 * 2 ^ 59
def prefixEnd_610660 : Nat := 4983230072969 + 3 ^ 40 * 610660 * 2
def baseEnd_610660 : Nat := 139360931766527121618503

theorem tailTrace_610660 : CollatzResearch.WordTrace tailWord_610660 prefixEnd_610660 139360931766527121618503 := by
  unfold tailWord_610660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11136299983845293634982717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14848399978460391513310289 11136299983845293634982717)
  ·
    refine ⟨4176112493941985113118519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11136299983845293634982717 4176112493941985113118519)
    ·
      refine ⟨6264168740912977669677779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4176112493941985113118519 6264168740912977669677779)
      ·
        refine ⟨9396253111369466504516669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264168740912977669677779 9396253111369466504516669)
        ·
          refine ⟨3523594916763549939193751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9396253111369466504516669 3523594916763549939193751)
          ·
            refine ⟨5285392375145324908790627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523594916763549939193751 5285392375145324908790627)
            ·
              refine ⟨7928088562717987363185941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285392375145324908790627 7928088562717987363185941)
              ·
                refine ⟨371629151377405657649341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7928088562717987363185941 371629151377405657649341)
                ·
                  refine ⟨139360931766527121618503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371629151377405657649341 139360931766527121618503)
                  ·
                    rfl

theorem cell21_610660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_610660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610660 prefixEnd_610660 := by exact prefixLift 610660
  have htrace : WordTrace (prefixWord ++ tailWord_610660) baseStart_610660 baseEnd_610660 := by
    simpa [prefixWord, tailWord_610660, baseEnd_610660] using wordTrace_append hprefix tailTrace_610660
  have hstable : (prefixWord ++ tailWord_610660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610660).length < 2 ^ (prefixWord ++ tailWord_610660).sum := by decide
  have hdescent : baseEnd_610660 < baseStart_610660 := by decide
  rcases family_descends (prefixWord ++ tailWord_610660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610764 : List Nat := [2, 2, 1, 4, 3, 9]
def baseStart_610764 : Nat := 118140960795 + 610764 * 2 ^ 59
def prefixEnd_610764 : Nat := 4983230072969 + 3 ^ 40 * 610764 * 2
def baseEnd_610764 : Nat := 5162395036423927847591

theorem tailTrace_610764 : CollatzResearch.WordTrace tailWord_610764 prefixEnd_610764 5162395036423927847591 := by
  unfold tailWord_610764
  simp only [CollatzResearch.WordTrace]
  refine ⟨11138196579656906515875673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14850928772875875354500897 11138196579656906515875673)
  ·
    refine ⟨8353647434742679886906755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11138196579656906515875673 8353647434742679886906755)
    ·
      refine ⟨12530471152114019830360133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8353647434742679886906755 12530471152114019830360133)
      ·
        refine ⟨2349463341021378718192525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12530471152114019830360133 2349463341021378718192525)
        ·
          refine ⟨881048752883017019322197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2349463341021378718192525 881048752883017019322197)
          ·
            refine ⟨5162395036423927847591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 881048752883017019322197 5162395036423927847591)
            ·
              rfl

theorem cell21_610764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 9].length) (baseStart_610764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610764 prefixEnd_610764 := by exact prefixLift 610764
  have htrace : WordTrace (prefixWord ++ tailWord_610764) baseStart_610764 baseEnd_610764 := by
    simpa [prefixWord, tailWord_610764, baseEnd_610764] using wordTrace_append hprefix tailTrace_610764
  have hstable : (prefixWord ++ tailWord_610764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610764).length < 2 ^ (prefixWord ++ tailWord_610764).sum := by decide
  have hdescent : baseEnd_610764 < baseStart_610764 := by decide
  rcases family_descends (prefixWord ++ tailWord_610764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610770 : List Nat := [3, 2, 2, 4, 1, 1, 1, 4, 3]
def baseStart_610770 : Nat := 118140960795 + 610770 * 2 ^ 59
def prefixEnd_610770 : Nat := 4983230072969 + 3 ^ 40 * 610770 * 2
def baseEnd_610770 : Nat := 139386035265191374784945

theorem tailTrace_610770 : CollatzResearch.WordTrace tailWord_610770 prefixEnd_610770 139386035265191374784945 := by
  unfold tailWord_610770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5569152999323019014117441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14851074664861384037646509 5569152999323019014117441)
  ·
    refine ⟨4176864749492264260588081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5569152999323019014117441 4176864749492264260588081)
    ·
      refine ⟨3132648562119198195441061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4176864749492264260588081 3132648562119198195441061)
      ·
        refine ⟨587371605397349661645199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3132648562119198195441061 587371605397349661645199)
        ·
          refine ⟨881057408096024492467799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587371605397349661645199 881057408096024492467799)
          ·
            refine ⟨1321586112144036738701699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881057408096024492467799 1321586112144036738701699)
            ·
              refine ⟨1982379168216055108052549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321586112144036738701699 1982379168216055108052549)
              ·
                refine ⟨371696094040510332759853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1982379168216055108052549 371696094040510332759853)
                ·
                  refine ⟨139386035265191374784945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371696094040510332759853 139386035265191374784945)
                  ·
                    rfl

theorem cell21_610770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_610770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610770 prefixEnd_610770 := by exact prefixLift 610770
  have htrace : WordTrace (prefixWord ++ tailWord_610770) baseStart_610770 baseEnd_610770 := by
    simpa [prefixWord, tailWord_610770, baseEnd_610770] using wordTrace_append hprefix tailTrace_610770
  have hstable : (prefixWord ++ tailWord_610770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610770).length < 2 ^ (prefixWord ++ tailWord_610770).sum := by decide
  have hdescent : baseEnd_610770 < baseStart_610770 := by decide
  rcases family_descends (prefixWord ++ tailWord_610770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610829 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 5]
def baseStart_610829 : Nat := 118140960795 + 610829 * 2 ^ 59
def prefixEnd_610829 : Nat := 4983230072969 + 3 ^ 40 * 610829 * 2
def baseEnd_610829 : Nat := 139399499869020383301491

theorem tailTrace_610829 : CollatzResearch.WordTrace tailWord_610829 prefixEnd_610829 139399499869020383301491 := by
  unfold tailWord_610829
  simp only [CollatzResearch.WordTrace]
  refine ⟨22278763904078329132867541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14852509269385552755245027 22278763904078329132867541)
  ·
    refine ⟨522158529001835839051583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 22278763904078329132867541 522158529001835839051583)
    ·
      refine ⟨783237793502753758577375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 522158529001835839051583 783237793502753758577375)
      ·
        refine ⟨1174856690254130637866063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783237793502753758577375 1174856690254130637866063)
        ·
          refine ⟨1762285035381195956799095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174856690254130637866063 1762285035381195956799095)
          ·
            refine ⟨2643427553071793935198643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762285035381195956799095 2643427553071793935198643)
            ·
              refine ⟨3965141329607690902797965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2643427553071793935198643 3965141329607690902797965)
              ·
                refine ⟨1486927998602884088549237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3965141329607690902797965 1486927998602884088549237)
                ·
                  refine ⟨139399499869020383301491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1486927998602884088549237 139399499869020383301491)
                  ·
                    rfl

theorem cell21_610829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_610829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610829 prefixEnd_610829 := by exact prefixLift 610829
  have htrace : WordTrace (prefixWord ++ tailWord_610829) baseStart_610829 baseEnd_610829 := by
    simpa [prefixWord, tailWord_610829, baseEnd_610829] using wordTrace_append hprefix tailTrace_610829
  have hstable : (prefixWord ++ tailWord_610829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610829).length < 2 ^ (prefixWord ++ tailWord_610829).sum := by decide
  have hdescent : baseEnd_610829 < baseStart_610829 := by decide
  rcases family_descends (prefixWord ++ tailWord_610829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610885 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 6]
def baseStart_610885 : Nat := 118140960795 + 610885 * 2 ^ 59
def prefixEnd_610885 : Nat := 4983230072969 + 3 ^ 40 * 610885 * 2
def baseEnd_610885 : Nat := 139412279831976730368043

theorem tailTrace_610885 : CollatzResearch.WordTrace tailWord_610885 prefixEnd_610885 139412279831976730368043 := by
  unfold tailWord_610885
  simp only [CollatzResearch.WordTrace]
  refine ⟨22280806391875450696906109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14853870927916967131270739 22280806391875450696906109)
  ·
    refine ⟨8355302396953294011339791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22280806391875450696906109 8355302396953294011339791)
    ·
      refine ⟨12532953595429941017009687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8355302396953294011339791 12532953595429941017009687)
      ·
        refine ⟨18799430393144911525514531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12532953595429941017009687 18799430393144911525514531)
        ·
          refine ⟨28199145589717367288271797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18799430393144911525514531 28199145589717367288271797)
          ·
            refine ⟨2643669899036003183275481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28199145589717367288271797 2643669899036003183275481)
            ·
              refine ⟨1982752424277002387456611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2643669899036003183275481 1982752424277002387456611)
              ·
                refine ⟨2974128636415503581184917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982752424277002387456611 2974128636415503581184917)
                ·
                  refine ⟨139412279831976730368043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2974128636415503581184917 139412279831976730368043)
                  ·
                    rfl

theorem cell21_610885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_610885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610885 prefixEnd_610885 := by exact prefixLift 610885
  have htrace : WordTrace (prefixWord ++ tailWord_610885) baseStart_610885 baseEnd_610885 := by
    simpa [prefixWord, tailWord_610885, baseEnd_610885] using wordTrace_append hprefix tailTrace_610885
  have hstable : (prefixWord ++ tailWord_610885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610885).length < 2 ^ (prefixWord ++ tailWord_610885).sum := by decide
  have hdescent : baseEnd_610885 < baseStart_610885 := by decide
  rcases family_descends (prefixWord ++ tailWord_610885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610933 : List Nat := [1, 3, 4, 2, 3, 8]
def baseStart_610933 : Nat := 118140960795 + 610933 * 2 ^ 59
def prefixEnd_610933 : Nat := 4983230072969 + 3 ^ 40 * 610933 * 2
def baseEnd_610933 : Nat := 5163823484664419021035

theorem tailTrace_610933 : CollatzResearch.WordTrace tailWord_610933 prefixEnd_610933 5163823484664419021035 := by
  unfold tailWord_610933
  simp only [CollatzResearch.WordTrace]
  refine ⟨22282557095701554894653453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14855038063801036596435635 22282557095701554894653453)
  ·
    refine ⟨8355958910888083085495045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22282557095701554894653453 8355958910888083085495045)
    ·
      refine ⟨1566742295791515578530321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8355958910888083085495045 1566742295791515578530321)
      ·
        refine ⟨1175056721843636683897741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1566742295791515578530321 1175056721843636683897741)
        ·
          refine ⟨440646270691363756461653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1175056721843636683897741 440646270691363756461653)
          ·
            refine ⟨5163823484664419021035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 440646270691363756461653 5163823484664419021035)
            ·
              rfl

theorem cell21_610933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 8].length) (baseStart_610933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610933 prefixEnd_610933 := by exact prefixLift 610933
  have htrace : WordTrace (prefixWord ++ tailWord_610933) baseStart_610933 baseEnd_610933 := by
    simpa [prefixWord, tailWord_610933, baseEnd_610933] using wordTrace_append hprefix tailTrace_610933
  have hstable : (prefixWord ++ tailWord_610933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610933).length < 2 ^ (prefixWord ++ tailWord_610933).sum := by decide
  have hdescent : baseEnd_610933 < baseStart_610933 := by decide
  rcases family_descends (prefixWord ++ tailWord_610933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610964 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 5]
def baseStart_610964 : Nat := 118140960795 + 610964 * 2 ^ 59
def prefixEnd_610964 : Nat := 4983230072969 + 3 ^ 40 * 610964 * 2
def baseEnd_610964 : Nat := 139430308708290148551215

theorem tailTrace_610964 : CollatzResearch.WordTrace tailWord_610964 prefixEnd_610964 139430308708290148551215 := by
  unfold tailWord_610964
  simp only [CollatzResearch.WordTrace]
  refine ⟨11141843879294623594515973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14855791839059498126021297 11141843879294623594515973)
  ·
    refine ⟨2089095727367741923971745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11141843879294623594515973 2089095727367741923971745)
    ·
      refine ⟨1566821795525806442978809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2089095727367741923971745 1566821795525806442978809)
      ·
        refine ⟨1175116346644354832234107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1566821795525806442978809 1175116346644354832234107)
        ·
          refine ⟨1762674519966532248351161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175116346644354832234107 1762674519966532248351161)
          ·
            refine ⟨1322005889974899186263371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1762674519966532248351161 1322005889974899186263371)
            ·
              refine ⟨1983008834962348779395057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322005889974899186263371 1983008834962348779395057)
              ·
                refine ⟨1487256626221761584546293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1983008834962348779395057 1487256626221761584546293)
                ·
                  refine ⟨139430308708290148551215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1487256626221761584546293 139430308708290148551215)
                  ·
                    rfl

theorem cell21_610964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_610964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_610964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_610964 prefixEnd_610964 := by exact prefixLift 610964
  have htrace : WordTrace (prefixWord ++ tailWord_610964) baseStart_610964 baseEnd_610964 := by
    simpa [prefixWord, tailWord_610964, baseEnd_610964] using wordTrace_append hprefix tailTrace_610964
  have hstable : (prefixWord ++ tailWord_610964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610964).length < 2 ^ (prefixWord ++ tailWord_610964).sum := by decide
  have hdescent : baseEnd_610964 < baseStart_610964 := by decide
  rcases family_descends (prefixWord ++ tailWord_610964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611026 : List Nat := [3, 2, 2, 2, 3, 2, 2, 5]
def baseStart_611026 : Nat := 118140960795 + 611026 * 2 ^ 59
def prefixEnd_611026 : Nat := 4983230072969 + 3 ^ 40 * 611026 * 2
def baseEnd_611026 : Nat := 46481485984330606172585

theorem tailTrace_611026 : CollatzResearch.WordTrace tailWord_611026 prefixEnd_611026 46481485984330606172585 := by
  unfold tailWord_611026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5571487271091157944447233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14857299389576421185192621 5571487271091157944447233)
  ·
    refine ⟨4178615453318368458335425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5571487271091157944447233 4178615453318368458335425)
    ·
      refine ⟨3133961589988776343751569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4178615453318368458335425 3133961589988776343751569)
      ·
        refine ⟨2350471192491582257813677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3133961589988776343751569 2350471192491582257813677)
        ·
          refine ⟨881426697184343346680129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2350471192491582257813677 881426697184343346680129)
          ·
            refine ⟨661070022888257510010097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881426697184343346680129 661070022888257510010097)
            ·
              refine ⟨495802517166193132507573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661070022888257510010097 495802517166193132507573)
              ·
                refine ⟨46481485984330606172585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 495802517166193132507573 46481485984330606172585)
                ·
                  rfl

theorem cell21_611026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_611026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611026 prefixEnd_611026 := by exact prefixLift 611026
  have htrace : WordTrace (prefixWord ++ tailWord_611026) baseStart_611026 baseEnd_611026 := by
    simpa [prefixWord, tailWord_611026, baseEnd_611026] using wordTrace_append hprefix tailTrace_611026
  have hstable : (prefixWord ++ tailWord_611026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611026).length < 2 ^ (prefixWord ++ tailWord_611026).sum := by decide
  have hdescent : baseEnd_611026 < baseStart_611026 := by decide
  rcases family_descends (prefixWord ++ tailWord_611026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611068 : List Nat := [2, 2, 2, 1, 3, 3, 2, 6]
def baseStart_611068 : Nat := 118140960795 + 611068 * 2 ^ 59
def prefixEnd_611068 : Nat := 4983230072969 + 3 ^ 40 * 611068 * 2
def baseEnd_611068 : Nat := 46484680975069692939223

theorem tailTrace_611068 : CollatzResearch.WordTrace tailWord_611068 prefixEnd_611068 46484680975069692939223 := by
  unfold tailWord_611068
  simp only [CollatzResearch.WordTrace]
  refine ⟨11143740475106236475408929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14858320633474981967211905 11143740475106236475408929)
  ·
    refine ⟨8357805356329677356556697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11143740475106236475408929 8357805356329677356556697)
    ·
      refine ⟨6268354017247258017417523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8357805356329677356556697 6268354017247258017417523)
      ·
        refine ⟨9402531025870887026126285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6268354017247258017417523 9402531025870887026126285)
        ·
          refine ⟨3525949134701582634797357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9402531025870887026126285 3525949134701582634797357)
          ·
            refine ⟨1322230925513093488049009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3525949134701582634797357 1322230925513093488049009)
            ·
              refine ⟨991673194134820116036757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1322230925513093488049009 991673194134820116036757)
              ·
                refine ⟨46484680975069692939223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 991673194134820116036757 46484680975069692939223)
                ·
                  rfl

theorem cell21_611068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_611068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611068 prefixEnd_611068 := by exact prefixLift 611068
  have htrace : WordTrace (prefixWord ++ tailWord_611068) baseStart_611068 baseEnd_611068 := by
    simpa [prefixWord, tailWord_611068, baseEnd_611068] using wordTrace_append hprefix tailTrace_611068
  have hstable : (prefixWord ++ tailWord_611068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611068).length < 2 ^ (prefixWord ++ tailWord_611068).sum := by decide
  have hdescent : baseEnd_611068 < baseStart_611068 := by decide
  rcases family_descends (prefixWord ++ tailWord_611068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611082 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_611082 : Nat := 118140960795 + 611082 * 2 ^ 59
def prefixEnd_611082 : Nat := 4983230072969 + 3 ^ 40 * 611082 * 2
def baseEnd_611082 : Nat := 139457237915948165584307

theorem tailTrace_611082 : CollatzResearch.WordTrace tailWord_611082 prefixEnd_611082 139457237915948165584307 := by
  unfold tailWord_611082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5571997893040438335456875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14858661048107835561218333 5571997893040438335456875)
  ·
    refine ⟨8357996839560657503185313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5571997893040438335456875 8357996839560657503185313)
    ·
      refine ⟨6268497629670493127388985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8357996839560657503185313 6268497629670493127388985)
      ·
        refine ⟨4701373222252869845541739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6268497629670493127388985 4701373222252869845541739)
        ·
          refine ⟨7052059833379304768312609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4701373222252869845541739 7052059833379304768312609)
          ·
            refine ⟨5289044875034478576234457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7052059833379304768312609 5289044875034478576234457)
            ·
              refine ⟨3966783656275858932175843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5289044875034478576234457 3966783656275858932175843)
              ·
                refine ⟨5950175484413788398263765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3966783656275858932175843 5950175484413788398263765)
                ·
                  refine ⟨139457237915948165584307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5950175484413788398263765 139457237915948165584307)
                  ·
                    rfl

theorem cell21_611082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_611082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611082 prefixEnd_611082 := by exact prefixLift 611082
  have htrace : WordTrace (prefixWord ++ tailWord_611082) baseStart_611082 baseEnd_611082 := by
    simpa [prefixWord, tailWord_611082, baseEnd_611082] using wordTrace_append hprefix tailTrace_611082
  have hstable : (prefixWord ++ tailWord_611082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611082).length < 2 ^ (prefixWord ++ tailWord_611082).sum := by decide
  have hdescent : baseEnd_611082 < baseStart_611082 := by decide
  rcases family_descends (prefixWord ++ tailWord_611082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611144 : List Nat := [2, 1, 3, 1, 1, 3, 5, 5]
def baseStart_611144 : Nat := 118140960795 + 611144 * 2 ^ 59
def prefixEnd_611144 : Nat := 4983230072969 + 3 ^ 40 * 611144 * 2
def baseEnd_611144 : Nat := 46490462386883278516949

theorem tailTrace_611144 : CollatzResearch.WordTrace tailWord_611144 prefixEnd_611144 46490462386883278516949 := by
  unfold tailWord_611144
  simp only [CollatzResearch.WordTrace]
  refine ⟨11145126448968568965292243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14860168598624758620389657 11145126448968568965292243)
  ·
    refine ⟨16717689673452853447938365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11145126448968568965292243 16717689673452853447938365)
    ·
      refine ⟨6269133627544820042976887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16717689673452853447938365 6269133627544820042976887)
      ·
        refine ⟨9403700441317230064465331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6269133627544820042976887 9403700441317230064465331)
        ·
          refine ⟨14105550661975845096697997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9403700441317230064465331 14105550661975845096697997)
          ·
            refine ⟨5289581498240941911261749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14105550661975845096697997 5289581498240941911261749)
            ·
              refine ⟨495898265460088304180789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5289581498240941911261749 495898265460088304180789)
              ·
                refine ⟨46490462386883278516949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 495898265460088304180789 46490462386883278516949)
                ·
                  rfl

theorem cell21_611144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_611144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611144 prefixEnd_611144 := by exact prefixLift 611144
  have htrace : WordTrace (prefixWord ++ tailWord_611144) baseStart_611144 baseEnd_611144 := by
    simpa [prefixWord, tailWord_611144, baseEnd_611144] using wordTrace_append hprefix tailTrace_611144
  have hstable : (prefixWord ++ tailWord_611144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611144).length < 2 ^ (prefixWord ++ tailWord_611144).sum := by decide
  have hdescent : baseEnd_611144 < baseStart_611144 := by decide
  rcases family_descends (prefixWord ++ tailWord_611144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611175 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 5]
def baseStart_611175 : Nat := 118140960795 + 611175 * 2 ^ 59
def prefixEnd_611175 : Nat := 4983230072969 + 3 ^ 40 * 611175 * 2
def baseEnd_611175 : Nat := 139478461783000670534117

theorem tailTrace_611175 : CollatzResearch.WordTrace tailWord_611175 prefixEnd_611175 139478461783000670534117 := by
  unfold tailWord_611175
  simp only [CollatzResearch.WordTrace]
  refine ⟨22291383560824830224962979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14860922373883220149975319 22291383560824830224962979)
  ·
    refine ⟨33437075341237245337444469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22291383560824830224962979 33437075341237245337444469)
    ·
      refine ⟨3134725813240991750385419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33437075341237245337444469 3134725813240991750385419)
      ·
        refine ⟨4702088719861487625578129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3134725813240991750385419 4702088719861487625578129)
        ·
          refine ⟨3526566539896115719183597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4702088719861487625578129 3526566539896115719183597)
          ·
            refine ⟨1322462452461043394693849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3526566539896115719183597 1322462452461043394693849)
            ·
              refine ⟨991846839345782546020387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1322462452461043394693849 991846839345782546020387)
              ·
                refine ⟨1487770259018673819030581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991846839345782546020387 1487770259018673819030581)
                ·
                  refine ⟨139478461783000670534117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1487770259018673819030581 139478461783000670534117)
                  ·
                    rfl

theorem cell21_611175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 5].length) (baseStart_611175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611175 prefixEnd_611175 := by exact prefixLift 611175
  have htrace : WordTrace (prefixWord ++ tailWord_611175) baseStart_611175 baseEnd_611175 := by
    simpa [prefixWord, tailWord_611175, baseEnd_611175] using wordTrace_append hprefix tailTrace_611175
  have hstable : (prefixWord ++ tailWord_611175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611175).length < 2 ^ (prefixWord ++ tailWord_611175).sum := by decide
  have hdescent : baseEnd_611175 < baseStart_611175 := by decide
  rcases family_descends (prefixWord ++ tailWord_611175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611203 : List Nat := [1, 1, 1, 3, 4, 1, 3, 7]
def baseStart_611203 : Nat := 118140960795 + 611203 * 2 ^ 59
def prefixEnd_611203 : Nat := 4983230072969 + 3 ^ 40 * 611203 * 2
def baseEnd_611203 : Nat := 46494950588159614689131

theorem tailTrace_611203 : CollatzResearch.WordTrace tailWord_611203 prefixEnd_611203 46494950588159614689131 := by
  unfold tailWord_611203
  simp only [CollatzResearch.WordTrace]
  refine ⟨22292404804723391006982263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14861603203148927337988175 22292404804723391006982263)
  ·
    refine ⟨33438607207085086510473395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22292404804723391006982263 33438607207085086510473395)
    ·
      refine ⟨50157910810627629765710093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33438607207085086510473395 50157910810627629765710093)
      ·
        refine ⟨18809216553985361162141285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50157910810627629765710093 18809216553985361162141285)
        ·
          refine ⟨3526728103872255217901491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18809216553985361162141285 3526728103872255217901491)
          ·
            refine ⟨5290092155808382826852237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3526728103872255217901491 5290092155808382826852237)
            ·
              refine ⟨1983784558428143560069589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5290092155808382826852237 1983784558428143560069589)
              ·
                refine ⟨46494950588159614689131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1983784558428143560069589 46494950588159614689131)
                ·
                  rfl

theorem cell21_611203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 7].length) (baseStart_611203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611203 prefixEnd_611203 := by exact prefixLift 611203
  have htrace : WordTrace (prefixWord ++ tailWord_611203) baseStart_611203 baseEnd_611203 := by
    simpa [prefixWord, tailWord_611203, baseEnd_611203] using wordTrace_append hprefix tailTrace_611203
  have hstable : (prefixWord ++ tailWord_611203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611203).length < 2 ^ (prefixWord ++ tailWord_611203).sum := by decide
  have hdescent : baseEnd_611203 < baseStart_611203 := by decide
  rcases family_descends (prefixWord ++ tailWord_611203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611277 : List Nat := [1, 6, 3, 1, 2, 1, 2, 2, 3]
def baseStart_611277 : Nat := 118140960795 + 611277 * 2 ^ 59
def prefixEnd_611277 : Nat := 4983230072969 + 3 ^ 40 * 611277 * 2
def baseEnd_611277 : Nat := 139501739572671159833909

theorem tailTrace_611277 : CollatzResearch.WordTrace tailWord_611277 prefixEnd_611277 139501739572671159833909 := by
  unfold tailWord_611277
  simp only [CollatzResearch.WordTrace]
  refine ⟨22295103806455301645176085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14863402537636867763450723 22295103806455301645176085)
  ·
    refine ⟨1045082990927592264617629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22295103806455301645176085 1045082990927592264617629)
    ·
      refine ⟨391906121597847099231611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1045082990927592264617629 391906121597847099231611)
      ·
        refine ⟨587859182396770648847417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391906121597847099231611 587859182396770648847417)
        ·
          refine ⟨440894386797577986635563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587859182396770648847417 440894386797577986635563)
          ·
            refine ⟨661341580196366979953345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440894386797577986635563 661341580196366979953345)
            ·
              refine ⟨496006185147275234965009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661341580196366979953345 496006185147275234965009)
              ·
                refine ⟨372004638860456426223757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496006185147275234965009 372004638860456426223757)
                ·
                  refine ⟨139501739572671159833909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372004638860456426223757 139501739572671159833909)
                  ·
                    rfl

theorem cell21_611277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_611277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611277 prefixEnd_611277 := by exact prefixLift 611277
  have htrace : WordTrace (prefixWord ++ tailWord_611277) baseStart_611277 baseEnd_611277 := by
    simpa [prefixWord, tailWord_611277, baseEnd_611277] using wordTrace_append hprefix tailTrace_611277
  have hstable : (prefixWord ++ tailWord_611277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611277).length < 2 ^ (prefixWord ++ tailWord_611277).sum := by decide
  have hdescent : baseEnd_611277 < baseStart_611277 := by decide
  rcases family_descends (prefixWord ++ tailWord_611277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611282 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_611282 : Nat := 118140960795 + 611282 * 2 ^ 59
def prefixEnd_611282 : Nat := 4983230072969 + 3 ^ 40 * 611282 * 2
def baseEnd_611282 : Nat := 139502880640792262250565

theorem tailTrace_611282 : CollatzResearch.WordTrace tailWord_611282 prefixEnd_611282 139502880640792262250565 := by
  unfold tailWord_611282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5573821542859296874777025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14863524114291458332738733 5573821542859296874777025)
  ·
    refine ⟨4180366157144472656082769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5573821542859296874777025 4180366157144472656082769)
    ·
      refine ⟨3135274617858354492062077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4180366157144472656082769 3135274617858354492062077)
      ·
        refine ⟨1175727981696882934523279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3135274617858354492062077 1175727981696882934523279)
        ·
          refine ⟨1763591972545324401784919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175727981696882934523279 1763591972545324401784919)
          ·
            refine ⟨2645387958817986602677379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763591972545324401784919 2645387958817986602677379)
            ·
              refine ⟨3968081938226979904016069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645387958817986602677379 3968081938226979904016069)
              ·
                refine ⟨744015363417558732003013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3968081938226979904016069 744015363417558732003013)
                ·
                  refine ⟨139502880640792262250565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 744015363417558732003013 139502880640792262250565)
                  ·
                    rfl

theorem cell21_611282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_611282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611282 prefixEnd_611282 := by exact prefixLift 611282
  have htrace : WordTrace (prefixWord ++ tailWord_611282) baseStart_611282 baseEnd_611282 := by
    simpa [prefixWord, tailWord_611282, baseEnd_611282] using wordTrace_append hprefix tailTrace_611282
  have hstable : (prefixWord ++ tailWord_611282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611282).length < 2 ^ (prefixWord ++ tailWord_611282).sum := by decide
  have hdescent : baseEnd_611282 < baseStart_611282 := by decide
  rcases family_descends (prefixWord ++ tailWord_611282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611400 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_611400 : Nat := 118140960795 + 611400 * 2 ^ 59
def prefixEnd_611400 : Nat := 4983230072969 + 3 ^ 40 * 611400 * 2
def baseEnd_611400 : Nat := 139529809848450279283657

theorem tailTrace_611400 : CollatzResearch.WordTrace tailWord_611400 prefixEnd_611400 139529809848450279283657 := by
  unfold tailWord_611400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11149794992504846825951827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14866393323339795767935769 11149794992504846825951827)
  ·
    refine ⟨16724692488757270238927741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11149794992504846825951827 16724692488757270238927741)
    ·
      refine ⟨6271759683283976339597903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16724692488757270238927741 6271759683283976339597903)
      ·
        refine ⟨9407639524925964509396855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6271759683283976339597903 9407639524925964509396855)
        ·
          refine ⟨14111459287388946764095283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9407639524925964509396855 14111459287388946764095283)
          ·
            refine ⟨21167188931083420146142925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14111459287388946764095283 21167188931083420146142925)
            ·
              refine ⟨7937695849156282554803597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21167188931083420146142925 7937695849156282554803597)
              ·
                refine ⟨2976635943433605958051349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7937695849156282554803597 2976635943433605958051349)
                ·
                  refine ⟨139529809848450279283657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2976635943433605958051349 139529809848450279283657)
                  ·
                    rfl

theorem cell21_611400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_611400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611400 prefixEnd_611400 := by exact prefixLift 611400
  have htrace : WordTrace (prefixWord ++ tailWord_611400) baseStart_611400 baseEnd_611400 := by
    simpa [prefixWord, tailWord_611400, baseEnd_611400] using wordTrace_append hprefix tailTrace_611400
  have hstable : (prefixWord ++ tailWord_611400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611400).length < 2 ^ (prefixWord ++ tailWord_611400).sum := by decide
  have hdescent : baseEnd_611400 < baseStart_611400 := by decide
  rcases family_descends (prefixWord ++ tailWord_611400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611431 : List Nat := [1, 1, 5, 1, 1, 3, 2, 7]
def baseStart_611431 : Nat := 118140960795 + 611431 * 2 ^ 59
def prefixEnd_611431 : Nat := 4983230072969 + 3 ^ 40 * 611431 * 2
def baseEnd_611431 : Nat := 46512294823600371422309

theorem tailTrace_611431 : CollatzResearch.WordTrace tailWord_611431 prefixEnd_611431 46512294823600371422309 := by
  unfold tailWord_611431
  simp only [CollatzResearch.WordTrace]
  refine ⟨22300720647897385946282147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14867147098598257297521431 22300720647897385946282147)
  ·
    refine ⟨33451080971846078919423221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22300720647897385946282147 33451080971846078919423221)
    ·
      refine ⟨3136038841110569898695927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33451080971846078919423221 3136038841110569898695927)
      ·
        refine ⟨4704058261665854848043891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3136038841110569898695927 4704058261665854848043891)
        ·
          refine ⟨7056087392498782272065837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704058261665854848043891 7056087392498782272065837)
          ·
            refine ⟨2646032772187043352024689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7056087392498782272065837 2646032772187043352024689)
            ·
              refine ⟨1984524579140282514018517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2646032772187043352024689 1984524579140282514018517)
              ·
                refine ⟨46512294823600371422309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1984524579140282514018517 46512294823600371422309)
                ·
                  rfl

theorem cell21_611431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 7].length) (baseStart_611431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611431 prefixEnd_611431 := by exact prefixLift 611431
  have htrace : WordTrace (prefixWord ++ tailWord_611431) baseStart_611431 baseEnd_611431 := by
    simpa [prefixWord, tailWord_611431, baseEnd_611431] using wordTrace_append hprefix tailTrace_611431
  have hstable : (prefixWord ++ tailWord_611431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611431).length < 2 ^ (prefixWord ++ tailWord_611431).sum := by decide
  have hdescent : baseEnd_611431 < baseStart_611431 := by decide
  rcases family_descends (prefixWord ++ tailWord_611431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611538 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_611538 : Nat := 118140960795 + 611538 * 2 ^ 59
def prefixEnd_611538 : Nat := 4983230072969 + 3 ^ 40 * 611538 * 2
def baseEnd_611538 : Nat := 139561303328592705983375

theorem tailTrace_611538 : CollatzResearch.WordTrace tailWord_611538 prefixEnd_611538 139561303328592705983375 := by
  unfold tailWord_611538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5576155814627435805106817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14869748839006495480284845 5576155814627435805106817)
  ·
    refine ⟨4182116860970576853830113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5576155814627435805106817 4182116860970576853830113)
    ·
      refine ⟨3136587645727932640372585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4182116860970576853830113 3136587645727932640372585)
      ·
        refine ⟨2352440734295949480279439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3136587645727932640372585 2352440734295949480279439)
        ·
          refine ⟨3528661101443924220419159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2352440734295949480279439 3528661101443924220419159)
          ·
            refine ⟨5292991652165886330628739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528661101443924220419159 5292991652165886330628739)
            ·
              refine ⟨7939487478248829495943109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5292991652165886330628739 7939487478248829495943109)
              ·
                refine ⟨1488653902171655530489333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7939487478248829495943109 1488653902171655530489333)
                ·
                  refine ⟨139561303328592705983375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1488653902171655530489333 139561303328592705983375)
                  ·
                    rfl

theorem cell21_611538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_611538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611538 prefixEnd_611538 := by exact prefixLift 611538
  have htrace : WordTrace (prefixWord ++ tailWord_611538) baseStart_611538 baseEnd_611538 := by
    simpa [prefixWord, tailWord_611538, baseEnd_611538] using wordTrace_append hprefix tailTrace_611538
  have hstable : (prefixWord ++ tailWord_611538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611538).length < 2 ^ (prefixWord ++ tailWord_611538).sum := by decide
  have hdescent : baseEnd_611538 < baseStart_611538 := by decide
  rcases family_descends (prefixWord ++ tailWord_611538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611541 : List Nat := [1, 3, 2, 4, 1, 3, 2, 5]
def baseStart_611541 : Nat := 118140960795 + 611541 * 2 ^ 59
def prefixEnd_611541 : Nat := 4983230072969 + 3 ^ 40 * 611541 * 2
def baseEnd_611541 : Nat := 46520662656488455811123

theorem tailTrace_611541 : CollatzResearch.WordTrace tailWord_611541 prefixEnd_611541 46520662656488455811123 := by
  unfold tailWord_611541
  simp only [CollatzResearch.WordTrace]
  refine ⟨22304732677498874732786477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14869821784999249821857651 22304732677498874732786477)
  ·
    refine ⟨8364274754062078024794929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22304732677498874732786477 8364274754062078024794929)
    ·
      refine ⟨6273206065546558518596197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8364274754062078024794929 6273206065546558518596197)
      ·
        refine ⟨1176226137289979722236787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6273206065546558518596197 1176226137289979722236787)
        ·
          refine ⟨1764339205934969583355181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176226137289979722236787 1764339205934969583355181)
          ·
            refine ⟨661627202225613593758193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1764339205934969583355181 661627202225613593758193)
            ·
              refine ⟨496220401669210195318645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661627202225613593758193 496220401669210195318645)
              ·
                refine ⟨46520662656488455811123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 496220401669210195318645 46520662656488455811123)
                ·
                  rfl

theorem cell21_611541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 5].length) (baseStart_611541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611541 prefixEnd_611541 := by exact prefixLift 611541
  have htrace : WordTrace (prefixWord ++ tailWord_611541) baseStart_611541 baseEnd_611541 := by
    simpa [prefixWord, tailWord_611541, baseEnd_611541] using wordTrace_append hprefix tailTrace_611541
  have hstable : (prefixWord ++ tailWord_611541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611541).length < 2 ^ (prefixWord ++ tailWord_611541).sum := by decide
  have hdescent : baseEnd_611541 < baseStart_611541 := by decide
  rcases family_descends (prefixWord ++ tailWord_611541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611552 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_611552 : Nat := 118140960795 + 611552 * 2 ^ 59
def prefixEnd_611552 : Nat := 4983230072969 + 3 ^ 40 * 611552 * 2
def baseEnd_611552 : Nat := 139564498319331792750013

theorem tailTrace_611552 : CollatzResearch.WordTrace tailWord_611552 prefixEnd_611552 139564498319331792750013 := by
  unfold tailWord_611552
  simp only [CollatzResearch.WordTrace]
  refine ⟨11152566940229511805718455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14870089253639349074291273 11152566940229511805718455)
  ·
    refine ⟨16728850410344267708577683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11152566940229511805718455 16728850410344267708577683)
    ·
      refine ⟨25093275615516401562866525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16728850410344267708577683 25093275615516401562866525)
      ·
        refine ⟨9409978355818650586074947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25093275615516401562866525 9409978355818650586074947)
        ·
          refine ⟨14114967533727975879112421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9409978355818650586074947 14114967533727975879112421)
          ·
            refine ⟨2646556412573995477333579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14114967533727975879112421 2646556412573995477333579)
            ·
              refine ⟨3969834618860993216000369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646556412573995477333579 3969834618860993216000369)
              ·
                refine ⟨2977375964145744912000277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3969834618860993216000369 2977375964145744912000277)
                ·
                  refine ⟨139564498319331792750013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2977375964145744912000277 139564498319331792750013)
                  ·
                    rfl

theorem cell21_611552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_611552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611552 prefixEnd_611552 := by exact prefixLift 611552
  have htrace : WordTrace (prefixWord ++ tailWord_611552) baseStart_611552 baseEnd_611552 := by
    simpa [prefixWord, tailWord_611552, baseEnd_611552] using wordTrace_append hprefix tailTrace_611552
  have hstable : (prefixWord ++ tailWord_611552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611552).length < 2 ^ (prefixWord ++ tailWord_611552).sum := by decide
  have hdescent : baseEnd_611552 < baseStart_611552 := by decide
  rcases family_descends (prefixWord ++ tailWord_611552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611583 : List Nat := [1, 1, 2, 2, 1, 6, 2, 6]
def baseStart_611583 : Nat := 118140960795 + 611583 * 2 ^ 59
def prefixEnd_611583 : Nat := 4983230072969 + 3 ^ 40 * 611583 * 2
def baseEnd_611583 : Nat := 46523857647227542577761

theorem tailTrace_611583 : CollatzResearch.WordTrace tailWord_611583 prefixEnd_611583 46523857647227542577761 := by
  unfold tailWord_611583
  simp only [CollatzResearch.WordTrace]
  refine ⟨22306264543346715905815403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14870843028897810603876935 22306264543346715905815403)
  ·
    refine ⟨33459396815020073858723105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22306264543346715905815403 33459396815020073858723105)
    ·
      refine ⟨25094547611265055394042329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33459396815020073858723105 25094547611265055394042329)
      ·
        refine ⟨18820910708448791545531747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25094547611265055394042329 18820910708448791545531747)
        ·
          refine ⟨28231366062673187318297621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18820910708448791545531747 28231366062673187318297621)
          ·
            refine ⟨1323345284187805655545201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28231366062673187318297621 1323345284187805655545201)
            ·
              refine ⟨992508963140854241658901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1323345284187805655545201 992508963140854241658901)
              ·
                refine ⟨46523857647227542577761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 992508963140854241658901 46523857647227542577761)
                ·
                  rfl

theorem cell21_611583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 6].length) (baseStart_611583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611583 prefixEnd_611583 := by exact prefixLift 611583
  have htrace : WordTrace (prefixWord ++ tailWord_611583) baseStart_611583 baseEnd_611583 := by
    simpa [prefixWord, tailWord_611583, baseEnd_611583] using wordTrace_append hprefix tailTrace_611583
  have hstable : (prefixWord ++ tailWord_611583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611583).length < 2 ^ (prefixWord ++ tailWord_611583).sum := by decide
  have hdescent : baseEnd_611583 < baseStart_611583 := by decide
  rcases family_descends (prefixWord ++ tailWord_611583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611749 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 5]
def baseStart_611749 : Nat := 118140960795 + 611749 * 2 ^ 59
def prefixEnd_611749 : Nat := 4983230072969 + 3 ^ 40 * 611749 * 2
def baseEnd_611749 : Nat := 139609456403303227966277

theorem tailTrace_611749 : CollatzResearch.WordTrace tailWord_611749 prefixEnd_611749 139609456403303227966277 := by
  unfold tailWord_611749
  simp only [CollatzResearch.WordTrace]
  refine ⟨22312319060745326256358301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14874879373830217504238867 22312319060745326256358301)
  ·
    refine ⟨8367119647779497346134363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22312319060745326256358301 8367119647779497346134363)
    ·
      refine ⟨12550679471669246019201545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8367119647779497346134363 12550679471669246019201545)
      ·
        refine ⟨9413009603751934514401159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12550679471669246019201545 9413009603751934514401159)
        ·
          refine ⟨14119514405627901771601739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9413009603751934514401159 14119514405627901771601739)
          ·
            refine ⟨21179271608441852657402609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14119514405627901771601739 21179271608441852657402609)
            ·
              refine ⟨15884453706331389493051957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21179271608441852657402609 15884453706331389493051957)
              ·
                refine ⟨1489167534968567764973621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15884453706331389493051957 1489167534968567764973621)
                ·
                  refine ⟨139609456403303227966277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1489167534968567764973621 139609456403303227966277)
                  ·
                    rfl

theorem cell21_611749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_611749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611749 prefixEnd_611749 := by exact prefixLift 611749
  have htrace : WordTrace (prefixWord ++ tailWord_611749) baseStart_611749 baseEnd_611749 := by
    simpa [prefixWord, tailWord_611749, baseEnd_611749] using wordTrace_append hprefix tailTrace_611749
  have hstable : (prefixWord ++ tailWord_611749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611749).length < 2 ^ (prefixWord ++ tailWord_611749).sum := by decide
  have hdescent : baseEnd_611749 < baseStart_611749 := by decide
  rcases family_descends (prefixWord ++ tailWord_611749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611794 : List Nat := [3, 2, 2, 14]
def baseStart_611794 : Nat := 118140960795 + 611794 * 2 ^ 59
def prefixEnd_611794 : Nat := 4983230072969 + 3 ^ 40 * 611794 * 2
def baseEnd_611794 : Nat := 574566773730012961795

theorem tailTrace_611794 : CollatzResearch.WordTrace tailWord_611794 prefixEnd_611794 574566773730012961795 := by
  unfold tailWord_611794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5578490086395574735436609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14875973563721532627830957 5578490086395574735436609)
  ·
    refine ⟨4183867564796681051577457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5578490086395574735436609 4183867564796681051577457)
    ·
      refine ⟨3137900673597510788683093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4183867564796681051577457 3137900673597510788683093)
      ·
        refine ⟨574566773730012961795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 3137900673597510788683093 574566773730012961795)
        ·
          rfl

theorem cell21_611794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 14].length) (baseStart_611794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611794 prefixEnd_611794 := by exact prefixLift 611794
  have htrace : WordTrace (prefixWord ++ tailWord_611794) baseStart_611794 baseEnd_611794 := by
    simpa [prefixWord, tailWord_611794, baseEnd_611794] using wordTrace_append hprefix tailTrace_611794
  have hstable : (prefixWord ++ tailWord_611794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611794).length < 2 ^ (prefixWord ++ tailWord_611794).sum := by decide
  have hdescent : baseEnd_611794 < baseStart_611794 := by decide
  rcases family_descends (prefixWord ++ tailWord_611794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611797 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 4]
def baseStart_611797 : Nat := 118140960795 + 611797 * 2 ^ 59
def prefixEnd_611797 : Nat := 4983230072969 + 3 ^ 40 * 611797 * 2
def baseEnd_611797 : Nat := 139620410657265811166179

theorem tailTrace_611797 : CollatzResearch.WordTrace tailWord_611797 prefixEnd_611797 139620410657265811166179 := by
  unfold tailWord_611797
  simp only [CollatzResearch.WordTrace]
  refine ⟨22314069764571430454105645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14876046509714286969403763 22314069764571430454105645)
  ·
    refine ⟨8367776161714286420289617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22314069764571430454105645 8367776161714286420289617)
    ·
      refine ⟨6275832121285714815217213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8367776161714286420289617 6275832121285714815217213)
      ·
        refine ⟨2353437045482143055706455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6275832121285714815217213 2353437045482143055706455)
        ·
          refine ⟨3530155568223214583559683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353437045482143055706455 3530155568223214583559683)
          ·
            refine ⟨5295233352334821875339525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530155568223214583559683 5295233352334821875339525)
            ·
              refine ⟨992856253562779101626161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5295233352334821875339525 992856253562779101626161)
              ·
                refine ⟨744642190172084326219621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992856253562779101626161 744642190172084326219621)
                ·
                  refine ⟨139620410657265811166179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 744642190172084326219621 139620410657265811166179)
                  ·
                    rfl

theorem cell21_611797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_611797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611797 prefixEnd_611797 := by exact prefixLift 611797
  have htrace : WordTrace (prefixWord ++ tailWord_611797) baseStart_611797 baseEnd_611797 := by
    simpa [prefixWord, tailWord_611797, baseEnd_611797] using wordTrace_append hprefix tailTrace_611797
  have hstable : (prefixWord ++ tailWord_611797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611797).length < 2 ^ (prefixWord ++ tailWord_611797).sum := by decide
  have hdescent : baseEnd_611797 < baseStart_611797 := by decide
  rcases family_descends (prefixWord ++ tailWord_611797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611811 : List Nat := [1, 1, 1, 6, 2, 1, 3, 6]
def baseStart_611811 : Nat := 118140960795 + 611811 * 2 ^ 59
def prefixEnd_611811 : Nat := 4983230072969 + 3 ^ 40 * 611811 * 2
def baseEnd_611811 : Nat := 46541201882668299310939

theorem tailTrace_611811 : CollatzResearch.WordTrace tailWord_611811 prefixEnd_611811 46541201882668299310939 := by
  unfold tailWord_611811
  simp only [CollatzResearch.WordTrace]
  refine ⟨22314580386520710845115287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14876386924347140563410191 22314580386520710845115287)
  ·
    refine ⟨33471870579781066267672931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22314580386520710845115287 33471870579781066267672931)
    ·
      refine ⟨50207805869671599401509397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33471870579781066267672931 50207805869671599401509397)
      ·
        refine ⟨2353490900140856221945753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50207805869671599401509397 2353490900140856221945753)
        ·
          refine ⟨1765118175105642166459315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2353490900140856221945753 1765118175105642166459315)
          ·
            refine ⟨2647677262658463249688973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765118175105642166459315 2647677262658463249688973)
            ·
              refine ⟨992878973496923718633365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2647677262658463249688973 992878973496923718633365)
              ·
                refine ⟨46541201882668299310939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 992878973496923718633365 46541201882668299310939)
                ·
                  rfl

theorem cell21_611811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 6].length) (baseStart_611811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611811 prefixEnd_611811 := by exact prefixLift 611811
  have htrace : WordTrace (prefixWord ++ tailWord_611811) baseStart_611811 baseEnd_611811 := by
    simpa [prefixWord, tailWord_611811, baseEnd_611811] using wordTrace_append hprefix tailTrace_611811
  have hstable : (prefixWord ++ tailWord_611811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611811).length < 2 ^ (prefixWord ++ tailWord_611811).sum := by decide
  have hdescent : baseEnd_611811 < baseStart_611811 := by decide
  rcases family_descends (prefixWord ++ tailWord_611811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611825 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 7]
def baseStart_611825 : Nat := 118140960795 + 611825 * 2 ^ 59
def prefixEnd_611825 : Nat := 4983230072969 + 3 ^ 40 * 611825 * 2
def baseEnd_611825 : Nat := 139626800638743984699455

theorem tailTrace_611825 : CollatzResearch.WordTrace tailWord_611825 prefixEnd_611825 139626800638743984699455 := by
  unfold tailWord_611825
  simp only [CollatzResearch.WordTrace]
  refine ⟨22315091008469991236124929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14876727338979994157416619 22315091008469991236124929)
  ·
    refine ⟨16736318256352493427093697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22315091008469991236124929 16736318256352493427093697)
    ·
      refine ⟨12552238692264370070320273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16736318256352493427093697 12552238692264370070320273)
      ·
        refine ⟨9414179019198277552740205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12552238692264370070320273 9414179019198277552740205)
        ·
          refine ⟨3530317132199354082277577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9414179019198277552740205 3530317132199354082277577)
          ·
            refine ⟨2647737849149515561708183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530317132199354082277577 2647737849149515561708183)
            ·
              refine ⟨3971606773724273342562275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647737849149515561708183 3971606773724273342562275)
              ·
                refine ⟨5957410160586410013843413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971606773724273342562275 5957410160586410013843413)
                ·
                  refine ⟨139626800638743984699455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5957410160586410013843413 139626800638743984699455)
                  ·
                    rfl

theorem cell21_611825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_611825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611825 prefixEnd_611825 := by exact prefixLift 611825
  have htrace : WordTrace (prefixWord ++ tailWord_611825) baseStart_611825 baseEnd_611825 := by
    simpa [prefixWord, tailWord_611825, baseEnd_611825] using wordTrace_append hprefix tailTrace_611825
  have hstable : (prefixWord ++ tailWord_611825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611825).length < 2 ^ (prefixWord ++ tailWord_611825).sum := by decide
  have hdescent : baseEnd_611825 < baseStart_611825 := by decide
  rcases family_descends (prefixWord ++ tailWord_611825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611910 : List Nat := [6, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_611910 : Nat := 118140960795 + 611910 * 2 ^ 59
def prefixEnd_611910 : Nat := 4983230072969 + 3 ^ 40 * 611910 * 2
def baseEnd_611910 : Nat := 139646198796802725782615

theorem tailTrace_611910 : CollatzResearch.WordTrace tailWord_611910 prefixEnd_611910 139646198796802725782615 := by
  unfold tailWord_611910
  simp only [CollatzResearch.WordTrace]
  refine ⟨697443475411314086030287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14878794142108033835312789 697443475411314086030287)
  ·
    refine ⟨1046165213116971129045431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 697443475411314086030287 1046165213116971129045431)
    ·
      refine ⟨1569247819675456693568147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1046165213116971129045431 1569247819675456693568147)
      ·
        refine ⟨2353871729513185040352221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569247819675456693568147 2353871729513185040352221)
        ·
          refine ⟨882701898567444390132083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2353871729513185040352221 882701898567444390132083)
          ·
            refine ⟨1324052847851166585198125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882701898567444390132083 1324052847851166585198125)
            ·
              refine ⟨496519817944187469449297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1324052847851166585198125 496519817944187469449297)
              ·
                refine ⟨372389863458140602086973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496519817944187469449297 372389863458140602086973)
                ·
                  refine ⟨139646198796802725782615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372389863458140602086973 139646198796802725782615)
                  ·
                    rfl

theorem cell21_611910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_611910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_611910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_611910 prefixEnd_611910 := by exact prefixLift 611910
  have htrace : WordTrace (prefixWord ++ tailWord_611910) baseStart_611910 baseEnd_611910 := by
    simpa [prefixWord, tailWord_611910, baseEnd_611910] using wordTrace_append hprefix tailTrace_611910
  have hstable : (prefixWord ++ tailWord_611910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611910).length < 2 ^ (prefixWord ++ tailWord_611910).sum := by decide
  have hdescent : baseEnd_611910 < baseStart_611910 := by decide
  rcases family_descends (prefixWord ++ tailWord_611910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612042 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_612042 : Nat := 118140960795 + 612042 * 2 ^ 59
def prefixEnd_612042 : Nat := 4983230072969 + 3 ^ 40 * 612042 * 2
def baseEnd_612042 : Nat := 139676322995199829582345

theorem tailTrace_612042 : CollatzResearch.WordTrace tailWord_612042 prefixEnd_612042 139676322995199829582345 := by
  unfold tailWord_612042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5580751412170959324193595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14882003765789224864516253 5580751412170959324193595)
  ·
    refine ⟨8371127118256438986290393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5580751412170959324193595 8371127118256438986290393)
    ·
      refine ⟨6278345338692329239717795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8371127118256438986290393 6278345338692329239717795)
      ·
        refine ⟨9417518008038493859576693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6278345338692329239717795 9417518008038493859576693)
        ·
          refine ⟨882892313253608799335315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9417518008038493859576693 882892313253608799335315)
          ·
            refine ⟨1324338469880413199002973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882892313253608799335315 1324338469880413199002973)
            ·
              refine ⟨496626926205154949626115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1324338469880413199002973 496626926205154949626115)
              ·
                refine ⟨744940389307732424439173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496626926205154949626115 744940389307732424439173)
                ·
                  refine ⟨139676322995199829582345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 744940389307732424439173 139676322995199829582345)
                  ·
                    rfl

theorem cell21_612042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_612042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612042 prefixEnd_612042 := by exact prefixLift 612042
  have htrace : WordTrace (prefixWord ++ tailWord_612042) baseStart_612042 baseEnd_612042 := by
    simpa [prefixWord, tailWord_612042, baseEnd_612042] using wordTrace_append hprefix tailTrace_612042
  have hstable : (prefixWord ++ tailWord_612042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612042).length < 2 ^ (prefixWord ++ tailWord_612042).sum := by decide
  have hdescent : baseEnd_612042 < baseStart_612042 := by decide
  rcases family_descends (prefixWord ++ tailWord_612042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612194 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_612194 : Nat := 118140960795 + 612194 * 2 ^ 59
def prefixEnd_612194 : Nat := 4983230072969 + 3 ^ 40 * 612194 * 2
def baseEnd_612194 : Nat := 139711011466081343048701

theorem tailTrace_612194 : CollatzResearch.WordTrace tailWord_612194 prefixEnd_612194 139711011466081343048701 := by
  unfold tailWord_612194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5582137386033291814076909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14885699696088778170871757 5582137386033291814076909)
  ·
    refine ⟨2093301519762484430278841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5582137386033291814076909 2093301519762484430278841)
    ·
      refine ⟨1569976139821863322709131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2093301519762484430278841 1569976139821863322709131)
      ·
        refine ⟨2354964209732794984063697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569976139821863322709131 2354964209732794984063697)
        ·
          refine ⟨1766223157299596238047773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2354964209732794984063697 1766223157299596238047773)
          ·
            refine ⟨662333683987348589267915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1766223157299596238047773 662333683987348589267915)
            ·
              refine ⟨993500525981022883901873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662333683987348589267915 993500525981022883901873)
              ·
                refine ⟨745125394485767162926405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993500525981022883901873 745125394485767162926405)
                ·
                  refine ⟨139711011466081343048701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 745125394485767162926405 139711011466081343048701)
                  ·
                    rfl

theorem cell21_612194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_612194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612194 prefixEnd_612194 := by exact prefixLift 612194
  have htrace : WordTrace (prefixWord ++ tailWord_612194) baseStart_612194 baseEnd_612194 := by
    simpa [prefixWord, tailWord_612194, baseEnd_612194] using wordTrace_append hprefix tailTrace_612194
  have hstable : (prefixWord ++ tailWord_612194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612194).length < 2 ^ (prefixWord ++ tailWord_612194).sum := by decide
  have hdescent : baseEnd_612194 < baseStart_612194 := by decide
  rcases family_descends (prefixWord ++ tailWord_612194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612205 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 5]
def baseStart_612205 : Nat := 118140960795 + 612205 * 2 ^ 59
def prefixEnd_612205 : Nat := 4983230072969 + 3 ^ 40 * 612205 * 2
def baseEnd_612205 : Nat := 139713521815947768365345

theorem tailTrace_612205 : CollatzResearch.WordTrace tailWord_612205 prefixEnd_612205 139713521815947768365345 := by
  unfold tailWord_612205
  simp only [CollatzResearch.WordTrace]
  refine ⟨22328950747093316134958069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14885967164728877423305379 22328950747093316134958069)
  ·
    refine ⟨2093339132539998387652319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22328950747093316134958069 2093339132539998387652319)
    ·
      refine ⟨3140008698809997581478479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2093339132539998387652319 3140008698809997581478479)
      ·
        refine ⟨4710013048214996372217719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3140008698809997581478479 4710013048214996372217719)
        ·
          refine ⟨7065019572322494558326579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4710013048214996372217719 7065019572322494558326579)
          ·
            refine ⟨10597529358483741837489869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7065019572322494558326579 10597529358483741837489869)
            ·
              refine ⟨3974073509431403189058701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10597529358483741837489869 3974073509431403189058701)
              ·
                refine ⟨1490277566036776195897013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3974073509431403189058701 1490277566036776195897013)
                ·
                  refine ⟨139713521815947768365345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1490277566036776195897013 139713521815947768365345)
                  ·
                    rfl

theorem cell21_612205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_612205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612205 prefixEnd_612205 := by exact prefixLift 612205
  have htrace : WordTrace (prefixWord ++ tailWord_612205) baseStart_612205 baseEnd_612205 := by
    simpa [prefixWord, tailWord_612205, baseEnd_612205] using wordTrace_append hprefix tailTrace_612205
  have hstable : (prefixWord ++ tailWord_612205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612205).length < 2 ^ (prefixWord ++ tailWord_612205).sum := by decide
  have hdescent : baseEnd_612205 < baseStart_612205 := by decide
  rcases family_descends (prefixWord ++ tailWord_612205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612225 : List Nat := [1, 2, 4, 4, 1, 2, 2, 5]
def baseStart_612225 : Nat := 118140960795 + 612225 * 2 ^ 59
def prefixEnd_612225 : Nat := 4983230072969 + 3 ^ 40 * 612225 * 2
def baseEnd_612225 : Nat := 46572695362810726010657

theorem tailTrace_612225 : CollatzResearch.WordTrace tailWord_612225 prefixEnd_612225 46572695362810726010657 := by
  unfold tailWord_612225
  simp only [CollatzResearch.WordTrace]
  refine ⟨22329680207020859550686129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14886453471347239700457419 22329680207020859550686129)
  ·
    refine ⟨16747260155265644663014597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22329680207020859550686129 16747260155265644663014597)
    ·
      refine ⟨3140111279112308374315237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16747260155265644663014597 3140111279112308374315237)
      ·
        refine ⟨588770864833557820184107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3140111279112308374315237 588770864833557820184107)
        ·
          refine ⟨883156297250336730276161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588770864833557820184107 883156297250336730276161)
          ·
            refine ⟨662367222937752547707121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883156297250336730276161 662367222937752547707121)
            ·
              refine ⟨496775417203314410780341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662367222937752547707121 496775417203314410780341)
              ·
                refine ⟨46572695362810726010657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 496775417203314410780341 46572695362810726010657)
                ·
                  rfl

theorem cell21_612225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 5].length) (baseStart_612225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612225 prefixEnd_612225 := by exact prefixLift 612225
  have htrace : WordTrace (prefixWord ++ tailWord_612225) baseStart_612225 baseEnd_612225 := by
    simpa [prefixWord, tailWord_612225, baseEnd_612225] using wordTrace_append hprefix tailTrace_612225
  have hstable : (prefixWord ++ tailWord_612225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612225).length < 2 ^ (prefixWord ++ tailWord_612225).sum := by decide
  have hdescent : baseEnd_612225 < baseStart_612225 := by decide
  rcases family_descends (prefixWord ++ tailWord_612225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612250 : List Nat := [3, 1, 1, 4, 2, 1, 9]
def baseStart_612250 : Nat := 118140960795 + 612250 * 2 ^ 59
def prefixEnd_612250 : Nat := 4983230072969 + 3 ^ 40 * 612250 * 2
def baseEnd_612250 : Nat := 15524865714337521123917

theorem tailTrace_612250 : CollatzResearch.WordTrace tailWord_612250 prefixEnd_612250 15524865714337521123917 := by
  unfold tailWord_612250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5582648007982572205086551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14887061354620192546897469 5582648007982572205086551)
  ·
    refine ⟨8373972011973858307629827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5582648007982572205086551 8373972011973858307629827)
    ·
      refine ⟨12560958017960787461444741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8373972011973858307629827 12560958017960787461444741)
      ·
        refine ⟨2355179628367647649020889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12560958017960787461444741 2355179628367647649020889)
        ·
          refine ⟨1766384721275735736765667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2355179628367647649020889 1766384721275735736765667)
          ·
            refine ⟨2649577081913603605148501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766384721275735736765667 2649577081913603605148501)
            ·
              refine ⟨15524865714337521123917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2649577081913603605148501 15524865714337521123917)
              ·
                rfl

theorem cell21_612250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 9].length) (baseStart_612250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612250 prefixEnd_612250 := by exact prefixLift 612250
  have htrace : WordTrace (prefixWord ++ tailWord_612250) baseStart_612250 baseEnd_612250 := by
    simpa [prefixWord, tailWord_612250, baseEnd_612250] using wordTrace_append hprefix tailTrace_612250
  have hstable : (prefixWord ++ tailWord_612250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612250).length < 2 ^ (prefixWord ++ tailWord_612250).sum := by decide
  have hdescent : baseEnd_612250 < baseStart_612250 := by decide
  rcases family_descends (prefixWord ++ tailWord_612250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612312 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 4]
def baseStart_612312 : Nat := 118140960795 + 612312 * 2 ^ 59
def prefixEnd_612312 : Nat := 4983230072969 + 3 ^ 40 * 612312 * 2
def baseEnd_612312 : Nat := 139737940673739360081793

theorem tailTrace_612312 : CollatzResearch.WordTrace tailWord_612312 prefixEnd_612312 139737940673739360081793 := by
  unfold tailWord_612312
  simp only [CollatzResearch.WordTrace]
  refine ⟨11166426678852836704551595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14888568905137115606068793 11166426678852836704551595)
  ·
    refine ⟨16749640018279255056827393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11166426678852836704551595 16749640018279255056827393)
    ·
      refine ⟨12562230013709441292620545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16749640018279255056827393 12562230013709441292620545)
      ·
        refine ⟨9421672510282080969465409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12562230013709441292620545 9421672510282080969465409)
        ·
          refine ⟨7066254382711560727099057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9421672510282080969465409 7066254382711560727099057)
          ·
            refine ⟨5299690787033670545324293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7066254382711560727099057 5299690787033670545324293)
            ·
              refine ⟨993692022568813227248305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5299690787033670545324293 993692022568813227248305)
              ·
                refine ⟨745269016926609920436229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993692022568813227248305 745269016926609920436229)
                ·
                  refine ⟨139737940673739360081793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 745269016926609920436229 139737940673739360081793)
                  ·
                    rfl

theorem cell21_612312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_612312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612312 prefixEnd_612312 := by exact prefixLift 612312
  have htrace : WordTrace (prefixWord ++ tailWord_612312) baseStart_612312 baseEnd_612312 := by
    simpa [prefixWord, tailWord_612312, baseEnd_612312] using wordTrace_append hprefix tailTrace_612312
  have hstable : (prefixWord ++ tailWord_612312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612312).length < 2 ^ (prefixWord ++ tailWord_612312).sum := by decide
  have hdescent : baseEnd_612312 < baseStart_612312 := by decide
  rcases family_descends (prefixWord ++ tailWord_612312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612402 : List Nat := [3, 2, 1, 1, 2, 4, 1, 7]
def baseStart_612402 : Nat := 118140960795 + 612402 * 2 ^ 59
def prefixEnd_612402 : Nat := 4983230072969 + 3 ^ 40 * 612402 * 2
def baseEnd_612402 : Nat := 46586159966639734527203

theorem tailTrace_612402 : CollatzResearch.WordTrace tailWord_612402 prefixEnd_612402 46586159966639734527203 := by
  unfold tailWord_612402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5584033981844904694969865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14890757284919745853252973 5584033981844904694969865)
  ·
    refine ⟨4188025486383678521227399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5584033981844904694969865 4188025486383678521227399)
    ·
      refine ⟨6282038229575517781841099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4188025486383678521227399 6282038229575517781841099)
      ·
        refine ⟨9423057344363276672761649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6282038229575517781841099 9423057344363276672761649)
        ·
          refine ⟨7067293008272457504571237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9423057344363276672761649 7067293008272457504571237)
          ·
            refine ⟨1325117439051085782107107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7067293008272457504571237 1325117439051085782107107)
            ·
              refine ⟨1987676158576628673160661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325117439051085782107107 1987676158576628673160661)
              ·
                refine ⟨46586159966639734527203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1987676158576628673160661 46586159966639734527203)
                ·
                  rfl

theorem cell21_612402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_612402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612402 prefixEnd_612402 := by exact prefixLift 612402
  have htrace : WordTrace (prefixWord ++ tailWord_612402) baseStart_612402 baseEnd_612402 := by
    simpa [prefixWord, tailWord_612402, baseEnd_612402] using wordTrace_append hprefix tailTrace_612402
  have hstable : (prefixWord ++ tailWord_612402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612402).length < 2 ^ (prefixWord ++ tailWord_612402).sum := by decide
  have hdescent : baseEnd_612402 < baseStart_612402 := by decide
  rcases family_descends (prefixWord ++ tailWord_612402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612408 : List Nat := [2, 1, 2, 1, 7, 1, 1, 3, 3]
def baseStart_612408 : Nat := 118140960795 + 612408 * 2 ^ 59
def prefixEnd_612408 : Nat := 4983230072969 + 3 ^ 40 * 612408 * 2
def baseEnd_612408 : Nat := 139759849181664526481597

theorem tailTrace_612408 : CollatzResearch.WordTrace tailWord_612408 prefixEnd_612408 139759849181664526481597 := by
  unfold tailWord_612408
  simp only [CollatzResearch.WordTrace]
  refine ⟨11168177382678940902298939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14890903176905254536398585 11168177382678940902298939)
  ·
    refine ⟨16752266074018411353448409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11168177382678940902298939 16752266074018411353448409)
    ·
      refine ⟨12564199555513808515086307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16752266074018411353448409 12564199555513808515086307)
      ·
        refine ⟨18846299333270712772629461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12564199555513808515086307 18846299333270712772629461)
        ·
          refine ⟨441710140623532330608503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 18846299333270712772629461 441710140623532330608503)
          ·
            refine ⟨662565210935298495912755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441710140623532330608503 662565210935298495912755)
            ·
              refine ⟨993847816402947743869133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662565210935298495912755 993847816402947743869133)
              ·
                refine ⟨372692931151105403950925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 993847816402947743869133 372692931151105403950925)
                ·
                  refine ⟨139759849181664526481597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372692931151105403950925 139759849181664526481597)
                  ·
                    rfl

theorem cell21_612408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 3].length) (baseStart_612408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612408 prefixEnd_612408 := by exact prefixLift 612408
  have htrace : WordTrace (prefixWord ++ tailWord_612408) baseStart_612408 baseEnd_612408 := by
    simpa [prefixWord, tailWord_612408, baseEnd_612408] using wordTrace_append hprefix tailTrace_612408
  have hstable : (prefixWord ++ tailWord_612408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612408).length < 2 ^ (prefixWord ++ tailWord_612408).sum := by decide
  have hdescent : baseEnd_612408 < baseStart_612408 := by decide
  rcases family_descends (prefixWord ++ tailWord_612408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612481 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 4]
def baseStart_612481 : Nat := 118140960795 + 612481 * 2 ^ 59
def prefixEnd_612481 : Nat := 4983230072969 + 3 ^ 40 * 612481 * 2
def baseEnd_612481 : Nat := 139776508776232621764781

theorem tailTrace_612481 : CollatzResearch.WordTrace tailWord_612481 prefixEnd_612481 139776508776232621764781 := by
  unfold tailWord_612481
  simp only [CollatzResearch.WordTrace]
  refine ⟨22339017294093415272005297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14892678196062276848003531 22339017294093415272005297)
  ·
    refine ⟨16754262970570061454003973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22339017294093415272005297 16754262970570061454003973)
    ·
      refine ⟨3141424306981886522625745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16754262970570061454003973 3141424306981886522625745)
      ·
        refine ⟨2356068230236414891969309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3141424306981886522625745 2356068230236414891969309)
        ·
          refine ⟨883525586338655584488491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2356068230236414891969309 883525586338655584488491)
          ·
            refine ⟨1325288379507983376732737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883525586338655584488491 1325288379507983376732737)
            ·
              refine ⟨993966284630987532549553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1325288379507983376732737 993966284630987532549553)
              ·
                refine ⟨745474713473240649412165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993966284630987532549553 745474713473240649412165)
                ·
                  refine ⟨139776508776232621764781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 745474713473240649412165 139776508776232621764781)
                  ·
                    rfl

theorem cell21_612481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_612481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612481 prefixEnd_612481 := by exact prefixLift 612481
  have htrace : WordTrace (prefixWord ++ tailWord_612481) baseStart_612481 baseEnd_612481 := by
    simpa [prefixWord, tailWord_612481, baseEnd_612481] using wordTrace_append hprefix tailTrace_612481
  have hstable : (prefixWord ++ tailWord_612481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612481).length < 2 ^ (prefixWord ++ tailWord_612481).sum := by decide
  have hdescent : baseEnd_612481 < baseStart_612481 := by decide
  rcases family_descends (prefixWord ++ tailWord_612481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612509 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 5]
def baseStart_612509 : Nat := 118140960795 + 612509 * 2 ^ 59
def prefixEnd_612509 : Nat := 4983230072969 + 3 ^ 40 * 612509 * 2
def baseEnd_612509 : Nat := 139782898757710795298057

theorem tailTrace_612509 : CollatzResearch.WordTrace tailWord_612509 prefixEnd_612509 139782898757710795298057 := by
  unfold tailWord_612509
  simp only [CollatzResearch.WordTrace]
  refine ⟨22340038537991976054024581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14893359025327984036016387 22340038537991976054024581)
  ·
    refine ⟨4188757225873495510129609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22340038537991976054024581 4188757225873495510129609)
    ·
      refine ⟨3141567919405121632597207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4188757225873495510129609 3141567919405121632597207)
      ·
        refine ⟨4712351879107682448895811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3141567919405121632597207 4712351879107682448895811)
        ·
          refine ⟨7068527818661523673343717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4712351879107682448895811 7068527818661523673343717)
          ·
            refine ⟨1325348965999035688751947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7068527818661523673343717 1325348965999035688751947)
            ·
              refine ⟨1988023448998553533127921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325348965999035688751947 1988023448998553533127921)
              ·
                refine ⟨1491017586748915149845941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1988023448998553533127921 1491017586748915149845941)
                ·
                  refine ⟨139782898757710795298057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1491017586748915149845941 139782898757710795298057)
                  ·
                    rfl

theorem cell21_612509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_612509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612509 prefixEnd_612509 := by exact prefixLift 612509
  have htrace : WordTrace (prefixWord ++ tailWord_612509) baseStart_612509 baseEnd_612509 := by
    simpa [prefixWord, tailWord_612509, baseEnd_612509] using wordTrace_append hprefix tailTrace_612509
  have hstable : (prefixWord ++ tailWord_612509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612509).length < 2 ^ (prefixWord ++ tailWord_612509).sum := by decide
  have hdescent : baseEnd_612509 < baseStart_612509 := by decide
  rcases family_descends (prefixWord ++ tailWord_612509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612532 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 4]
def baseStart_612532 : Nat := 118140960795 + 612532 * 2 ^ 59
def prefixEnd_612532 : Nat := 4983230072969 + 3 ^ 40 * 612532 * 2
def baseEnd_612532 : Nat := 139788147671067866414677

theorem tailTrace_612532 : CollatzResearch.WordTrace tailWord_612532 prefixEnd_612532 139788147671067866414677 := by
  unfold tailWord_612532
  simp only [CollatzResearch.WordTrace]
  refine ⟨11170438708454325491055925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14893918277939100654741233 11170438708454325491055925)
  ·
    refine ⟨1047228628917593014786493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11170438708454325491055925 1047228628917593014786493)
    ·
      refine ⟨392710735844097380544935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1047228628917593014786493 392710735844097380544935)
      ·
        refine ⟨589066103766146070817403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392710735844097380544935 589066103766146070817403)
        ·
          refine ⟨883599155649219106226105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589066103766146070817403 883599155649219106226105)
          ·
            refine ⟨662699366736914329669579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883599155649219106226105 662699366736914329669579)
            ·
              refine ⟨994049050105371494504369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662699366736914329669579 994049050105371494504369)
              ·
                refine ⟨745536787579028620878277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 994049050105371494504369 745536787579028620878277)
                ·
                  refine ⟨139788147671067866414677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 745536787579028620878277 139788147671067866414677)
                  ·
                    rfl

theorem cell21_612532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_612532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612532 prefixEnd_612532 := by exact prefixLift 612532
  have htrace : WordTrace (prefixWord ++ tailWord_612532) baseStart_612532 baseEnd_612532 := by
    simpa [prefixWord, tailWord_612532, baseEnd_612532] using wordTrace_append hprefix tailTrace_612532
  have hstable : (prefixWord ++ tailWord_612532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612532).length < 2 ^ (prefixWord ++ tailWord_612532).sum := by decide
  have hdescent : baseEnd_612532 < baseStart_612532 := by decide
  rcases family_descends (prefixWord ++ tailWord_612532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612537 : List Nat := [1, 2, 1, 4, 1, 2, 10]
def baseStart_612537 : Nat := 118140960795 + 612537 * 2 ^ 59
def prefixEnd_612537 : Nat := 4983230072969 + 3 ^ 40 * 612537 * 2
def baseEnd_612537 : Nat := 15532143193243218759037

theorem tailTrace_612537 : CollatzResearch.WordTrace tailWord_612537 prefixEnd_612537 15532143193243218759037 := by
  unfold tailWord_612537
  simp only [CollatzResearch.WordTrace]
  refine ⟨22341059781890536836043865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14894039854593691224029243 22341059781890536836043865)
  ·
    refine ⟨16755794836417902627032899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22341059781890536836043865 16755794836417902627032899)
    ·
      refine ⟨25133692254626853940549349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16755794836417902627032899 25133692254626853940549349)
      ·
        refine ⟨4712567297742535113853003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25133692254626853940549349 4712567297742535113853003)
        ·
          refine ⟨7068850946613802670779505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4712567297742535113853003 7068850946613802670779505)
          ·
            refine ⟨5301638209960352003084629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7068850946613802670779505 5301638209960352003084629)
            ·
              refine ⟨15532143193243218759037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5301638209960352003084629 15532143193243218759037)
              ·
                rfl

theorem cell21_612537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 10].length) (baseStart_612537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612537 prefixEnd_612537 := by exact prefixLift 612537
  have htrace : WordTrace (prefixWord ++ tailWord_612537) baseStart_612537 baseEnd_612537 := by
    simpa [prefixWord, tailWord_612537, baseEnd_612537] using wordTrace_append hprefix tailTrace_612537
  have hstable : (prefixWord ++ tailWord_612537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612537).length < 2 ^ (prefixWord ++ tailWord_612537).sum := by decide
  have hdescent : baseEnd_612537 < baseStart_612537 := by decide
  rcases family_descends (prefixWord ++ tailWord_612537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612540 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 6]
def baseStart_612540 : Nat := 118140960795 + 612540 * 2 ^ 59
def prefixEnd_612540 : Nat := 4983230072969 + 3 ^ 40 * 612540 * 2
def baseEnd_612540 : Nat := 139789973380061630281327

theorem tailTrace_612540 : CollatzResearch.WordTrace tailWord_612540 prefixEnd_612540 139789973380061630281327 := by
  unfold tailWord_612540
  simp only [CollatzResearch.WordTrace]
  refine ⟨11170584600439834174201537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14894112800586445565602049 11170584600439834174201537)
  ·
    refine ⟨8377938450329875630651153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11170584600439834174201537 8377938450329875630651153)
    ·
      refine ⟨6283453837747406722988365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8377938450329875630651153 6283453837747406722988365)
      ·
        refine ⟨2356295189155277521120637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6283453837747406722988365 2356295189155277521120637)
        ·
          refine ⟨883610695933229070420239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2356295189155277521120637 883610695933229070420239)
          ·
            refine ⟨1325416043899843605630359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883610695933229070420239 1325416043899843605630359)
            ·
              refine ⟨1988124065849765408445539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325416043899843605630359 1988124065849765408445539)
              ·
                refine ⟨2982186098774648112668309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988124065849765408445539 2982186098774648112668309)
                ·
                  refine ⟨139789973380061630281327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2982186098774648112668309 139789973380061630281327)
                  ·
                    rfl

theorem cell21_612540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_612540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612540 prefixEnd_612540 := by exact prefixLift 612540
  have htrace : WordTrace (prefixWord ++ tailWord_612540) baseStart_612540 baseEnd_612540 := by
    simpa [prefixWord, tailWord_612540, baseEnd_612540] using wordTrace_append hprefix tailTrace_612540
  have hstable : (prefixWord ++ tailWord_612540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612540).length < 2 ^ (prefixWord ++ tailWord_612540).sum := by decide
  have hdescent : baseEnd_612540 < baseStart_612540 := by decide
  rcases family_descends (prefixWord ++ tailWord_612540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612616 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 4]
def baseStart_612616 : Nat := 118140960795 + 612616 * 2 ^ 59
def prefixEnd_612616 : Nat := 4983230072969 + 3 ^ 40 * 612616 * 2
def baseEnd_612616 : Nat := 139807317615502387014505

theorem tailTrace_612616 : CollatzResearch.WordTrace tailWord_612616 prefixEnd_612616 139807317615502387014505 := by
  unfold tailWord_612616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11171970574302166664084851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14895960765736222218779801 11171970574302166664084851)
  ·
    refine ⟨16757955861453249996127277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11171970574302166664084851 16757955861453249996127277)
    ·
      refine ⟨6284233448044968748547729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16757955861453249996127277 6284233448044968748547729)
      ·
        refine ⟨4713175086033726561410797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6284233448044968748547729 4713175086033726561410797)
        ·
          refine ⟨1767440657262647460529049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4713175086033726561410797 1767440657262647460529049)
          ·
            refine ⟨1325580492946985595396787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1767440657262647460529049 1325580492946985595396787)
            ·
              refine ⟨1988370739420478393095181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325580492946985595396787 1988370739420478393095181)
              ·
                refine ⟨745639027282679397410693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1988370739420478393095181 745639027282679397410693)
                ·
                  refine ⟨139807317615502387014505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 745639027282679397410693 139807317615502387014505)
                  ·
                    rfl

theorem cell21_612616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_612616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612616 prefixEnd_612616 := by exact prefixLift 612616
  have htrace : WordTrace (prefixWord ++ tailWord_612616) baseStart_612616 baseEnd_612616 := by
    simpa [prefixWord, tailWord_612616, baseEnd_612616] using wordTrace_append hprefix tailTrace_612616
  have hstable : (prefixWord ++ tailWord_612616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612616).length < 2 ^ (prefixWord ++ tailWord_612616).sum := by decide
  have hdescent : baseEnd_612616 < baseStart_612616 := by decide
  rcases family_descends (prefixWord ++ tailWord_612616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612647 : List Nat := [1, 1, 8, 1, 10]
def baseStart_612647 : Nat := 118140960795 + 612647 * 2 ^ 59
def prefixEnd_612647 : Nat := 4983230072969 + 3 ^ 40 * 612647 * 2
def baseEnd_612647 : Nat := 1726103607874731135775

theorem tailTrace_612647 : CollatzResearch.WordTrace tailWord_612647 prefixEnd_612647 1726103607874731135775 := by
  unfold tailWord_612647
  simp only [CollatzResearch.WordTrace]
  refine ⟨22345071811492025622548195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14896714540994683748365463 22345071811492025622548195)
  ·
    refine ⟨33517607717238038433822293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22345071811492025622548195 33517607717238038433822293)
    ·
      refine ⟨392784465436383262896355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 33517607717238038433822293 392784465436383262896355)
      ·
        refine ⟨589176698154574894344533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392784465436383262896355 589176698154574894344533)
        ·
          refine ⟨1726103607874731135775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 589176698154574894344533 1726103607874731135775)
          ·
            rfl

theorem cell21_612647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 10].length) (baseStart_612647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612647 prefixEnd_612647 := by exact prefixLift 612647
  have htrace : WordTrace (prefixWord ++ tailWord_612647) baseStart_612647 baseEnd_612647 := by
    simpa [prefixWord, tailWord_612647, baseEnd_612647] using wordTrace_append hprefix tailTrace_612647
  have hstable : (prefixWord ++ tailWord_612647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612647).length < 2 ^ (prefixWord ++ tailWord_612647).sum := by decide
  have hdescent : baseEnd_612647 < baseStart_612647 := by decide
  rcases family_descends (prefixWord ++ tailWord_612647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612653 : List Nat := [1, 5, 3, 1, 2, 2, 2, 2, 3]
def baseStart_612653 : Nat := 118140960795 + 612653 * 2 ^ 59
def prefixEnd_612653 : Nat := 4983230072969 + 3 ^ 40 * 612653 * 2
def baseEnd_612653 : Nat := 139815761519598544897763

theorem tailTrace_612653 : CollatzResearch.WordTrace tailWord_612653 prefixEnd_612653 139815761519598544897763 := by
  unfold tailWord_612653
  simp only [CollatzResearch.WordTrace]
  refine ⟨22345290649470288647266613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14896860432980192431511075 22345290649470288647266613)
  ·
    refine ⟨2094870998387839560681245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22345290649470288647266613 2094870998387839560681245)
    ·
      refine ⟨785576624395439835255467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2094870998387839560681245 785576624395439835255467)
      ·
        refine ⟨1178364936593159752883201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785576624395439835255467 1178364936593159752883201)
        ·
          refine ⟨883773702444869814662401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1178364936593159752883201 883773702444869814662401)
          ·
            refine ⟨662830276833652360996801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883773702444869814662401 662830276833652360996801)
            ·
              refine ⟨497122707625239270747601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662830276833652360996801 497122707625239270747601)
              ·
                refine ⟨372842030718929453060701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497122707625239270747601 372842030718929453060701)
                ·
                  refine ⟨139815761519598544897763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372842030718929453060701 139815761519598544897763)
                  ·
                    rfl

theorem cell21_612653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_612653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612653 prefixEnd_612653 := by exact prefixLift 612653
  have htrace : WordTrace (prefixWord ++ tailWord_612653) baseStart_612653 baseEnd_612653 := by
    simpa [prefixWord, tailWord_612653, baseEnd_612653] using wordTrace_append hprefix tailTrace_612653
  have hstable : (prefixWord ++ tailWord_612653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612653).length < 2 ^ (prefixWord ++ tailWord_612653).sum := by decide
  have hdescent : baseEnd_612653 < baseStart_612653 := by decide
  rcases family_descends (prefixWord ++ tailWord_612653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612675 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 4]
def baseStart_612675 : Nat := 118140960795 + 612675 * 2 ^ 59
def prefixEnd_612675 : Nat := 4983230072969 + 3 ^ 40 * 612675 * 2
def baseEnd_612675 : Nat := 139820782219331395531051

theorem tailTrace_612675 : CollatzResearch.WordTrace tailWord_612675 prefixEnd_612675 139820782219331395531051 := by
  unfold tailWord_612675
  simp only [CollatzResearch.WordTrace]
  refine ⟨22346093055390586404567479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14897395370260390936378319 22346093055390586404567479)
  ·
    refine ⟨33519139583085879606851219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22346093055390586404567479 33519139583085879606851219)
    ·
      refine ⟨50278709374628819410276829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33519139583085879606851219 50278709374628819410276829)
      ·
        refine ⟨18854516015485807278853811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50278709374628819410276829 18854516015485807278853811)
        ·
          refine ⟨28281774023228710918280717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18854516015485807278853811 28281774023228710918280717)
          ·
            refine ⟨10605665258710766594355269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28281774023228710918280717 10605665258710766594355269)
            ·
              refine ⟨1988562236008268736441613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10605665258710766594355269 1988562236008268736441613)
              ·
                refine ⟨745710838503100776165605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1988562236008268736441613 745710838503100776165605)
                ·
                  refine ⟨139820782219331395531051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 745710838503100776165605 139820782219331395531051)
                  ·
                    rfl

theorem cell21_612675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 4].length) (baseStart_612675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612675 prefixEnd_612675 := by exact prefixLift 612675
  have htrace : WordTrace (prefixWord ++ tailWord_612675) baseStart_612675 baseEnd_612675 := by
    simpa [prefixWord, tailWord_612675, baseEnd_612675] using wordTrace_append hprefix tailTrace_612675
  have hstable : (prefixWord ++ tailWord_612675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612675).length < 2 ^ (prefixWord ++ tailWord_612675).sum := by decide
  have hdescent : baseEnd_612675 < baseStart_612675 := by decide
  rcases family_descends (prefixWord ++ tailWord_612675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612706 : List Nat := [3, 3, 2, 1, 1, 3, 8]
def baseStart_612706 : Nat := 118140960795 + 612706 * 2 ^ 59
def prefixEnd_612706 : Nat := 4983230072969 + 3 ^ 40 * 612706 * 2
def baseEnd_612706 : Nat := 15536428537964692279369

theorem tailTrace_612706 : CollatzResearch.WordTrace tailWord_612706 prefixEnd_612706 15536428537964692279369 := by
  unfold tailWord_612706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586805929569569674736493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14898149145518852465963981 5586805929569569674736493)
  ·
    refine ⟨2095052223588588628026185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5586805929569569674736493 2095052223588588628026185)
    ·
      refine ⟨1571289167691441471019639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2095052223588588628026185 1571289167691441471019639)
      ·
        refine ⟨2356933751537162206529459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571289167691441471019639 2356933751537162206529459)
        ·
          refine ⟨3535400627305743309794189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356933751537162206529459 3535400627305743309794189)
          ·
            refine ⟨1325775235239653741172821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3535400627305743309794189 1325775235239653741172821)
            ·
              refine ⟨15536428537964692279369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1325775235239653741172821 15536428537964692279369)
              ·
                rfl

theorem cell21_612706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 8].length) (baseStart_612706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612706 prefixEnd_612706 := by exact prefixLift 612706
  have htrace : WordTrace (prefixWord ++ tailWord_612706) baseStart_612706 baseEnd_612706 := by
    simpa [prefixWord, tailWord_612706, baseEnd_612706] using wordTrace_append hprefix tailTrace_612706
  have hstable : (prefixWord ++ tailWord_612706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612706).length < 2 ^ (prefixWord ++ tailWord_612706).sum := by decide
  have hdescent : baseEnd_612706 < baseStart_612706 := by decide
  rcases family_descends (prefixWord ++ tailWord_612706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612720 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_612720 : Nat := 118140960795 + 612720 * 2 ^ 59
def prefixEnd_612720 : Nat := 4983230072969 + 3 ^ 40 * 612720 * 2
def baseEnd_612720 : Nat := 139831051832421317280959

theorem tailTrace_612720 : CollatzResearch.WordTrace tailWord_612720 prefixEnd_612720 139831051832421317280959 := by
  unfold tailWord_612720
  simp only [CollatzResearch.WordTrace]
  refine ⟨11173867170113779544977807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14898489560151706059970409 11173867170113779544977807)
  ·
    refine ⟨16760800755170669317466711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11173867170113779544977807 16760800755170669317466711)
    ·
      refine ⟨25141201132756003976200067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16760800755170669317466711 25141201132756003976200067)
      ·
        refine ⟨37711801699134005964300101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25141201132756003976200067 37711801699134005964300101)
        ·
          refine ⟨7070962818587626118306269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37711801699134005964300101 7070962818587626118306269)
          ·
            refine ⟨2651611056970359794364851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7070962818587626118306269 2651611056970359794364851)
            ·
              refine ⟨3977416585455539691547277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2651611056970359794364851 3977416585455539691547277)
              ·
                refine ⟨1491531219545827384330229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3977416585455539691547277 1491531219545827384330229)
                ·
                  refine ⟨139831051832421317280959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1491531219545827384330229 139831051832421317280959)
                  ·
                    rfl

theorem cell21_612720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_612720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612720 prefixEnd_612720 := by exact prefixLift 612720
  have htrace : WordTrace (prefixWord ++ tailWord_612720) baseStart_612720 baseEnd_612720 := by
    simpa [prefixWord, tailWord_612720, baseEnd_612720] using wordTrace_append hprefix tailTrace_612720
  have hstable : (prefixWord ++ tailWord_612720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612720).length < 2 ^ (prefixWord ++ tailWord_612720).sum := by decide
  have hdescent : baseEnd_612720 < baseStart_612720 := by decide
  rcases family_descends (prefixWord ++ tailWord_612720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612737 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 5]
def baseStart_612737 : Nat := 118140960795 + 612737 * 2 ^ 59
def prefixEnd_612737 : Nat := 4983230072969 + 3 ^ 40 * 612737 * 2
def baseEnd_612737 : Nat := 139834931464033065497591

theorem tailTrace_612737 : CollatzResearch.WordTrace tailWord_612737 prefixEnd_612737 139834931464033065497591 := by
  unfold tailWord_612737
  simp only [CollatzResearch.WordTrace]
  refine ⟨22348354381165970993324465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14898902920777313995549643 22348354381165970993324465)
  ·
    refine ⟨16761265785874478244993349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22348354381165970993324465 16761265785874478244993349)
    ·
      refine ⟨3142737334851464670936253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16761265785874478244993349 3142737334851464670936253)
      ·
        refine ⟨1178526500569299251601095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3142737334851464670936253 1178526500569299251601095)
        ·
          refine ⟨1767789750853948877401643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178526500569299251601095 1767789750853948877401643)
          ·
            refine ⟨2651684626280923316102465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767789750853948877401643 2651684626280923316102465)
            ·
              refine ⟨1988763469710692487076849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2651684626280923316102465 1988763469710692487076849)
              ·
                refine ⟨1491572602283019365307637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1988763469710692487076849 1491572602283019365307637)
                ·
                  refine ⟨139834931464033065497591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1491572602283019365307637 139834931464033065497591)
                  ·
                    rfl

theorem cell21_612737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_612737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612737 prefixEnd_612737 := by exact prefixLift 612737
  have htrace : WordTrace (prefixWord ++ tailWord_612737) baseStart_612737 baseEnd_612737 := by
    simpa [prefixWord, tailWord_612737, baseEnd_612737] using wordTrace_append hprefix tailTrace_612737
  have hstable : (prefixWord ++ tailWord_612737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612737).length < 2 ^ (prefixWord ++ tailWord_612737).sum := by decide
  have hdescent : baseEnd_612737 < baseStart_612737 := by decide
  rcases family_descends (prefixWord ++ tailWord_612737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612785 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 4]
def baseStart_612785 : Nat := 118140960795 + 612785 * 2 ^ 59
def prefixEnd_612785 : Nat := 4983230072969 + 3 ^ 40 * 612785 * 2
def baseEnd_612785 : Nat := 139845885717995648697493

theorem tailTrace_612785 : CollatzResearch.WordTrace tailWord_612785 prefixEnd_612785 139845885717995648697493 := by
  unfold tailWord_612785
  simp only [CollatzResearch.WordTrace]
  refine ⟨22350105084992075191071809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14900070056661383460714539 22350105084992075191071809)
  ·
    refine ⟨16762578813744056393303857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22350105084992075191071809 16762578813744056393303857)
    ·
      refine ⟨12571934110308042294977893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16762578813744056393303857 12571934110308042294977893)
      ·
        refine ⟨2357237645682757930308355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12571934110308042294977893 2357237645682757930308355)
        ·
          refine ⟨3535856468524136895462533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357237645682757930308355 3535856468524136895462533)
          ·
            refine ⟨662973087848275667899225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3535856468524136895462533 662973087848275667899225)
            ·
              refine ⟨497229815886206750924419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662973087848275667899225 497229815886206750924419)
              ·
                refine ⟨745844723829310126386629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497229815886206750924419 745844723829310126386629)
                ·
                  refine ⟨139845885717995648697493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 745844723829310126386629 139845885717995648697493)
                  ·
                    rfl

theorem cell21_612785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_612785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612785 prefixEnd_612785 := by exact prefixLift 612785
  have htrace : WordTrace (prefixWord ++ tailWord_612785) baseStart_612785 baseEnd_612785 := by
    simpa [prefixWord, tailWord_612785, baseEnd_612785] using wordTrace_append hprefix tailTrace_612785
  have hstable : (prefixWord ++ tailWord_612785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612785).length < 2 ^ (prefixWord ++ tailWord_612785).sum := by decide
  have hdescent : baseEnd_612785 < baseStart_612785 := by decide
  rcases family_descends (prefixWord ++ tailWord_612785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612917 : List Nat := [1, 3, 3, 1, 1, 2, 3, 7]
def baseStart_612917 : Nat := 118140960795 + 612917 * 2 ^ 59
def prefixEnd_612917 : Nat := 4983230072969 + 3 ^ 40 * 612917 * 2
def baseEnd_612917 : Nat := 46625336638797584165741

theorem tailTrace_612917 : CollatzResearch.WordTrace tailWord_612917 prefixEnd_612917 46625336638797584165741 := by
  unfold tailWord_612917
  simp only [CollatzResearch.WordTrace]
  refine ⟨22354919520513861734877005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14903279680342574489918003 22354919520513861734877005)
  ·
    refine ⟨8383094820192698150578877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22354919520513861734877005 8383094820192698150578877)
    ·
      refine ⟨3143660557572261806467079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8383094820192698150578877 3143660557572261806467079)
      ·
        refine ⟨4715490836358392709700619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3143660557572261806467079 4715490836358392709700619)
        ·
          refine ⟨7073236254537589064550929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4715490836358392709700619 7073236254537589064550929)
          ·
            refine ⟨5304927190903191798413197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7073236254537589064550929 5304927190903191798413197)
            ·
              refine ⟨1989347696588696924404949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5304927190903191798413197 1989347696588696924404949)
              ·
                refine ⟨46625336638797584165741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1989347696588696924404949 46625336638797584165741)
                ·
                  rfl

theorem cell21_612917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 7].length) (baseStart_612917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612917 prefixEnd_612917 := by exact prefixLift 612917
  have htrace : WordTrace (prefixWord ++ tailWord_612917) baseStart_612917 baseEnd_612917 := by
    simpa [prefixWord, tailWord_612917, baseEnd_612917] using wordTrace_append hprefix tailTrace_612917
  have hstable : (prefixWord ++ tailWord_612917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612917).length < 2 ^ (prefixWord ++ tailWord_612917).sum := by decide
  have hdescent : baseEnd_612917 < baseStart_612917 := by decide
  rcases family_descends (prefixWord ++ tailWord_612917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612931 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 7]
def baseStart_612931 : Nat := 118140960795 + 612931 * 2 ^ 59
def prefixEnd_612931 : Nat := 4983230072969 + 3 ^ 40 * 612931 * 2
def baseEnd_612931 : Nat := 139879204907131839263861

theorem tailTrace_612931 : CollatzResearch.WordTrace tailWord_612931 prefixEnd_612931 139879204907131839263861 := by
  unfold tailWord_612931
  simp only [CollatzResearch.WordTrace]
  refine ⟨22355430142463142125886647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14903620094975428083924431 22355430142463142125886647)
  ·
    refine ⟨33533145213694713188829971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22355430142463142125886647 33533145213694713188829971)
    ·
      refine ⟨50299717820542069783244957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33533145213694713188829971 50299717820542069783244957)
      ·
        refine ⟨18862394182703276168716859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50299717820542069783244957 18862394182703276168716859)
        ·
          refine ⟨28293591274054914253075289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18862394182703276168716859 28293591274054914253075289)
          ·
            refine ⟨21220193455541185689806467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28293591274054914253075289 21220193455541185689806467)
            ·
              refine ⟨31830290183311778534709701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21220193455541185689806467 31830290183311778534709701)
              ·
                refine ⟨5968179409370958475258069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31830290183311778534709701 5968179409370958475258069)
                ·
                  refine ⟨139879204907131839263861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5968179409370958475258069 139879204907131839263861)
                  ·
                    rfl

theorem cell21_612931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_612931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612931 prefixEnd_612931 := by exact prefixLift 612931
  have htrace : WordTrace (prefixWord ++ tailWord_612931) baseStart_612931 baseEnd_612931 := by
    simpa [prefixWord, tailWord_612931, baseEnd_612931] using wordTrace_append hprefix tailTrace_612931
  have hstable : (prefixWord ++ tailWord_612931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612931).length < 2 ^ (prefixWord ++ tailWord_612931).sum := by decide
  have hdescent : baseEnd_612931 < baseStart_612931 := by decide
  rcases family_descends (prefixWord ++ tailWord_612931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612996 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 4]
def baseStart_612996 : Nat := 118140960795 + 612996 * 2 ^ 59
def prefixEnd_612996 : Nat := 4983230072969 + 3 ^ 40 * 612996 * 2
def baseEnd_612996 : Nat := 139894038792706170680395

theorem tailTrace_612996 : CollatzResearch.WordTrace tailWord_612996 prefixEnd_612996 139894038792706170680395 := by
  unfold tailWord_612996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11178900443613829113501421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14905200591485105484668561 11178900443613829113501421)
  ·
    refine ⟨4192087666355185917563033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11178900443613829113501421 4192087666355185917563033)
    ·
      refine ⟨3144065749766389438172275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4192087666355185917563033 3144065749766389438172275)
      ·
        refine ⟨4716098624649584157258413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3144065749766389438172275 4716098624649584157258413)
        ·
          refine ⟨1768536984243594058971905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4716098624649584157258413 1768536984243594058971905)
          ·
            refine ⟨1326402738182695544228929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1768536984243594058971905 1326402738182695544228929)
            ·
              refine ⟨994802053637021658171697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1326402738182695544228929 994802053637021658171697)
              ·
                refine ⟨746101540227766243628773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 994802053637021658171697 746101540227766243628773)
                ·
                  refine ⟨139894038792706170680395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 746101540227766243628773 139894038792706170680395)
                  ·
                    rfl

theorem cell21_612996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_612996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612996 prefixEnd_612996 := by exact prefixLift 612996
  have htrace : WordTrace (prefixWord ++ tailWord_612996) baseStart_612996 baseEnd_612996 := by
    simpa [prefixWord, tailWord_612996, baseEnd_612996] using wordTrace_append hprefix tailTrace_612996
  have hstable : (prefixWord ++ tailWord_612996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612996).length < 2 ^ (prefixWord ++ tailWord_612996).sum := by decide
  have hdescent : baseEnd_612996 < baseStart_612996 := by decide
  rcases family_descends (prefixWord ++ tailWord_612996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613010 : List Nat := [3, 2, 3, 1, 2, 1, 3, 6]
def baseStart_613010 : Nat := 118140960795 + 613010 * 2 ^ 59
def prefixEnd_613010 : Nat := 4983230072969 + 3 ^ 40 * 613010 * 2
def baseEnd_613010 : Nat := 46632411261148419149011

theorem tailTrace_613010 : CollatzResearch.WordTrace tailWord_613010 prefixEnd_613010 46632411261148419149011 := by
  unfold tailWord_613010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5589577877294234654503121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14905541006117959078674989 5589577877294234654503121)
  ·
    refine ⟨4192183407970675990877341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5589577877294234654503121 4192183407970675990877341)
    ·
      refine ⟨1572068777989003496579003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4192183407970675990877341 1572068777989003496579003)
      ·
        refine ⟨2358103166983505244868505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572068777989003496579003 2358103166983505244868505)
        ·
          refine ⟨1768577375237628933651379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2358103166983505244868505 1768577375237628933651379)
          ·
            refine ⟨2652866062856443400477069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768577375237628933651379 2652866062856443400477069)
            ·
              refine ⟨994824773571166275178901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2652866062856443400477069 994824773571166275178901)
              ·
                refine ⟨46632411261148419149011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 994824773571166275178901 46632411261148419149011)
                ·
                  rfl

theorem cell21_613010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_613010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613010 prefixEnd_613010 := by exact prefixLift 613010
  have htrace : WordTrace (prefixWord ++ tailWord_613010) baseStart_613010 baseEnd_613010 := by
    simpa [prefixWord, tailWord_613010, baseEnd_613010] using wordTrace_append hprefix tailTrace_613010
  have hstable : (prefixWord ++ tailWord_613010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613010).length < 2 ^ (prefixWord ++ tailWord_613010).sum := by decide
  have hdescent : baseEnd_613010 < baseStart_613010 := by decide
  rcases family_descends (prefixWord ++ tailWord_613010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613055 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 4]
def baseStart_613055 : Nat := 118140960795 + 613055 * 2 ^ 59
def prefixEnd_613055 : Nat := 4983230072969 + 3 ^ 40 * 613055 * 2
def baseEnd_613055 : Nat := 139907503396535179196941

theorem tailTrace_613055 : CollatzResearch.WordTrace tailWord_613055 prefixEnd_613055 139907503396535179196941 := by
  unfold tailWord_613055
  simp only [CollatzResearch.WordTrace]
  refine ⟨22359952794013911303400619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14906635196009274202267079 22359952794013911303400619)
  ·
    refine ⟨33539929191020866955100929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22359952794013911303400619 33539929191020866955100929)
    ·
      refine ⟨25154946893265650216325697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33539929191020866955100929 25154946893265650216325697)
      ·
        refine ⟨18866210169949237662244273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25154946893265650216325697 18866210169949237662244273)
        ·
          refine ⟨14149657627461928246683205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18866210169949237662244273 14149657627461928246683205)
          ·
            refine ⟨2653060805149111546253101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14149657627461928246683205 2653060805149111546253101)
            ·
              refine ⟨994897801930916829844913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2653060805149111546253101 994897801930916829844913)
              ·
                refine ⟨746173351448187622383685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 994897801930916829844913 746173351448187622383685)
                ·
                  refine ⟨139907503396535179196941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 746173351448187622383685 139907503396535179196941)
                  ·
                    rfl

theorem cell21_613055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 4].length) (baseStart_613055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613055 prefixEnd_613055 := by exact prefixLift 613055
  have htrace : WordTrace (prefixWord ++ tailWord_613055) baseStart_613055 baseEnd_613055 := by
    simpa [prefixWord, tailWord_613055, baseEnd_613055] using wordTrace_append hprefix tailTrace_613055
  have hstable : (prefixWord ++ tailWord_613055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613055).length < 2 ^ (prefixWord ++ tailWord_613055).sum := by decide
  have hdescent : baseEnd_613055 < baseStart_613055 := by decide
  rcases family_descends (prefixWord ++ tailWord_613055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613109 : List Nat := [1, 3, 6, 1, 1, 1, 3, 2, 3]
def baseStart_613109 : Nat := 118140960795 + 613109 * 2 ^ 59
def prefixEnd_613109 : Nat := 4983230072969 + 3 ^ 40 * 613109 * 2
def baseEnd_613109 : Nat := 139919826932243085296831

theorem tailTrace_613109 : CollatzResearch.WordTrace tailWord_613109 prefixEnd_613109 139919826932243085296831 := by
  unfold tailWord_613109
  simp only [CollatzResearch.WordTrace]
  refine ⟨22361922335818278525866381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14907948223878852350577587 22361922335818278525866381)
  ·
    refine ⟨8385720875931854447199893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22361922335818278525866381 8385720875931854447199893)
    ·
      refine ⟨393080666059305677212495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8385720875931854447199893 393080666059305677212495)
      ·
        refine ⟨589620999088958515818743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393080666059305677212495 589620999088958515818743)
        ·
          refine ⟨884431498633437773728115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589620999088958515818743 884431498633437773728115)
          ·
            refine ⟨1326647247950156660592173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884431498633437773728115 1326647247950156660592173)
            ·
              refine ⟨497492717981308747722065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1326647247950156660592173 497492717981308747722065)
              ·
                refine ⟨373119538485981560791549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497492717981308747722065 373119538485981560791549)
                ·
                  refine ⟨139919826932243085296831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373119538485981560791549 139919826932243085296831)
                  ·
                    rfl

theorem cell21_613109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_613109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613109 prefixEnd_613109 := by exact prefixLift 613109
  have htrace : WordTrace (prefixWord ++ tailWord_613109) baseStart_613109 baseEnd_613109 := by
    simpa [prefixWord, tailWord_613109, baseEnd_613109] using wordTrace_append hprefix tailTrace_613109
  have hstable : (prefixWord ++ tailWord_613109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613109).length < 2 ^ (prefixWord ++ tailWord_613109).sum := by decide
  have hdescent : baseEnd_613109 < baseStart_613109 := by decide
  rcases family_descends (prefixWord ++ tailWord_613109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613114 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_613114 : Nat := 118140960795 + 613114 * 2 ^ 59
def prefixEnd_613114 : Nat := 4983230072969 + 3 ^ 40 * 613114 * 2
def baseEnd_613114 : Nat := 139920968000364187713487

theorem tailTrace_613114 : CollatzResearch.WordTrace tailWord_613114 prefixEnd_613114 139920968000364187713487 := by
  unfold tailWord_613114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5590526175200041094949599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14908069800533442919865597 5590526175200041094949599)
  ·
    refine ⟨8385789262800061642424399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5590526175200041094949599 8385789262800061642424399)
    ·
      refine ⟨12578683894200092463636599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8385789262800061642424399 12578683894200092463636599)
      ·
        refine ⟨18868025841300138695454899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12578683894200092463636599 18868025841300138695454899)
        ·
          refine ⟨28302038761950208043182349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18868025841300138695454899 28302038761950208043182349)
          ·
            refine ⟨10613264535731328016193381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28302038761950208043182349 10613264535731328016193381)
            ·
              refine ⟨1989987100449624003036259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10613264535731328016193381 1989987100449624003036259)
              ·
                refine ⟨2984980650674436004554389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989987100449624003036259 2984980650674436004554389)
                ·
                  refine ⟨139920968000364187713487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2984980650674436004554389 139920968000364187713487)
                  ·
                    rfl

theorem cell21_613114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_613114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613114 prefixEnd_613114 := by exact prefixLift 613114
  have htrace : WordTrace (prefixWord ++ tailWord_613114) baseStart_613114 baseEnd_613114 := by
    simpa [prefixWord, tailWord_613114, baseEnd_613114] using wordTrace_append hprefix tailTrace_613114
  have hstable : (prefixWord ++ tailWord_613114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613114).length < 2 ^ (prefixWord ++ tailWord_613114).sum := by decide
  have hdescent : baseEnd_613114 < baseStart_613114 := by decide
  rcases family_descends (prefixWord ++ tailWord_613114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613162 : List Nat := [3, 1, 4, 3, 1, 9]
def baseStart_613162 : Nat := 118140960795 + 613162 * 2 ^ 59
def prefixEnd_613162 : Nat := 4983230072969 + 3 ^ 40 * 613162 * 2
def baseEnd_613162 : Nat := 5182663787197287811607

theorem tailTrace_613162 : CollatzResearch.WordTrace tailWord_613162 prefixEnd_613162 5182663787197287811607 := by
  unfold tailWord_613162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5590963851156567144386435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14909236936417512385030493 5590963851156567144386435)
  ·
    refine ⟨8386445776734850716579653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5590963851156567144386435 8386445776734850716579653)
    ·
      refine ⟨1572458583137784509358685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8386445776734850716579653 1572458583137784509358685)
      ·
        refine ⟨589671968676669191009507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1572458583137784509358685 589671968676669191009507)
        ·
          refine ⟨884507953015003786514261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589671968676669191009507 884507953015003786514261)
          ·
            refine ⟨5182663787197287811607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 884507953015003786514261 5182663787197287811607)
            ·
              rfl

theorem cell21_613162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 9].length) (baseStart_613162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613162 prefixEnd_613162 := by exact prefixLift 613162
  have htrace : WordTrace (prefixWord ++ tailWord_613162) baseStart_613162 baseEnd_613162 := by
    simpa [prefixWord, tailWord_613162, baseEnd_613162] using wordTrace_append hprefix tailTrace_613162
  have hstable : (prefixWord ++ tailWord_613162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613162).length < 2 ^ (prefixWord ++ tailWord_613162).sum := by decide
  have hdescent : baseEnd_613162 < baseStart_613162 := by decide
  rcases family_descends (prefixWord ++ tailWord_613162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613224 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 4]
def baseStart_613224 : Nat := 118140960795 + 613224 * 2 ^ 59
def prefixEnd_613224 : Nat := 4983230072969 + 3 ^ 40 * 613224 * 2
def baseEnd_613224 : Nat := 139946071499028440879929

theorem tailTrace_613224 : CollatzResearch.WordTrace tailWord_613224 prefixEnd_613224 139946071499028440879929 := by
  unfold tailWord_613224
  simp only [CollatzResearch.WordTrace]
  refine ⟨11183058365200826583151363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14910744486934435444201817 11183058365200826583151363)
  ·
    refine ⟨16774587547801239874727045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11183058365200826583151363 16774587547801239874727045)
    ·
      refine ⟨3145235165212732476511321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16774587547801239874727045 3145235165212732476511321)
      ·
        refine ⟨2358926373909549357383491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3145235165212732476511321 2358926373909549357383491)
        ·
          refine ⟨3538389560864324036075237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358926373909549357383491 3538389560864324036075237)
          ·
            refine ⟨663448042662060756764107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3538389560864324036075237 663448042662060756764107)
            ·
              refine ⟨995172063993091135146161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663448042662060756764107 995172063993091135146161)
              ·
                refine ⟨746379047994818351359621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 995172063993091135146161 746379047994818351359621)
                ·
                  refine ⟨139946071499028440879929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 746379047994818351359621 139946071499028440879929)
                  ·
                    rfl

theorem cell21_613224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_613224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613224 prefixEnd_613224 := by exact prefixLift 613224
  have htrace : WordTrace (prefixWord ++ tailWord_613224) baseStart_613224 baseEnd_613224 := by
    simpa [prefixWord, tailWord_613224, baseEnd_613224] using wordTrace_append hprefix tailTrace_613224
  have hstable : (prefixWord ++ tailWord_613224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613224).length < 2 ^ (prefixWord ++ tailWord_613224).sum := by decide
  have hdescent : baseEnd_613224 < baseStart_613224 := by decide
  rcases family_descends (prefixWord ++ tailWord_613224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613235 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 5]
def baseStart_613235 : Nat := 118140960795 + 613235 * 2 ^ 59
def prefixEnd_613235 : Nat := 4983230072969 + 3 ^ 40 * 613235 * 2
def baseEnd_613235 : Nat := 139948581848894866196573

theorem tailTrace_613235 : CollatzResearch.WordTrace tailWord_613235 prefixEnd_613235 139948581848894866196573 := by
  unfold tailWord_613235
  simp only [CollatzResearch.WordTrace]
  refine ⟨22366517933361802044953159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14911011955574534696635439 22366517933361802044953159)
  ·
    refine ⟨33549776900042703067429739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22366517933361802044953159 33549776900042703067429739)
    ·
      refine ⟨50324665350064054601144609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33549776900042703067429739 50324665350064054601144609)
      ·
        refine ⟨37743499012548040950858457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50324665350064054601144609 37743499012548040950858457)
        ·
          refine ⟨28307624259411030713143843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37743499012548040950858457 28307624259411030713143843)
          ·
            refine ⟨42461436389116546069715765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28307624259411030713143843 42461436389116546069715765)
            ·
              refine ⟨3980759661479676194035853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42461436389116546069715765 3980759661479676194035853)
              ·
                refine ⟨1492784873054878572763445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3980759661479676194035853 1492784873054878572763445)
                ·
                  refine ⟨139948581848894866196573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1492784873054878572763445 139948581848894866196573)
                  ·
                    rfl

theorem cell21_613235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_613235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613235 prefixEnd_613235 := by exact prefixLift 613235
  have htrace : WordTrace (prefixWord ++ tailWord_613235) baseStart_613235 baseEnd_613235 := by
    simpa [prefixWord, tailWord_613235, baseEnd_613235] using wordTrace_append hprefix tailTrace_613235
  have hstable : (prefixWord ++ tailWord_613235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613235).length < 2 ^ (prefixWord ++ tailWord_613235).sum := by decide
  have hdescent : baseEnd_613235 < baseStart_613235 := by decide
  rcases family_descends (prefixWord ++ tailWord_613235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613269 : List Nat := [1, 3, 2, 1, 1, 4, 3, 3, 3]
def baseStart_613269 : Nat := 118140960795 + 613269 * 2 ^ 59
def prefixEnd_613269 : Nat := 4983230072969 + 3 ^ 40 * 613269 * 2
def baseEnd_613269 : Nat := 139956341112118362629837

theorem tailTrace_613269 : CollatzResearch.WordTrace tailWord_613269 prefixEnd_613269 139956341112118362629837 := by
  unfold tailWord_613269
  simp only [CollatzResearch.WordTrace]
  refine ⟨22367758015238625851690861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14911838676825750567793907 22367758015238625851690861)
  ·
    refine ⟨8387909255714484694384073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22367758015238625851690861 8387909255714484694384073)
    ·
      refine ⟨6290931941785863520788055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8387909255714484694384073 6290931941785863520788055)
      ·
        refine ⟨9436397912678795281182083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6290931941785863520788055 9436397912678795281182083)
        ·
          refine ⟨14154596869018192921773125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9436397912678795281182083 14154596869018192921773125)
          ·
            refine ⟨2653986912940911172832461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14154596869018192921773125 2653986912940911172832461)
            ·
              refine ⟨995245092352841689812173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2653986912940911172832461 995245092352841689812173)
              ·
                refine ⟨373216909632315633679565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 995245092352841689812173 373216909632315633679565)
                ·
                  refine ⟨139956341112118362629837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373216909632315633679565 139956341112118362629837)
                  ·
                    rfl

theorem cell21_613269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_613269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613269 prefixEnd_613269 := by exact prefixLift 613269
  have htrace : WordTrace (prefixWord ++ tailWord_613269) baseStart_613269 baseEnd_613269 := by
    simpa [prefixWord, tailWord_613269, baseEnd_613269] using wordTrace_append hprefix tailTrace_613269
  have hstable : (prefixWord ++ tailWord_613269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613269).length < 2 ^ (prefixWord ++ tailWord_613269).sum := by decide
  have hdescent : baseEnd_613269 < baseStart_613269 := by decide
  rcases family_descends (prefixWord ++ tailWord_613269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613280 : List Nat := [2, 1, 1, 4, 1, 1, 11]
def baseStart_613280 : Nat := 118140960795 + 613280 * 2 ^ 59
def prefixEnd_613280 : Nat := 4983230072969 + 3 ^ 40 * 613280 * 2
def baseEnd_613280 : Nat := 15550983495776087549609

theorem tailTrace_613280 : CollatzResearch.WordTrace tailWord_613280 prefixEnd_613280 15550983495776087549609 := by
  unfold tailWord_613280
  simp only [CollatzResearch.WordTrace]
  refine ⟨11184079609099387365170647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14912106145465849820227529 11184079609099387365170647)
  ·
    refine ⟨16776119413649081047755971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11184079609099387365170647 16776119413649081047755971)
    ·
      refine ⟨25164179120473621571633957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16776119413649081047755971 25164179120473621571633957)
      ·
        refine ⟨4718283585088804044681367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25164179120473621571633957 4718283585088804044681367)
        ·
          refine ⟨7077425377633206067022051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4718283585088804044681367 7077425377633206067022051)
          ·
            refine ⟨10616138066449809100533077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7077425377633206067022051 10616138066449809100533077)
            ·
              refine ⟨15550983495776087549609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10616138066449809100533077 15550983495776087549609)
              ·
                rfl

theorem cell21_613280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 11].length) (baseStart_613280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613280 prefixEnd_613280 := by exact prefixLift 613280
  have htrace : WordTrace (prefixWord ++ tailWord_613280) baseStart_613280 baseEnd_613280 := by
    simpa [prefixWord, tailWord_613280, baseEnd_613280] using wordTrace_append hprefix tailTrace_613280
  have hstable : (prefixWord ++ tailWord_613280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613280).length < 2 ^ (prefixWord ++ tailWord_613280).sum := by decide
  have hdescent : baseEnd_613280 < baseStart_613280 := by decide
  rcases family_descends (prefixWord ++ tailWord_613280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613328 : List Nat := [2, 1, 1, 1, 1, 2, 3, 7, 3]
def baseStart_613328 : Nat := 118140960795 + 613328 * 2 ^ 59
def prefixEnd_613328 : Nat := 4983230072969 + 3 ^ 40 * 613328 * 2
def baseEnd_613328 : Nat := 139969805715947371146383

theorem tailTrace_613328 : CollatzResearch.WordTrace tailWord_613328 prefixEnd_613328 139969805715947371146383 := by
  unfold tailWord_613328
  simp only [CollatzResearch.WordTrace]
  refine ⟨11184954961012439464044319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14913273281349919285392425 11184954961012439464044319)
  ·
    refine ⟨16777432441518659196066479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11184954961012439464044319 16777432441518659196066479)
    ·
      refine ⟨25166148662277988794099719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16777432441518659196066479 25166148662277988794099719)
      ·
        refine ⟨37749222993416983191149579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25166148662277988794099719 37749222993416983191149579)
        ·
          refine ⟨56623834490125474786724369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37749222993416983191149579 56623834490125474786724369)
          ·
            refine ⟨42467875867594106090043277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56623834490125474786724369 42467875867594106090043277)
            ·
              refine ⟨15925453450347789783766229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42467875867594106090043277 15925453450347789783766229)
              ·
                refine ⟨373252815242526323057021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15925453450347789783766229 373252815242526323057021)
                ·
                  refine ⟨139969805715947371146383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373252815242526323057021 139969805715947371146383)
                  ·
                    rfl

theorem cell21_613328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 3].length) (baseStart_613328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613328 prefixEnd_613328 := by exact prefixLift 613328
  have htrace : WordTrace (prefixWord ++ tailWord_613328) baseStart_613328 baseEnd_613328 := by
    simpa [prefixWord, tailWord_613328, baseEnd_613328] using wordTrace_append hprefix tailTrace_613328
  have hstable : (prefixWord ++ tailWord_613328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613328).length < 2 ^ (prefixWord ++ tailWord_613328).sum := by decide
  have hdescent : baseEnd_613328 < baseStart_613328 := by decide
  rcases family_descends (prefixWord ++ tailWord_613328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613438 : List Nat := [4, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_613438 : Nat := 118140960795 + 613438 * 2 ^ 59
def prefixEnd_613438 : Nat := 4983230072969 + 3 ^ 40 * 613438 * 2
def baseEnd_613438 : Nat := 139994909214611624312825

theorem tailTrace_613438 : CollatzResearch.WordTrace tailWord_613438 prefixEnd_613438 139994909214611624312825 := by
  unfold tailWord_613438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2796740243953295964324121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14915947967750911809728645 2796740243953295964324121)
  ·
    refine ⟨2097555182964971973243091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2796740243953295964324121 2097555182964971973243091)
    ·
      refine ⟨3146332774447457959864637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2097555182964971973243091 3146332774447457959864637)
      ·
        refine ⟨1179874790417796734949239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3146332774447457959864637 1179874790417796734949239)
        ·
          refine ⟨1769812185626695102423859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179874790417796734949239 1769812185626695102423859)
          ·
            refine ⟨2654718278440042653635789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769812185626695102423859 2654718278440042653635789)
            ·
              refine ⟨995519354415015995113421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2654718278440042653635789 995519354415015995113421)
              ·
                refine ⟨373319757905630998167533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 995519354415015995113421 373319757905630998167533)
                ·
                  refine ⟨139994909214611624312825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373319757905630998167533 139994909214611624312825)
                  ·
                    rfl

theorem cell21_613438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_613438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613438 prefixEnd_613438 := by exact prefixLift 613438
  have htrace : WordTrace (prefixWord ++ tailWord_613438) baseStart_613438 baseEnd_613438 := by
    simpa [prefixWord, tailWord_613438, baseEnd_613438] using wordTrace_append hprefix tailTrace_613438
  have hstable : (prefixWord ++ tailWord_613438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613438).length < 2 ^ (prefixWord ++ tailWord_613438).sum := by decide
  have hdescent : baseEnd_613438 < baseStart_613438 := by decide
  rcases family_descends (prefixWord ++ tailWord_613438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613508 : List Nat := [2, 3, 2, 1, 2, 11]
def baseStart_613508 : Nat := 118140960795 + 613508 * 2 ^ 59
def prefixEnd_613508 : Nat := 4983230072969 + 3 ^ 40 * 613508 * 2
def baseEnd_613508 : Nat := 5185588302529891042445

theorem tailTrace_613508 : CollatzResearch.WordTrace tailWord_613508 prefixEnd_613508 5185588302529891042445 := by
  unfold tailWord_613508
  simp only [CollatzResearch.WordTrace]
  refine ⟨11188237530686384834820589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14917650040915179779760785 11188237530686384834820589)
  ·
    refine ⟨4195589074007394313057721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11188237530686384834820589 4195589074007394313057721)
    ·
      refine ⟨3146691805505545734793291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4195589074007394313057721 3146691805505545734793291)
      ·
        refine ⟨4720037708258318602189937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3146691805505545734793291 4720037708258318602189937)
        ·
          refine ⟨3540028281193738951642453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4720037708258318602189937 3540028281193738951642453)
          ·
            refine ⟨5185588302529891042445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3540028281193738951642453 5185588302529891042445)
            ·
              rfl

theorem cell21_613508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 11].length) (baseStart_613508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613508 prefixEnd_613508 := by exact prefixLift 613508
  have htrace : WordTrace (prefixWord ++ tailWord_613508) baseStart_613508 baseEnd_613508 := by
    simpa [prefixWord, tailWord_613508, baseEnd_613508] using wordTrace_append hprefix tailTrace_613508
  have hstable : (prefixWord ++ tailWord_613508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613508).length < 2 ^ (prefixWord ++ tailWord_613508).sum := by decide
  have hdescent : baseEnd_613508 < baseStart_613508 := by decide
  rcases family_descends (prefixWord ++ tailWord_613508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613601 : List Nat := [1, 2, 3, 1, 3, 2, 4, 5]
def baseStart_613601 : Nat := 118140960795 + 613601 * 2 ^ 59
def prefixEnd_613601 : Nat := 4983230072969 + 3 ^ 40 * 613601 * 2
def baseEnd_613601 : Nat := 46677369345119854365275

theorem tailTrace_613601 : CollatzResearch.WordTrace tailWord_613601 prefixEnd_613601 46677369345119854365275 := by
  unfold tailWord_613601
  simp only [CollatzResearch.WordTrace]
  refine ⟨22379867050035846552776657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14919911366690564368517771 22379867050035846552776657)
  ·
    refine ⟨16784900287526884914582493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22379867050035846552776657 16784900287526884914582493)
    ·
      refine ⟨6294337607822581842968435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16784900287526884914582493 6294337607822581842968435)
      ·
        refine ⟨9441506411733872764452653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6294337607822581842968435 9441506411733872764452653)
        ·
          refine ⟨3540564904400202286669745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9441506411733872764452653 3540564904400202286669745)
          ·
            refine ⟨2655423678300151715002309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3540564904400202286669745 2655423678300151715002309)
            ·
              refine ⟨497891939681278446562933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2655423678300151715002309 497891939681278446562933)
              ·
                refine ⟨46677369345119854365275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 497891939681278446562933 46677369345119854365275)
                ·
                  rfl

theorem cell21_613601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 5].length) (baseStart_613601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613601 prefixEnd_613601 := by exact prefixLift 613601
  have htrace : WordTrace (prefixWord ++ tailWord_613601) baseStart_613601 baseEnd_613601 := by
    simpa [prefixWord, tailWord_613601, baseEnd_613601] using wordTrace_append hprefix tailTrace_613601
  have hstable : (prefixWord ++ tailWord_613601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613601).length < 2 ^ (prefixWord ++ tailWord_613601).sum := by decide
  have hdescent : baseEnd_613601 < baseStart_613601 := by decide
  rcases family_descends (prefixWord ++ tailWord_613601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613607 : List Nat := [1, 1, 5, 3, 3, 1, 1, 3, 3]
def baseStart_613607 : Nat := 118140960795 + 613607 * 2 ^ 59
def prefixEnd_613607 : Nat := 4983230072969 + 3 ^ 40 * 613607 * 2
def baseEnd_613607 : Nat := 140033477317104885995813

theorem tailTrace_613607 : CollatzResearch.WordTrace tailWord_613607 prefixEnd_613607 140033477317104885995813 := by
  unfold tailWord_613607
  simp only [CollatzResearch.WordTrace]
  refine ⟨22380085888014109577495075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14920057258676073051663383 22380085888014109577495075)
  ·
    refine ⟨33570128832021164366242613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22380085888014109577495075 33570128832021164366242613)
    ·
      refine ⟨3147199578001984159335245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33570128832021164366242613 3147199578001984159335245)
      ·
        refine ⟨1180199841750744059750717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3147199578001984159335245 1180199841750744059750717)
        ·
          refine ⟨442574940656529022406519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1180199841750744059750717 442574940656529022406519)
          ·
            refine ⟨663862410984793533609779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442574940656529022406519 663862410984793533609779)
            ·
              refine ⟨995793616477190300414669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663862410984793533609779 995793616477190300414669)
              ·
                refine ⟨373422606178946362655501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 995793616477190300414669 373422606178946362655501)
                ·
                  refine ⟨140033477317104885995813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373422606178946362655501 140033477317104885995813)
                  ·
                    rfl

theorem cell21_613607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 3].length) (baseStart_613607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613607 prefixEnd_613607 := by exact prefixLift 613607
  have htrace : WordTrace (prefixWord ++ tailWord_613607) baseStart_613607 baseEnd_613607 := by
    simpa [prefixWord, tailWord_613607, baseEnd_613607] using wordTrace_append hprefix tailTrace_613607
  have hstable : (prefixWord ++ tailWord_613607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613607).length < 2 ^ (prefixWord ++ tailWord_613607).sum := by decide
  have hdescent : baseEnd_613607 < baseStart_613607 := by decide
  rcases family_descends (prefixWord ++ tailWord_613607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613618 : List Nat := [3, 2, 1, 3, 4, 1, 7]
def baseStart_613618 : Nat := 118140960795 + 613618 * 2 ^ 59
def prefixEnd_613618 : Nat := 4983230072969 + 3 ^ 40 * 613618 * 2
def baseEnd_613618 : Nat := 15559554185219034590273

theorem tailTrace_613618 : CollatzResearch.WordTrace tailWord_613618 prefixEnd_613618 15559554185219034590273 := by
  unfold tailWord_613618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5595121772743564614036377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14920324727316172304097005 5595121772743564614036377)
  ·
    refine ⟨4196341329557673460527283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5595121772743564614036377 4196341329557673460527283)
    ·
      refine ⟨6294511994336510190790925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4196341329557673460527283 6294511994336510190790925)
      ·
        refine ⟨2360441997876191321546597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6294511994336510190790925 2360441997876191321546597)
        ·
          refine ⟨442582874601785872789987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2360441997876191321546597 442582874601785872789987)
          ·
            refine ⟨663874311902678809184981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442582874601785872789987 663874311902678809184981)
            ·
              refine ⟨15559554185219034590273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 663874311902678809184981 15559554185219034590273)
              ·
                rfl

theorem cell21_613618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 7].length) (baseStart_613618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613618 prefixEnd_613618 := by exact prefixLift 613618
  have htrace : WordTrace (prefixWord ++ tailWord_613618) baseStart_613618 baseEnd_613618 := by
    simpa [prefixWord, tailWord_613618, baseEnd_613618] using wordTrace_append hprefix tailTrace_613618
  have hstable : (prefixWord ++ tailWord_613618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613618).length < 2 ^ (prefixWord ++ tailWord_613618).sum := by decide
  have hdescent : baseEnd_613618 < baseStart_613618 := by decide
  rcases family_descends (prefixWord ++ tailWord_613618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613660 : List Nat := [2, 2, 3, 1, 1, 1, 4, 7]
def baseStart_613660 : Nat := 118140960795 + 613660 * 2 ^ 59
def prefixEnd_613660 : Nat := 4983230072969 + 3 ^ 40 * 613660 * 2
def baseEnd_613660 : Nat := 46681857546396190537457

theorem tailTrace_613660 : CollatzResearch.WordTrace tailWord_613660 prefixEnd_613660 46681857546396190537457 := by
  unfold tailWord_613660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11191009478411049814587217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14921345971214733086116289 11191009478411049814587217)
  ·
    refine ⟨8393257108808287360940413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11191009478411049814587217 8393257108808287360940413)
    ·
      refine ⟨3147471415803107760352655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8393257108808287360940413 3147471415803107760352655)
      ·
        refine ⟨4721207123704661640528983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3147471415803107760352655 4721207123704661640528983)
        ·
          refine ⟨7081810685556992460793475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721207123704661640528983 7081810685556992460793475)
          ·
            refine ⟨10622716028335488691190213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7081810685556992460793475 10622716028335488691190213)
            ·
              refine ⟨1991759255312904129598165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10622716028335488691190213 1991759255312904129598165)
              ·
                refine ⟨46681857546396190537457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1991759255312904129598165 46681857546396190537457)
                ·
                  rfl

theorem cell21_613660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_613660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613660 prefixEnd_613660 := by exact prefixLift 613660
  have htrace : WordTrace (prefixWord ++ tailWord_613660) baseStart_613660 baseEnd_613660 := by
    simpa [prefixWord, tailWord_613660, baseEnd_613660] using wordTrace_append hprefix tailTrace_613660
  have hstable : (prefixWord ++ tailWord_613660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613660).length < 2 ^ (prefixWord ++ tailWord_613660).sum := by decide
  have hdescent : baseEnd_613660 < baseStart_613660 := by decide
  rcases family_descends (prefixWord ++ tailWord_613660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613677 : List Nat := [1, 5, 3, 1, 1, 10]
def baseStart_613677 : Nat := 118140960795 + 613677 * 2 ^ 59
def prefixEnd_613677 : Nat := 4983230072969 + 3 ^ 40 * 613677 * 2
def baseEnd_613677 : Nat := 5187016750770382215889

theorem tailTrace_613677 : CollatzResearch.WordTrace tailWord_613677 prefixEnd_613677 5187016750770382215889 := by
  unfold tailWord_613677
  simp only [CollatzResearch.WordTrace]
  refine ⟨22382638997760511532543285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14921759331840341021695523 22382638997760511532543285)
  ·
    refine ⟨2098372406040047956175933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22382638997760511532543285 2098372406040047956175933)
    ·
      refine ⟨786889652265017983565975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2098372406040047956175933 786889652265017983565975)
      ·
        refine ⟨1180334478397526975348963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786889652265017983565975 1180334478397526975348963)
        ·
          refine ⟨1770501717596290463023445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180334478397526975348963 1770501717596290463023445)
          ·
            refine ⟨5187016750770382215889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1770501717596290463023445 5187016750770382215889)
            ·
              rfl

theorem cell21_613677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 10].length) (baseStart_613677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613677 prefixEnd_613677 := by exact prefixLift 613677
  have htrace : WordTrace (prefixWord ++ tailWord_613677) baseStart_613677 baseEnd_613677 := by
    simpa [prefixWord, tailWord_613677, baseEnd_613677] using wordTrace_append hprefix tailTrace_613677
  have hstable : (prefixWord ++ tailWord_613677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613677).length < 2 ^ (prefixWord ++ tailWord_613677).sum := by decide
  have hdescent : baseEnd_613677 < baseStart_613677 := by decide
  rcases family_descends (prefixWord ++ tailWord_613677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613767 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 5]
def baseStart_613767 : Nat := 118140960795 + 613767 * 2 ^ 59
def prefixEnd_613767 : Nat := 4983230072969 + 3 ^ 40 * 613767 * 2
def baseEnd_613767 : Nat := 140069991496980163328819

theorem tailTrace_613767 : CollatzResearch.WordTrace tailWord_613767 prefixEnd_613767 140069991496980163328819 := by
  unfold tailWord_613767
  simp only [CollatzResearch.WordTrace]
  refine ⟨22385921567434456903319555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14923947711622971268879703 22385921567434456903319555)
  ·
    refine ⟨33578882351151685354979333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22385921567434456903319555 33578882351151685354979333)
    ·
      refine ⟨6296040440840941004058625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33578882351151685354979333 6296040440840941004058625)
      ·
        refine ⟨4722030330630705753043969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6296040440840941004058625 4722030330630705753043969)
        ·
          refine ⟨3541522747973029314782977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4722030330630705753043969 3541522747973029314782977)
          ·
            refine ⟨2656142060979771986087233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3541522747973029314782977 2656142060979771986087233)
            ·
              refine ⟨1992106545734828989565425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2656142060979771986087233 1992106545734828989565425)
              ·
                refine ⟨1494079909301121742174069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1992106545734828989565425 1494079909301121742174069)
                ·
                  refine ⟨140069991496980163328819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1494079909301121742174069 140069991496980163328819)
                  ·
                    rfl

theorem cell21_613767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_613767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613767 prefixEnd_613767 := by exact prefixLift 613767
  have htrace : WordTrace (prefixWord ++ tailWord_613767) baseStart_613767 baseEnd_613767 := by
    simpa [prefixWord, tailWord_613767, baseEnd_613767] using wordTrace_append hprefix tailTrace_613767
  have hstable : (prefixWord ++ tailWord_613767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613767).length < 2 ^ (prefixWord ++ tailWord_613767).sum := by decide
  have hdescent : baseEnd_613767 < baseStart_613767 := by decide
  rcases family_descends (prefixWord ++ tailWord_613767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613781 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 6]
def baseStart_613781 : Nat := 118140960795 + 613781 * 2 ^ 59
def prefixEnd_613781 : Nat := 4983230072969 + 3 ^ 40 * 613781 * 2
def baseEnd_613781 : Nat := 140073186487719250095457

theorem tailTrace_613781 : CollatzResearch.WordTrace tailWord_613781 prefixEnd_613781 140073186487719250095457 := by
  unfold tailWord_613781
  simp only [CollatzResearch.WordTrace]
  refine ⟨22386432189383737294329197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14924288126255824862886131 22386432189383737294329197)
  ·
    refine ⟨8394912071018901485373449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22386432189383737294329197 8394912071018901485373449)
    ·
      refine ⟨6296184053264176114030087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8394912071018901485373449 6296184053264176114030087)
      ·
        refine ⟨9444276079896264171045131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6296184053264176114030087 9444276079896264171045131)
        ·
          refine ⟨14166414119844396256567697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9444276079896264171045131 14166414119844396256567697)
          ·
            refine ⟨10624810589883297192425773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14166414119844396256567697 10624810589883297192425773)
            ·
              refine ⟨3984303971206236447159665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10624810589883297192425773 3984303971206236447159665)
              ·
                refine ⟨2988227978404677335369749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3984303971206236447159665 2988227978404677335369749)
                ·
                  refine ⟨140073186487719250095457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2988227978404677335369749 140073186487719250095457)
                  ·
                    rfl

theorem cell21_613781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_613781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613781 prefixEnd_613781 := by exact prefixLift 613781
  have htrace : WordTrace (prefixWord ++ tailWord_613781) baseStart_613781 baseEnd_613781 := by
    simpa [prefixWord, tailWord_613781, baseEnd_613781] using wordTrace_append hprefix tailTrace_613781
  have hstable : (prefixWord ++ tailWord_613781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613781).length < 2 ^ (prefixWord ++ tailWord_613781).sum := by decide
  have hdescent : baseEnd_613781 < baseStart_613781 := by decide
  rcases family_descends (prefixWord ++ tailWord_613781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613964 : List Nat := [2, 2, 1, 3, 1, 5, 7]
def baseStart_613964 : Nat := 118140960795 + 613964 * 2 ^ 59
def prefixEnd_613964 : Nat := 4983230072969 + 3 ^ 40 * 613964 * 2
def baseEnd_613964 : Nat := 15568327731216844282787

theorem tailTrace_613964 : CollatzResearch.WordTrace tailWord_613964 prefixEnd_613964 15568327731216844282787 := by
  unfold tailWord_613964
  simp only [CollatzResearch.WordTrace]
  refine ⟨11196553373860379774120473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14928737831813839698827297 11196553373860379774120473)
  ·
    refine ⟨8397415030395284830590355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11196553373860379774120473 8397415030395284830590355)
    ·
      refine ⟨12596122545592927245885533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8397415030395284830590355 12596122545592927245885533)
      ·
        refine ⟨4723545954597347717207075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12596122545592927245885533 4723545954597347717207075)
        ·
          refine ⟨7085318931896021575810613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4723545954597347717207075 7085318931896021575810613)
          ·
            refine ⟨664248649865252022732245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7085318931896021575810613 664248649865252022732245)
            ·
              refine ⟨15568327731216844282787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 664248649865252022732245 15568327731216844282787)
              ·
                rfl

theorem cell21_613964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 7].length) (baseStart_613964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_613964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_613964 prefixEnd_613964 := by exact prefixLift 613964
  have htrace : WordTrace (prefixWord ++ tailWord_613964) baseStart_613964 baseEnd_613964 := by
    simpa [prefixWord, tailWord_613964, baseEnd_613964] using wordTrace_append hprefix tailTrace_613964
  have hstable : (prefixWord ++ tailWord_613964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613964).length < 2 ^ (prefixWord ++ tailWord_613964).sum := by decide
  have hdescent : baseEnd_613964 < baseStart_613964 := by decide
  rcases family_descends (prefixWord ++ tailWord_613964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614023 : List Nat := [1, 1, 4, 2, 1, 12]
def baseStart_614023 : Nat := 118140960795 + 614023 * 2 ^ 59
def prefixEnd_614023 : Nat := 4983230072969 + 3 ^ 40 * 614023 * 2
def baseEnd_614023 : Nat := 5189941266102985446727

theorem tailTrace_614023 : CollatzResearch.WordTrace tailWord_614023 prefixEnd_614023 5189941266102985446727 := by
  unfold tailWord_614023
  simp only [CollatzResearch.WordTrace]
  refine ⟨22395258654507012624638723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14930172436338008416425815 22395258654507012624638723)
  ·
    refine ⟨33592887981760518936958085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22395258654507012624638723 33592887981760518936958085)
    ·
      refine ⟨6298666496580097300679641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33592887981760518936958085 6298666496580097300679641)
      ·
        refine ⟨4723999872435072975509731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6298666496580097300679641 4723999872435072975509731)
        ·
          refine ⟨7085999808652609463264597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4723999872435072975509731 7085999808652609463264597)
          ·
            refine ⟨5189941266102985446727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7085999808652609463264597 5189941266102985446727)
            ·
              rfl

theorem cell21_614023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 12].length) (baseStart_614023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614023 prefixEnd_614023 := by exact prefixLift 614023
  have htrace : WordTrace (prefixWord ++ tailWord_614023) baseStart_614023 baseEnd_614023 := by
    simpa [prefixWord, tailWord_614023, baseEnd_614023] using wordTrace_append hprefix tailTrace_614023
  have hstable : (prefixWord ++ tailWord_614023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614023).length < 2 ^ (prefixWord ++ tailWord_614023).sum := by decide
  have hdescent : baseEnd_614023 < baseStart_614023 := by decide
  rcases family_descends (prefixWord ++ tailWord_614023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614026 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_614026 : Nat := 118140960795 + 614026 * 2 ^ 59
def prefixEnd_614026 : Nat := 4983230072969 + 3 ^ 40 * 614026 * 2
def baseEnd_614026 : Nat := 140129098825653268511623

theorem tailTrace_614026 : CollatzResearch.WordTrace tailWord_614026 prefixEnd_614026 140129098825653268511623 := by
  unfold tailWord_614026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5598842018374036034249483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14930245382330762757998621 5598842018374036034249483)
  ·
    refine ⟨8398263027561054051374225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5598842018374036034249483 8398263027561054051374225)
    ·
      refine ⟨6298697270670790538530669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8398263027561054051374225 6298697270670790538530669)
      ·
        refine ⟨2362011476501546451949001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6298697270670790538530669 2362011476501546451949001)
        ·
          refine ⟨1771508607376159838961751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2362011476501546451949001 1771508607376159838961751)
          ·
            refine ⟨2657262911064239758442627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771508607376159838961751 2657262911064239758442627)
            ·
              refine ⟨3985894366596359637663941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657262911064239758442627 3985894366596359637663941)
              ·
                refine ⟨747355193736817432061989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3985894366596359637663941 747355193736817432061989)
                ·
                  refine ⟨140129098825653268511623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 747355193736817432061989 140129098825653268511623)
                  ·
                    rfl

theorem cell21_614026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_614026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614026 prefixEnd_614026 := by exact prefixLift 614026
  have htrace : WordTrace (prefixWord ++ tailWord_614026) baseStart_614026 baseEnd_614026 := by
    simpa [prefixWord, tailWord_614026, baseEnd_614026] using wordTrace_append hprefix tailTrace_614026
  have hstable : (prefixWord ++ tailWord_614026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614026).length < 2 ^ (prefixWord ++ tailWord_614026).sum := by decide
  have hdescent : baseEnd_614026 < baseStart_614026 := by decide
  rcases family_descends (prefixWord ++ tailWord_614026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614040 : List Nat := [2, 1, 2, 4, 1, 2, 3, 6]
def baseStart_614040 : Nat := 118140960795 + 614040 * 2 ^ 59
def prefixEnd_614040 : Nat := 4983230072969 + 3 ^ 40 * 614040 * 2
def baseEnd_614040 : Nat := 46710764605464118426087

theorem tailTrace_614040 : CollatzResearch.WordTrace tailWord_614040 prefixEnd_614040 46710764605464118426087 := by
  unfold tailWord_614040
  simp only [CollatzResearch.WordTrace]
  refine ⟨11197939347722712264003787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14930585796963616352005049 11197939347722712264003787)
  ·
    refine ⟨16796909021584068396005681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11197939347722712264003787 16796909021584068396005681)
    ·
      refine ⟨12597681766188051297004261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16796909021584068396005681 12597681766188051297004261)
      ·
        refine ⟨2362065331160259618188299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12597681766188051297004261 2362065331160259618188299)
        ·
          refine ⟨3543097996740389427282449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2362065331160259618188299 3543097996740389427282449)
          ·
            refine ⟨2657323497555292070461837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3543097996740389427282449 2657323497555292070461837)
            ·
              refine ⟨996496311583234526423189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2657323497555292070461837 996496311583234526423189)
              ·
                refine ⟨46710764605464118426087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 996496311583234526423189 46710764605464118426087)
                ·
                  rfl

theorem cell21_614040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_614040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614040 prefixEnd_614040 := by exact prefixLift 614040
  have htrace : WordTrace (prefixWord ++ tailWord_614040) baseStart_614040 baseEnd_614040 := by
    simpa [prefixWord, tailWord_614040, baseEnd_614040] using wordTrace_append hprefix tailTrace_614040
  have hstable : (prefixWord ++ tailWord_614040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614040).length < 2 ^ (prefixWord ++ tailWord_614040).sum := by decide
  have hdescent : baseEnd_614040 < baseStart_614040 := by decide
  rcases family_descends (prefixWord ++ tailWord_614040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614147 : List Nat := [1, 1, 1, 3, 2, 2, 2, 6, 3]
def baseStart_614147 : Nat := 118140960795 + 614147 * 2 ^ 59
def prefixEnd_614147 : Nat := 4983230072969 + 3 ^ 40 * 614147 * 2
def baseEnd_614147 : Nat := 140156712674183946994709

theorem tailTrace_614147 : CollatzResearch.WordTrace tailWord_614147 prefixEnd_614147 140156712674183946994709 := by
  unfold tailWord_614147
  simp only [CollatzResearch.WordTrace]
  refine ⟨22399781306057781802152695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14933187537371854534768463 22399781306057781802152695)
  ·
    refine ⟨33599671959086672703229043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22399781306057781802152695 33599671959086672703229043)
    ·
      refine ⟨50399507938630009054843565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33599671959086672703229043 50399507938630009054843565)
      ·
        refine ⟨18899815476986253395566337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50399507938630009054843565 18899815476986253395566337)
        ·
          refine ⟨14174861607739690046674753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18899815476986253395566337 14174861607739690046674753)
          ·
            refine ⟨10631146205804767535006065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14174861607739690046674753 10631146205804767535006065)
            ·
              refine ⟨7973359654353575651254549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10631146205804767535006065 7973359654353575651254549)
              ·
                refine ⟨373751233797823858652557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7973359654353575651254549 373751233797823858652557)
                ·
                  refine ⟨140156712674183946994709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373751233797823858652557 140156712674183946994709)
                  ·
                    rfl

theorem cell21_614147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 3].length) (baseStart_614147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614147 prefixEnd_614147 := by exact prefixLift 614147
  have htrace : WordTrace (prefixWord ++ tailWord_614147) baseStart_614147 baseEnd_614147 := by
    simpa [prefixWord, tailWord_614147, baseEnd_614147] using wordTrace_append hprefix tailTrace_614147
  have hstable : (prefixWord ++ tailWord_614147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614147).length < 2 ^ (prefixWord ++ tailWord_614147).sum := by decide
  have hdescent : baseEnd_614147 < baseStart_614147 := by decide
  rcases family_descends (prefixWord ++ tailWord_614147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614175 : List Nat := [1, 1, 2, 4, 2, 1, 1, 9]
def baseStart_614175 : Nat := 118140960795 + 614175 * 2 ^ 59
def prefixEnd_614175 : Nat := 4983230072969 + 3 ^ 40 * 614175 * 2
def baseEnd_614175 : Nat := 46721034218554040175995

theorem tailTrace_614175 : CollatzResearch.WordTrace tailWord_614175 prefixEnd_614175 46721034218554040175995 := by
  unfold tailWord_614175
  simp only [CollatzResearch.WordTrace]
  refine ⟨22400802549956342584171979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14933868366637561722781319 22400802549956342584171979)
  ·
    refine ⟨33601203824934513876257969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22400802549956342584171979 33601203824934513876257969)
    ·
      refine ⟨25200902868700885407193477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33601203824934513876257969 25200902868700885407193477)
      ·
        refine ⟨4725169287881416013848777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25200902868700885407193477 4725169287881416013848777)
        ·
          refine ⟨3543876965911062010386583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4725169287881416013848777 3543876965911062010386583)
          ·
            refine ⟨5315815448866593015579875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543876965911062010386583 5315815448866593015579875)
            ·
              refine ⟨7973723173299889523369813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5315815448866593015579875 7973723173299889523369813)
              ·
                refine ⟨46721034218554040175995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7973723173299889523369813 46721034218554040175995)
                ·
                  rfl

theorem cell21_614175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 9].length) (baseStart_614175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614175 prefixEnd_614175 := by exact prefixLift 614175
  have htrace : WordTrace (prefixWord ++ tailWord_614175) baseStart_614175 baseEnd_614175 := by
    simpa [prefixWord, tailWord_614175, baseEnd_614175] using wordTrace_append hprefix tailTrace_614175
  have hstable : (prefixWord ++ tailWord_614175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614175).length < 2 ^ (prefixWord ++ tailWord_614175).sum := by decide
  have hdescent : baseEnd_614175 < baseStart_614175 := by decide
  rcases family_descends (prefixWord ++ tailWord_614175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614198 : List Nat := [5, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_614198 : Nat := 118140960795 + 614198 * 2 ^ 59
def prefixEnd_614198 : Nat := 4983230072969 + 3 ^ 40 * 614198 * 2
def baseEnd_614198 : Nat := 140168351569019191644605

theorem tailTrace_614198 : CollatzResearch.WordTrace tailWord_614198 prefixEnd_614198 140168351569019191644605 := by
  unfold tailWord_614198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1400102589304563594516203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14934427619248678341506165 1400102589304563594516203)
  ·
    refine ⟨2100153883956845391774305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1400102589304563594516203 2100153883956845391774305)
    ·
      refine ⟨1575115412967634043830729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2100153883956845391774305 1575115412967634043830729)
      ·
        refine ⟨1181336559725725532873047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1575115412967634043830729 1181336559725725532873047)
        ·
          refine ⟨1772004839588588299309571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181336559725725532873047 1772004839588588299309571)
          ·
            refine ⟨2658007259382882448964357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772004839588588299309571 2658007259382882448964357)
            ·
              refine ⟨498376361134290459180817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2658007259382882448964357 498376361134290459180817)
              ·
                refine ⟨373782270850717844385613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498376361134290459180817 373782270850717844385613)
                ·
                  refine ⟨140168351569019191644605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373782270850717844385613 140168351569019191644605)
                  ·
                    rfl

theorem cell21_614198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_614198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614198 prefixEnd_614198 := by exact prefixLift 614198
  have htrace : WordTrace (prefixWord ++ tailWord_614198) baseStart_614198 baseEnd_614198 := by
    simpa [prefixWord, tailWord_614198, baseEnd_614198] using wordTrace_append hprefix tailTrace_614198
  have hstable : (prefixWord ++ tailWord_614198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614198).length < 2 ^ (prefixWord ++ tailWord_614198).sum := by decide
  have hdescent : baseEnd_614198 < baseStart_614198 := by decide
  rcases family_descends (prefixWord ++ tailWord_614198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614240 : List Nat := [2, 1, 1, 3, 3, 3, 2, 3, 3]
def baseStart_614240 : Nat := 118140960795 + 614240 * 2 ^ 59
def prefixEnd_614240 : Nat := 4983230072969 + 3 ^ 40 * 614240 * 2
def baseEnd_614240 : Nat := 140177936541236451944519

theorem tailTrace_614240 : CollatzResearch.WordTrace tailWord_614240 prefixEnd_614240 140177936541236451944519 := by
  unfold tailWord_614240
  simp only [CollatzResearch.WordTrace]
  refine ⟨11201586647360429342644087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14935448863147239123525449 11201586647360429342644087)
  ·
    refine ⟨16802379971040644013966131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11201586647360429342644087 16802379971040644013966131)
    ·
      refine ⟨25203569956560966020949197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16802379971040644013966131 25203569956560966020949197)
      ·
        refine ⟨9451338733710362257855949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25203569956560966020949197 9451338733710362257855949)
        ·
          refine ⟨3544252025141385846695981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9451338733710362257855949 3544252025141385846695981)
          ·
            refine ⟨1329094509428019692510993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3544252025141385846695981 1329094509428019692510993)
            ·
              refine ⟨996820882071014769383245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1329094509428019692510993 996820882071014769383245)
              ·
                refine ⟨373807830776630538518717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 996820882071014769383245 373807830776630538518717)
                ·
                  refine ⟨140177936541236451944519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373807830776630538518717 140177936541236451944519)
                  ·
                    rfl

theorem cell21_614240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 3].length) (baseStart_614240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614240 prefixEnd_614240 := by exact prefixLift 614240
  have htrace : WordTrace (prefixWord ++ tailWord_614240) baseStart_614240 baseEnd_614240 := by
    simpa [prefixWord, tailWord_614240, baseEnd_614240] using wordTrace_append hprefix tailTrace_614240
  have hstable : (prefixWord ++ tailWord_614240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614240).length < 2 ^ (prefixWord ++ tailWord_614240).sum := by decide
  have hdescent : baseEnd_614240 < baseStart_614240 := by decide
  rcases family_descends (prefixWord ++ tailWord_614240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614254 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_614254 : Nat := 118140960795 + 614254 * 2 ^ 59
def prefixEnd_614254 : Nat := 4983230072969 + 3 ^ 40 * 614254 * 2
def baseEnd_614254 : Nat := 140181131531975538711157

theorem tailTrace_614254 : CollatzResearch.WordTrace tailWord_614254 prefixEnd_614254 140181131531975538711157 := by
  unfold tailWord_614254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800460489583767384537227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14935789277780092717531877 2800460489583767384537227)
  ·
    refine ⟨4200690734375651076805841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2800460489583767384537227 4200690734375651076805841)
    ·
      refine ⟨3150518050781738307604381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4200690734375651076805841 3150518050781738307604381)
      ·
        refine ⟨1181444269043151865351643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3150518050781738307604381 1181444269043151865351643)
        ·
          refine ⟨1772166403564727798027465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181444269043151865351643 1772166403564727798027465)
          ·
            refine ⟨1329124802673545848520599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1772166403564727798027465 1329124802673545848520599)
            ·
              refine ⟨1993687204010318772780899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329124802673545848520599 1993687204010318772780899)
              ·
                refine ⟨2990530806015478159171349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993687204010318772780899 2990530806015478159171349)
                ·
                  refine ⟨140181131531975538711157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2990530806015478159171349 140181131531975538711157)
                  ·
                    rfl

theorem cell21_614254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_614254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614254 prefixEnd_614254 := by exact prefixLift 614254
  have htrace : WordTrace (prefixWord ++ tailWord_614254) baseStart_614254 baseEnd_614254 := by
    simpa [prefixWord, tailWord_614254, baseEnd_614254] using wordTrace_append hprefix tailTrace_614254
  have hstable : (prefixWord ++ tailWord_614254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614254).length < 2 ^ (prefixWord ++ tailWord_614254).sum := by decide
  have hdescent : baseEnd_614254 < baseStart_614254 := by decide
  rcases family_descends (prefixWord ++ tailWord_614254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614302 : List Nat := [4, 3, 1, 3, 1, 2, 7]
def baseStart_614302 : Nat := 118140960795 + 614302 * 2 ^ 59
def prefixEnd_614302 : Nat := 4983230072969 + 3 ^ 40 * 614302 * 2
def baseEnd_614302 : Nat := 15576898420659791323451

theorem tailTrace_614302 : CollatzResearch.WordTrace tailWord_614302 prefixEnd_614302 15576898420659791323451 := by
  unfold tailWord_614302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800679327562030409255645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14936956413664162182696773 2800679327562030409255645)
  ·
    refine ⟨1050254747835761403470867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2800679327562030409255645 1050254747835761403470867)
    ·
      refine ⟨1575382121753642105206301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1050254747835761403470867 1575382121753642105206301)
      ·
        refine ⟨590768295657615789452363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1575382121753642105206301 590768295657615789452363)
        ·
          refine ⟨886152443486423684178545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590768295657615789452363 886152443486423684178545)
          ·
            refine ⟨664614332614817763133909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886152443486423684178545 664614332614817763133909)
            ·
              refine ⟨15576898420659791323451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 664614332614817763133909 15576898420659791323451)
              ·
                rfl

theorem cell21_614302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 7].length) (baseStart_614302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614302 prefixEnd_614302 := by exact prefixLift 614302
  have htrace : WordTrace (prefixWord ++ tailWord_614302) baseStart_614302 baseEnd_614302 := by
    simpa [prefixWord, tailWord_614302, baseEnd_614302] using wordTrace_append hprefix tailTrace_614302
  have hstable : (prefixWord ++ tailWord_614302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614302).length < 2 ^ (prefixWord ++ tailWord_614302).sum := by decide
  have hdescent : baseEnd_614302 < baseStart_614302 := by decide
  rcases family_descends (prefixWord ++ tailWord_614302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614423 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 4]
def baseStart_614423 : Nat := 118140960795 + 614423 * 2 ^ 59
def prefixEnd_614423 : Nat := 4983230072969 + 3 ^ 40 * 614423 * 2
def baseEnd_614423 : Nat := 140219699634468800394145

theorem tailTrace_614423 : CollatzResearch.WordTrace tailWord_614423 prefixEnd_614423 140219699634468800394145 := by
  unfold tailWord_614423
  simp only [CollatzResearch.WordTrace]
  refine ⟨22409847853057880939199923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14939898568705253959466615 22409847853057880939199923)
  ·
    refine ⟨33614771779586821408799885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22409847853057880939199923 33614771779586821408799885)
    ·
      refine ⟨12605539417345058028299957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33614771779586821408799885 12605539417345058028299957)
      ·
        refine ⟨1181769320376099190153121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12605539417345058028299957 1181769320376099190153121)
        ·
          refine ⟨886326990282074392614841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1181769320376099190153121 886326990282074392614841)
          ·
            refine ⟨664745242711555794461131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886326990282074392614841 664745242711555794461131)
            ·
              refine ⟨997117864067333691691697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664745242711555794461131 997117864067333691691697)
              ·
                refine ⟨747838398050500268768773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997117864067333691691697 747838398050500268768773)
                ·
                  refine ⟨140219699634468800394145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 747838398050500268768773 140219699634468800394145)
                  ·
                    rfl

theorem cell21_614423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 4].length) (baseStart_614423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614423 prefixEnd_614423 := by exact prefixLift 614423
  have htrace : WordTrace (prefixWord ++ tailWord_614423) baseStart_614423 baseEnd_614423 := by
    simpa [prefixWord, tailWord_614423, baseEnd_614423] using wordTrace_append hprefix tailTrace_614423
  have hstable : (prefixWord ++ tailWord_614423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614423).length < 2 ^ (prefixWord ++ tailWord_614423).sum := by decide
  have hdescent : baseEnd_614423 < baseStart_614423 := by decide
  rcases family_descends (prefixWord ++ tailWord_614423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614440 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 4]
def baseStart_614440 : Nat := 118140960795 + 614440 * 2 ^ 59
def prefixEnd_614440 : Nat := 4983230072969 + 3 ^ 40 * 614440 * 2
def baseEnd_614440 : Nat := 140223579266080548610777

theorem tailTrace_614440 : CollatzResearch.WordTrace tailWord_614440 prefixEnd_614440 140223579266080548610777 := by
  unfold tailWord_614440
  simp only [CollatzResearch.WordTrace]
  refine ⟨11205233946998146421284387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14940311929330861895045849 11205233946998146421284387)
  ·
    refine ⟨16807850920497219631926581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11205233946998146421284387 16807850920497219631926581)
    ·
      refine ⟨1575736023796614340493117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16807850920497219631926581 1575736023796614340493117)
      ·
        refine ⟨590901008923730377684919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1575736023796614340493117 590901008923730377684919)
        ·
          refine ⟨886351513385595566527379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590901008923730377684919 886351513385595566527379)
          ·
            refine ⟨1329527270078393349791069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886351513385595566527379 1329527270078393349791069)
            ·
              refine ⟨498572726279397506171651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1329527270078393349791069 498572726279397506171651)
              ·
                refine ⟨747859089419096259257477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498572726279397506171651 747859089419096259257477)
                ·
                  refine ⟨140223579266080548610777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 747859089419096259257477 140223579266080548610777)
                  ·
                    rfl

theorem cell21_614440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_614440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614440 prefixEnd_614440 := by exact prefixLift 614440
  have htrace : WordTrace (prefixWord ++ tailWord_614440) baseStart_614440 baseEnd_614440 := by
    simpa [prefixWord, tailWord_614440, baseEnd_614440] using wordTrace_append hprefix tailTrace_614440
  have hstable : (prefixWord ++ tailWord_614440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614440).length < 2 ^ (prefixWord ++ tailWord_614440).sum := by decide
  have hdescent : baseEnd_614440 < baseStart_614440 := by decide
  rcases family_descends (prefixWord ++ tailWord_614440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614465 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 6]
def baseStart_614465 : Nat := 118140960795 + 614465 * 2 ^ 59
def prefixEnd_614465 : Nat := 4983230072969 + 3 ^ 40 * 614465 * 2
def baseEnd_614465 : Nat := 140229284606686060694059

theorem tailTrace_614465 : CollatzResearch.WordTrace tailWord_614465 prefixEnd_614465 140229284606686060694059 := by
  unfold tailWord_614465
  simp only [CollatzResearch.WordTrace]
  refine ⟨22411379718905722112228849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14940919812603814741485899 22411379718905722112228849)
  ·
    refine ⟨16808534789179291584171637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22411379718905722112228849 16808534789179291584171637)
    ·
      refine ⟨1575800136485558586016091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16808534789179291584171637 1575800136485558586016091)
      ·
        refine ⟨2363700204728337879024137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1575800136485558586016091 2363700204728337879024137)
        ·
          refine ⟨1772775153546253409268103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2363700204728337879024137 1772775153546253409268103)
          ·
            refine ⟨2659162730319380113902155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772775153546253409268103 2659162730319380113902155)
            ·
              refine ⟨3988744095479070170853233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2659162730319380113902155 3988744095479070170853233)
              ·
                refine ⟨2991558071609302628139925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3988744095479070170853233 2991558071609302628139925)
                ·
                  refine ⟨140229284606686060694059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2991558071609302628139925 140229284606686060694059)
                  ·
                    rfl

theorem cell21_614465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_614465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614465 prefixEnd_614465 := by exact prefixLift 614465
  have htrace : WordTrace (prefixWord ++ tailWord_614465) baseStart_614465 baseEnd_614465 := by
    simpa [prefixWord, tailWord_614465, baseEnd_614465] using wordTrace_append hprefix tailTrace_614465
  have hstable : (prefixWord ++ tailWord_614465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614465).length < 2 ^ (prefixWord ++ tailWord_614465).sum := by decide
  have hdescent : baseEnd_614465 < baseStart_614465 := by decide
  rcases family_descends (prefixWord ++ tailWord_614465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614510 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_614510 : Nat := 118140960795 + 614510 * 2 ^ 59
def prefixEnd_614510 : Nat := 4983230072969 + 3 ^ 40 * 614510 * 2
def baseEnd_614510 : Nat := 140239554219775982443967

theorem tailTrace_614510 : CollatzResearch.WordTrace tailWord_614510 prefixEnd_614510 140239554219775982443967 := by
  unfold tailWord_614510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2801627625467836849702123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14942014002495129865077989 2801627625467836849702123)
  ·
    refine ⟨4202441438201755274553185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2801627625467836849702123 4202441438201755274553185)
    ·
      refine ⟨3151831078651316455914889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4202441438201755274553185 3151831078651316455914889)
      ·
        refine ⟨2363873308988487341936167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3151831078651316455914889 2363873308988487341936167)
        ·
          refine ⟨3545809963482731012904251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363873308988487341936167 3545809963482731012904251)
          ·
            refine ⟨5318714945224096519356377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545809963482731012904251 5318714945224096519356377)
            ·
              refine ⟨3989036208918072389517283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5318714945224096519356377 3989036208918072389517283)
              ·
                refine ⟨5983554313377108584275925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3989036208918072389517283 5983554313377108584275925)
                ·
                  refine ⟨140239554219775982443967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5983554313377108584275925 140239554219775982443967)
                  ·
                    rfl

theorem cell21_614510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_614510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614510 prefixEnd_614510 := by exact prefixLift 614510
  have htrace : WordTrace (prefixWord ++ tailWord_614510) baseStart_614510 baseEnd_614510 := by
    simpa [prefixWord, tailWord_614510, baseEnd_614510] using wordTrace_append hprefix tailTrace_614510
  have hstable : (prefixWord ++ tailWord_614510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614510).length < 2 ^ (prefixWord ++ tailWord_614510).sum := by decide
  have hdescent : baseEnd_614510 < baseStart_614510 := by decide
  rcases family_descends (prefixWord ++ tailWord_614510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614637 : List Nat := [1, 5, 1, 2, 3, 2, 1, 3, 3]
def baseStart_614637 : Nat := 118140960795 + 614637 * 2 ^ 59
def prefixEnd_614637 : Nat := 4983230072969 + 3 ^ 40 * 614637 * 2
def baseEnd_614637 : Nat := 140268537350051983827041

theorem tailTrace_614637 : CollatzResearch.WordTrace tailWord_614637 prefixEnd_614637 140268537350051983827041 := by
  unfold tailWord_614637
  simp only [CollatzResearch.WordTrace]
  refine ⟨22417653074282595487490165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14945102049521730324993443 22417653074282595487490165)
  ·
    refine ⟨2101654975713993326952203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22417653074282595487490165 2101654975713993326952203)
    ·
      refine ⟨3152482463570989990428305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2101654975713993326952203 3152482463570989990428305)
      ·
        refine ⟨2364361847678242492821229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3152482463570989990428305 2364361847678242492821229)
        ·
          refine ⟨886635692879340934807961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2364361847678242492821229 886635692879340934807961)
          ·
            refine ⟨664976769659505701105971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886635692879340934807961 664976769659505701105971)
            ·
              refine ⟨997465154489258551658957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664976769659505701105971 997465154489258551658957)
              ·
                refine ⟨374049432933471956872109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 997465154489258551658957 374049432933471956872109)
                ·
                  refine ⟨140268537350051983827041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374049432933471956872109 140268537350051983827041)
                  ·
                    rfl

theorem cell21_614637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_614637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614637 prefixEnd_614637 := by exact prefixLift 614637
  have htrace : WordTrace (prefixWord ++ tailWord_614637) baseStart_614637 baseEnd_614637 := by
    simpa [prefixWord, tailWord_614637, baseEnd_614637] using wordTrace_append hprefix tailTrace_614637
  have hstable : (prefixWord ++ tailWord_614637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614637).length < 2 ^ (prefixWord ++ tailWord_614637).sum := by decide
  have hdescent : baseEnd_614637 < baseStart_614637 := by decide
  rcases family_descends (prefixWord ++ tailWord_614637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614713 : List Nat := [1, 2, 1, 6, 1, 3, 2, 2, 3]
def baseStart_614713 : Nat := 118140960795 + 614713 * 2 ^ 59
def prefixEnd_614713 : Nat := 4983230072969 + 3 ^ 40 * 614713 * 2
def baseEnd_614713 : Nat := 140285881585492740560219

theorem tailTrace_614713 : CollatzResearch.WordTrace tailWord_614713 prefixEnd_614713 140285881585492740560219 := by
  unfold tailWord_614713
  simp only [CollatzResearch.WordTrace]
  refine ⟨22420425022007260467256793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14946950014671506978171195 22420425022007260467256793)
  ·
    refine ⟨16815318766505445350442595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22420425022007260467256793 16815318766505445350442595)
    ·
      refine ⟨25222978149758168025663893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16815318766505445350442595 25222978149758168025663893)
      ·
        refine ⟨1182327100769914126202995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25222978149758168025663893 1182327100769914126202995)
        ·
          refine ⟨1773490651154871189304493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182327100769914126202995 1773490651154871189304493)
          ·
            refine ⟨665058994183076695989185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1773490651154871189304493 665058994183076695989185)
            ·
              refine ⟨498794245637307521991889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665058994183076695989185 498794245637307521991889)
              ·
                refine ⟨374095684227980641493917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498794245637307521991889 374095684227980641493917)
                ·
                  refine ⟨140285881585492740560219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374095684227980641493917 140285881585492740560219)
                  ·
                    rfl

theorem cell21_614713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 3].length) (baseStart_614713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614713 prefixEnd_614713 := by exact prefixLift 614713
  have htrace : WordTrace (prefixWord ++ tailWord_614713) baseStart_614713 baseEnd_614713 := by
    simpa [prefixWord, tailWord_614713, baseEnd_614713] using wordTrace_append hprefix tailTrace_614713
  have hstable : (prefixWord ++ tailWord_614713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614713).length < 2 ^ (prefixWord ++ tailWord_614713).sum := by decide
  have hdescent : baseEnd_614713 < baseStart_614713 := by decide
  rcases family_descends (prefixWord ++ tailWord_614713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614755 : List Nat := [1, 1, 1, 5, 2, 1, 4, 3, 3]
def baseStart_614755 : Nat := 118140960795 + 614755 * 2 ^ 59
def prefixEnd_614755 : Nat := 4983230072969 + 3 ^ 40 * 614755 * 2
def baseEnd_614755 : Nat := 140295466557710000860133

theorem tailTrace_614755 : CollatzResearch.WordTrace tailWord_614755 prefixEnd_614755 140295466557710000860133 := by
  unfold tailWord_614755
  simp only [CollatzResearch.WordTrace]
  refine ⟨22421956887855101640285719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14947971258570067760190479 22421956887855101640285719)
  ·
    refine ⟨33632935331782652460428579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22421956887855101640285719 33632935331782652460428579)
    ·
      refine ⟨50449402997673978690642869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33632935331782652460428579 50449402997673978690642869)
      ·
        refine ⟨4729631531031935502247769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50449402997673978690642869 4729631531031935502247769)
        ·
          refine ⟨3547223648273951626685827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4729631531031935502247769 3547223648273951626685827)
          ·
            refine ⟨5320835472410927440028741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547223648273951626685827 5320835472410927440028741)
            ·
              refine ⟨997656651077048895005389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5320835472410927440028741 997656651077048895005389)
              ·
                refine ⟨374121244153893335627021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 997656651077048895005389 374121244153893335627021)
                ·
                  refine ⟨140295466557710000860133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374121244153893335627021 140295466557710000860133)
                  ·
                    rfl

theorem cell21_614755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 3].length) (baseStart_614755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614755 prefixEnd_614755 := by exact prefixLift 614755
  have htrace : WordTrace (prefixWord ++ tailWord_614755) baseStart_614755 baseEnd_614755 := by
    simpa [prefixWord, tailWord_614755, baseEnd_614755] using wordTrace_append hprefix tailTrace_614755
  have hstable : (prefixWord ++ tailWord_614755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614755).length < 2 ^ (prefixWord ++ tailWord_614755).sum := by decide
  have hdescent : baseEnd_614755 < baseStart_614755 := by decide
  rcases family_descends (prefixWord ++ tailWord_614755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614817 : List Nat := [1, 2, 3, 5, 2, 1, 7]
def baseStart_614817 : Nat := 118140960795 + 614817 * 2 ^ 59
def prefixEnd_614817 : Nat := 4983230072969 + 3 ^ 40 * 614817 * 2
def baseEnd_614817 : Nat := 15589957311379074536297

theorem tailTrace_614817 : CollatzResearch.WordTrace tailWord_614817 prefixEnd_614817 15589957311379074536297 := by
  unfold tailWord_614817
  simp only [CollatzResearch.WordTrace]
  refine ⟨22424218213630486229042705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14949478809086990819361803 22424218213630486229042705)
  ·
    refine ⟨16818163660222864671782029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22424218213630486229042705 16818163660222864671782029)
    ·
      refine ⟨6306811372583574251918261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16818163660222864671782029 6306811372583574251918261)
      ·
        refine ⟨591263566179710086117337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6306811372583574251918261 591263566179710086117337)
        ·
          refine ⟨443447674634782564588003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591263566179710086117337 443447674634782564588003)
          ·
            refine ⟨665171511952173846882005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443447674634782564588003 665171511952173846882005)
            ·
              refine ⟨15589957311379074536297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 665171511952173846882005 15589957311379074536297)
              ·
                rfl

theorem cell21_614817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 7].length) (baseStart_614817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614817 prefixEnd_614817 := by exact prefixLift 614817
  have htrace : WordTrace (prefixWord ++ tailWord_614817) baseStart_614817 baseEnd_614817 := by
    simpa [prefixWord, tailWord_614817, baseEnd_614817] using wordTrace_append hprefix tailTrace_614817
  have hstable : (prefixWord ++ tailWord_614817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614817).length < 2 ^ (prefixWord ++ tailWord_614817).sum := by decide
  have hdescent : baseEnd_614817 < baseStart_614817 := by decide
  rcases family_descends (prefixWord ++ tailWord_614817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614828 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 4]
def baseStart_614828 : Nat := 118140960795 + 614828 * 2 ^ 59
def prefixEnd_614828 : Nat := 4983230072969 + 3 ^ 40 * 614828 * 2
def baseEnd_614828 : Nat := 140312126152278096143317

theorem tailTrace_614828 : CollatzResearch.WordTrace tailWord_614828 prefixEnd_614828 140312126152278096143317 := by
  unfold tailWord_614828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11212309708295317553846569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14949746277727090071795425 11212309708295317553846569)
  ·
    refine ⟨8409232281221488165384927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11212309708295317553846569 8409232281221488165384927)
    ·
      refine ⟨12613848421832232248077391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8409232281221488165384927 12613848421832232248077391)
      ·
        refine ⟨18920772632748348372116087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12613848421832232248077391 18920772632748348372116087)
        ·
          refine ⟨28381158949122522558174131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18920772632748348372116087 28381158949122522558174131)
          ·
            refine ⟨42571738423683783837261197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28381158949122522558174131 42571738423683783837261197)
            ·
              refine ⟨15964401908881418938972949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42571738423683783837261197 15964401908881418938972949)
              ·
                refine ⟨748331339478816512764357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15964401908881418938972949 748331339478816512764357)
                ·
                  refine ⟨140312126152278096143317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 748331339478816512764357 140312126152278096143317)
                  ·
                    rfl

theorem cell21_614828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_614828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614828 prefixEnd_614828 := by exact prefixLift 614828
  have htrace : WordTrace (prefixWord ++ tailWord_614828) baseStart_614828 baseEnd_614828 := by
    simpa [prefixWord, tailWord_614828, baseEnd_614828] using wordTrace_append hprefix tailTrace_614828
  have hstable : (prefixWord ++ tailWord_614828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614828).length < 2 ^ (prefixWord ++ tailWord_614828).sum := by decide
  have hdescent : baseEnd_614828 < baseStart_614828 := by decide
  rcases family_descends (prefixWord ++ tailWord_614828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614845 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 4]
def baseStart_614845 : Nat := 118140960795 + 614845 * 2 ^ 59
def prefixEnd_614845 : Nat := 4983230072969 + 3 ^ 40 * 614845 * 2
def baseEnd_614845 : Nat := 140316005783889844359949

theorem tailTrace_614845 : CollatzResearch.WordTrace tailWord_614845 prefixEnd_614845 140316005783889844359949 := by
  unfold tailWord_614845
  simp only [CollatzResearch.WordTrace]
  refine ⟨22425239457529047011061989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14950159638352698007374659 22425239457529047011061989)
  ·
    refine ⟨4204732398286696314574123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22425239457529047011061989 4204732398286696314574123)
    ·
      refine ⟨6307098597430044471861185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4204732398286696314574123 6307098597430044471861185)
      ·
        refine ⟨4730323948072533353895889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6307098597430044471861185 4730323948072533353895889)
        ·
          refine ⟨3547742961054400015421917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4730323948072533353895889 3547742961054400015421917)
          ·
            refine ⟨1330403610395400005783219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3547742961054400015421917 1330403610395400005783219)
            ·
              refine ⟨1995605415593100008674829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330403610395400005783219 1995605415593100008674829)
              ·
                refine ⟨748352030847412503253061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1995605415593100008674829 748352030847412503253061)
                ·
                  refine ⟨140316005783889844359949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 748352030847412503253061 140316005783889844359949)
                  ·
                    rfl

theorem cell21_614845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_614845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614845 prefixEnd_614845 := by exact prefixLift 614845
  have htrace : WordTrace (prefixWord ++ tailWord_614845) baseStart_614845 baseEnd_614845 := by
    simpa [prefixWord, tailWord_614845, baseEnd_614845] using wordTrace_append hprefix tailTrace_614845
  have hstable : (prefixWord ++ tailWord_614845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614845).length < 2 ^ (prefixWord ++ tailWord_614845).sum := by decide
  have hdescent : baseEnd_614845 < baseStart_614845 := by decide
  rcases family_descends (prefixWord ++ tailWord_614845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614904 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 4]
def baseStart_614904 : Nat := 118140960795 + 614904 * 2 ^ 59
def prefixEnd_614904 : Nat := 4983230072969 + 3 ^ 40 * 614904 * 2
def baseEnd_614904 : Nat := 140329470387718852876495

theorem tailTrace_614904 : CollatzResearch.WordTrace tailWord_614904 prefixEnd_614904 140329470387718852876495 := by
  unfold tailWord_614904
  simp only [CollatzResearch.WordTrace]
  refine ⟨11213695682157650043729883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14951594242876866724973177 11213695682157650043729883)
  ·
    refine ⟨16820543523236475065594825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11213695682157650043729883 16820543523236475065594825)
    ·
      refine ⟨12615407642427356299196119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16820543523236475065594825 12615407642427356299196119)
      ·
        refine ⟨18923111463641034448794179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12615407642427356299196119 18923111463641034448794179)
        ·
          refine ⟨28384667195461551673191269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18923111463641034448794179 28384667195461551673191269)
          ·
            refine ⟨5322125099149040938723363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28384667195461551673191269 5322125099149040938723363)
            ·
              refine ⟨7983187648723561408085045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322125099149040938723363 7983187648723561408085045)
              ·
                refine ⟨748423842067833882007973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7983187648723561408085045 748423842067833882007973)
                ·
                  refine ⟨140329470387718852876495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 748423842067833882007973 140329470387718852876495)
                  ·
                    rfl

theorem cell21_614904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_614904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614904 prefixEnd_614904 := by exact prefixLift 614904
  have htrace : WordTrace (prefixWord ++ tailWord_614904) baseStart_614904 baseEnd_614904 := by
    simpa [prefixWord, tailWord_614904, baseEnd_614904] using wordTrace_append hprefix tailTrace_614904
  have hstable : (prefixWord ++ tailWord_614904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614904).length < 2 ^ (prefixWord ++ tailWord_614904).sum := by decide
  have hdescent : baseEnd_614904 < baseStart_614904 := by decide
  rcases family_descends (prefixWord ++ tailWord_614904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614949 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 5]
def baseStart_614949 : Nat := 118140960795 + 614949 * 2 ^ 59
def prefixEnd_614949 : Nat := 4983230072969 + 3 ^ 40 * 614949 * 2
def baseEnd_614949 : Nat := 140339740000808774626403

theorem tailTrace_614949 : CollatzResearch.WordTrace tailWord_614949 prefixEnd_614949 140339740000808774626403 := by
  unfold tailWord_614949
  simp only [CollatzResearch.WordTrace]
  refine ⟨22429032649152272772847901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14952688432768181848565267 22429032649152272772847901)
  ·
    refine ⟨8410887243432102289817963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22429032649152272772847901 8410887243432102289817963)
    ·
      refine ⟨12616330865148153434726945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8410887243432102289817963 12616330865148153434726945)
      ·
        refine ⟨9462248148861115076045209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12616330865148153434726945 9462248148861115076045209)
        ·
          refine ⟨7096686111645836307033907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9462248148861115076045209 7096686111645836307033907)
          ·
            refine ⟨10645029167468754460550861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7096686111645836307033907 10645029167468754460550861)
            ·
              refine ⟨3991885937800782922706573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10645029167468754460550861 3991885937800782922706573)
              ·
                refine ⟨1496957226675293596014965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3991885937800782922706573 1496957226675293596014965)
                ·
                  refine ⟨140339740000808774626403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1496957226675293596014965 140339740000808774626403)
                  ·
                    rfl

theorem cell21_614949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_614949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614949 prefixEnd_614949 := by exact prefixLift 614949
  have htrace : WordTrace (prefixWord ++ tailWord_614949) baseStart_614949 baseEnd_614949 := by
    simpa [prefixWord, tailWord_614949, baseEnd_614949] using wordTrace_append hprefix tailTrace_614949
  have hstable : (prefixWord ++ tailWord_614949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614949).length < 2 ^ (prefixWord ++ tailWord_614949).sum := by decide
  have hdescent : baseEnd_614949 < baseStart_614949 := by decide
  rcases family_descends (prefixWord ++ tailWord_614949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614983 : List Nat := [1, 1, 4, 1, 4, 1, 3, 3, 3]
def baseStart_614983 : Nat := 118140960795 + 614983 * 2 ^ 59
def prefixEnd_614983 : Nat := 4983230072969 + 3 ^ 40 * 614983 * 2
def baseEnd_614983 : Nat := 140347499264032271059667

theorem tailTrace_614983 : CollatzResearch.WordTrace tailWord_614983 prefixEnd_614983 140347499264032271059667 := by
  unfold tailWord_614983
  simp only [CollatzResearch.WordTrace]
  refine ⟨22430272731029096579585603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14953515154019397719723735 22430272731029096579585603)
  ·
    refine ⟨33645409096543644869378405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22430272731029096579585603 33645409096543644869378405)
    ·
      refine ⟨6308514205601933413008451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33645409096543644869378405 6308514205601933413008451)
      ·
        refine ⟨9462771308402900119512677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6308514205601933413008451 9462771308402900119512677)
        ·
          refine ⟨1774269620325543772408627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9462771308402900119512677 1774269620325543772408627)
          ·
            refine ⟨2661404430488315658612941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774269620325543772408627 2661404430488315658612941)
            ·
              refine ⟨998026661433118371979853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2661404430488315658612941 998026661433118371979853)
              ·
                refine ⟨374259998037419389492445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 998026661433118371979853 374259998037419389492445)
                ·
                  refine ⟨140347499264032271059667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374259998037419389492445 140347499264032271059667)
                  ·
                    rfl

theorem cell21_614983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 3].length) (baseStart_614983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_614983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_614983 prefixEnd_614983 := by exact prefixLift 614983
  have htrace : WordTrace (prefixWord ++ tailWord_614983) baseStart_614983 baseEnd_614983 := by
    simpa [prefixWord, tailWord_614983, baseEnd_614983] using wordTrace_append hprefix tailTrace_614983
  have hstable : (prefixWord ++ tailWord_614983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614983).length < 2 ^ (prefixWord ++ tailWord_614983).sum := by decide
  have hdescent : baseEnd_614983 < baseStart_614983 := by decide
  rcases family_descends (prefixWord ++ tailWord_614983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615006 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_615006 : Nat := 118140960795 + 615006 * 2 ^ 59
def prefixEnd_615006 : Nat := 4983230072969 + 3 ^ 40 * 615006 * 2
def baseEnd_615006 : Nat := 140352748177389342176287

theorem tailTrace_615006 : CollatzResearch.WordTrace tailWord_615006 prefixEnd_615006 140352748177389342176287 := by
  unfold tailWord_615006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2803888951243221438459109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14954074406630514338448581 2803888951243221438459109)
  ·
    refine ⟨525729178358104019711083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2803888951243221438459109 525729178358104019711083)
    ·
      refine ⟨788593767537156029566625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525729178358104019711083 788593767537156029566625)
      ·
        refine ⟨591445325652867022174969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 788593767537156029566625 591445325652867022174969)
        ·
          refine ⟨443583994239650266631227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591445325652867022174969 443583994239650266631227)
          ·
            refine ⟨665375991359475399946841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443583994239650266631227 665375991359475399946841)
            ·
              refine ⟨499031993519606549960131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665375991359475399946841 499031993519606549960131)
              ·
                refine ⟨748547990279409824940197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499031993519606549960131 748547990279409824940197)
                ·
                  refine ⟨140352748177389342176287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 748547990279409824940197 140352748177389342176287)
                  ·
                    rfl

theorem cell21_615006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_615006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615006 prefixEnd_615006 := by exact prefixLift 615006
  have htrace : WordTrace (prefixWord ++ tailWord_615006) baseStart_615006 baseEnd_615006 := by
    simpa [prefixWord, tailWord_615006, baseEnd_615006] using wordTrace_append hprefix tailTrace_615006
  have hstable : (prefixWord ++ tailWord_615006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615006).length < 2 ^ (prefixWord ++ tailWord_615006).sum := by decide
  have hdescent : baseEnd_615006 < baseStart_615006 := by decide
  rcases family_descends (prefixWord ++ tailWord_615006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615039 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 6]
def baseStart_615039 : Nat := 118140960795 + 615039 * 2 ^ 59
def prefixEnd_615039 : Nat := 4983230072969 + 3 ^ 40 * 615039 * 2
def baseEnd_615039 : Nat := 140360279226988618126219

theorem tailTrace_615039 : CollatzResearch.WordTrace tailWord_615039 prefixEnd_615039 140360279226988618126219 := by
  unfold tailWord_615039
  simp only [CollatzResearch.WordTrace]
  refine ⟨22432315218826218143624171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14954876812550812095749447 22432315218826218143624171)
  ·
    refine ⟨33648472828239327215436257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22432315218826218143624171 33648472828239327215436257)
    ·
      refine ⟨25236354621179495411577193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33648472828239327215436257 25236354621179495411577193)
      ·
        refine ⟨18927265965884621558682895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25236354621179495411577193 18927265965884621558682895)
        ·
          refine ⟨28390898948826932338024343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18927265965884621558682895 28390898948826932338024343)
          ·
            refine ⟨42586348423240398507036515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28390898948826932338024343 42586348423240398507036515)
            ·
              refine ⟨63879522634860597760554773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42586348423240398507036515 63879522634860597760554773)
              ·
                refine ⟨2994352623509090520026005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63879522634860597760554773 2994352623509090520026005)
                ·
                  refine ⟨140360279226988618126219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2994352623509090520026005 140360279226988618126219)
                  ·
                    rfl

theorem cell21_615039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_615039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615039 prefixEnd_615039 := by exact prefixLift 615039
  have htrace : WordTrace (prefixWord ++ tailWord_615039) baseStart_615039 baseEnd_615039 := by
    simpa [prefixWord, tailWord_615039, baseEnd_615039] using wordTrace_append hprefix tailTrace_615039
  have hstable : (prefixWord ++ tailWord_615039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615039).length < 2 ^ (prefixWord ++ tailWord_615039).sum := by decide
  have hdescent : baseEnd_615039 < baseStart_615039 := by decide
  rcases family_descends (prefixWord ++ tailWord_615039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615087 : List Nat := [1, 1, 2, 1, 2, 6, 3, 5]
def baseStart_615087 : Nat := 118140960795 + 615087 * 2 ^ 59
def prefixEnd_615087 : Nat := 4983230072969 + 3 ^ 40 * 615087 * 2
def baseEnd_615087 : Nat := 46790411160317067108707

theorem tailTrace_615087 : CollatzResearch.WordTrace tailWord_615087 prefixEnd_615087 46790411160317067108707 := by
  unfold tailWord_615087
  simp only [CollatzResearch.WordTrace]
  refine ⟨22434065922652322341371515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14956043948434881560914343 22434065922652322341371515)
  ·
    refine ⟨33651098883978483512057273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22434065922652322341371515 33651098883978483512057273)
    ·
      refine ⟨25238324162983862634042955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33651098883978483512057273 25238324162983862634042955)
      ·
        refine ⟨37857486244475793951064433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25238324162983862634042955 37857486244475793951064433)
        ·
          refine ⟨28393114683356845463298325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37857486244475793951064433 28393114683356845463298325)
          ·
            refine ⟨1330927250782352131092109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28393114683356845463298325 1330927250782352131092109)
            ·
              refine ⟨499097719043382049159541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1330927250782352131092109 499097719043382049159541)
              ·
                refine ⟨46790411160317067108707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 499097719043382049159541 46790411160317067108707)
                ·
                  rfl

theorem cell21_615087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 5].length) (baseStart_615087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615087 prefixEnd_615087 := by exact prefixLift 615087
  have htrace : WordTrace (prefixWord ++ tailWord_615087) baseStart_615087 baseEnd_615087 := by
    simpa [prefixWord, tailWord_615087, baseEnd_615087] using wordTrace_append hprefix tailTrace_615087
  have hstable : (prefixWord ++ tailWord_615087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615087).length < 2 ^ (prefixWord ++ tailWord_615087).sum := by decide
  have hdescent : baseEnd_615087 < baseStart_615087 := by decide
  rcases family_descends (prefixWord ++ tailWord_615087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615118 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_615118 : Nat := 118140960795 + 615118 * 2 ^ 59
def prefixEnd_615118 : Nat := 4983230072969 + 3 ^ 40 * 615118 * 2
def baseEnd_615118 : Nat := 140378308103302036309391

theorem tailTrace_615118 : CollatzResearch.WordTrace tailWord_615118 prefixEnd_615118 140378308103302036309391 := by
  unfold tailWord_615118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2804399573192501829468751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14956797723693343090500005 2804399573192501829468751)
  ·
    refine ⟨4206599359788752744203127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2804399573192501829468751 4206599359788752744203127)
    ·
      refine ⟨6309899039683129116304691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4206599359788752744203127 6309899039683129116304691)
      ·
        refine ⟨9464848559524693674457037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6309899039683129116304691 9464848559524693674457037)
        ·
          refine ⟨3549318209821760127921389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9464848559524693674457037 3549318209821760127921389)
          ·
            refine ⟨1330994328683160047970521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3549318209821760127921389 1330994328683160047970521)
            ·
              refine ⟨998245746512370035977891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1330994328683160047970521 998245746512370035977891)
              ·
                refine ⟨1497368619768555053966837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998245746512370035977891 1497368619768555053966837)
                ·
                  refine ⟨140378308103302036309391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1497368619768555053966837 140378308103302036309391)
                  ·
                    rfl

theorem cell21_615118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_615118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615118 prefixEnd_615118 := by exact prefixLift 615118
  have htrace : WordTrace (prefixWord ++ tailWord_615118) baseStart_615118 baseEnd_615118 := by
    simpa [prefixWord, tailWord_615118, baseEnd_615118] using wordTrace_append hprefix tailTrace_615118
  have hstable : (prefixWord ++ tailWord_615118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615118).length < 2 ^ (prefixWord ++ tailWord_615118).sum := by decide
  have hdescent : baseEnd_615118 < baseStart_615118 := by decide
  rcases family_descends (prefixWord ++ tailWord_615118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615177 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 5]
def baseStart_615177 : Nat := 118140960795 + 615177 * 2 ^ 59
def prefixEnd_615177 : Nat := 4983230072969 + 3 ^ 40 * 615177 * 2
def baseEnd_615177 : Nat := 140391772707131044825937

theorem tailTrace_615177 : CollatzResearch.WordTrace tailWord_615177 prefixEnd_615177 140391772707131044825937 := by
  unfold tailWord_615177
  simp only [CollatzResearch.WordTrace]
  refine ⟨22437348492326267712147785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14958232328217511808098523 22437348492326267712147785)
  ·
    refine ⟨16828011369244700784110839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22437348492326267712147785 16828011369244700784110839)
    ·
      refine ⟨25242017053867051176166259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16828011369244700784110839 25242017053867051176166259)
      ·
        refine ⟨37863025580800576764249389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25242017053867051176166259 37863025580800576764249389)
        ·
          refine ⟨14198634592800216286593521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37863025580800576764249389 14198634592800216286593521)
          ·
            refine ⟨10648975944600162214945141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14198634592800216286593521 10648975944600162214945141)
            ·
              refine ⟨998341494806265207651107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10648975944600162214945141 998341494806265207651107)
              ·
                refine ⟨1497512242209397811476661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998341494806265207651107 1497512242209397811476661)
                ·
                  refine ⟨140391772707131044825937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1497512242209397811476661 140391772707131044825937)
                  ·
                    rfl

theorem cell21_615177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_615177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615177 prefixEnd_615177 := by exact prefixLift 615177
  have htrace : WordTrace (prefixWord ++ tailWord_615177) baseStart_615177 baseEnd_615177 := by
    simpa [prefixWord, tailWord_615177, baseEnd_615177] using wordTrace_append hprefix tailTrace_615177
  have hstable : (prefixWord ++ tailWord_615177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615177).length < 2 ^ (prefixWord ++ tailWord_615177).sum := by decide
  have hdescent : baseEnd_615177 < baseStart_615177 := by decide
  rcases family_descends (prefixWord ++ tailWord_615177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615253 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 5]
def baseStart_615253 : Nat := 118140960795 + 615253 * 2 ^ 59
def prefixEnd_615253 : Nat := 4983230072969 + 3 ^ 40 * 615253 * 2
def baseEnd_615253 : Nat := 140409116942571801559115

theorem tailTrace_615253 : CollatzResearch.WordTrace tailWord_615253 prefixEnd_615253 140409116942571801559115 := by
  unfold tailWord_615253
  simp only [CollatzResearch.WordTrace]
  refine ⟨22440120440050932691914413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14960080293367288461276275 22440120440050932691914413)
  ·
    refine ⟨8415045165019099759467905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22440120440050932691914413 8415045165019099759467905)
    ·
      refine ⟨6311283873764324819600929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8415045165019099759467905 6311283873764324819600929)
      ·
        refine ⟨4733462905323243614700697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6311283873764324819600929 4733462905323243614700697)
        ·
          refine ⟨3550097178992432711025523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4733462905323243614700697 3550097178992432711025523)
          ·
            refine ⟨5325145768488649066538285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3550097178992432711025523 5325145768488649066538285)
            ·
              refine ⟨1996929663183243399951857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5325145768488649066538285 1996929663183243399951857)
              ·
                refine ⟨1497697247387432549963893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1996929663183243399951857 1497697247387432549963893)
                ·
                  refine ⟨140409116942571801559115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1497697247387432549963893 140409116942571801559115)
                  ·
                    rfl

theorem cell21_615253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_615253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615253 prefixEnd_615253 := by exact prefixLift 615253
  have htrace : WordTrace (prefixWord ++ tailWord_615253) baseStart_615253 baseEnd_615253 := by
    simpa [prefixWord, tailWord_615253, baseEnd_615253] using wordTrace_append hprefix tailTrace_615253
  have hstable : (prefixWord ++ tailWord_615253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615253).length < 2 ^ (prefixWord ++ tailWord_615253).sum := by decide
  have hdescent : baseEnd_615253 < baseStart_615253 := by decide
  rcases family_descends (prefixWord ++ tailWord_615253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615301 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 4]
def baseStart_615301 : Nat := 118140960795 + 615301 * 2 ^ 59
def prefixEnd_615301 : Nat := 4983230072969 + 3 ^ 40 * 615301 * 2
def baseEnd_615301 : Nat := 140420071196534384759017

theorem tailTrace_615301 : CollatzResearch.WordTrace tailWord_615301 prefixEnd_615301 140420071196534384759017 := by
  unfold tailWord_615301
  simp only [CollatzResearch.WordTrace]
  refine ⟨22441871143877036889661757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14961247429251357926441171 22441871143877036889661757)
  ·
    refine ⟨8415701678953888833623159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22441871143877036889661757 8415701678953888833623159)
    ·
      refine ⟨12623552518430833250434739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8415701678953888833623159 12623552518430833250434739)
      ·
        refine ⟨18935328777646249875652109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12623552518430833250434739 18935328777646249875652109)
        ·
          refine ⟨7100748291617343703369541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18935328777646249875652109 7100748291617343703369541)
          ·
            refine ⟨1331390304678251944381789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7100748291617343703369541 1331390304678251944381789)
            ·
              refine ⟨499271364254344479143171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1331390304678251944381789 499271364254344479143171)
              ·
                refine ⟨748907046381516718714757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499271364254344479143171 748907046381516718714757)
                ·
                  refine ⟨140420071196534384759017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 748907046381516718714757 140420071196534384759017)
                  ·
                    rfl

theorem cell21_615301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_615301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615301 prefixEnd_615301 := by exact prefixLift 615301
  have htrace : WordTrace (prefixWord ++ tailWord_615301) baseStart_615301 baseEnd_615301 := by
    simpa [prefixWord, tailWord_615301, baseEnd_615301] using wordTrace_append hprefix tailTrace_615301
  have hstable : (prefixWord ++ tailWord_615301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615301).length < 2 ^ (prefixWord ++ tailWord_615301).sum := by decide
  have hdescent : baseEnd_615301 < baseStart_615301 := by decide
  rcases family_descends (prefixWord ++ tailWord_615301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615318 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_615318 : Nat := 118140960795 + 615318 * 2 ^ 59
def prefixEnd_615318 : Nat := 4983230072969 + 3 ^ 40 * 615318 * 2
def baseEnd_615318 : Nat := 140423950828146132975649

theorem tailTrace_615318 : CollatzResearch.WordTrace tailWord_615318 prefixEnd_615318 140423950828146132975649 := by
  unfold tailWord_615318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402655699050965549564413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14961660789876965862020405 1402655699050965549564413)
  ·
    refine ⟨525995887144112081086655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1402655699050965549564413 525995887144112081086655)
    ·
      refine ⟨788993830716168121629983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525995887144112081086655 788993830716168121629983)
      ·
        refine ⟨1183490746074252182444975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788993830716168121629983 1183490746074252182444975)
        ·
          refine ⟨1775236119111378273667463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183490746074252182444975 1775236119111378273667463)
          ·
            refine ⟨2662854178667067410501195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775236119111378273667463 2662854178667067410501195)
            ·
              refine ⟨3994281268000601115751793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2662854178667067410501195 3994281268000601115751793)
              ·
                refine ⟨2995710951000450836813845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3994281268000601115751793 2995710951000450836813845)
                ·
                  refine ⟨140423950828146132975649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2995710951000450836813845 140423950828146132975649)
                  ·
                    rfl

theorem cell21_615318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_615318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615318 prefixEnd_615318 := by exact prefixLift 615318
  have htrace : WordTrace (prefixWord ++ tailWord_615318) baseStart_615318 baseEnd_615318 := by
    simpa [prefixWord, tailWord_615318, baseEnd_615318] using wordTrace_append hprefix tailTrace_615318
  have hstable : (prefixWord ++ tailWord_615318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615318).length < 2 ^ (prefixWord ++ tailWord_615318).sum := by decide
  have hdescent : baseEnd_615318 < baseStart_615318 := by decide
  rcases family_descends (prefixWord ++ tailWord_615318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615360 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 4]
def baseStart_615360 : Nat := 118140960795 + 615360 * 2 ^ 59
def prefixEnd_615360 : Nat := 4983230072969 + 3 ^ 40 * 615360 * 2
def baseEnd_615360 : Nat := 140433535800363393275563

theorem tailTrace_615360 : CollatzResearch.WordTrace tailWord_615360 prefixEnd_615360 140433535800363393275563 := by
  unfold tailWord_615360
  simp only [CollatzResearch.WordTrace]
  refine ⟨11222011525331644983029767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14962682033775526644039689 11222011525331644983029767)
  ·
    refine ⟨16833017287997467474544651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11222011525331644983029767 16833017287997467474544651)
    ·
      refine ⟨25249525931996201211816977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16833017287997467474544651 25249525931996201211816977)
      ·
        refine ⟨18937144448997150908862733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25249525931996201211816977 18937144448997150908862733)
        ·
          refine ⟨7101429168373931590823525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18937144448997150908862733 7101429168373931590823525)
          ·
            refine ⟨1331517969070112173279411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7101429168373931590823525 1331517969070112173279411)
            ·
              refine ⟨1997276953605168259919117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331517969070112173279411 1997276953605168259919117)
              ·
                refine ⟨748978857601938097469669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1997276953605168259919117 748978857601938097469669)
                ·
                  refine ⟨140433535800363393275563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 748978857601938097469669 140433535800363393275563)
                  ·
                    rfl

theorem cell21_615360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_615360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615360 prefixEnd_615360 := by exact prefixLift 615360
  have htrace : WordTrace (prefixWord ++ tailWord_615360) baseStart_615360 baseEnd_615360 := by
    simpa [prefixWord, tailWord_615360, baseEnd_615360] using wordTrace_append hprefix tailTrace_615360
  have hstable : (prefixWord ++ tailWord_615360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615360).length < 2 ^ (prefixWord ++ tailWord_615360).sum := by decide
  have hdescent : baseEnd_615360 < baseStart_615360 := by decide
  rcases family_descends (prefixWord ++ tailWord_615360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615374 : List Nat := [4, 1, 1, 1, 2, 3, 2, 7]
def baseStart_615374 : Nat := 118140960795 + 615374 * 2 ^ 59
def prefixEnd_615374 : Nat := 4983230072969 + 3 ^ 40 * 615374 * 2
def baseEnd_615374 : Nat := 46812243597034160014067

theorem tailTrace_615374 : CollatzResearch.WordTrace tailWord_615374 prefixEnd_615374 46812243597034160014067 := by
  unfold tailWord_615374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2805566709076571294633647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14963022448408380238046117 2805566709076571294633647)
  ·
    refine ⟨4208350063614856941950471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2805566709076571294633647 4208350063614856941950471)
    ·
      refine ⟨6312525095422285412925707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208350063614856941950471 6312525095422285412925707)
      ·
        refine ⟨9468787643133428119388561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6312525095422285412925707 9468787643133428119388561)
        ·
          refine ⟨7101590732350071089541421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9468787643133428119388561 7101590732350071089541421)
          ·
            refine ⟨2663096524631276658578033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7101590732350071089541421 2663096524631276658578033)
            ·
              refine ⟨1997322393473457493933525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2663096524631276658578033 1997322393473457493933525)
              ·
                refine ⟨46812243597034160014067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1997322393473457493933525 46812243597034160014067)
                ·
                  rfl

theorem cell21_615374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_615374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615374 prefixEnd_615374 := by exact prefixLift 615374
  have htrace : WordTrace (prefixWord ++ tailWord_615374) baseStart_615374 baseEnd_615374 := by
    simpa [prefixWord, tailWord_615374, baseEnd_615374] using wordTrace_append hprefix tailTrace_615374
  have hstable : (prefixWord ++ tailWord_615374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615374).length < 2 ^ (prefixWord ++ tailWord_615374).sum := by decide
  have hdescent : baseEnd_615374 < baseStart_615374 := by decide
  rcases family_descends (prefixWord ++ tailWord_615374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615394 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_615394 : Nat := 118140960795 + 615394 * 2 ^ 59
def prefixEnd_615394 : Nat := 4983230072969 + 3 ^ 40 * 615394 * 2
def baseEnd_615394 : Nat := 140441295063586889708827

theorem tailTrace_615394 : CollatzResearch.WordTrace tailWord_615394 prefixEnd_615394 140441295063586889708827 := by
  unfold tailWord_615394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611315783135028443199309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14963508755026742515198157 5611315783135028443199309)
  ·
    refine ⟨2104243418675635666199741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5611315783135028443199309 2104243418675635666199741)
    ·
      refine ⟨789091282003363374824903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2104243418675635666199741 789091282003363374824903)
      ·
        refine ⟨1183636923005045062237355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789091282003363374824903 1183636923005045062237355)
        ·
          refine ⟨1775455384507567593356033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183636923005045062237355 1775455384507567593356033)
          ·
            refine ⟨1331591538380675695017025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1775455384507567593356033 1331591538380675695017025)
            ·
              refine ⟨998693653785506771262769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1331591538380675695017025 998693653785506771262769)
              ·
                refine ⟨749020240339130078447077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998693653785506771262769 749020240339130078447077)
                ·
                  refine ⟨140441295063586889708827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749020240339130078447077 140441295063586889708827)
                  ·
                    rfl

theorem cell21_615394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_615394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615394 prefixEnd_615394 := by exact prefixLift 615394
  have htrace : WordTrace (prefixWord ++ tailWord_615394) baseStart_615394 baseEnd_615394 := by
    simpa [prefixWord, tailWord_615394, baseEnd_615394] using wordTrace_append hprefix tailTrace_615394
  have hstable : (prefixWord ++ tailWord_615394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615394).length < 2 ^ (prefixWord ++ tailWord_615394).sum := by decide
  have hdescent : baseEnd_615394 < baseStart_615394 := by decide
  rcases family_descends (prefixWord ++ tailWord_615394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615397 : List Nat := [1, 3, 1, 6, 1, 2, 2, 2, 3]
def baseStart_615397 : Nat := 118140960795 + 615397 * 2 ^ 59
def prefixEnd_615397 : Nat := 4983230072969 + 3 ^ 40 * 615397 * 2
def baseEnd_615397 : Nat := 140441979704459551158821

theorem tailTrace_615397 : CollatzResearch.WordTrace tailWord_615397 prefixEnd_615397 140441979704459551158821 := by
  unfold tailWord_615397
  simp only [CollatzResearch.WordTrace]
  refine ⟨22445372551529245285156445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14963581701019496856770963 22445372551529245285156445)
  ·
    refine ⟨8417014706823466981933667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22445372551529245285156445 8417014706823466981933667)
    ·
      refine ⟨12625522060235200472900501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8417014706823466981933667 12625522060235200472900501)
      ·
        refine ⟨591821346573525022167211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12625522060235200472900501 591821346573525022167211)
        ·
          refine ⟨887732019860287533250817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591821346573525022167211 887732019860287533250817)
          ·
            refine ⟨665799014895215649938113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 887732019860287533250817 665799014895215649938113)
            ·
              refine ⟨499349261171411737453585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665799014895215649938113 499349261171411737453585)
              ·
                refine ⟨374511945878558803090189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 499349261171411737453585 374511945878558803090189)
                ·
                  refine ⟨140441979704459551158821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374511945878558803090189 140441979704459551158821)
                  ·
                    rfl

theorem cell21_615397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_615397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615397 prefixEnd_615397 := by exact prefixLift 615397
  have htrace : WordTrace (prefixWord ++ tailWord_615397) baseStart_615397 baseEnd_615397 := by
    simpa [prefixWord, tailWord_615397, baseEnd_615397] using wordTrace_append hprefix tailTrace_615397
  have hstable : (prefixWord ++ tailWord_615397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615397).length < 2 ^ (prefixWord ++ tailWord_615397).sum := by decide
  have hdescent : baseEnd_615397 < baseStart_615397 := by decide
  rcases family_descends (prefixWord ++ tailWord_615397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615433 : List Nat := [1, 2, 1, 1, 3, 1, 1, 11]
def baseStart_615433 : Nat := 118140960795 + 615433 * 2 ^ 59
def prefixEnd_615433 : Nat := 4983230072969 + 3 ^ 40 * 615433 * 2
def baseEnd_615433 : Nat := 46816731798310496186249

theorem tailTrace_615433 : CollatzResearch.WordTrace tailWord_615433 prefixEnd_615433 46816731798310496186249 := by
  unfold tailWord_615433
  simp only [CollatzResearch.WordTrace]
  refine ⟨22446685579398823433466953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14964457052932548955644635 22446685579398823433466953)
  ·
    refine ⟨16835014184549117575100215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22446685579398823433466953 16835014184549117575100215)
    ·
      refine ⟨25252521276823676362650323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16835014184549117575100215 25252521276823676362650323)
      ·
        refine ⟨37878781915235514543975485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25252521276823676362650323 37878781915235514543975485)
        ·
          refine ⟨14204543218213317953990807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37878781915235514543975485 14204543218213317953990807)
          ·
            refine ⟨21306814827319976930986211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14204543218213317953990807 21306814827319976930986211)
            ·
              refine ⟨31960222240979965396479317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21306814827319976930986211 31960222240979965396479317)
              ·
                refine ⟨46816731798310496186249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 31960222240979965396479317 46816731798310496186249)
                ·
                  rfl

theorem cell21_615433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 11].length) (baseStart_615433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615433 prefixEnd_615433 := by exact prefixLift 615433
  have htrace : WordTrace (prefixWord ++ tailWord_615433) baseStart_615433 baseEnd_615433 := by
    simpa [prefixWord, tailWord_615433, baseEnd_615433] using wordTrace_append hprefix tailTrace_615433
  have hstable : (prefixWord ++ tailWord_615433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615433).length < 2 ^ (prefixWord ++ tailWord_615433).sum := by decide
  have hdescent : baseEnd_615433 < baseStart_615433 := by decide
  rcases family_descends (prefixWord ++ tailWord_615433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615481 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 5]
def baseStart_615481 : Nat := 118140960795 + 615481 * 2 ^ 59
def prefixEnd_615481 : Nat := 4983230072969 + 3 ^ 40 * 615481 * 2
def baseEnd_615481 : Nat := 140461149648894071758649

theorem tailTrace_615481 : CollatzResearch.WordTrace tailWord_615481 prefixEnd_615481 140461149648894071758649 := by
  unfold tailWord_615481
  simp only [CollatzResearch.WordTrace]
  refine ⟨22448436283224927631214297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14965624188816618420809531 22448436283224927631214297)
  ·
    refine ⟨16836327212418695723410723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22448436283224927631214297 16836327212418695723410723)
    ·
      refine ⟨25254490818628043585116085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16836327212418695723410723 25254490818628043585116085)
      ·
        refine ⟨2367608514246379086104633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25254490818628043585116085 2367608514246379086104633)
        ·
          refine ⟨1775706385684784314578475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2367608514246379086104633 1775706385684784314578475)
          ·
            refine ⟨2663559578527176471867713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775706385684784314578475 2663559578527176471867713)
            ·
              refine ⟨1997669683895382353900785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2663559578527176471867713 1997669683895382353900785)
              ·
                refine ⟨1498252262921536765425589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997669683895382353900785 1498252262921536765425589)
                ·
                  refine ⟨140461149648894071758649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1498252262921536765425589 140461149648894071758649)
                  ·
                    rfl

theorem cell21_615481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_615481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615481 prefixEnd_615481 := by exact prefixLift 615481
  have htrace : WordTrace (prefixWord ++ tailWord_615481) baseStart_615481 baseEnd_615481 := by
    simpa [prefixWord, tailWord_615481, baseEnd_615481] using wordTrace_append hprefix tailTrace_615481
  have hstable : (prefixWord ++ tailWord_615481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615481).length < 2 ^ (prefixWord ++ tailWord_615481).sum := by decide
  have hdescent : baseEnd_615481 < baseStart_615481 := by decide
  rcases family_descends (prefixWord ++ tailWord_615481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615495 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 6]
def baseStart_615495 : Nat := 118140960795 + 615495 * 2 ^ 59
def prefixEnd_615495 : Nat := 4983230072969 + 3 ^ 40 * 615495 * 2
def baseEnd_615495 : Nat := 140464344639633158525287

theorem tailTrace_615495 : CollatzResearch.WordTrace tailWord_615495 prefixEnd_615495 140464344639633158525287 := by
  unfold tailWord_615495
  simp only [CollatzResearch.WordTrace]
  refine ⟨22448946905174208022223939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14965964603449472014815959 22448946905174208022223939)
  ·
    refine ⟨33673420357761312033335909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22448946905174208022223939 33673420357761312033335909)
    ·
      refine ⟨6313766317080246006250483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33673420357761312033335909 6313766317080246006250483)
      ·
        refine ⟨9470649475620369009375725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6313766317080246006250483 9470649475620369009375725)
        ·
          refine ⟨3551493553357638378515897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9470649475620369009375725 3551493553357638378515897)
          ·
            refine ⟨2663620165018228783886923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3551493553357638378515897 2663620165018228783886923)
            ·
              refine ⟨3995430247527343175830385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663620165018228783886923 3995430247527343175830385)
              ·
                refine ⟨2996572685645507381872789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3995430247527343175830385 2996572685645507381872789)
                ·
                  refine ⟨140464344639633158525287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2996572685645507381872789 140464344639633158525287)
                  ·
                    rfl

theorem cell21_615495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_615495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615495 prefixEnd_615495 := by exact prefixLift 615495
  have htrace : WordTrace (prefixWord ++ tailWord_615495) baseStart_615495 baseEnd_615495 := by
    simpa [prefixWord, tailWord_615495, baseEnd_615495] using wordTrace_append hprefix tailTrace_615495
  have hstable : (prefixWord ++ tailWord_615495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615495).length < 2 ^ (prefixWord ++ tailWord_615495).sum := by decide
  have hdescent : baseEnd_615495 < baseStart_615495 := by decide
  rcases family_descends (prefixWord ++ tailWord_615495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615498 : List Nat := [3, 1, 2, 1, 1, 2, 5, 3, 3]
def baseStart_615498 : Nat := 118140960795 + 615498 * 2 ^ 59
def prefixEnd_615498 : Nat := 4983230072969 + 3 ^ 40 * 615498 * 2
def baseEnd_615498 : Nat := 140465029280505819975281

theorem tailTrace_615498 : CollatzResearch.WordTrace tailWord_615498 prefixEnd_615498 140465029280505819975281 := by
  unfold tailWord_615498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5612264081040834883645787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14966037549442226356388765 5612264081040834883645787)
  ·
    refine ⟨8418396121561252325468681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5612264081040834883645787 8418396121561252325468681)
    ·
      refine ⟨6313797091170939244101511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8418396121561252325468681 6313797091170939244101511)
      ·
        refine ⟨9470695636756408866152267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6313797091170939244101511 9470695636756408866152267)
        ·
          refine ⟨14206043455134613299228401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9470695636756408866152267 14206043455134613299228401)
          ·
            refine ⟨10654532591350959974421301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14206043455134613299228401 10654532591350959974421301)
            ·
              refine ⟨998862430439152497601997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10654532591350959974421301 998862430439152497601997)
              ·
                refine ⟨374573411414682186600749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 998862430439152497601997 374573411414682186600749)
                ·
                  refine ⟨140465029280505819975281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374573411414682186600749 140465029280505819975281)
                  ·
                    rfl

theorem cell21_615498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_615498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615498 prefixEnd_615498 := by exact prefixLift 615498
  have htrace : WordTrace (prefixWord ++ tailWord_615498) baseStart_615498 baseEnd_615498 := by
    simpa [prefixWord, tailWord_615498, baseEnd_615498] using wordTrace_append hprefix tailTrace_615498
  have hstable : (prefixWord ++ tailWord_615498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615498).length < 2 ^ (prefixWord ++ tailWord_615498).sum := by decide
  have hdescent : baseEnd_615498 < baseStart_615498 := by decide
  rcases family_descends (prefixWord ++ tailWord_615498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615529 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 4]
def baseStart_615529 : Nat := 118140960795 + 615529 * 2 ^ 59
def prefixEnd_615529 : Nat := 4983230072969 + 3 ^ 40 * 615529 * 2
def baseEnd_615529 : Nat := 140472103902856654958551

theorem tailTrace_615529 : CollatzResearch.WordTrace tailWord_615529 prefixEnd_615529 140472103902856654958551 := by
  unfold tailWord_615529
  simp only [CollatzResearch.WordTrace]
  refine ⟨22450186987051031828961641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14966791324700687885974427 22450186987051031828961641)
  ·
    refine ⟨16837640240288273871721231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22450186987051031828961641 16837640240288273871721231)
    ·
      refine ⟨25256460360432410807581847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16837640240288273871721231 25256460360432410807581847)
      ·
        refine ⟨37884690540648616211372771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25256460360432410807581847 37884690540648616211372771)
        ·
          refine ⟨56827035810972924317059157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37884690540648616211372771 56827035810972924317059157)
          ·
            refine ⟨665941825909838956840537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 56827035810972924317059157 665941825909838956840537)
            ·
              refine ⟨499456369432379217630403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665941825909838956840537 499456369432379217630403)
              ·
                refine ⟨749184554148568826445605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499456369432379217630403 749184554148568826445605)
                ·
                  refine ⟨140472103902856654958551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749184554148568826445605 140472103902856654958551)
                  ·
                    rfl

theorem cell21_615529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_615529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615529 prefixEnd_615529 := by exact prefixLift 615529
  have htrace : WordTrace (prefixWord ++ tailWord_615529) baseStart_615529 baseEnd_615529 := by
    simpa [prefixWord, tailWord_615529, baseEnd_615529] using wordTrace_append hprefix tailTrace_615529
  have hstable : (prefixWord ++ tailWord_615529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615529).length < 2 ^ (prefixWord ++ tailWord_615529).sum := by decide
  have hdescent : baseEnd_615529 < baseStart_615529 := by decide
  rcases family_descends (prefixWord ++ tailWord_615529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615571 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 4]
def baseStart_615571 : Nat := 118140960795 + 615571 * 2 ^ 59
def prefixEnd_615571 : Nat := 4983230072969 + 3 ^ 40 * 615571 * 2
def baseEnd_615571 : Nat := 140481688875073915258465

theorem tailTrace_615571 : CollatzResearch.WordTrace tailWord_615571 prefixEnd_615571 140481688875073915258465 := by
  unfold tailWord_615571
  simp only [CollatzResearch.WordTrace]
  refine ⟨22451718852898873001990567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14967812568599248667993711 22451718852898873001990567)
  ·
    refine ⟨33677578279348309502985851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22451718852898873001990567 33677578279348309502985851)
    ·
      refine ⟨50516367419022464254478777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33677578279348309502985851 50516367419022464254478777)
      ·
        refine ⟨37887275564266848190859083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50516367419022464254478777 37887275564266848190859083)
        ·
          refine ⟨56830913346400272286288625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37887275564266848190859083 56830913346400272286288625)
          ·
            refine ⟨42623185009800204214716469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56830913346400272286288625 42623185009800204214716469)
            ·
              refine ⟨3995923594668769145129669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42623185009800204214716469 3995923594668769145129669)
              ·
                refine ⟨749235674000394214711813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3995923594668769145129669 749235674000394214711813)
                ·
                  refine ⟨140481688875073915258465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749235674000394214711813 140481688875073915258465)
                  ·
                    rfl

theorem cell21_615571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 4].length) (baseStart_615571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615571 prefixEnd_615571 := by exact prefixLift 615571
  have htrace : WordTrace (prefixWord ++ tailWord_615571) baseStart_615571 baseEnd_615571 := by
    simpa [prefixWord, tailWord_615571, baseEnd_615571] using wordTrace_append hprefix tailTrace_615571
  have hstable : (prefixWord ++ tailWord_615571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615571).length < 2 ^ (prefixWord ++ tailWord_615571).sum := by decide
  have hdescent : baseEnd_615571 < baseStart_615571 := by decide
  rcases family_descends (prefixWord ++ tailWord_615571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615588 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 4]
def baseStart_615588 : Nat := 118140960795 + 615588 * 2 ^ 59
def prefixEnd_615588 : Nat := 4983230072969 + 3 ^ 40 * 615588 * 2
def baseEnd_615588 : Nat := 140485568506685663475097

theorem tailTrace_615588 : CollatzResearch.WordTrace tailWord_615588 prefixEnd_615588 140485568506685663475097 := by
  unfold tailWord_615588
  simp only [CollatzResearch.WordTrace]
  refine ⟨11226169446918642452679709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14968225929224856603572945 11226169446918642452679709)
  ·
    refine ⟨4209813542594490919754891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11226169446918642452679709 4209813542594490919754891)
    ·
      refine ⟨6314720313891736379632337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4209813542594490919754891 6314720313891736379632337)
      ·
        refine ⟨4736040235418802284724253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6314720313891736379632337 4736040235418802284724253)
        ·
          refine ⟨1776015088282050856771595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4736040235418802284724253 1776015088282050856771595)
          ·
            refine ⟨2664022632423076285157393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776015088282050856771595 2664022632423076285157393)
            ·
              refine ⟨1998016974317307213868045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2664022632423076285157393 1998016974317307213868045)
              ·
                refine ⟨749256365368990205200517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1998016974317307213868045 749256365368990205200517)
                ·
                  refine ⟨140485568506685663475097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749256365368990205200517 140485568506685663475097)
                  ·
                    rfl

theorem cell21_615588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_615588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615588 prefixEnd_615588 := by exact prefixLift 615588
  have htrace : WordTrace (prefixWord ++ tailWord_615588) baseStart_615588 baseEnd_615588 := by
    simpa [prefixWord, tailWord_615588, baseEnd_615588] using wordTrace_append hprefix tailTrace_615588
  have hstable : (prefixWord ++ tailWord_615588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615588).length < 2 ^ (prefixWord ++ tailWord_615588).sum := by decide
  have hdescent : baseEnd_615588 < baseStart_615588 := by decide
  rcases family_descends (prefixWord ++ tailWord_615588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
