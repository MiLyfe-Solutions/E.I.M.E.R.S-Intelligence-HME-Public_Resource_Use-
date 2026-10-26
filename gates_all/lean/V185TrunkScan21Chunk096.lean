import V185TrunkScan21Chunk095

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1166263 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 6]
def baseStart_1166263 : Nat := 118140960795 + 1166263 * 2 ^ 59
def prefixEnd_1166263 : Nat := 4983230072969 + 3 ^ 40 * 1166263 * 2
def baseEnd_1166263 : Nat := 266157106024300321932871

theorem tailTrace_1166263 : CollatzResearch.WordTrace tailWord_1166263 prefixEnd_1166263 266157106024300321932871 := by
  unfold tailWord_1166263
  simp only [CollatzResearch.WordTrace]
  refine ⟨42537106173835807707831443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28358070782557205138554295 42537106173835807707831443)
  ·
    refine ⟨63805659260753711561747165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42537106173835807707831443 63805659260753711561747165)
    ·
      refine ⟨23927122222782641835655187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63805659260753711561747165 23927122222782641835655187)
      ·
        refine ⟨35890683334173962753482781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23927122222782641835655187 35890683334173962753482781)
        ·
          refine ⟨13459006250315236032556043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35890683334173962753482781 13459006250315236032556043)
          ·
            refine ⟨20188509375472854048834065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13459006250315236032556043 20188509375472854048834065)
            ·
              refine ⟨15141382031604640536625549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20188509375472854048834065 15141382031604640536625549)
              ·
                refine ⟨5678018261851740201234581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15141382031604640536625549 5678018261851740201234581)
                ·
                  refine ⟨266157106024300321932871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5678018261851740201234581 266157106024300321932871)
                  ·
                    rfl

theorem cell21_1166263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_1166263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166263 prefixEnd_1166263 := by exact prefixLift 1166263
  have htrace : WordTrace (prefixWord ++ tailWord_1166263) baseStart_1166263 baseEnd_1166263 := by
    simpa [prefixWord, tailWord_1166263, baseEnd_1166263] using wordTrace_append hprefix tailTrace_1166263
  have hstable : (prefixWord ++ tailWord_1166263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166263).length < 2 ^ (prefixWord ++ tailWord_1166263).sum := by decide
  have hdescent : baseEnd_1166263 < baseStart_1166263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166266 : List Nat := [3, 1, 1, 1, 2, 1, 5, 4, 3]
def baseStart_1166266 : Nat := 118140960795 + 1166266 * 2 ^ 59
def prefixEnd_1166266 : Nat := 4983230072969 + 3 ^ 40 * 1166266 * 2
def baseEnd_1166266 : Nat := 266157790665172983382865

theorem tailTrace_1166266 : CollatzResearch.WordTrace tailWord_1166266 prefixEnd_1166266 266157790665172983382865 := by
  unfold tailWord_1166266
  simp only [CollatzResearch.WordTrace]
  refine ⟨10634303898206234805047663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28358143728549959480127101 10634303898206234805047663)
  ·
    refine ⟨15951455847309352207571495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10634303898206234805047663 15951455847309352207571495)
    ·
      refine ⟨23927183770964028311357243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15951455847309352207571495 23927183770964028311357243)
      ·
        refine ⟨35890775656446042467035865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23927183770964028311357243 35890775656446042467035865)
        ·
          refine ⟨26918081742334531850276899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35890775656446042467035865 26918081742334531850276899)
          ·
            refine ⟨40377122613501797775415349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26918081742334531850276899 40377122613501797775415349)
            ·
              refine ⟨3785355245015793541445189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40377122613501797775415349 3785355245015793541445189)
              ·
                refine ⟨709754108440461289020973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3785355245015793541445189 709754108440461289020973)
                ·
                  refine ⟨266157790665172983382865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709754108440461289020973 266157790665172983382865)
                  ·
                    rfl

theorem cell21_1166266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_1166266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166266 prefixEnd_1166266 := by exact prefixLift 1166266
  have htrace : WordTrace (prefixWord ++ tailWord_1166266) baseStart_1166266 baseEnd_1166266 := by
    simpa [prefixWord, tailWord_1166266, baseEnd_1166266] using wordTrace_append hprefix tailTrace_1166266
  have hstable : (prefixWord ++ tailWord_1166266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166266).length < 2 ^ (prefixWord ++ tailWord_1166266).sum := by decide
  have hdescent : baseEnd_1166266 < baseStart_1166266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166359 : List Nat := [1, 1, 3, 5, 1, 1, 3, 3, 3]
def baseStart_1166359 : Nat := 118140960795 + 1166359 * 2 ^ 59
def prefixEnd_1166359 : Nat := 4983230072969 + 3 ^ 40 * 1166359 * 2
def baseEnd_1166359 : Nat := 266179014532225488332675

theorem tailTrace_1166359 : CollatzResearch.WordTrace tailWord_1166359 prefixEnd_1166359 266179014532225488332675 := by
  unfold tailWord_1166359
  simp only [CollatzResearch.WordTrace]
  refine ⟨42540607581488016103326131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28360405054325344068884087 42540607581488016103326131)
  ·
    refine ⟨63810911372232024154989197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42540607581488016103326131 63810911372232024154989197)
    ·
      refine ⟨23929091764587009058120949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63810911372232024154989197 23929091764587009058120949)
      ·
        refine ⟨2243352352930032099198839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23929091764587009058120949 2243352352930032099198839)
        ·
          refine ⟨3365028529395048148798259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243352352930032099198839 3365028529395048148798259)
          ·
            refine ⟨5047542794092572223197389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365028529395048148798259 5047542794092572223197389)
            ·
              refine ⟨1892828547784714583699021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5047542794092572223197389 1892828547784714583699021)
              ·
                refine ⟨709810705419267968887133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1892828547784714583699021 709810705419267968887133)
                ·
                  refine ⟨266179014532225488332675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709810705419267968887133 266179014532225488332675)
                  ·
                    rfl

theorem cell21_1166359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 3].length) (baseStart_1166359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166359 prefixEnd_1166359 := by exact prefixLift 1166359
  have htrace : WordTrace (prefixWord ++ tailWord_1166359) baseStart_1166359 baseEnd_1166359 := by
    simpa [prefixWord, tailWord_1166359, baseEnd_1166359] using wordTrace_append hprefix tailTrace_1166359
  have hstable : (prefixWord ++ tailWord_1166359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166359).length < 2 ^ (prefixWord ++ tailWord_1166359).sum := by decide
  have hdescent : baseEnd_1166359 < baseStart_1166359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166370 : List Nat := [3, 3, 1, 1, 1, 3, 9]
def baseStart_1166370 : Nat := 118140960795 + 1166370 * 2 ^ 59
def prefixEnd_1166370 : Nat := 4983230072969 + 3 ^ 40 * 1166370 * 2
def baseEnd_1166370 : Nat := 29575724986899101516591

theorem tailTrace_1166370 : CollatzResearch.WordTrace tailWord_1166370 prefixEnd_1166370 29575724986899101516591 := by
  unfold tailWord_1166370
  simp only [CollatzResearch.WordTrace]
  refine ⟨10635252196112041245494141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28360672522965443321317709 10635252196112041245494141)
  ·
    refine ⟨3988219573542015467060303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10635252196112041245494141 3988219573542015467060303)
    ·
      refine ⟨5982329360313023200590455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3988219573542015467060303 5982329360313023200590455)
      ·
        refine ⟨8973494040469534800885683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5982329360313023200590455 8973494040469534800885683)
        ·
          refine ⟨13460241060704302201328525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8973494040469534800885683 13460241060704302201328525)
          ·
            refine ⟨5047590397764113325498197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13460241060704302201328525 5047590397764113325498197)
            ·
              refine ⟨29575724986899101516591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5047590397764113325498197 29575724986899101516591)
              ·
                rfl

theorem cell21_1166370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 9].length) (baseStart_1166370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166370 prefixEnd_1166370 := by exact prefixLift 1166370
  have htrace : WordTrace (prefixWord ++ tailWord_1166370) baseStart_1166370 baseEnd_1166370 := by
    simpa [prefixWord, tailWord_1166370, baseEnd_1166370] using wordTrace_append hprefix tailTrace_1166370
  have hstable : (prefixWord ++ tailWord_1166370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166370).length < 2 ^ (prefixWord ++ tailWord_1166370).sum := by decide
  have hdescent : baseEnd_1166370 < baseStart_1166370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166390 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1166390 : Nat := 118140960795 + 1166390 * 2 ^ 59
def prefixEnd_1166390 : Nat := 4983230072969 + 3 ^ 40 * 1166390 * 2
def baseEnd_1166390 : Nat := 266186089154576323315945

theorem tailTrace_1166390 : CollatzResearch.WordTrace tailWord_1166390 prefixEnd_1166390 266186089154576323315945 := by
  unfold tailWord_1166390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2658858640273481774856539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28361158829583805598469749 2658858640273481774856539)
  ·
    refine ⟨3988287960410222662284809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2658858640273481774856539 3988287960410222662284809)
    ·
      refine ⟨2991215970307666996713607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3988287960410222662284809 2991215970307666996713607)
      ·
        refine ⟨4486823955461500495070411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2991215970307666996713607 4486823955461500495070411)
        ·
          refine ⟨6730235933192250742605617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4486823955461500495070411 6730235933192250742605617)
          ·
            refine ⟨5047676949894188056954213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6730235933192250742605617 5047676949894188056954213)
            ·
              refine ⟨946439428105160260678915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5047676949894188056954213 946439428105160260678915)
              ·
                refine ⟨1419659142157740391018373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946439428105160260678915 1419659142157740391018373)
                ·
                  refine ⟨266186089154576323315945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1419659142157740391018373 266186089154576323315945)
                  ·
                    rfl

theorem cell21_1166390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1166390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166390 prefixEnd_1166390 := by exact prefixLift 1166390
  have htrace : WordTrace (prefixWord ++ tailWord_1166390) baseStart_1166390 baseEnd_1166390 := by
    simpa [prefixWord, tailWord_1166390, baseEnd_1166390] using wordTrace_append hprefix tailTrace_1166390
  have hstable : (prefixWord ++ tailWord_1166390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166390).length < 2 ^ (prefixWord ++ tailWord_1166390).sum := by decide
  have hdescent : baseEnd_1166390 < baseStart_1166390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166432 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 4]
def baseStart_1166432 : Nat := 118140960795 + 1166432 * 2 ^ 59
def prefixEnd_1166432 : Nat := 4983230072969 + 3 ^ 40 * 1166432 * 2
def baseEnd_1166432 : Nat := 266195674126793583615859

theorem tailTrace_1166432 : CollatzResearch.WordTrace tailWord_1166432 prefixEnd_1166432 266195674126793583615859 := by
  unfold tailWord_1166432
  simp only [CollatzResearch.WordTrace]
  refine ⟨21271635055111774785366775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28362180073482366380489033 21271635055111774785366775)
  ·
    refine ⟨31907452582667662178050163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21271635055111774785366775 31907452582667662178050163)
    ·
      refine ⟨47861178874001493267075245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31907452582667662178050163 47861178874001493267075245)
      ·
        refine ⟨17947942077750559975153217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47861178874001493267075245 17947942077750559975153217)
        ·
          refine ⟨13460956558312919981364913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17947942077750559975153217 13460956558312919981364913)
          ·
            refine ⟨10095717418734689986023685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13460956558312919981364913 10095717418734689986023685)
            ·
              refine ⟨1892947016012754372379441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10095717418734689986023685 1892947016012754372379441)
              ·
                refine ⟨1419710262009565779284581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1892947016012754372379441 1419710262009565779284581)
                ·
                  refine ⟨266195674126793583615859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1419710262009565779284581 266195674126793583615859)
                  ·
                    rfl

theorem cell21_1166432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_1166432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166432 prefixEnd_1166432 := by exact prefixLift 1166432
  have htrace : WordTrace (prefixWord ++ tailWord_1166432) baseStart_1166432 baseEnd_1166432 := by
    simpa [prefixWord, tailWord_1166432, baseEnd_1166432] using wordTrace_append hprefix tailTrace_1166432
  have hstable : (prefixWord ++ tailWord_1166432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166432).length < 2 ^ (prefixWord ++ tailWord_1166432).sum := by decide
  have hdescent : baseEnd_1166432 < baseStart_1166432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166494 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1166494 : Nat := 118140960795 + 1166494 * 2 ^ 59
def prefixEnd_1166494 : Nat := 4983230072969 + 3 ^ 40 * 1166494 * 2
def baseEnd_1166494 : Nat := 266209823371495253582399

theorem tailTrace_1166494 : CollatzResearch.WordTrace tailWord_1166494 prefixEnd_1166494 266209823371495253582399 := by
  unfold tailWord_1166494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5318191429499866769936317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28363687623999289439660357 5318191429499866769936317)
  ·
    refine ⟨1994321786062450038726119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5318191429499866769936317 1994321786062450038726119)
    ·
      refine ⟨2991482679093675058089179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1994321786062450038726119 2991482679093675058089179)
      ·
        refine ⟨4487224018640512587133769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2991482679093675058089179 4487224018640512587133769)
        ·
          refine ⟨3365418013980384440350327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4487224018640512587133769 3365418013980384440350327)
          ·
            refine ⟨5048127020970576660525491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365418013980384440350327 5048127020970576660525491)
            ·
              refine ⟨7572190531455864990788237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5048127020970576660525491 7572190531455864990788237)
              ·
                refine ⟨2839571449295949371545589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7572190531455864990788237 2839571449295949371545589)
                ·
                  refine ⟨266209823371495253582399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2839571449295949371545589 266209823371495253582399)
                  ·
                    rfl

theorem cell21_1166494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1166494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166494 prefixEnd_1166494 := by exact prefixLift 1166494
  have htrace : WordTrace (prefixWord ++ tailWord_1166494) baseStart_1166494 baseEnd_1166494 := by
    simpa [prefixWord, tailWord_1166494, baseEnd_1166494] using wordTrace_append hprefix tailTrace_1166494
  have hstable : (prefixWord ++ tailWord_1166494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166494).length < 2 ^ (prefixWord ++ tailWord_1166494).sum := by decide
  have hdescent : baseEnd_1166494 < baseStart_1166494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166528 : List Nat := [2, 1, 1, 2, 7, 1, 1, 3, 3]
def baseStart_1166528 : Nat := 118140960795 + 1166528 * 2 ^ 59
def prefixEnd_1166528 : Nat := 4983230072969 + 3 ^ 40 * 1166528 * 2
def baseEnd_1166528 : Nat := 266217582634718750015663

theorem tailTrace_1166528 : CollatzResearch.WordTrace tailWord_1166528 prefixEnd_1166528 266217582634718750015663 := by
  unfold tailWord_1166528
  simp only [CollatzResearch.WordTrace]
  refine ⟨21273385758937878983114119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28364514345250505310818825 21273385758937878983114119)
  ·
    refine ⟨31910078638406818474671179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21273385758937878983114119 31910078638406818474671179)
    ·
      refine ⟨47865117957610227712006769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31910078638406818474671179 47865117957610227712006769)
      ·
        refine ⟨35898838468207670784005077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47865117957610227712006769 35898838468207670784005077)
        ·
          refine ⟨841379026598617284000119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35898838468207670784005077 841379026598617284000119)
          ·
            refine ⟨1262068539897925926000179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841379026598617284000119 1262068539897925926000179)
            ·
              refine ⟨1893102809846888889000269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262068539897925926000179 1893102809846888889000269)
              ·
                refine ⟨709913553692583333375101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1893102809846888889000269 709913553692583333375101)
                ·
                  refine ⟨266217582634718750015663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709913553692583333375101 266217582634718750015663)
                  ·
                    rfl

theorem cell21_1166528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 3].length) (baseStart_1166528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166528 prefixEnd_1166528 := by exact prefixLift 1166528
  have htrace : WordTrace (prefixWord ++ tailWord_1166528) baseStart_1166528 baseEnd_1166528 := by
    simpa [prefixWord, tailWord_1166528, baseEnd_1166528] using wordTrace_append hprefix tailTrace_1166528
  have hstable : (prefixWord ++ tailWord_1166528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166528).length < 2 ^ (prefixWord ++ tailWord_1166528).sum := by decide
  have hdescent : baseEnd_1166528 < baseStart_1166528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166536 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_1166536 : Nat := 118140960795 + 1166536 * 2 ^ 59
def prefixEnd_1166536 : Nat := 4983230072969 + 3 ^ 40 * 1166536 * 2
def baseEnd_1166536 : Nat := 266219408343712513882313

theorem tailTrace_1166536 : CollatzResearch.WordTrace tailWord_1166536 prefixEnd_1166536 266219408343712513882313 := by
  unfold tailWord_1166536
  simp only [CollatzResearch.WordTrace]
  refine ⟨21273531650923387666259731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28364708867897850221679641 21273531650923387666259731)
  ·
    refine ⟨31910297476385081499389597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21273531650923387666259731 31910297476385081499389597)
    ·
      refine ⟨11966361553644405562271099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31910297476385081499389597 11966361553644405562271099)
      ·
        refine ⟨17949542330466608343406649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11966361553644405562271099 17949542330466608343406649)
        ·
          refine ⟨13462156747849956257554987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17949542330466608343406649 13462156747849956257554987)
          ·
            refine ⟨20193235121774934386332481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13462156747849956257554987 20193235121774934386332481)
            ·
              refine ⟨15144926341331200789749361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20193235121774934386332481 15144926341331200789749361)
              ·
                refine ⟨11358694755998400592312021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15144926341331200789749361 11358694755998400592312021)
                ·
                  refine ⟨266219408343712513882313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11358694755998400592312021 266219408343712513882313)
                  ·
                    rfl

theorem cell21_1166536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_1166536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166536 prefixEnd_1166536 := by exact prefixLift 1166536
  have htrace : WordTrace (prefixWord ++ tailWord_1166536) baseStart_1166536 baseEnd_1166536 := by
    simpa [prefixWord, tailWord_1166536, baseEnd_1166536] using wordTrace_append hprefix tailTrace_1166536
  have hstable : (prefixWord ++ tailWord_1166536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166536).length < 2 ^ (prefixWord ++ tailWord_1166536).sum := by decide
  have hdescent : baseEnd_1166536 < baseStart_1166536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166629 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 5]
def baseStart_1166629 : Nat := 118140960795 + 1166629 * 2 ^ 59
def prefixEnd_1166629 : Nat := 4983230072969 + 3 ^ 40 * 1166629 * 2
def baseEnd_1166629 : Nat := 266240632210765018832123

theorem tailTrace_1166629 : CollatzResearch.WordTrace tailWord_1166629 prefixEnd_1166629 266240632210765018832123 := by
  unfold tailWord_1166629
  simp only [CollatzResearch.WordTrace]
  refine ⟨42550455290509852215654941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28366970193673234810436627 42550455290509852215654941)
  ·
    refine ⟨15956420733941194580870603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42550455290509852215654941 15956420733941194580870603)
    ·
      refine ⟨23934631100911791871305905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15956420733941194580870603 23934631100911791871305905)
      ·
        refine ⟨17950973325683843903479429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23934631100911791871305905 17950973325683843903479429)
        ·
          refine ⟨3365807498565720731902393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17950973325683843903479429 3365807498565720731902393)
          ·
            refine ⟨2524355623924290548926795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3365807498565720731902393 2524355623924290548926795)
            ·
              refine ⟨3786533435886435823390193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2524355623924290548926795 3786533435886435823390193)
              ·
                refine ⟨2839900076914826867542645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3786533435886435823390193 2839900076914826867542645)
                ·
                  refine ⟨266240632210765018832123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2839900076914826867542645 266240632210765018832123)
                  ·
                    rfl

theorem cell21_1166629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_1166629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166629 prefixEnd_1166629 := by exact prefixLift 1166629
  have htrace : WordTrace (prefixWord ++ tailWord_1166629) baseStart_1166629 baseEnd_1166629 := by
    simpa [prefixWord, tailWord_1166629, baseEnd_1166629] using wordTrace_append hprefix tailTrace_1166629
  have hstable : (prefixWord ++ tailWord_1166629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166629).length < 2 ^ (prefixWord ++ tailWord_1166629).sum := by decide
  have hdescent : baseEnd_1166629 < baseStart_1166629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166677 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 4]
def baseStart_1166677 : Nat := 118140960795 + 1166677 * 2 ^ 59
def prefixEnd_1166677 : Nat := 4983230072969 + 3 ^ 40 * 1166677 * 2
def baseEnd_1166677 : Nat := 266251586464727602032025

theorem tailTrace_1166677 : CollatzResearch.WordTrace tailWord_1166677 prefixEnd_1166677 266251586464727602032025 := by
  unfold tailWord_1166677
  simp only [CollatzResearch.WordTrace]
  refine ⟨42552205994335956413402285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28368137329557304275601523 42552205994335956413402285)
  ·
    refine ⟨15957077247875983655025857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42552205994335956413402285 15957077247875983655025857)
    ·
      refine ⟨11967807935906987741269393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15957077247875983655025857 11967807935906987741269393)
      ·
        refine ⟨8975855951930240805952045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11967807935906987741269393 8975855951930240805952045)
        ·
          refine ⟨3365945981973840302232017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8975855951930240805952045 3365945981973840302232017)
          ·
            refine ⟨2524459486480380226674013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3365945981973840302232017 2524459486480380226674013)
            ·
              refine ⟨946672307430142585002755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2524459486480380226674013 946672307430142585002755)
              ·
                refine ⟨1420008461145213877504133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946672307430142585002755 1420008461145213877504133)
                ·
                  refine ⟨266251586464727602032025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1420008461145213877504133 266251586464727602032025)
                  ·
                    rfl

theorem cell21_1166677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_1166677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166677 prefixEnd_1166677 := by exact prefixLift 1166677
  have htrace : WordTrace (prefixWord ++ tailWord_1166677) baseStart_1166677 baseEnd_1166677 := by
    simpa [prefixWord, tailWord_1166677, baseEnd_1166677] using wordTrace_append hprefix tailTrace_1166677
  have hstable : (prefixWord ++ tailWord_1166677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166677).length < 2 ^ (prefixWord ++ tailWord_1166677).sum := by decide
  have hdescent : baseEnd_1166677 < baseStart_1166677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166691 : List Nat := [1, 1, 1, 5, 2, 4, 2, 5]
def baseStart_1166691 : Nat := 118140960795 + 1166691 * 2 ^ 59
def prefixEnd_1166691 : Nat := 4983230072969 + 3 ^ 40 * 1166691 * 2
def baseEnd_1166691 : Nat := 88751593818488896266221

theorem tailTrace_1166691 : CollatzResearch.WordTrace tailWord_1166691 prefixEnd_1166691 88751593818488896266221 := by
  unfold tailWord_1166691
  simp only [CollatzResearch.WordTrace]
  refine ⟨42552716616285236804411927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28368477744190157869607951 42552716616285236804411927)
  ·
    refine ⟨63829074924427855206617891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42552716616285236804411927 63829074924427855206617891)
    ·
      refine ⟨95743612386641782809926837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63829074924427855206617891 95743612386641782809926837)
      ·
        refine ⟨8975963661247667138430641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95743612386641782809926837 8975963661247667138430641)
        ·
          refine ⟨6731972745935750353822981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8975963661247667138430641 6731972745935750353822981)
          ·
            refine ⟨1262244889862953191341809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6731972745935750353822981 1262244889862953191341809)
            ·
              refine ⟨946683667397214893506357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1262244889862953191341809 946683667397214893506357)
              ·
                refine ⟨88751593818488896266221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 946683667397214893506357 88751593818488896266221)
                ·
                  rfl

theorem cell21_1166691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 5].length) (baseStart_1166691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166691 prefixEnd_1166691 := by exact prefixLift 1166691
  have htrace : WordTrace (prefixWord ++ tailWord_1166691) baseStart_1166691 baseEnd_1166691 := by
    simpa [prefixWord, tailWord_1166691, baseEnd_1166691] using wordTrace_append hprefix tailTrace_1166691
  have hstable : (prefixWord ++ tailWord_1166691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166691).length < 2 ^ (prefixWord ++ tailWord_1166691).sum := by decide
  have hdescent : baseEnd_1166691 < baseStart_1166691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166795 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 4]
def baseStart_1166795 : Nat := 118140960795 + 1166795 * 2 ^ 59
def prefixEnd_1166795 : Nat := 4983230072969 + 3 ^ 40 * 1166795 * 2
def baseEnd_1166795 : Nat := 266278515672385619065117

theorem tailTrace_1166795 : CollatzResearch.WordTrace tailWord_1166795 prefixEnd_1166795 266278515672385619065117 := by
  unfold tailWord_1166795
  simp only [CollatzResearch.WordTrace]
  refine ⟨42556509807908462566197839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28371006538605641710798559 42556509807908462566197839)
  ·
    refine ⟨63834764711862693849296759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42556509807908462566197839 63834764711862693849296759)
    ·
      refine ⟨95752147067794040773945139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63834764711862693849296759 95752147067794040773945139)
      ·
        refine ⟨143628220601691061160917709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95752147067794040773945139 143628220601691061160917709)
        ·
          refine ⟨53860582725634147935344141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143628220601691061160917709 53860582725634147935344141)
          ·
            refine ⟨20197718522112805475754053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53860582725634147935344141 20197718522112805475754053)
            ·
              refine ⟨3787072222896151026703885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20197718522112805475754053 3787072222896151026703885)
              ·
                refine ⟨1420152083586056635013957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3787072222896151026703885 1420152083586056635013957)
                ·
                  refine ⟨266278515672385619065117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1420152083586056635013957 266278515672385619065117)
                  ·
                    rfl

theorem cell21_1166795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 4].length) (baseStart_1166795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166795 prefixEnd_1166795 := by exact prefixLift 1166795
  have htrace : WordTrace (prefixWord ++ tailWord_1166795) baseStart_1166795 baseEnd_1166795 := by
    simpa [prefixWord, tailWord_1166795, baseEnd_1166795] using wordTrace_append hprefix tailTrace_1166795
  have hstable : (prefixWord ++ tailWord_1166795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166795).length < 2 ^ (prefixWord ++ tailWord_1166795).sum := by decide
  have hdescent : baseEnd_1166795 < baseStart_1166795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166826 : List Nat := [3, 1, 3, 1, 4, 1, 8]
def baseStart_1166826 : Nat := 118140960795 + 1166826 * 2 ^ 59
def prefixEnd_1166826 : Nat := 4983230072969 + 3 ^ 40 * 1166826 * 2
def baseEnd_1166826 : Nat := 29587287810526272672043

theorem tailTrace_1166826 : CollatzResearch.WordTrace tailWord_1166826 prefixEnd_1166826 29587287810526272672043 := by
  unfold tailWord_1166826
  simp only [CollatzResearch.WordTrace]
  refine ⟨10639410117699038715144083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28371760313864103240384221 10639410117699038715144083)
  ·
    refine ⟨15959115176548558072716125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10639410117699038715144083 15959115176548558072716125)
    ·
      refine ⟨5984668191205709277268547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15959115176548558072716125 5984668191205709277268547)
      ·
        refine ⟨8977002286808563915902821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5984668191205709277268547 8977002286808563915902821)
        ·
          refine ⟨1683187928776605734231779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8977002286808563915902821 1683187928776605734231779)
          ·
            refine ⟨2524781893164908601347669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683187928776605734231779 2524781893164908601347669)
            ·
              refine ⟨29587287810526272672043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2524781893164908601347669 29587287810526272672043)
              ·
                rfl

theorem cell21_1166826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 8].length) (baseStart_1166826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166826 prefixEnd_1166826 := by exact prefixLift 1166826
  have htrace : WordTrace (prefixWord ++ tailWord_1166826) baseStart_1166826 baseEnd_1166826 := by
    simpa [prefixWord, tailWord_1166826, baseEnd_1166826] using wordTrace_append hprefix tailTrace_1166826
  have hstable : (prefixWord ++ tailWord_1166826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166826).length < 2 ^ (prefixWord ++ tailWord_1166826).sum := by decide
  have hdescent : baseEnd_1166826 < baseStart_1166826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166840 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_1166840 : Nat := 118140960795 + 1166840 * 2 ^ 59
def prefixEnd_1166840 : Nat := 4983230072969 + 3 ^ 40 * 1166840 * 2
def baseEnd_1166840 : Nat := 266288785285475540815025

theorem tailTrace_1166840 : CollatzResearch.WordTrace tailWord_1166840 prefixEnd_1166840 266288785285475540815025 := by
  unfold tailWord_1166840
  simp only [CollatzResearch.WordTrace]
  refine ⟨21279075546372717625792987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28372100728496956834390649 21279075546372717625792987)
  ·
    refine ⟨31918613319559076438689481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21279075546372717625792987 31918613319559076438689481)
    ·
      refine ⟨23938959989669307329017111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31918613319559076438689481 23938959989669307329017111)
      ·
        refine ⟨35908439984503960993525667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23938959989669307329017111 35908439984503960993525667)
        ·
          refine ⟨53862659976755941490288501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35908439984503960993525667 53862659976755941490288501)
          ·
            refine ⟨5049624372820869514714547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53862659976755941490288501 5049624372820869514714547)
            ·
              refine ⟨7574436559231304272071821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049624372820869514714547 7574436559231304272071821)
              ·
                refine ⟨2840413709711739102026933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7574436559231304272071821 2840413709711739102026933)
                ·
                  refine ⟨266288785285475540815025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2840413709711739102026933 266288785285475540815025)
                  ·
                    rfl

theorem cell21_1166840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_1166840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166840 prefixEnd_1166840 := by exact prefixLift 1166840
  have htrace : WordTrace (prefixWord ++ tailWord_1166840) baseStart_1166840 baseEnd_1166840 := by
    simpa [prefixWord, tailWord_1166840, baseEnd_1166840] using wordTrace_append hprefix tailTrace_1166840
  have hstable : (prefixWord ++ tailWord_1166840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166840).length < 2 ^ (prefixWord ++ tailWord_1166840).sum := by decide
  have hdescent : baseEnd_1166840 < baseStart_1166840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166860 : List Nat := [2, 2, 1, 2, 6, 1, 2, 5]
def baseStart_1166860 : Nat := 118140960795 + 1166860 * 2 ^ 59
def prefixEnd_1166860 : Nat := 4983230072969 + 3 ^ 40 * 1166860 * 2
def baseEnd_1166860 : Nat := 88764449852653316827217

theorem tailTrace_1166860 : CollatzResearch.WordTrace tailWord_1166860 prefixEnd_1166860 88764449852653316827217 := by
  unfold tailWord_1166860
  simp only [CollatzResearch.WordTrace]
  refine ⟨21279440276336489333657017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28372587035115319111542689 21279440276336489333657017)
  ·
    refine ⟨15959580207252367000242763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21279440276336489333657017 15959580207252367000242763)
    ·
      refine ⟨23939370310878550500364145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15959580207252367000242763 23939370310878550500364145)
      ·
        refine ⟨17954527733158912875273109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23939370310878550500364145 17954527733158912875273109)
        ·
          refine ⟨841618487491824041028427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17954527733158912875273109 841618487491824041028427)
          ·
            refine ⟨1262427731237736061542641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841618487491824041028427 1262427731237736061542641)
            ·
              refine ⟨946820798428302046156981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1262427731237736061542641 946820798428302046156981)
              ·
                refine ⟨88764449852653316827217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 946820798428302046156981 88764449852653316827217)
                ·
                  rfl

theorem cell21_1166860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 5].length) (baseStart_1166860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166860 prefixEnd_1166860 := by exact prefixLift 1166860
  have htrace : WordTrace (prefixWord ++ tailWord_1166860) baseStart_1166860 baseEnd_1166860 := by
    simpa [prefixWord, tailWord_1166860, baseEnd_1166860] using wordTrace_append hprefix tailTrace_1166860
  have hstable : (prefixWord ++ tailWord_1166860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166860).length < 2 ^ (prefixWord ++ tailWord_1166860).sum := by decide
  have hdescent : baseEnd_1166860 < baseStart_1166860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166905 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 4]
def baseStart_1166905 : Nat := 118140960795 + 1166905 * 2 ^ 59
def prefixEnd_1166905 : Nat := 4983230072969 + 3 ^ 40 * 1166905 * 2
def baseEnd_1166905 : Nat := 266303619171049872231559

theorem tailTrace_1166905 : CollatzResearch.WordTrace tailWord_1166905 prefixEnd_1166905 266303619171049872231559 := by
  unfold tailWord_1166905
  simp only [CollatzResearch.WordTrace]
  refine ⟨42560521837509951352702169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28373681225006634235134779 42560521837509951352702169)
  ·
    refine ⟨31920391378132463514526627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42560521837509951352702169 31920391378132463514526627)
    ·
      refine ⟨47880587067198695271789941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31920391378132463514526627 47880587067198695271789941)
      ·
        refine ⟨4488805037549877681730307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47880587067198695271789941 4488805037549877681730307)
        ·
          refine ⟨6733207556324816522595461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4488805037549877681730307 6733207556324816522595461)
          ·
            refine ⟨1262476416810903097986649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6733207556324816522595461 1262476416810903097986649)
            ·
              refine ⟨946857312608177323489987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1262476416810903097986649 946857312608177323489987)
              ·
                refine ⟨1420285968912265985234981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946857312608177323489987 1420285968912265985234981)
                ·
                  refine ⟨266303619171049872231559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1420285968912265985234981 266303619171049872231559)
                  ·
                    rfl

theorem cell21_1166905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_1166905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166905 prefixEnd_1166905 := by exact prefixLift 1166905
  have htrace : WordTrace (prefixWord ++ tailWord_1166905) baseStart_1166905 baseEnd_1166905 := by
    simpa [prefixWord, tailWord_1166905, baseEnd_1166905] using wordTrace_append hprefix tailTrace_1166905
  have hstable : (prefixWord ++ tailWord_1166905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166905).length < 2 ^ (prefixWord ++ tailWord_1166905).sum := by decide
  have hdescent : baseEnd_1166905 < baseStart_1166905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166933 : List Nat := [1, 3, 2, 2, 1, 1, 1, 7, 3]
def baseStart_1166933 : Nat := 118140960795 + 1166933 * 2 ^ 59
def prefixEnd_1166933 : Nat := 4983230072969 + 3 ^ 40 * 1166933 * 2
def baseEnd_1166933 : Nat := 266310009152528045764835

theorem tailTrace_1166933 : CollatzResearch.WordTrace tailWord_1166933 prefixEnd_1166933 266310009152528045764835 := by
  unfold tailWord_1166933
  simp only [CollatzResearch.WordTrace]
  refine ⟨42561543081408512134721453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28374362054272341423147635 42561543081408512134721453)
  ·
    refine ⟨15960578655528192050520545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42561543081408512134721453 15960578655528192050520545)
    ·
      refine ⟨11970433991646144037890409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15960578655528192050520545 11970433991646144037890409)
      ·
        refine ⟨8977825493734608028417807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11970433991646144037890409 8977825493734608028417807)
        ·
          refine ⟨13466738240601912042626711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8977825493734608028417807 13466738240601912042626711)
          ·
            refine ⟨20200107360902868063940067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13466738240601912042626711 20200107360902868063940067)
            ·
              refine ⟨30300161041354302095910101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20200107360902868063940067 30300161041354302095910101)
              ·
                refine ⟨710160024406741455372893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30300161041354302095910101 710160024406741455372893)
                ·
                  refine ⟨266310009152528045764835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710160024406741455372893 266310009152528045764835)
                  ·
                    rfl

theorem cell21_1166933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_1166933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166933 prefixEnd_1166933 := by exact prefixLift 1166933
  have htrace : WordTrace (prefixWord ++ tailWord_1166933) baseStart_1166933 baseEnd_1166933 := by
    simpa [prefixWord, tailWord_1166933, baseEnd_1166933] using wordTrace_append hprefix tailTrace_1166933
  have hstable : (prefixWord ++ tailWord_1166933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166933).length < 2 ^ (prefixWord ++ tailWord_1166933).sum := by decide
  have hdescent : baseEnd_1166933 < baseStart_1166933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166947 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 4]
def baseStart_1166947 : Nat := 118140960795 + 1166947 * 2 ^ 59
def prefixEnd_1166947 : Nat := 4983230072969 + 3 ^ 40 * 1166947 * 2
def baseEnd_1166947 : Nat := 266313204143267132531473

theorem tailTrace_1166947 : CollatzResearch.WordTrace tailWord_1166947 prefixEnd_1166947 266313204143267132531473 := by
  unfold tailWord_1166947
  simp only [CollatzResearch.WordTrace]
  refine ⟨42562053703357792525731095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28374702468905195017154063 42562053703357792525731095)
  ·
    refine ⟨63843080555036688788596643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42562053703357792525731095 63843080555036688788596643)
    ·
      refine ⟨95764620832555033182894965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63843080555036688788596643 95764620832555033182894965)
      ·
        refine ⟨8977933203052034360896403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95764620832555033182894965 8977933203052034360896403)
        ·
          refine ⟨13466899804578051541344605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8977933203052034360896403 13466899804578051541344605)
          ·
            refine ⟨5050087426716769328004227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13466899804578051541344605 5050087426716769328004227)
            ·
              refine ⟨7575131140075153992006341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5050087426716769328004227 7575131140075153992006341)
              ·
                refine ⟨1420337088764091373501189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7575131140075153992006341 1420337088764091373501189)
                ·
                  refine ⟨266313204143267132531473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1420337088764091373501189 266313204143267132531473)
                  ·
                    rfl

theorem cell21_1166947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 4].length) (baseStart_1166947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166947 prefixEnd_1166947 := by exact prefixLift 1166947
  have htrace : WordTrace (prefixWord ++ tailWord_1166947) baseStart_1166947 baseEnd_1166947 := by
    simpa [prefixWord, tailWord_1166947, baseEnd_1166947] using wordTrace_append hprefix tailTrace_1166947
  have hstable : (prefixWord ++ tailWord_1166947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166947).length < 2 ^ (prefixWord ++ tailWord_1166947).sum := by decide
  have hdescent : baseEnd_1166947 < baseStart_1166947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167009 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 5]
def baseStart_1167009 : Nat := 118140960795 + 1167009 * 2 ^ 59
def prefixEnd_1167009 : Nat := 4983230072969 + 3 ^ 40 * 1167009 * 2
def baseEnd_1167009 : Nat := 266327353387968802498013

theorem tailTrace_1167009 : CollatzResearch.WordTrace tailWord_1167009 prefixEnd_1167009 266327353387968802498013 := by
  unfold tailWord_1167009
  simp only [CollatzResearch.WordTrace]
  refine ⟨42564315029133177114488081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28376210019422118076325387 42564315029133177114488081)
  ·
    refine ⟨31923236271849882835866061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42564315029133177114488081 31923236271849882835866061)
    ·
      refine ⟨11971213601943706063449773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31923236271849882835866061 11971213601943706063449773)
      ·
        refine ⟨4489205100728889773793665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11971213601943706063449773 4489205100728889773793665)
        ·
          refine ⟨3366903825546667330345249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4489205100728889773793665 3366903825546667330345249)
          ·
            refine ⟨2525177869160000497758937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3366903825546667330345249 2525177869160000497758937)
            ·
              refine ⟨1893883401870000373319203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2525177869160000497758937 1893883401870000373319203)
              ·
                refine ⟨2840825102805000559978805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1893883401870000373319203 2840825102805000559978805)
                ·
                  refine ⟨266327353387968802498013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2840825102805000559978805 266327353387968802498013)
                  ·
                    rfl

theorem cell21_1167009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_1167009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167009 prefixEnd_1167009 := by exact prefixLift 1167009
  have htrace : WordTrace (prefixWord ++ tailWord_1167009) baseStart_1167009 baseEnd_1167009 := by
    simpa [prefixWord, tailWord_1167009, baseEnd_1167009] using wordTrace_append hprefix tailTrace_1167009
  have hstable : (prefixWord ++ tailWord_1167009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167009).length < 2 ^ (prefixWord ++ tailWord_1167009).sum := by decide
  have hdescent : baseEnd_1167009 < baseStart_1167009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167037 : List Nat := [1, 4, 1, 2, 1, 2, 3, 7]
def baseStart_1167037 : Nat := 118140960795 + 1167037 * 2 ^ 59
def prefixEnd_1167037 : Nat := 4983230072969 + 3 ^ 40 * 1167037 * 2
def baseEnd_1167037 : Nat := 88777914456482325343763

theorem tailTrace_1167037 : CollatzResearch.WordTrace tailWord_1167037 prefixEnd_1167037 88777914456482325343763 := by
  unfold tailWord_1167037
  simp only [CollatzResearch.WordTrace]
  refine ⟨42565336273031737896507365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28376890848687825264338243 42565336273031737896507365)
  ·
    refine ⟨7981000551193450855595131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42565336273031737896507365 7981000551193450855595131)
    ·
      refine ⟨11971500826790176283392697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7981000551193450855595131 11971500826790176283392697)
      ·
        refine ⟨8978625620092632212544523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11971500826790176283392697 8978625620092632212544523)
        ·
          refine ⟨13467938430138948318816785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8978625620092632212544523 13467938430138948318816785)
          ·
            refine ⟨10100953822604211239112589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13467938430138948318816785 10100953822604211239112589)
            ·
              refine ⟨3787857683476579214667221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10100953822604211239112589 3787857683476579214667221)
              ·
                refine ⟨88777914456482325343763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3787857683476579214667221 88777914456482325343763)
                ·
                  rfl

theorem cell21_1167037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 7].length) (baseStart_1167037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167037 prefixEnd_1167037 := by exact prefixLift 1167037
  have htrace : WordTrace (prefixWord ++ tailWord_1167037) baseStart_1167037 baseEnd_1167037 := by
    simpa [prefixWord, tailWord_1167037, baseEnd_1167037] using wordTrace_append hprefix tailTrace_1167037
  have hstable : (prefixWord ++ tailWord_1167037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167037).length < 2 ^ (prefixWord ++ tailWord_1167037).sum := by decide
  have hdescent : baseEnd_1167037 < baseStart_1167037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167051 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 7]
def baseStart_1167051 : Nat := 118140960795 + 1167051 * 2 ^ 59
def prefixEnd_1167051 : Nat := 4983230072969 + 3 ^ 40 * 1167051 * 2
def baseEnd_1167051 : Nat := 266336938360186062797927

theorem tailTrace_1167051 : CollatzResearch.WordTrace tailWord_1167051 prefixEnd_1167051 266336938360186062797927 := by
  unfold tailWord_1167051
  simp only [CollatzResearch.WordTrace]
  refine ⟨42565846894981018287517007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28377231263320678858344671 42565846894981018287517007)
  ·
    refine ⟨63848770342471527431275511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42565846894981018287517007 63848770342471527431275511)
    ·
      refine ⟨95773155513707291146913267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63848770342471527431275511 95773155513707291146913267)
      ·
        refine ⟨143659733270560936720369901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95773155513707291146913267 143659733270560936720369901)
        ·
          refine ⟨53872399976460351270138713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143659733270560936720369901 53872399976460351270138713)
          ·
            refine ⟨40404299982345263452604035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53872399976460351270138713 40404299982345263452604035)
            ·
              refine ⟨60606449973517895178906053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40404299982345263452604035 60606449973517895178906053)
              ·
                refine ⟨11363709370034605346044885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60606449973517895178906053 11363709370034605346044885)
                ·
                  refine ⟨266336938360186062797927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11363709370034605346044885 266336938360186062797927)
                  ·
                    rfl

theorem cell21_1167051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_1167051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167051 prefixEnd_1167051 := by exact prefixLift 1167051
  have htrace : WordTrace (prefixWord ++ tailWord_1167051) baseStart_1167051 baseEnd_1167051 := by
    simpa [prefixWord, tailWord_1167051, baseEnd_1167051] using wordTrace_append hprefix tailTrace_1167051
  have hstable : (prefixWord ++ tailWord_1167051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167051).length < 2 ^ (prefixWord ++ tailWord_1167051).sum := by decide
  have hdescent : baseEnd_1167051 < baseStart_1167051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167130 : List Nat := [3, 1, 1, 3, 2, 4, 1, 6]
def baseStart_1167130 : Nat := 118140960795 + 1167130 * 2 ^ 59
def prefixEnd_1167130 : Nat := 4983230072969 + 3 ^ 40 * 1167130 * 2
def baseEnd_1167130 : Nat := 88784989078833160327033

theorem tailTrace_1167130 : CollatzResearch.WordTrace tailWord_1167130 prefixEnd_1167130 88784989078833160327033 := by
  unfold tailWord_1167130
  simp only [CollatzResearch.WordTrace]
  refine ⟨10642182065423703694910711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28379152174463209853095229 10642182065423703694910711)
  ·
    refine ⟨15963273098135555542366067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10642182065423703694910711 15963273098135555542366067)
    ·
      refine ⟨23944909647203333313549101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15963273098135555542366067 23944909647203333313549101)
      ·
        refine ⟨8979341117701249992580913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23944909647203333313549101 8979341117701249992580913)
        ·
          refine ⟨6734505838275937494435685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8979341117701249992580913 6734505838275937494435685)
          ·
            refine ⟨1262719844676738280206691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6734505838275937494435685 1262719844676738280206691)
            ·
              refine ⟨1894079767015107420310037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262719844676738280206691 1894079767015107420310037)
              ·
                refine ⟨88784989078833160327033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1894079767015107420310037 88784989078833160327033)
                ·
                  rfl

theorem cell21_1167130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_1167130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167130 prefixEnd_1167130 := by exact prefixLift 1167130
  have htrace : WordTrace (prefixWord ++ tailWord_1167130) baseStart_1167130 baseEnd_1167130 := by
    simpa [prefixWord, tailWord_1167130, baseEnd_1167130] using wordTrace_append hprefix tailTrace_1167130
  have hstable : (prefixWord ++ tailWord_1167130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167130).length < 2 ^ (prefixWord ++ tailWord_1167130).sum := by decide
  have hdescent : baseEnd_1167130 < baseStart_1167130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167144 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_1167144 : Nat := 118140960795 + 1167144 * 2 ^ 59
def prefixEnd_1167144 : Nat := 4983230072969 + 3 ^ 40 * 1167144 * 2
def baseEnd_1167144 : Nat := 266358162227238567747737

theorem tailTrace_1167144 : CollatzResearch.WordTrace tailWord_1167144 prefixEnd_1167144 266358162227238567747737 := by
  unfold tailWord_1167144
  simp only [CollatzResearch.WordTrace]
  refine ⟨21284619441822047585326243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28379492589096063447101657 21284619441822047585326243)
  ·
    refine ⟨31926929162733071377989365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21284619441822047585326243 31926929162733071377989365)
    ·
      refine ⟨2993149609006225441686503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31926929162733071377989365 2993149609006225441686503)
      ·
        refine ⟨4489724413509338162529755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2993149609006225441686503 4489724413509338162529755)
        ·
          refine ⟨6734586620264007243794633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4489724413509338162529755 6734586620264007243794633)
          ·
            refine ⟨5050939965198005432845975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6734586620264007243794633 5050939965198005432845975)
            ·
              refine ⟨7576409947797008149268963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5050939965198005432845975 7576409947797008149268963)
              ·
                refine ⟨11364614921695512223903445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7576409947797008149268963 11364614921695512223903445)
                ·
                  refine ⟨266358162227238567747737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11364614921695512223903445 266358162227238567747737)
                  ·
                    rfl

theorem cell21_1167144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_1167144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167144 prefixEnd_1167144 := by exact prefixLift 1167144
  have htrace : WordTrace (prefixWord ++ tailWord_1167144) baseStart_1167144 baseEnd_1167144 := by
    simpa [prefixWord, tailWord_1167144, baseEnd_1167144] using wordTrace_append hprefix tailTrace_1167144
  have hstable : (prefixWord ++ tailWord_1167144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167144).length < 2 ^ (prefixWord ++ tailWord_1167144).sum := by decide
  have hdescent : baseEnd_1167144 < baseStart_1167144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167175 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 4]
def baseStart_1167175 : Nat := 118140960795 + 1167175 * 2 ^ 59
def prefixEnd_1167175 : Nat := 4983230072969 + 3 ^ 40 * 1167175 * 2
def baseEnd_1167175 : Nat := 266365236849589402731007

theorem tailTrace_1167175 : CollatzResearch.WordTrace tailWord_1167175 prefixEnd_1167175 266365236849589402731007 := by
  unfold tailWord_1167175
  simp only [CollatzResearch.WordTrace]
  refine ⟨42570369546531787465030979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28380246364354524976687319 42570369546531787465030979)
  ·
    refine ⟨63855554319797681197546469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42570369546531787465030979 63855554319797681197546469)
    ·
      refine ⟨11972916434962065224539963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63855554319797681197546469 11972916434962065224539963)
      ·
        refine ⟨17959374652443097836809945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11972916434962065224539963 17959374652443097836809945)
        ·
          refine ⟨13469530989332323377607459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17959374652443097836809945 13469530989332323377607459)
          ·
            refine ⟨20204296483998485066411189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13469530989332323377607459 20204296483998485066411189)
            ·
              refine ⟨1894152795374857974976049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20204296483998485066411189 1894152795374857974976049)
              ·
                refine ⟨1420614596531143481232037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1894152795374857974976049 1420614596531143481232037)
                ·
                  refine ⟨266365236849589402731007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1420614596531143481232037 266365236849589402731007)
                  ·
                    rfl

theorem cell21_1167175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 4].length) (baseStart_1167175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167175 prefixEnd_1167175 := by exact prefixLift 1167175
  have htrace : WordTrace (prefixWord ++ tailWord_1167175) baseStart_1167175 baseEnd_1167175 := by
    simpa [prefixWord, tailWord_1167175, baseEnd_1167175] using wordTrace_append hprefix tailTrace_1167175
  have hstable : (prefixWord ++ tailWord_1167175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167175).length < 2 ^ (prefixWord ++ tailWord_1167175).sum := by decide
  have hdescent : baseEnd_1167175 < baseStart_1167175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167248 : List Nat := [2, 1, 1, 1, 1, 1, 2, 12]
def baseStart_1167248 : Nat := 118140960795 + 1167248 * 2 ^ 59
def prefixEnd_1167248 : Nat := 4983230072969 + 3 ^ 40 * 1167248 * 2
def baseEnd_1167248 : Nat := 88793965481385832671397

theorem tailTrace_1167248 : CollatzResearch.WordTrace tailWord_1167248 prefixEnd_1167248 88793965481385832671397 := by
  unfold tailWord_1167248
  simp only [CollatzResearch.WordTrace]
  refine ⟨21286516037633660466219199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28382021383511547288292265 21286516037633660466219199)
  ·
    refine ⟨31929774056450490699328799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21286516037633660466219199 31929774056450490699328799)
    ·
      refine ⟨47894661084675736048993199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31929774056450490699328799 47894661084675736048993199)
      ·
        refine ⟨71841991627013604073489799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47894661084675736048993199 71841991627013604073489799)
        ·
          refine ⟨107762987440520406110234699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71841991627013604073489799 107762987440520406110234699)
          ·
            refine ⟨161644481160780609165352049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107762987440520406110234699 161644481160780609165352049)
            ·
              refine ⟨121233360870585456874014037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161644481160780609165352049 121233360870585456874014037)
              ·
                refine ⟨88793965481385832671397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 121233360870585456874014037 88793965481385832671397)
                ·
                  rfl

theorem cell21_1167248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_1167248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167248 prefixEnd_1167248 := by exact prefixLift 1167248
  have htrace : WordTrace (prefixWord ++ tailWord_1167248) baseStart_1167248 baseEnd_1167248 := by
    simpa [prefixWord, tailWord_1167248, baseEnd_1167248] using wordTrace_append hprefix tailTrace_1167248
  have hstable : (prefixWord ++ tailWord_1167248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167248).length < 2 ^ (prefixWord ++ tailWord_1167248).sum := by decide
  have hdescent : baseEnd_1167248 < baseStart_1167248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167355 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 5]
def baseStart_1167355 : Nat := 118140960795 + 1167355 * 2 ^ 59
def prefixEnd_1167355 : Nat := 4983230072969 + 3 ^ 40 * 1167355 * 2
def baseEnd_1167355 : Nat := 266406315301949089730639

theorem tailTrace_1167355 : CollatzResearch.WordTrace tailWord_1167355 prefixEnd_1167355 266406315301949089730639 := by
  unfold tailWord_1167355
  simp only [CollatzResearch.WordTrace]
  refine ⟨42576934685879678206583519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28384623123919785471055679 42576934685879678206583519)
  ·
    refine ⟨63865402028819517309875279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42576934685879678206583519 63865402028819517309875279)
    ·
      refine ⟨95798103043229275964812919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63865402028819517309875279 95798103043229275964812919)
      ·
        refine ⟨143697154564843913947219379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95798103043229275964812919 143697154564843913947219379)
        ·
          refine ⟨215545731847265870920829069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143697154564843913947219379 215545731847265870920829069)
          ·
            refine ⟨80829649442724701595310901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215545731847265870920829069 80829649442724701595310901)
            ·
              refine ⟨7577779635255440774560397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80829649442724701595310901 7577779635255440774560397)
              ·
                refine ⟨2841667363220790290460149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7577779635255440774560397 2841667363220790290460149)
                ·
                  refine ⟨266406315301949089730639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2841667363220790290460149 266406315301949089730639)
                  ·
                    rfl

theorem cell21_1167355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_1167355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167355 prefixEnd_1167355 := by exact prefixLift 1167355
  have htrace : WordTrace (prefixWord ++ tailWord_1167355) baseStart_1167355 baseEnd_1167355 := by
    simpa [prefixWord, tailWord_1167355, baseEnd_1167355] using wordTrace_append hprefix tailTrace_1167355
  have hstable : (prefixWord ++ tailWord_1167355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167355).length < 2 ^ (prefixWord ++ tailWord_1167355).sum := by decide
  have hdescent : baseEnd_1167355 < baseStart_1167355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167386 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_1167386 : Nat := 118140960795 + 1167386 * 2 ^ 59
def prefixEnd_1167386 : Nat := 4983230072969 + 3 ^ 40 * 1167386 * 2
def baseEnd_1167386 : Nat := 266413389924299924713909

theorem tailTrace_1167386 : CollatzResearch.WordTrace tailWord_1167386 prefixEnd_1167386 266413389924299924713909 := by
  unfold tailWord_1167386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10644516337191842625240503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28385376899178247000641341 10644516337191842625240503)
  ·
    refine ⟨15966774505787763937860755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10644516337191842625240503 15966774505787763937860755)
    ·
      refine ⟨23950161758681645906791133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15966774505787763937860755 23950161758681645906791133)
      ·
        refine ⟨8981310659505617215046675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23950161758681645906791133 8981310659505617215046675)
        ·
          refine ⟨13471965989258425822570013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8981310659505617215046675 13471965989258425822570013)
          ·
            refine ⟨5051987245971909683463755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13471965989258425822570013 5051987245971909683463755)
            ·
              refine ⟨7577980868957864525195633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5051987245971909683463755 7577980868957864525195633)
              ·
                refine ⟨5683485651718398393896725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7577980868957864525195633 5683485651718398393896725)
                ·
                  refine ⟨266413389924299924713909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5683485651718398393896725 266413389924299924713909)
                  ·
                    rfl

theorem cell21_1167386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_1167386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167386 prefixEnd_1167386 := by exact prefixLift 1167386
  have htrace : WordTrace (prefixWord ++ tailWord_1167386) baseStart_1167386 baseEnd_1167386 := by
    simpa [prefixWord, tailWord_1167386, baseEnd_1167386] using wordTrace_append hprefix tailTrace_1167386
  have hstable : (prefixWord ++ tailWord_1167386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167386).length < 2 ^ (prefixWord ++ tailWord_1167386).sum := by decide
  have hdescent : baseEnd_1167386 < baseStart_1167386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167431 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 7]
def baseStart_1167431 : Nat := 118140960795 + 1167431 * 2 ^ 59
def prefixEnd_1167431 : Nat := 4983230072969 + 3 ^ 40 * 1167431 * 2
def baseEnd_1167431 : Nat := 266423659537389846463817

theorem tailTrace_1167431 : CollatzResearch.WordTrace tailWord_1167431 prefixEnd_1167431 266423659537389846463817 := by
  unfold tailWord_1167431
  simp only [CollatzResearch.WordTrace]
  refine ⟨42579706633604343186350147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28386471089069562124233431 42579706633604343186350147)
  ·
    refine ⟨63869559950406514779525221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42579706633604343186350147 63869559950406514779525221)
    ·
      refine ⟨11975542490701221521160979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63869559950406514779525221 11975542490701221521160979)
      ·
        refine ⟨17963313736051832281741469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11975542490701221521160979 17963313736051832281741469)
        ·
          refine ⟨6736242651019437105653051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17963313736051832281741469 6736242651019437105653051)
          ·
            refine ⟨10104363976529155658479577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736242651019437105653051 10104363976529155658479577)
            ·
              refine ⟨7578272982396866743859683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10104363976529155658479577 7578272982396866743859683)
              ·
                refine ⟨11367409473595300115789525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7578272982396866743859683 11367409473595300115789525)
                ·
                  refine ⟨266423659537389846463817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11367409473595300115789525 266423659537389846463817)
                  ·
                    rfl

theorem cell21_1167431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_1167431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167431 prefixEnd_1167431 := by exact prefixLift 1167431
  have htrace : WordTrace (prefixWord ++ tailWord_1167431) baseStart_1167431 baseEnd_1167431 := by
    simpa [prefixWord, tailWord_1167431, baseEnd_1167431] using wordTrace_append hprefix tailTrace_1167431
  have hstable : (prefixWord ++ tailWord_1167431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167431).length < 2 ^ (prefixWord ++ tailWord_1167431).sum := by decide
  have hdescent : baseEnd_1167431 < baseStart_1167431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167454 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1167454 : Nat := 118140960795 + 1167454 * 2 ^ 59
def prefixEnd_1167454 : Nat := 4983230072969 + 3 ^ 40 * 1167454 * 2
def baseEnd_1167454 : Nat := 266428908450746917580437

theorem tailTrace_1167454 : CollatzResearch.WordTrace tailWord_1167454 prefixEnd_1167454 266428908450746917580437 := by
  unfold tailWord_1167454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322568189065127264304677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28387030341680678742958277 5322568189065127264304677)
  ·
    refine ⟨997981535449711362057127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5322568189065127264304677 997981535449711362057127)
    ·
      refine ⟨1496972303174567043085691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 997981535449711362057127 1496972303174567043085691)
      ·
        refine ⟨2245458454761850564628537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1496972303174567043085691 2245458454761850564628537)
        ·
          refine ⟨1684093841071387923471403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2245458454761850564628537 1684093841071387923471403)
          ·
            refine ⟨2526140761607081885207105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684093841071387923471403 2526140761607081885207105)
            ·
              refine ⟨1894605571205311413905329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2526140761607081885207105 1894605571205311413905329)
              ·
                refine ⟨1420954178403983560428997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1894605571205311413905329 1420954178403983560428997)
                ·
                  refine ⟨266428908450746917580437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1420954178403983560428997 266428908450746917580437)
                  ·
                    rfl

theorem cell21_1167454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1167454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167454 prefixEnd_1167454 := by exact prefixLift 1167454
  have htrace : WordTrace (prefixWord ++ tailWord_1167454) baseStart_1167454 baseEnd_1167454 := by
    simpa [prefixWord, tailWord_1167454, baseEnd_1167454] using wordTrace_append hprefix tailTrace_1167454
  have hstable : (prefixWord ++ tailWord_1167454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167454).length < 2 ^ (prefixWord ++ tailWord_1167454).sum := by decide
  have hdescent : baseEnd_1167454 < baseStart_1167454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167780 : List Nat := [2, 3, 1, 2, 1, 1, 4, 7]
def baseStart_1167780 : Nat := 118140960795 + 1167780 * 2 ^ 59
def prefixEnd_1167780 : Nat := 4983230072969 + 3 ^ 40 * 1167780 * 2
def baseEnd_1167780 : Nat := 88834435364080931715479

theorem tailTrace_1167780 : CollatzResearch.WordTrace tailWord_1167780 prefixEnd_1167780 88834435364080931715479 := by
  unfold tailWord_1167780
  simp only [CollatzResearch.WordTrace]
  refine ⟨21296217854669987895402397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28394957139559983860536529 21296217854669987895402397)
  ·
    refine ⟨7986081695501245460775899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21296217854669987895402397 7986081695501245460775899)
    ·
      refine ⟨11979122543251868191163849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7986081695501245460775899 11979122543251868191163849)
      ·
        refine ⟨8984341907438901143372887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11979122543251868191163849 8984341907438901143372887)
        ·
          refine ⟨13476512861158351715059331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8984341907438901143372887 13476512861158351715059331)
          ·
            refine ⟨20214769291737527572588997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13476512861158351715059331 20214769291737527572588997)
            ·
              refine ⟨3790269242200786419860437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20214769291737527572588997 3790269242200786419860437)
              ·
                refine ⟨88834435364080931715479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3790269242200786419860437 88834435364080931715479)
                ·
                  rfl

theorem cell21_1167780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_1167780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167780 prefixEnd_1167780 := by exact prefixLift 1167780
  have htrace : WordTrace (prefixWord ++ tailWord_1167780) baseStart_1167780 baseEnd_1167780 := by
    simpa [prefixWord, tailWord_1167780, baseEnd_1167780] using wordTrace_append hprefix tailTrace_1167780
  have hstable : (prefixWord ++ tailWord_1167780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167780).length < 2 ^ (prefixWord ++ tailWord_1167780).sum := by decide
  have hdescent : baseEnd_1167780 < baseStart_1167780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167797 : List Nat := [1, 3, 3, 2, 4, 8]
def baseStart_1167797 : Nat := 118140960795 + 1167797 * 2 ^ 59
def prefixEnd_1167797 : Nat := 4983230072969 + 3 ^ 40 * 1167797 * 2
def baseEnd_1167797 : Nat := 9870636508290909013447

theorem tailTrace_1167797 : CollatzResearch.WordTrace tailWord_1167797 prefixEnd_1167797 9870636508290909013447 := by
  unfold tailWord_1167797
  simp only [CollatzResearch.WordTrace]
  refine ⟨42593055750278387694173645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28395370500185591796115763 42593055750278387694173645)
  ·
    refine ⟨15972395906354395385315117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42593055750278387694173645 15972395906354395385315117)
    ·
      refine ⟨5989648464882898269493169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15972395906354395385315117 5989648464882898269493169)
      ·
        refine ⟨4492236348662173702119877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5989648464882898269493169 4492236348662173702119877)
        ·
          refine ⟨842294315374157569147477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4492236348662173702119877 842294315374157569147477)
          ·
            refine ⟨9870636508290909013447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 842294315374157569147477 9870636508290909013447)
            ·
              rfl

theorem cell21_1167797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 8].length) (baseStart_1167797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167797 prefixEnd_1167797 := by exact prefixLift 1167797
  have htrace : WordTrace (prefixWord ++ tailWord_1167797) baseStart_1167797 baseEnd_1167797 := by
    simpa [prefixWord, tailWord_1167797, baseEnd_1167797] using wordTrace_append hprefix tailTrace_1167797
  have hstable : (prefixWord ++ tailWord_1167797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167797).length < 2 ^ (prefixWord ++ tailWord_1167797).sum := by decide
  have hdescent : baseEnd_1167797 < baseStart_1167797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167828 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1167828 : Nat := 118140960795 + 1167828 * 2 ^ 59
def prefixEnd_1167828 : Nat := 4983230072969 + 3 ^ 40 * 1167828 * 2
def baseEnd_1167828 : Nat := 266514260346205378346339

theorem tailTrace_1167828 : CollatzResearch.WordTrace tailWord_1167828 prefixEnd_1167828 266514260346205378346339 := by
  unfold tailWord_1167828
  simp only [CollatzResearch.WordTrace]
  refine ⟨21297093206583039994276069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28396124275444053325701425 21297093206583039994276069)
  ·
    refine ⟨3993204976234319998926763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21297093206583039994276069 3993204976234319998926763)
    ·
      refine ⟨5989807464351479998390145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3993204976234319998926763 5989807464351479998390145)
      ·
        refine ⟨4492355598263609998792609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5989807464351479998390145 4492355598263609998792609)
        ·
          refine ⟨3369266698697707499094457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4492355598263609998792609 3369266698697707499094457)
          ·
            refine ⟨2526950024023280624320843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3369266698697707499094457 2526950024023280624320843)
            ·
              refine ⟨3790425036034920936481265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526950024023280624320843 3790425036034920936481265)
              ·
                refine ⟨2842818777026190702360949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3790425036034920936481265 2842818777026190702360949)
                ·
                  refine ⟨266514260346205378346339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2842818777026190702360949 266514260346205378346339)
                  ·
                    rfl

theorem cell21_1167828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1167828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167828 prefixEnd_1167828 := by exact prefixLift 1167828
  have htrace : WordTrace (prefixWord ++ tailWord_1167828) baseStart_1167828 baseEnd_1167828 := by
    simpa [prefixWord, tailWord_1167828, baseEnd_1167828] using wordTrace_append hprefix tailTrace_1167828
  have hstable : (prefixWord ++ tailWord_1167828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167828).length < 2 ^ (prefixWord ++ tailWord_1167828).sum := by decide
  have hdescent : baseEnd_1167828 < baseStart_1167828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167876 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 4]
def baseStart_1167876 : Nat := 118140960795 + 1167876 * 2 ^ 59
def prefixEnd_1167876 : Nat := 4983230072969 + 3 ^ 40 * 1167876 * 2
def baseEnd_1167876 : Nat := 266525214600167961546241

theorem tailTrace_1167876 : CollatzResearch.WordTrace tailWord_1167876 prefixEnd_1167876 266525214600167961546241 := by
  unfold tailWord_1167876
  simp only [CollatzResearch.WordTrace]
  refine ⟨21297968558496092093149741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28397291411328122790866321 21297968558496092093149741)
  ·
    refine ⟨7986738209436034534931153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21297968558496092093149741 7986738209436034534931153)
    ·
      refine ⟨5990053657077025901198365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7986738209436034534931153 5990053657077025901198365)
      ·
        refine ⟨2246270121403884712949387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5990053657077025901198365 2246270121403884712949387)
        ·
          refine ⟨3369405182105827069424081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2246270121403884712949387 3369405182105827069424081)
          ·
            refine ⟨2527053886579370302068061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3369405182105827069424081 2527053886579370302068061)
            ·
              refine ⟨947645207467263863275523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2527053886579370302068061 947645207467263863275523)
              ·
                refine ⟨1421467811200895794913285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947645207467263863275523 1421467811200895794913285)
                ·
                  refine ⟨266525214600167961546241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1421467811200895794913285 266525214600167961546241)
                  ·
                    rfl

theorem cell21_1167876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_1167876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167876 prefixEnd_1167876 := by exact prefixLift 1167876
  have htrace : WordTrace (prefixWord ++ tailWord_1167876) baseStart_1167876 baseEnd_1167876 := by
    simpa [prefixWord, tailWord_1167876, baseEnd_1167876] using wordTrace_append hprefix tailTrace_1167876
  have hstable : (prefixWord ++ tailWord_1167876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167876).length < 2 ^ (prefixWord ++ tailWord_1167876).sum := by decide
  have hdescent : baseEnd_1167876 < baseStart_1167876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167932 : List Nat := [2, 2, 2, 2, 3, 1, 1, 8]
def baseStart_1167932 : Nat := 118140960795 + 1167932 * 2 ^ 59
def prefixEnd_1167932 : Nat := 4983230072969 + 3 ^ 40 * 1167932 * 2
def baseEnd_1167932 : Nat := 88845998187708102870931

theorem tailTrace_1167932 : CollatzResearch.WordTrace tailWord_1167932 prefixEnd_1167932 88845998187708102870931 := by
  unfold tailWord_1167932
  simp only [CollatzResearch.WordTrace]
  refine ⟨21298989802394652875169025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28398653069859537166892033 21298989802394652875169025)
  ·
    refine ⟨15974242351795989656376769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21298989802394652875169025 15974242351795989656376769)
    ·
      refine ⟨11980681763846992242282577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15974242351795989656376769 11980681763846992242282577)
      ·
        refine ⟨8985511322885244181711933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11980681763846992242282577 8985511322885244181711933)
        ·
          refine ⟨3369566746081966568141975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8985511322885244181711933 3369566746081966568141975)
          ·
            refine ⟨5054350119122949852212963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3369566746081966568141975 5054350119122949852212963)
            ·
              refine ⟨7581525178684424778319445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054350119122949852212963 7581525178684424778319445)
              ·
                refine ⟨88845998187708102870931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7581525178684424778319445 88845998187708102870931)
                ·
                  rfl

theorem cell21_1167932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_1167932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167932 prefixEnd_1167932 := by exact prefixLift 1167932
  have htrace : WordTrace (prefixWord ++ tailWord_1167932) baseStart_1167932 baseEnd_1167932 := by
    simpa [prefixWord, tailWord_1167932, baseEnd_1167932] using wordTrace_append hprefix tailTrace_1167932
  have hstable : (prefixWord ++ tailWord_1167932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167932).length < 2 ^ (prefixWord ++ tailWord_1167932).sum := by decide
  have hdescent : baseEnd_1167932 < baseStart_1167932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167949 : List Nat := [1, 6, 1, 1, 2, 1, 2, 7]
def baseStart_1167949 : Nat := 118140960795 + 1167949 * 2 ^ 59
def prefixEnd_1167949 : Nat := 4983230072969 + 3 ^ 40 * 1167949 * 2
def baseEnd_1167949 : Nat := 88847291398245352276475

theorem tailTrace_1167949 : CollatzResearch.WordTrace tailWord_1167949 prefixEnd_1167949 88847291398245352276475 := by
  unfold tailWord_1167949
  simp only [CollatzResearch.WordTrace]
  refine ⟨42598599645727717653706901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28399066430485145102471267 42598599645727717653706901)
  ·
    refine ⟨1996809358393486765017511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42598599645727717653706901 1996809358393486765017511)
    ·
      refine ⟨2995214037590230147526267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1996809358393486765017511 2995214037590230147526267)
      ·
        refine ⟨4492821056385345221289401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2995214037590230147526267 4492821056385345221289401)
        ·
          refine ⟨3369615792289008915967051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4492821056385345221289401 3369615792289008915967051)
          ·
            refine ⟨5054423688433513373950577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3369615792289008915967051 5054423688433513373950577)
            ·
              refine ⟨3790817766325135030462933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5054423688433513373950577 3790817766325135030462933)
              ·
                refine ⟨88847291398245352276475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3790817766325135030462933 88847291398245352276475)
                ·
                  rfl

theorem cell21_1167949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 7].length) (baseStart_1167949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167949 prefixEnd_1167949 := by exact prefixLift 1167949
  have htrace : WordTrace (prefixWord ++ tailWord_1167949) baseStart_1167949 baseEnd_1167949 := by
    simpa [prefixWord, tailWord_1167949, baseEnd_1167949] using wordTrace_append hprefix tailTrace_1167949
  have hstable : (prefixWord ++ tailWord_1167949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167949).length < 2 ^ (prefixWord ++ tailWord_1167949).sum := by decide
  have hdescent : baseEnd_1167949 < baseStart_1167949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167966 : List Nat := [4, 4, 1, 2, 10]
def baseStart_1167966 : Nat := 118140960795 + 1167966 * 2 ^ 59
def prefixEnd_1167966 : Nat := 4983230072969 + 3 ^ 40 * 1167966 * 2
def baseEnd_1167966 : Nat := 3290688318843800062297

theorem tailTrace_1167966 : CollatzResearch.WordTrace tailWord_1167966 prefixEnd_1167966 3290688318843800062297 := by
  unfold tailWord_1167966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324902460833266194634469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28399479791110753038050501 5324902460833266194634469)
  ·
    refine ⟨998419211406237411493963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5324902460833266194634469 998419211406237411493963)
    ·
      refine ⟨1497628817109356117240945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 998419211406237411493963 1497628817109356117240945)
      ·
        refine ⟨1123221612832017087930709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1497628817109356117240945 1123221612832017087930709)
        ·
          refine ⟨3290688318843800062297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1123221612832017087930709 3290688318843800062297)
          ·
            rfl

theorem cell21_1167966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 10].length) (baseStart_1167966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1167966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1167966 prefixEnd_1167966 := by exact prefixLift 1167966
  have htrace : WordTrace (prefixWord ++ tailWord_1167966) baseStart_1167966 baseEnd_1167966 := by
    simpa [prefixWord, tailWord_1167966, baseEnd_1167966] using wordTrace_append hprefix tailTrace_1167966
  have hstable : (prefixWord ++ tailWord_1167966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167966).length < 2 ^ (prefixWord ++ tailWord_1167966).sum := by decide
  have hdescent : baseEnd_1167966 < baseStart_1167966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168104 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 4]
def baseStart_1168104 : Nat := 118140960795 + 1168104 * 2 ^ 59
def prefixEnd_1168104 : Nat := 4983230072969 + 3 ^ 40 * 1168104 * 2
def baseEnd_1168104 : Nat := 266577247306490231745775

theorem tailTrace_1168104 : CollatzResearch.WordTrace tailWord_1168104 prefixEnd_1168104 266577247306490231745775 := by
  unfold tailWord_1168104
  simp only [CollatzResearch.WordTrace]
  refine ⟨21302126480083089562799683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28402835306777452750399577 21302126480083089562799683)
  ·
    refine ⟨31953189720124634344199525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21302126480083089562799683 31953189720124634344199525)
    ·
      refine ⟨5991223072523368939537411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31953189720124634344199525 5991223072523368939537411)
      ·
        refine ⟨8986834608785053409306117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5991223072523368939537411 8986834608785053409306117)
        ·
          refine ⟨1685031489147197514244897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8986834608785053409306117 1685031489147197514244897)
          ·
            refine ⟨1263773616860398135683673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1685031489147197514244897 1263773616860398135683673)
            ·
              refine ⟨947830212645298601762755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263773616860398135683673 947830212645298601762755)
              ·
                refine ⟨1421745318967947902644133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947830212645298601762755 1421745318967947902644133)
                ·
                  refine ⟨266577247306490231745775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1421745318967947902644133 266577247306490231745775)
                  ·
                    rfl

theorem cell21_1168104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_1168104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168104 prefixEnd_1168104 := by exact prefixLift 1168104
  have htrace : WordTrace (prefixWord ++ tailWord_1168104) baseStart_1168104 baseEnd_1168104 := by
    simpa [prefixWord, tailWord_1168104, baseEnd_1168104] using wordTrace_append hprefix tailTrace_1168104
  have hstable : (prefixWord ++ tailWord_1168104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168104).length < 2 ^ (prefixWord ++ tailWord_1168104).sum := by decide
  have hdescent : baseEnd_1168104 < baseStart_1168104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168132 : List Nat := [2, 3, 2, 2, 1, 1, 2, 5, 3]
def baseStart_1168132 : Nat := 118140960795 + 1168132 * 2 ^ 59
def prefixEnd_1168132 : Nat := 4983230072969 + 3 ^ 40 * 1168132 * 2
def baseEnd_1168132 : Nat := 266583637287968405279051

theorem tailTrace_1168132 : CollatzResearch.WordTrace tailWord_1168132 prefixEnd_1168132 266583637287968405279051 := by
  unfold tailWord_1168132
  simp only [CollatzResearch.WordTrace]
  refine ⟨21302637102032369953809325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28403516136043159938412433 21302637102032369953809325)
  ·
    refine ⟨7988488913262138732678497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21302637102032369953809325 7988488913262138732678497)
    ·
      refine ⟨5991366684946604049508873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7988488913262138732678497 5991366684946604049508873)
      ·
        refine ⟨4493525013709953037131655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5991366684946604049508873 4493525013709953037131655)
        ·
          refine ⟨6740287520564929555697483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493525013709953037131655 6740287520564929555697483)
          ·
            refine ⟨10110431280847394333546225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6740287520564929555697483 10110431280847394333546225)
            ·
              refine ⟨7582823460635545750159669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10110431280847394333546225 7582823460635545750159669)
              ·
                refine ⟨710889699434582414077469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7582823460635545750159669 710889699434582414077469)
                ·
                  refine ⟨266583637287968405279051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710889699434582414077469 266583637287968405279051)
                  ·
                    rfl

theorem cell21_1168132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_1168132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168132 prefixEnd_1168132 := by exact prefixLift 1168132
  have htrace : WordTrace (prefixWord ++ tailWord_1168132) baseStart_1168132 baseEnd_1168132 := by
    simpa [prefixWord, tailWord_1168132, baseEnd_1168132] using wordTrace_append hprefix tailTrace_1168132
  have hstable : (prefixWord ++ tailWord_1168132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168132).length < 2 ^ (prefixWord ++ tailWord_1168132).sum := by decide
  have hdescent : baseEnd_1168132 < baseStart_1168132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168160 : List Nat := [2, 1, 1, 5, 1, 2, 3, 6]
def baseStart_1168160 : Nat := 118140960795 + 1168160 * 2 ^ 59
def prefixEnd_1168160 : Nat := 4983230072969 + 3 ^ 40 * 1168160 * 2
def baseEnd_1168160 : Nat := 88863342423148859604109

theorem tailTrace_1168160 : CollatzResearch.WordTrace tailWord_1168160 prefixEnd_1168160 88863342423148859604109 := by
  unfold tailWord_1168160
  simp only [CollatzResearch.WordTrace]
  refine ⟨21303147723981650344818967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28404196965308867126425289 21303147723981650344818967)
  ·
    refine ⟨31954721585972475517228451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21303147723981650344818967 31954721585972475517228451)
    ·
      refine ⟨47932082378958713275842677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31954721585972475517228451 47932082378958713275842677)
      ·
        refine ⟨4493632723027379369610251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47932082378958713275842677 4493632723027379369610251)
        ·
          refine ⟨6740449084541069054415377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493632723027379369610251 6740449084541069054415377)
          ·
            refine ⟨5055336813405801790811533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6740449084541069054415377 5055336813405801790811533)
            ·
              refine ⟨1895751305027175671554325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5055336813405801790811533 1895751305027175671554325)
              ·
                refine ⟨88863342423148859604109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1895751305027175671554325 88863342423148859604109)
                ·
                  rfl

theorem cell21_1168160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_1168160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168160 prefixEnd_1168160 := by exact prefixLift 1168160
  have htrace : WordTrace (prefixWord ++ tailWord_1168160) baseStart_1168160 baseEnd_1168160 := by
    simpa [prefixWord, tailWord_1168160, baseEnd_1168160] using wordTrace_append hprefix tailTrace_1168160
  have hstable : (prefixWord ++ tailWord_1168160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168160).length < 2 ^ (prefixWord ++ tailWord_1168160).sum := by decide
  have hdescent : baseEnd_1168160 < baseStart_1168160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168267 : List Nat := [1, 1, 1, 1, 4, 2, 2, 6, 3]
def baseStart_1168267 : Nat := 118140960795 + 1168267 * 2 ^ 59
def prefixEnd_1168267 : Nat := 4983230072969 + 3 ^ 40 * 1168267 * 2
def baseEnd_1168267 : Nat := 266614446127238170528775

theorem tailTrace_1168267 : CollatzResearch.WordTrace tailWord_1168267 prefixEnd_1168267 266614446127238170528775 := by
  unfold tailWord_1168267
  simp only [CollatzResearch.WordTrace]
  refine ⟨42610198058575657963783055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28406798705717105309188703 42610198058575657963783055)
  ·
    refine ⟨63915297087863486945674583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42610198058575657963783055 63915297087863486945674583)
    ·
      refine ⟨95872945631795230418511875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63915297087863486945674583 95872945631795230418511875)
      ·
        refine ⟨143809418447692845627767813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95872945631795230418511875 143809418447692845627767813)
        ·
          refine ⟨26964265958942408555206465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143809418447692845627767813 26964265958942408555206465)
          ·
            refine ⟨20223199469206806416404849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26964265958942408555206465 20223199469206806416404849)
            ·
              refine ⟨15167399601905104812303637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20223199469206806416404849 15167399601905104812303637)
              ·
                refine ⟨710971856339301788076733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15167399601905104812303637 710971856339301788076733)
                ·
                  refine ⟨266614446127238170528775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710971856339301788076733 266614446127238170528775)
                  ·
                    rfl

theorem cell21_1168267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 3].length) (baseStart_1168267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168267 prefixEnd_1168267 := by exact prefixLift 1168267
  have htrace : WordTrace (prefixWord ++ tailWord_1168267) baseStart_1168267 baseEnd_1168267 := by
    simpa [prefixWord, tailWord_1168267, baseEnd_1168267] using wordTrace_append hprefix tailTrace_1168267
  have hstable : (prefixWord ++ tailWord_1168267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168267).length < 2 ^ (prefixWord ++ tailWord_1168267).sum := by decide
  have hdescent : baseEnd_1168267 < baseStart_1168267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168374 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1168374 : Nat := 118140960795 + 1168374 * 2 ^ 59
def prefixEnd_1168374 : Nat := 4983230072969 + 3 ^ 40 * 1168374 * 2
def baseEnd_1168374 : Nat := 266638864985029762245223

theorem tailTrace_1168374 : CollatzResearch.WordTrace tailWord_1168374 prefixEnd_1168374 266638864985029762245223 := by
  unfold tailWord_1168374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663381291824250952370511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28409400446125343491952117 2663381291824250952370511)
  ·
    refine ⟨3995071937736376428555767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2663381291824250952370511 3995071937736376428555767)
    ·
      refine ⟨5992607906604564642833651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3995071937736376428555767 5992607906604564642833651)
      ·
        refine ⟨8988911859906846964250477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5992607906604564642833651 8988911859906846964250477)
        ·
          refine ⟨3370841947465067611593929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8988911859906846964250477 3370841947465067611593929)
          ·
            refine ⟨2528131460598800708695447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3370841947465067611593929 2528131460598800708695447)
            ·
              refine ⟨3792197190898201063043171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2528131460598800708695447 3792197190898201063043171)
              ·
                refine ⟨5688295786347301594564757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3792197190898201063043171 5688295786347301594564757)
                ·
                  refine ⟨266638864985029762245223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5688295786347301594564757 266638864985029762245223)
                  ·
                    rfl

theorem cell21_1168374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1168374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168374 prefixEnd_1168374 := by exact prefixLift 1168374
  have htrace : WordTrace (prefixWord ++ tailWord_1168374) baseStart_1168374 baseEnd_1168374 := by
    simpa [prefixWord, tailWord_1168374, baseEnd_1168374] using wordTrace_append hprefix tailTrace_1168374
  have hstable : (prefixWord ++ tailWord_1168374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168374).length < 2 ^ (prefixWord ++ tailWord_1168374).sum := by decide
  have hdescent : baseEnd_1168374 < baseStart_1168374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168405 : List Nat := [1, 3, 2, 1, 4, 3, 2, 5]
def baseStart_1168405 : Nat := 118140960795 + 1168405 * 2 ^ 59
def prefixEnd_1168405 : Nat := 4983230072969 + 3 ^ 40 * 1168405 * 2
def baseEnd_1168405 : Nat := 88881979869126865742831

theorem tailTrace_1168405 : CollatzResearch.WordTrace tailWord_1168405 prefixEnd_1168405 88881979869126865742831 := by
  unfold tailWord_1168405
  simp only [CollatzResearch.WordTrace]
  refine ⟨42615231332075707532306669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28410154221383805021537779 42615231332075707532306669)
  ·
    refine ⟨15980711749528390324615001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42615231332075707532306669 15980711749528390324615001)
    ·
      refine ⟨11985533812146292743461251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15980711749528390324615001 11985533812146292743461251)
      ·
        refine ⟨17978300718219439115191877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11985533812146292743461251 17978300718219439115191877)
        ·
          refine ⟨3370931384666144834098477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17978300718219439115191877 3370931384666144834098477)
          ·
            refine ⟨1264099269249804312786929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3370931384666144834098477 1264099269249804312786929)
            ·
              refine ⟨948074451937353234590197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1264099269249804312786929 948074451937353234590197)
              ·
                refine ⟨88881979869126865742831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 948074451937353234590197 88881979869126865742831)
                ·
                  rfl

theorem cell21_1168405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 5].length) (baseStart_1168405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168405 prefixEnd_1168405 := by exact prefixLift 1168405
  have htrace : WordTrace (prefixWord ++ tailWord_1168405) baseStart_1168405 baseEnd_1168405 := by
    simpa [prefixWord, tailWord_1168405, baseEnd_1168405] using wordTrace_append hprefix tailTrace_1168405
  have hstable : (prefixWord ++ tailWord_1168405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168405).length < 2 ^ (prefixWord ++ tailWord_1168405).sum := by decide
  have hdescent : baseEnd_1168405 < baseStart_1168405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168433 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 4]
def baseStart_1168433 : Nat := 118140960795 + 1168433 * 2 ^ 59
def prefixEnd_1168433 : Nat := 4983230072969 + 3 ^ 40 * 1168433 * 2
def baseEnd_1168433 : Nat := 266652329588858770761769

theorem tailTrace_1168433 : CollatzResearch.WordTrace tailWord_1168433 prefixEnd_1168433 266652329588858770761769 := by
  unfold tailWord_1168433
  simp only [CollatzResearch.WordTrace]
  refine ⟨42616252575974268314325953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28410835050649512209550635 42616252575974268314325953)
  ·
    refine ⟨31962189431980701235744465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42616252575974268314325953 31962189431980701235744465)
    ·
      refine ⟨23971642073985525926808349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31962189431980701235744465 23971642073985525926808349)
      ·
        refine ⟨8989365777744572222553131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23971642073985525926808349 8989365777744572222553131)
        ·
          refine ⟨13484048666616858333829697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8989365777744572222553131 13484048666616858333829697)
          ·
            refine ⟨10113036499962643750372273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13484048666616858333829697 10113036499962643750372273)
            ·
              refine ⟨7584777374971982812779205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10113036499962643750372273 7584777374971982812779205)
              ·
                refine ⟨1422145757807246777396101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7584777374971982812779205 1422145757807246777396101)
                ·
                  refine ⟨266652329588858770761769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1422145757807246777396101 266652329588858770761769)
                  ·
                    rfl

theorem cell21_1168433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_1168433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168433 prefixEnd_1168433 := by exact prefixLift 1168433
  have htrace : WordTrace (prefixWord ++ tailWord_1168433) baseStart_1168433 baseEnd_1168433 := by
    simpa [prefixWord, tailWord_1168433, baseEnd_1168433] using wordTrace_append hprefix tailTrace_1168433
  have hstable : (prefixWord ++ tailWord_1168433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168433).length < 2 ^ (prefixWord ++ tailWord_1168433).sum := by decide
  have hdescent : baseEnd_1168433 < baseStart_1168433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168436 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1168436 : Nat := 118140960795 + 1168436 * 2 ^ 59
def prefixEnd_1168436 : Nat := 4983230072969 + 3 ^ 40 * 1168436 * 2
def baseEnd_1168436 : Nat := 266653014229731432211763

theorem tailTrace_1168436 : CollatzResearch.WordTrace tailWord_1168436 prefixEnd_1168436 266653014229731432211763 := by
  unfold tailWord_1168436
  simp only [CollatzResearch.WordTrace]
  refine ⟨21308180997481699913342581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28410907996642266551123441 21308180997481699913342581)
  ·
    refine ⟨1997641968513909366875867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21308180997481699913342581 1997641968513909366875867)
    ·
      refine ⟨2996462952770864050313801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1997641968513909366875867 2996462952770864050313801)
      ·
        refine ⟨2247347214578148037735351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2996462952770864050313801 2247347214578148037735351)
        ·
          refine ⟨3371020821867222056603027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247347214578148037735351 3371020821867222056603027)
          ·
            refine ⟨5056531232800833084904541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371020821867222056603027 5056531232800833084904541)
            ·
              refine ⟨1896199212300312406839203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5056531232800833084904541 1896199212300312406839203)
              ·
                refine ⟨2844298818450468610258805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896199212300312406839203 2844298818450468610258805)
                ·
                  refine ⟨266653014229731432211763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2844298818450468610258805 266653014229731432211763)
                  ·
                    rfl

theorem cell21_1168436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1168436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168436 prefixEnd_1168436 := by exact prefixLift 1168436
  have htrace : WordTrace (prefixWord ++ tailWord_1168436) baseStart_1168436 baseEnd_1168436 := by
    simpa [prefixWord, tailWord_1168436, baseEnd_1168436] using wordTrace_append hprefix tailTrace_1168436
  have hstable : (prefixWord ++ tailWord_1168436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168436).length < 2 ^ (prefixWord ++ tailWord_1168436).sum := by decide
  have hdescent : baseEnd_1168436 < baseStart_1168436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168495 : List Nat := [1, 1, 2, 1, 3, 3, 3, 4, 3]
def baseStart_1168495 : Nat := 118140960795 + 1168495 * 2 ^ 59
def prefixEnd_1168495 : Nat := 4983230072969 + 3 ^ 40 * 1168495 * 2
def baseEnd_1168495 : Nat := 266666478833560440728309

theorem tailTrace_1168495 : CollatzResearch.WordTrace tailWord_1168495 prefixEnd_1168495 266666478833560440728309 := by
  unfold tailWord_1168495
  simp only [CollatzResearch.WordTrace]
  refine ⟨42618513901749652903082939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28412342601166435268721959 42618513901749652903082939)
  ·
    refine ⟨63927770852624479354624409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42618513901749652903082939 63927770852624479354624409)
    ·
      refine ⟨47945828139468359515968307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63927770852624479354624409 47945828139468359515968307)
      ·
        refine ⟨71918742209202539273952461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47945828139468359515968307 71918742209202539273952461)
        ·
          refine ⟨26969528328450952227732173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71918742209202539273952461 26969528328450952227732173)
          ·
            refine ⟨10113573123169107085399565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26969528328450952227732173 10113573123169107085399565)
            ·
              refine ⟨3792589921188415157024837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10113573123169107085399565 3792589921188415157024837)
              ·
                refine ⟨711110610222827841942157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3792589921188415157024837 711110610222827841942157)
                ·
                  refine ⟨266666478833560440728309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711110610222827841942157 266666478833560440728309)
                  ·
                    rfl

theorem cell21_1168495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 3].length) (baseStart_1168495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168495 prefixEnd_1168495 := by exact prefixLift 1168495
  have htrace : WordTrace (prefixWord ++ tailWord_1168495) baseStart_1168495 baseEnd_1168495 := by
    simpa [prefixWord, tailWord_1168495, baseEnd_1168495] using wordTrace_append hprefix tailTrace_1168495
  have hstable : (prefixWord ++ tailWord_1168495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168495).length < 2 ^ (prefixWord ++ tailWord_1168495).sum := by decide
  have hdescent : baseEnd_1168495 < baseStart_1168495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168509 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 4]
def baseStart_1168509 : Nat := 118140960795 + 1168509 * 2 ^ 59
def prefixEnd_1168509 : Nat := 4983230072969 + 3 ^ 40 * 1168509 * 2
def baseEnd_1168509 : Nat := 266669673824299527494947

theorem tailTrace_1168509 : CollatzResearch.WordTrace tailWord_1168509 prefixEnd_1168509 266669673824299527494947 := by
  unfold tailWord_1168509
  simp only [CollatzResearch.WordTrace]
  refine ⟨42619024523698933294092581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28412683015799288862728387 42619024523698933294092581)
  ·
    refine ⟨7991067098193549992642359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42619024523698933294092581 7991067098193549992642359)
    ·
      refine ⟨11986600647290324988963539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7991067098193549992642359 11986600647290324988963539)
      ·
        refine ⟨17979900970935487483445309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11986600647290324988963539 17979900970935487483445309)
        ·
          refine ⟨6742462864100807806291991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17979900970935487483445309 6742462864100807806291991)
          ·
            refine ⟨10113694296151211709437987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6742462864100807806291991 10113694296151211709437987)
            ·
              refine ⟨15170541444226817564156981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10113694296151211709437987 15170541444226817564156981)
              ·
                refine ⟨1422238260396264146639717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15170541444226817564156981 1422238260396264146639717)
                ·
                  refine ⟨266669673824299527494947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1422238260396264146639717 266669673824299527494947)
                  ·
                    rfl

theorem cell21_1168509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_1168509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168509 prefixEnd_1168509 := by exact prefixLift 1168509
  have htrace : WordTrace (prefixWord ++ tailWord_1168509) baseStart_1168509 baseEnd_1168509 := by
    simpa [prefixWord, tailWord_1168509, baseEnd_1168509] using wordTrace_append hprefix tailTrace_1168509
  have hstable : (prefixWord ++ tailWord_1168509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168509).length < 2 ^ (prefixWord ++ tailWord_1168509).sum := by decide
  have hdescent : baseEnd_1168509 < baseStart_1168509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168543 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 4]
def baseStart_1168543 : Nat := 118140960795 + 1168543 * 2 ^ 59
def prefixEnd_1168543 : Nat := 4983230072969 + 3 ^ 40 * 1168543 * 2
def baseEnd_1168543 : Nat := 266677433087523023928211

theorem tailTrace_1168543 : CollatzResearch.WordTrace tailWord_1168543 prefixEnd_1168543 266677433087523023928211 := by
  unfold tailWord_1168543
  simp only [CollatzResearch.WordTrace]
  refine ⟨42620264605575757100830283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28413509737050504733886855 42620264605575757100830283)
  ·
    refine ⟨63930396908363635651245425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42620264605575757100830283 63930396908363635651245425)
    ·
      refine ⟨47947797681272726738434069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63930396908363635651245425 47947797681272726738434069)
      ·
        refine ⟨2247553016309659065864097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47947797681272726738434069 2247553016309659065864097)
        ·
          refine ⟨1685664762232244299398073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2247553016309659065864097 1685664762232244299398073)
          ·
            refine ⟨1264248571674183224548555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1685664762232244299398073 1264248571674183224548555)
            ·
              refine ⟨1896372857511274836822833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264248571674183224548555 1896372857511274836822833)
              ·
                refine ⟨1422279643133456127617125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1896372857511274836822833 1422279643133456127617125)
                ·
                  refine ⟨266677433087523023928211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1422279643133456127617125 266677433087523023928211)
                  ·
                    rfl

theorem cell21_1168543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 4].length) (baseStart_1168543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168543 prefixEnd_1168543 := by exact prefixLift 1168543
  have htrace : WordTrace (prefixWord ++ tailWord_1168543) baseStart_1168543 baseEnd_1168543 := by
    simpa [prefixWord, tailWord_1168543, baseEnd_1168543] using wordTrace_append hprefix tailTrace_1168543
  have hstable : (prefixWord ++ tailWord_1168543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168543).length < 2 ^ (prefixWord ++ tailWord_1168543).sum := by decide
  have hdescent : baseEnd_1168543 < baseStart_1168543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168605 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 5]
def baseStart_1168605 : Nat := 118140960795 + 1168605 * 2 ^ 59
def prefixEnd_1168605 : Nat := 4983230072969 + 3 ^ 40 * 1168605 * 2
def baseEnd_1168605 : Nat := 266691582332224693894751

theorem tailTrace_1168605 : CollatzResearch.WordTrace tailWord_1168605 prefixEnd_1168605 266691582332224693894751 := by
  unfold tailWord_1168605
  simp only [CollatzResearch.WordTrace]
  refine ⟨42622525931351141689587269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28415017287567427793058179 42622525931351141689587269)
  ·
    refine ⟨7991723612128339066797613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42622525931351141689587269 7991723612128339066797613)
    ·
      refine ⟨2996896354548127150049105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7991723612128339066797613 2996896354548127150049105)
      ·
        refine ⟨2247672265911095362536829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2996896354548127150049105 2247672265911095362536829)
        ·
          refine ⟨842877099716660760951311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2247672265911095362536829 842877099716660760951311)
          ·
            refine ⟨1264315649574991141426967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842877099716660760951311 1264315649574991141426967)
            ·
              refine ⟨1896473474362486712140451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264315649574991141426967 1896473474362486712140451)
              ·
                refine ⟨2844710211543730068210677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896473474362486712140451 2844710211543730068210677)
                ·
                  refine ⟨266691582332224693894751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2844710211543730068210677 266691582332224693894751)
                  ·
                    rfl

theorem cell21_1168605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_1168605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168605 prefixEnd_1168605 := by exact prefixLift 1168605
  have htrace : WordTrace (prefixWord ++ tailWord_1168605) baseStart_1168605 baseEnd_1168605 := by
    simpa [prefixWord, tailWord_1168605, baseEnd_1168605] using wordTrace_append hprefix tailTrace_1168605
  have hstable : (prefixWord ++ tailWord_1168605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168605).length < 2 ^ (prefixWord ++ tailWord_1168605).sum := by decide
  have hdescent : baseEnd_1168605 < baseStart_1168605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168630 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1168630 : Nat := 118140960795 + 1168630 * 2 ^ 59
def prefixEnd_1168630 : Nat := 4983230072969 + 3 ^ 40 * 1168630 * 2
def baseEnd_1168630 : Nat := 266697287672830205978033

theorem tailTrace_1168630 : CollatzResearch.WordTrace tailWord_1168630 prefixEnd_1168630 266697287672830205978033 := by
  unfold tailWord_1168630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663964859766285684952959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28415625170840380639498229 2663964859766285684952959)
  ·
    refine ⟨3995947289649428527429439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2663964859766285684952959 3995947289649428527429439)
    ·
      refine ⟨5993920934474142791144159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3995947289649428527429439 5993920934474142791144159)
      ·
        refine ⟨8990881401711214186716239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5993920934474142791144159 8990881401711214186716239)
        ·
          refine ⟨13486322102566821280074359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8990881401711214186716239 13486322102566821280074359)
          ·
            refine ⟨20229483153850231920111539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13486322102566821280074359 20229483153850231920111539)
            ·
              refine ⟨30344224730775347880167309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20229483153850231920111539 30344224730775347880167309)
              ·
                refine ⟨11379084274040755455062741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30344224730775347880167309 11379084274040755455062741)
                ·
                  refine ⟨266697287672830205978033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11379084274040755455062741 266697287672830205978033)
                  ·
                    rfl

theorem cell21_1168630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1168630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168630 prefixEnd_1168630 := by exact prefixLift 1168630
  have htrace : WordTrace (prefixWord ++ tailWord_1168630) baseStart_1168630 baseEnd_1168630 := by
    simpa [prefixWord, tailWord_1168630, baseEnd_1168630] using wordTrace_append hprefix tailTrace_1168630
  have hstable : (prefixWord ++ tailWord_1168630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168630).length < 2 ^ (prefixWord ++ tailWord_1168630).sum := by decide
  have hdescent : baseEnd_1168630 < baseStart_1168630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168664 : List Nat := [2, 1, 2, 3, 1, 3, 4, 2, 3]
def baseStart_1168664 : Nat := 118140960795 + 1168664 * 2 ^ 59
def prefixEnd_1168664 : Nat := 4983230072969 + 3 ^ 40 * 1168664 * 2
def baseEnd_1168664 : Nat := 266705046936053702411297

theorem tailTrace_1168664 : CollatzResearch.WordTrace tailWord_1168664 prefixEnd_1168664 266705046936053702411297 := by
  unfold tailWord_1168664
  simp only [CollatzResearch.WordTrace]
  refine ⟨21312338919068697382992523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28416451892091596510656697 21312338919068697382992523)
  ·
    refine ⟨31968508378603046074488785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21312338919068697382992523 31968508378603046074488785)
    ·
      refine ⟨23976381283952284555866589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31968508378603046074488785 23976381283952284555866589)
      ·
        refine ⟨8991142981482106708449971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23976381283952284555866589 8991142981482106708449971)
        ·
          refine ⟨13486714472223160062674957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8991142981482106708449971 13486714472223160062674957)
          ·
            refine ⟨5057517927083685023503109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13486714472223160062674957 5057517927083685023503109)
            ·
              refine ⟨948284611328190941906833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5057517927083685023503109 948284611328190941906833)
              ·
                refine ⟨711213458496143206430125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948284611328190941906833 711213458496143206430125)
                ·
                  refine ⟨266705046936053702411297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711213458496143206430125 266705046936053702411297)
                  ·
                    rfl

theorem cell21_1168664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 3].length) (baseStart_1168664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168664 prefixEnd_1168664 := by exact prefixLift 1168664
  have htrace : WordTrace (prefixWord ++ tailWord_1168664) baseStart_1168664 baseEnd_1168664 := by
    simpa [prefixWord, tailWord_1168664, baseEnd_1168664] using wordTrace_append hprefix tailTrace_1168664
  have hstable : (prefixWord ++ tailWord_1168664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168664).length < 2 ^ (prefixWord ++ tailWord_1168664).sum := by decide
  have hdescent : baseEnd_1168664 < baseStart_1168664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168675 : List Nat := [1, 1, 1, 4, 2, 3, 3, 6]
def baseStart_1168675 : Nat := 118140960795 + 1168675 * 2 ^ 59
def prefixEnd_1168675 : Nat := 4983230072969 + 3 ^ 40 * 1168675 * 2
def baseEnd_1168675 : Nat := 88902519095306709242647

theorem tailTrace_1168675 : CollatzResearch.WordTrace tailWord_1168675 prefixEnd_1168675 88902519095306709242647 := by
  unfold tailWord_1168675
  simp only [CollatzResearch.WordTrace]
  refine ⟨42625079041097543644635479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28416719360731695763090319 42625079041097543644635479)
  ·
    refine ⟨63937618561646315466953219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42625079041097543644635479 63937618561646315466953219)
    ·
      refine ⟨95906427842469473200429829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63937618561646315466953219 95906427842469473200429829)
      ·
        refine ⟨17982455220463026225080593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95906427842469473200429829 17982455220463026225080593)
        ·
          refine ⟨13486841415347269668810445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17982455220463026225080593 13486841415347269668810445)
          ·
            refine ⟨5057565530755226125803917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13486841415347269668810445 5057565530755226125803917)
            ·
              refine ⟨1896587074033209797176469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5057565530755226125803917 1896587074033209797176469)
              ·
                refine ⟨88902519095306709242647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1896587074033209797176469 88902519095306709242647)
                ·
                  rfl

theorem cell21_1168675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 6].length) (baseStart_1168675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168675 prefixEnd_1168675 := by exact prefixLift 1168675
  have htrace : WordTrace (prefixWord ++ tailWord_1168675) baseStart_1168675 baseEnd_1168675 := by
    simpa [prefixWord, tailWord_1168675, baseEnd_1168675] using wordTrace_append hprefix tailTrace_1168675
  have hstable : (prefixWord ++ tailWord_1168675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168675).length < 2 ^ (prefixWord ++ tailWord_1168675).sum := by decide
  have hdescent : baseEnd_1168675 < baseStart_1168675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168720 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_1168720 : Nat := 118140960795 + 1168720 * 2 ^ 59
def prefixEnd_1168720 : Nat := 4983230072969 + 3 ^ 40 * 1168720 * 2
def baseEnd_1168720 : Nat := 266717826899010049477849

theorem tailTrace_1168720 : CollatzResearch.WordTrace tailWord_1168720 prefixEnd_1168720 266717826899010049477849 := by
  unfold tailWord_1168720
  simp only [CollatzResearch.WordTrace]
  refine ⟨21313360162967258165011807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28417813550623010886682409 21313360162967258165011807)
  ·
    refine ⟨31970040244450887247517711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21313360162967258165011807 31970040244450887247517711)
    ·
      refine ⟨47955060366676330871276567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31970040244450887247517711 47955060366676330871276567)
      ·
        refine ⟨71932590550014496306914851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47955060366676330871276567 71932590550014496306914851)
        ·
          refine ⟨107898885825021744460372277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71932590550014496306914851 107898885825021744460372277)
          ·
            refine ⟨10115520546095788543159901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107898885825021744460372277 10115520546095788543159901)
            ·
              refine ⟨3793320204785920703684963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10115520546095788543159901 3793320204785920703684963)
              ·
                refine ⟨5689980307178881055527445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3793320204785920703684963 5689980307178881055527445)
                ·
                  refine ⟨266717826899010049477849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5689980307178881055527445 266717826899010049477849)
                  ·
                    rfl

theorem cell21_1168720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_1168720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168720 prefixEnd_1168720 := by exact prefixLift 1168720
  have htrace : WordTrace (prefixWord ++ tailWord_1168720) baseStart_1168720 baseEnd_1168720 := by
    simpa [prefixWord, tailWord_1168720, baseEnd_1168720] using wordTrace_append hprefix tailTrace_1168720
  have hstable : (prefixWord ++ tailWord_1168720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168720).length < 2 ^ (prefixWord ++ tailWord_1168720).sum := by decide
  have hdescent : baseEnd_1168720 < baseStart_1168720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168757 : List Nat := [1, 3, 4, 1, 3, 2, 1, 3, 3]
def baseStart_1168757 : Nat := 118140960795 + 1168757 * 2 ^ 59
def prefixEnd_1168757 : Nat := 4983230072969 + 3 ^ 40 * 1168757 * 2
def baseEnd_1168757 : Nat := 266726270803106207361107

theorem tailTrace_1168757 : CollatzResearch.WordTrace tailWord_1168757 prefixEnd_1168757 266726270803106207361107 := by
  unfold tailWord_1168757
  simp only [CollatzResearch.WordTrace]
  refine ⟨42628069826800471649120525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28418713217866981099413683 42628069826800471649120525)
  ·
    refine ⟨15985526185050176868420197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42628069826800471649120525 15985526185050176868420197)
    ·
      refine ⟨2997286159696908162828787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15985526185050176868420197 2997286159696908162828787)
      ·
        refine ⟨4495929239545362244243181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2997286159696908162828787 4495929239545362244243181)
        ·
          refine ⟨1685973464829510841591193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4495929239545362244243181 1685973464829510841591193)
          ·
            refine ⟨1264480098622133131193395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1685973464829510841591193 1264480098622133131193395)
            ·
              refine ⟨1896720147933199696790093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264480098622133131193395 1896720147933199696790093)
              ·
                refine ⟨711270055474949886296285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1896720147933199696790093 711270055474949886296285)
                ·
                  refine ⟨266726270803106207361107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711270055474949886296285 266726270803106207361107)
                  ·
                    rfl

theorem cell21_1168757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_1168757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168757 prefixEnd_1168757 := by exact prefixLift 1168757
  have htrace : WordTrace (prefixWord ++ tailWord_1168757) baseStart_1168757 baseEnd_1168757 := by
    simpa [prefixWord, tailWord_1168757, baseEnd_1168757] using wordTrace_append hprefix tailTrace_1168757
  have hstable : (prefixWord ++ tailWord_1168757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168757).length < 2 ^ (prefixWord ++ tailWord_1168757).sum := by decide
  have hdescent : baseEnd_1168757 < baseStart_1168757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168841 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 5]
def baseStart_1168841 : Nat := 118140960795 + 1168841 * 2 ^ 59
def prefixEnd_1168841 : Nat := 4983230072969 + 3 ^ 40 * 1168841 * 2
def baseEnd_1168841 : Nat := 266745440747540727960935

theorem tailTrace_1168841 : CollatzResearch.WordTrace tailWord_1168841 prefixEnd_1168841 266745440747540727960935 := by
  unfold tailWord_1168841
  simp only [CollatzResearch.WordTrace]
  refine ⟨42631133558496153995178377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28420755705664102663452251 42631133558496153995178377)
  ·
    refine ⟨31973350168872115496383783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42631133558496153995178377 31973350168872115496383783)
    ·
      refine ⟨47960025253308173244575675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31973350168872115496383783 47960025253308173244575675)
      ·
        refine ⟨71940037879962259866863513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47960025253308173244575675 71940037879962259866863513)
        ·
          refine ⟨53955028409971694900147635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71940037879962259866863513 53955028409971694900147635)
          ·
            refine ⟨80932542614957542350221453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53955028409971694900147635 80932542614957542350221453)
            ·
              refine ⟨30349703480609078381333045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80932542614957542350221453 30349703480609078381333045)
              ·
                refine ⟨2845284701307101098249973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30349703480609078381333045 2845284701307101098249973)
                ·
                  refine ⟨266745440747540727960935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2845284701307101098249973 266745440747540727960935)
                  ·
                    rfl

theorem cell21_1168841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_1168841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168841 prefixEnd_1168841 := by exact prefixLift 1168841
  have htrace : WordTrace (prefixWord ++ tailWord_1168841) baseStart_1168841 baseEnd_1168841 := by
    simpa [prefixWord, tailWord_1168841, baseEnd_1168841] using wordTrace_append hprefix tailTrace_1168841
  have hstable : (prefixWord ++ tailWord_1168841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168841).length < 2 ^ (prefixWord ++ tailWord_1168841).sum := by decide
  have hdescent : baseEnd_1168841 < baseStart_1168841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168844 : List Nat := [2, 2, 1, 4, 2, 3, 1, 6]
def baseStart_1168844 : Nat := 118140960795 + 1168844 * 2 ^ 59
def prefixEnd_1168844 : Nat := 4983230072969 + 3 ^ 40 * 1168844 * 2
def baseEnd_1168844 : Nat := 88915375129471129803643

theorem tailTrace_1168844 : CollatzResearch.WordTrace tailWord_1168844 prefixEnd_1168844 88915375129471129803643 := by
  unfold tailWord_1168844
  simp only [CollatzResearch.WordTrace]
  refine ⟨21315621488742642753768793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28420828651656857005025057 21315621488742642753768793)
  ·
    refine ⟨15986716116556982065326595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21315621488742642753768793 15986716116556982065326595)
    ·
      refine ⟨23980074174835473097989893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15986716116556982065326595 23980074174835473097989893)
      ·
        refine ⟨4496263907781651205873105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23980074174835473097989893 4496263907781651205873105)
        ·
          refine ⟨3372197930836238404404829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4496263907781651205873105 3372197930836238404404829)
          ·
            refine ⟨1264574224063589401651811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3372197930836238404404829 1264574224063589401651811)
            ·
              refine ⟨1896861336095384102477717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264574224063589401651811 1896861336095384102477717)
              ·
                refine ⟨88915375129471129803643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1896861336095384102477717 88915375129471129803643)
                ·
                  rfl

theorem cell21_1168844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_1168844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168844 prefixEnd_1168844 := by exact prefixLift 1168844
  have htrace : WordTrace (prefixWord ++ tailWord_1168844) baseStart_1168844 baseEnd_1168844 := by
    simpa [prefixWord, tailWord_1168844, baseEnd_1168844] using wordTrace_append hprefix tailTrace_1168844
  have hstable : (prefixWord ++ tailWord_1168844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168844).length < 2 ^ (prefixWord ++ tailWord_1168844).sum := by decide
  have hdescent : baseEnd_1168844 < baseStart_1168844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168858 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_1168858 : Nat := 118140960795 + 1168858 * 2 ^ 59
def prefixEnd_1168858 : Nat := 4983230072969 + 3 ^ 40 * 1168858 * 2
def baseEnd_1168858 : Nat := 266749320379152476177567

theorem tailTrace_1168858 : CollatzResearch.WordTrace tailWord_1168858 prefixEnd_1168858 266749320379152476177567 := by
  unfold tailWord_1168858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10657938399858641474636807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28421169066289710599031485 10657938399858641474636807)
  ·
    refine ⟨15986907599787962211955211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10657938399858641474636807 15986907599787962211955211)
    ·
      refine ⟨23980361399681943317932817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15986907599787962211955211 23980361399681943317932817)
      ·
        refine ⟨17985271049761457488449613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23980361399681943317932817 17985271049761457488449613)
        ·
          refine ⟨6744476643660546558168605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17985271049761457488449613 6744476643660546558168605)
          ·
            refine ⟨2529178741372704959313227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6744476643660546558168605 2529178741372704959313227)
            ·
              refine ⟨3793768112059057438969841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529178741372704959313227 3793768112059057438969841)
              ·
                refine ⟨2845326084044293079227381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3793768112059057438969841 2845326084044293079227381)
                ·
                  refine ⟨266749320379152476177567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2845326084044293079227381 266749320379152476177567)
                  ·
                    rfl

theorem cell21_1168858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_1168858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168858 prefixEnd_1168858 := by exact prefixLift 1168858
  have htrace : WordTrace (prefixWord ++ tailWord_1168858) baseStart_1168858 baseEnd_1168858 := by
    simpa [prefixWord, tailWord_1168858, baseEnd_1168858] using wordTrace_append hprefix tailTrace_1168858
  have hstable : (prefixWord ++ tailWord_1168858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168858).length < 2 ^ (prefixWord ++ tailWord_1168858).sum := by decide
  have hdescent : baseEnd_1168858 < baseStart_1168858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168872 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_1168872 : Nat := 118140960795 + 1168872 * 2 ^ 59
def prefixEnd_1168872 : Nat := 4983230072969 + 3 ^ 40 * 1168872 * 2
def baseEnd_1168872 : Nat := 266752515369891562944205

theorem tailTrace_1168872 : CollatzResearch.WordTrace tailWord_1168872 prefixEnd_1168872 266752515369891562944205 := by
  unfold tailWord_1168872
  simp only [CollatzResearch.WordTrace]
  refine ⟨21316132110691923144778435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28421509480922564193037913 21316132110691923144778435)
  ·
    refine ⟨31974198166037884717167653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21316132110691923144778435 31974198166037884717167653)
    ·
      refine ⟨5995162156132103384468935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31974198166037884717167653 5995162156132103384468935)
      ·
        refine ⟨8992743234198155076703403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5995162156132103384468935 8992743234198155076703403)
        ·
          refine ⟨13489114851297232615055105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8992743234198155076703403 13489114851297232615055105)
          ·
            refine ⟨10116836138472924461291329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13489114851297232615055105 10116836138472924461291329)
            ·
              refine ⟨7587627103854693345968497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10116836138472924461291329 7587627103854693345968497)
              ·
                refine ⟨5690720327891020009476373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7587627103854693345968497 5690720327891020009476373)
                ·
                  refine ⟨266752515369891562944205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5690720327891020009476373 266752515369891562944205)
                  ·
                    rfl

theorem cell21_1168872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_1168872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168872 prefixEnd_1168872 := by exact prefixLift 1168872
  have htrace : WordTrace (prefixWord ++ tailWord_1168872) baseStart_1168872 baseEnd_1168872 := by
    simpa [prefixWord, tailWord_1168872, baseEnd_1168872] using wordTrace_append hprefix tailTrace_1168872
  have hstable : (prefixWord ++ tailWord_1168872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168872).length < 2 ^ (prefixWord ++ tailWord_1168872).sum := by decide
  have hdescent : baseEnd_1168872 < baseStart_1168872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168906 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_1168906 : Nat := 118140960795 + 1168906 * 2 ^ 59
def prefixEnd_1168906 : Nat := 4983230072969 + 3 ^ 40 * 1168906 * 2
def baseEnd_1168906 : Nat := 266760274633115059377469

theorem tailTrace_1168906 : CollatzResearch.WordTrace tailWord_1168906 prefixEnd_1168906 266760274633115059377469 := by
  unfold tailWord_1168906
  simp only [CollatzResearch.WordTrace]
  refine ⟨10658376075815167524073643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28422336202173780064196381 10658376075815167524073643)
  ·
    refine ⟨15987564113722751286110465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10658376075815167524073643 15987564113722751286110465)
    ·
      refine ⟨11990673085292063464582849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15987564113722751286110465 11990673085292063464582849)
      ·
        refine ⟨8993004813969047598437137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11990673085292063464582849 8993004813969047598437137)
        ·
          refine ⟨6744753610476785698827853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8993004813969047598437137 6744753610476785698827853)
          ·
            refine ⟨2529282603928794637060445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6744753610476785698827853 2529282603928794637060445)
            ·
              refine ⟨948480976473297988897667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2529282603928794637060445 948480976473297988897667)
              ·
                refine ⟨1422721464709946983346501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948480976473297988897667 1422721464709946983346501)
                ·
                  refine ⟨266760274633115059377469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1422721464709946983346501 266760274633115059377469)
                  ·
                    rfl

theorem cell21_1168906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_1168906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1168906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1168906 prefixEnd_1168906 := by exact prefixLift 1168906
  have htrace : WordTrace (prefixWord ++ tailWord_1168906) baseStart_1168906 baseEnd_1168906 := by
    simpa [prefixWord, tailWord_1168906, baseEnd_1168906] using wordTrace_append hprefix tailTrace_1168906
  have hstable : (prefixWord ++ tailWord_1168906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168906).length < 2 ^ (prefixWord ++ tailWord_1168906).sum := by decide
  have hdescent : baseEnd_1168906 < baseStart_1168906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169024 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 4]
def baseStart_1169024 : Nat := 118140960795 + 1169024 * 2 ^ 59
def prefixEnd_1169024 : Nat := 4983230072969 + 3 ^ 40 * 1169024 * 2
def baseEnd_1169024 : Nat := 266787203840773076410561

theorem tailTrace_1169024 : CollatzResearch.WordTrace tailWord_1169024 prefixEnd_1169024 266787203840773076410561 := by
  unfold tailWord_1169024
  simp only [CollatzResearch.WordTrace]
  refine ⟨21318904058416588124545063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28425205411222117499393417 21318904058416588124545063)
  ·
    refine ⟨31978356087624882186817595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21318904058416588124545063 31978356087624882186817595)
    ·
      refine ⟨47967534131437323280226393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31978356087624882186817595 47967534131437323280226393)
      ·
        refine ⟨35975650598577992460169795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47967534131437323280226393 35975650598577992460169795)
        ·
          refine ⟨53963475897866988690254693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35975650598577992460169795 53963475897866988690254693)
          ·
            refine ⟨10118151730850060379422755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53963475897866988690254693 10118151730850060379422755)
            ·
              refine ⟨15177227596275090569134133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10118151730850060379422755 15177227596275090569134133)
              ·
                refine ⟨1422865087150789740856325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15177227596275090569134133 1422865087150789740856325)
                ·
                  refine ⟨266787203840773076410561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1422865087150789740856325 266787203840773076410561)
                  ·
                    rfl

theorem cell21_1169024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_1169024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169024 prefixEnd_1169024 := by exact prefixLift 1169024
  have htrace : WordTrace (prefixWord ++ tailWord_1169024) baseStart_1169024 baseEnd_1169024 := by
    simpa [prefixWord, tailWord_1169024, baseEnd_1169024] using wordTrace_append hprefix tailTrace_1169024
  have hstable : (prefixWord ++ tailWord_1169024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169024).length < 2 ^ (prefixWord ++ tailWord_1169024).sum := by decide
  have hdescent : baseEnd_1169024 < baseStart_1169024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169058 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1169058 : Nat := 118140960795 + 1169058 * 2 ^ 59
def prefixEnd_1169058 : Nat := 4983230072969 + 3 ^ 40 * 1169058 * 2
def baseEnd_1169058 : Nat := 266794963103996572843825

theorem tailTrace_1169058 : CollatzResearch.WordTrace tailWord_1169058 prefixEnd_1169058 266794963103996572843825 := by
  unfold tailWord_1169058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10659762049677500013956957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28426032132473333370551885 10659762049677500013956957)
  ·
    refine ⟨3997410768629062505233859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10659762049677500013956957 3997410768629062505233859)
    ·
      refine ⟨5996116152943593757850789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3997410768629062505233859 5996116152943593757850789)
      ·
        refine ⟨1124271778676923829597023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5996116152943593757850789 1124271778676923829597023)
        ·
          refine ⟨1686407668015385744395535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124271778676923829597023 1686407668015385744395535)
          ·
            refine ⟨2529611502023078616593303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686407668015385744395535 2529611502023078616593303)
            ·
              refine ⟨3794417253034617924889955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529611502023078616593303 3794417253034617924889955)
              ·
                refine ⟨5691625879551926887334933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794417253034617924889955 5691625879551926887334933)
                ·
                  refine ⟨266794963103996572843825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5691625879551926887334933 266794963103996572843825)
                  ·
                    rfl

theorem cell21_1169058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1169058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169058 prefixEnd_1169058 := by exact prefixLift 1169058
  have htrace : WordTrace (prefixWord ++ tailWord_1169058) baseStart_1169058 baseEnd_1169058 := by
    simpa [prefixWord, tailWord_1169058, baseEnd_1169058] using wordTrace_append hprefix tailTrace_1169058
  have hstable : (prefixWord ++ tailWord_1169058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169058).length < 2 ^ (prefixWord ++ tailWord_1169058).sum := by decide
  have hdescent : baseEnd_1169058 < baseStart_1169058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169086 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_1169086 : Nat := 118140960795 + 1169086 * 2 ^ 59
def prefixEnd_1169086 : Nat := 4983230072969 + 3 ^ 40 * 1169086 * 2
def baseEnd_1169086 : Nat := 266801353085474746377101

theorem tailTrace_1169086 : CollatzResearch.WordTrace tailWord_1169086 prefixEnd_1169086 266801353085474746377101 := by
  unfold tailWord_1169086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5330008680326070104730889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28426712961739040558564741 5330008680326070104730889)
  ·
    refine ⟨3997506510244552578548167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5330008680326070104730889 3997506510244552578548167)
    ·
      refine ⟨5996259765366828867822251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3997506510244552578548167 5996259765366828867822251)
      ·
        refine ⟨8994389648050243301733377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5996259765366828867822251 8994389648050243301733377)
        ·
          refine ⟨6745792236037682476300033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8994389648050243301733377 6745792236037682476300033)
          ·
            refine ⟨5059344177028261857225025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6745792236037682476300033 5059344177028261857225025)
            ·
              refine ⟨3794508132771196392918769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5059344177028261857225025 3794508132771196392918769)
              ·
                refine ⟨2845881099578397294689077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3794508132771196392918769 2845881099578397294689077)
                ·
                  refine ⟨266801353085474746377101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2845881099578397294689077 266801353085474746377101)
                  ·
                    rfl

theorem cell21_1169086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_1169086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169086 prefixEnd_1169086 := by exact prefixLift 1169086
  have htrace : WordTrace (prefixWord ++ tailWord_1169086) baseStart_1169086 baseEnd_1169086 := by
    simpa [prefixWord, tailWord_1169086, baseEnd_1169086] using wordTrace_append hprefix tailTrace_1169086
  have hstable : (prefixWord ++ tailWord_1169086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169086).length < 2 ^ (prefixWord ++ tailWord_1169086).sum := by decide
  have hdescent : baseEnd_1169086 < baseStart_1169086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169114 : List Nat := [3, 1, 1, 2, 2, 3, 9]
def baseStart_1169114 : Nat := 118140960795 + 1169114 * 2 ^ 59
def prefixEnd_1169114 : Nat := 4983230072969 + 3 ^ 40 * 1169114 * 2
def baseEnd_1169114 : Nat := 29645304785216991101153

theorem tailTrace_1169114 : CollatzResearch.WordTrace tailWord_1169114 prefixEnd_1169114 29645304785216991101153 := by
  unfold tailWord_1169114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10660272671626780404966599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28427393791004747746577597 10660272671626780404966599)
  ·
    refine ⟨15990409007440170607449899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10660272671626780404966599 15990409007440170607449899)
    ·
      refine ⟨23985613511160255911174849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15990409007440170607449899 23985613511160255911174849)
      ·
        refine ⟨17989210133370191933381137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23985613511160255911174849 17989210133370191933381137)
        ·
          refine ⟨13491907600027643950035853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17989210133370191933381137 13491907600027643950035853)
          ·
            refine ⟨5059465350010366481263445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13491907600027643950035853 5059465350010366481263445)
            ·
              refine ⟨29645304785216991101153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5059465350010366481263445 29645304785216991101153)
              ·
                rfl

theorem cell21_1169114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 9].length) (baseStart_1169114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169114 prefixEnd_1169114 := by exact prefixLift 1169114
  have htrace : WordTrace (prefixWord ++ tailWord_1169114) baseStart_1169114 baseEnd_1169114 := by
    simpa [prefixWord, tailWord_1169114, baseEnd_1169114] using wordTrace_append hprefix tailTrace_1169114
  have hstable : (prefixWord ++ tailWord_1169114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169114).length < 2 ^ (prefixWord ++ tailWord_1169114).sum := by decide
  have hdescent : baseEnd_1169114 < baseStart_1169114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169165 : List Nat := [1, 7, 2, 1, 10]
def baseStart_1169165 : Nat := 118140960795 + 1169165 * 2 ^ 59
def prefixEnd_1169165 : Nat := 4983230072969 + 3 ^ 40 * 1169165 * 2
def baseEnd_1169165 : Nat := 3294066443972693389633

theorem tailTrace_1169165 : CollatzResearch.WordTrace tailWord_1169165 prefixEnd_1169165 3294066443972693389633 := by
  unfold tailWord_1169165
  simp only [CollatzResearch.WordTrace]
  refine ⟨42642950809322357329972949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28428633872881571553315299 42642950809322357329972949)
  ·
    refine ⟨999444159593492749921241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 42642950809322357329972949 999444159593492749921241)
    ·
      refine ⟨749583119695119562440931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 999444159593492749921241 749583119695119562440931)
      ·
        refine ⟨1124374679542679343661397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749583119695119562440931 1124374679542679343661397)
        ·
          refine ⟨3294066443972693389633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1124374679542679343661397 3294066443972693389633)
          ·
            rfl

theorem cell21_1169165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 10].length) (baseStart_1169165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169165 prefixEnd_1169165 := by exact prefixLift 1169165
  have htrace : WordTrace (prefixWord ++ tailWord_1169165) baseStart_1169165 baseEnd_1169165 := by
    simpa [prefixWord, tailWord_1169165, baseEnd_1169165] using wordTrace_append hprefix tailTrace_1169165
  have hstable : (prefixWord ++ tailWord_1169165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169165).length < 2 ^ (prefixWord ++ tailWord_1169165).sum := by decide
  have hdescent : baseEnd_1169165 < baseStart_1169165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169176 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 4]
def baseStart_1169176 : Nat := 118140960795 + 1169176 * 2 ^ 59
def prefixEnd_1169176 : Nat := 4983230072969 + 3 ^ 40 * 1169176 * 2
def baseEnd_1169176 : Nat := 266821892311654589876917

theorem tailTrace_1169176 : CollatzResearch.WordTrace tailWord_1169176 prefixEnd_1169176 266821892311654589876917 := by
  unfold tailWord_1169176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21321676006141253104311691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28428901341521670805748921 21321676006141253104311691)
  ·
    refine ⟨31982514009211879656467537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21321676006141253104311691 31982514009211879656467537)
    ·
      refine ⟨23986885506908909742350653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31982514009211879656467537 23986885506908909742350653)
      ·
        refine ⟨8995082065090841153381495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23986885506908909742350653 8995082065090841153381495)
        ·
          refine ⟨13492623097636261730072243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8995082065090841153381495 13492623097636261730072243)
          ·
            refine ⟨20238934646454392595108365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13492623097636261730072243 20238934646454392595108365)
            ·
              refine ⟨7589600492420397223165637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20238934646454392595108365 7589600492420397223165637)
              ·
                refine ⟨1423050092328824479343557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7589600492420397223165637 1423050092328824479343557)
                ·
                  refine ⟨266821892311654589876917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1423050092328824479343557 266821892311654589876917)
                  ·
                    rfl

theorem cell21_1169176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_1169176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169176 prefixEnd_1169176 := by exact prefixLift 1169176
  have htrace : WordTrace (prefixWord ++ tailWord_1169176) baseStart_1169176 baseEnd_1169176 := by
    simpa [prefixWord, tailWord_1169176, baseEnd_1169176] using wordTrace_append hprefix tailTrace_1169176
  have hstable : (prefixWord ++ tailWord_1169176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169176).length < 2 ^ (prefixWord ++ tailWord_1169176).sum := by decide
  have hdescent : baseEnd_1169176 < baseStart_1169176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169182 : List Nat := [4, 3, 2, 2, 1, 2, 1, 6]
def baseStart_1169182 : Nat := 118140960795 + 1169182 * 2 ^ 59
def prefixEnd_1169182 : Nat := 4983230072969 + 3 ^ 40 * 1169182 * 2
def baseEnd_1169182 : Nat := 88941087197799970925635

theorem tailTrace_1169182 : CollatzResearch.WordTrace tailWord_1169182 prefixEnd_1169182 88941087197799970925635 := by
  unfold tailWord_1169182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5330446356282596154167725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28429047233507179488894533 5330446356282596154167725)
  ·
    refine ⟨1998917383605973557812897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5330446356282596154167725 1998917383605973557812897)
    ·
      refine ⟨1499188037704480168359673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1998917383605973557812897 1499188037704480168359673)
      ·
        refine ⟨1124391028278360126269755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1499188037704480168359673 1124391028278360126269755)
        ·
          refine ⟨1686586542417540189404633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124391028278360126269755 1686586542417540189404633)
          ·
            refine ⟨1264939906813155142053475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686586542417540189404633 1264939906813155142053475)
            ·
              refine ⟨1897409860219732713080213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264939906813155142053475 1897409860219732713080213)
              ·
                refine ⟨88941087197799970925635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1897409860219732713080213 88941087197799970925635)
                ·
                  rfl

theorem cell21_1169182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_1169182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169182 prefixEnd_1169182 := by exact prefixLift 1169182
  have htrace : WordTrace (prefixWord ++ tailWord_1169182) baseStart_1169182 baseEnd_1169182 := by
    simpa [prefixWord, tailWord_1169182, baseEnd_1169182] using wordTrace_append hprefix tailTrace_1169182
  have hstable : (prefixWord ++ tailWord_1169182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169182).length < 2 ^ (prefixWord ++ tailWord_1169182).sum := by decide
  have hdescent : baseEnd_1169182 < baseStart_1169182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169258 : List Nat := [3, 1, 3, 4, 2, 1, 2, 5]
def baseStart_1169258 : Nat := 118140960795 + 1169258 * 2 ^ 59
def prefixEnd_1169258 : Nat := 4983230072969 + 3 ^ 40 * 1169258 * 2
def baseEnd_1169258 : Nat := 88946868609613556503361

theorem tailTrace_1169258 : CollatzResearch.WordTrace tailWord_1169258 prefixEnd_1169258 88946868609613556503361 := by
  unfold tailWord_1169258
  simp only [CollatzResearch.WordTrace]
  refine ⟨10661585699496358553277107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28430895198656956142072285 10661585699496358553277107)
  ·
    refine ⟨15992378549244537829915661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10661585699496358553277107 15992378549244537829915661)
    ·
      refine ⟨5997141955966701686218373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15992378549244537829915661 5997141955966701686218373)
      ·
        refine ⟨1124464116743756566165945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5997141955966701686218373 1124464116743756566165945)
        ·
          refine ⟨843348087557817424624459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1124464116743756566165945 843348087557817424624459)
          ·
            refine ⟨1265022131336726136936689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843348087557817424624459 1265022131336726136936689)
            ·
              refine ⟨948766598502544602702517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265022131336726136936689 948766598502544602702517)
              ·
                refine ⟨88946868609613556503361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 948766598502544602702517 88946868609613556503361)
                ·
                  rfl

theorem cell21_1169258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_1169258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169258 prefixEnd_1169258 := by exact prefixLift 1169258
  have htrace : WordTrace (prefixWord ++ tailWord_1169258) baseStart_1169258 baseEnd_1169258 := by
    simpa [prefixWord, tailWord_1169258, baseEnd_1169258] using wordTrace_append hprefix tailTrace_1169258
  have hstable : (prefixWord ++ tailWord_1169258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169258).length < 2 ^ (prefixWord ++ tailWord_1169258).sum := by decide
  have hdescent : baseEnd_1169258 < baseStart_1169258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169297 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 5]
def baseStart_1169297 : Nat := 118140960795 + 1169297 * 2 ^ 59
def prefixEnd_1169297 : Nat := 4983230072969 + 3 ^ 40 * 1169297 * 2
def baseEnd_1169297 : Nat := 266849506160185268360003

theorem tailTrace_1169297 : CollatzResearch.WordTrace tailWord_1169297 prefixEnd_1169297 266849506160185268360003 := by
  unfold tailWord_1169297
  simp only [CollatzResearch.WordTrace]
  refine ⟨42647765244844143873778145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28431843496562762582518763 42647765244844143873778145)
  ·
    refine ⟨31985823933633107905333609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42647765244844143873778145 31985823933633107905333609)
    ·
      refine ⟨23989367950224830929000207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31985823933633107905333609 23989367950224830929000207)
      ·
        refine ⟨35984051925337246393500311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23989367950224830929000207 35984051925337246393500311)
        ·
          refine ⟨53976077888005869590250467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35984051925337246393500311 53976077888005869590250467)
          ·
            refine ⟨80964116832008804385375701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53976077888005869590250467 80964116832008804385375701)
            ·
              refine ⟨1897596488250206352782243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 80964116832008804385375701 1897596488250206352782243)
              ·
                refine ⟨2846394732375309529173365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1897596488250206352782243 2846394732375309529173365)
                ·
                  refine ⟨266849506160185268360003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2846394732375309529173365 266849506160185268360003)
                  ·
                    rfl

theorem cell21_1169297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_1169297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169297 prefixEnd_1169297 := by exact prefixLift 1169297
  have htrace : WordTrace (prefixWord ++ tailWord_1169297) baseStart_1169297 baseEnd_1169297 := by
    simpa [prefixWord, tailWord_1169297, baseEnd_1169297] using wordTrace_append hprefix tailTrace_1169297
  have hstable : (prefixWord ++ tailWord_1169297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169297).length < 2 ^ (prefixWord ++ tailWord_1169297).sum := by decide
  have hdescent : baseEnd_1169297 < baseStart_1169297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169342 : List Nat := [4, 2, 1, 1, 1, 12]
def baseStart_1169342 : Nat := 118140960795 + 1169342 * 2 ^ 59
def prefixEnd_1169342 : Nat := 4983230072969 + 3 ^ 40 * 1169342 * 2
def baseEnd_1169342 : Nat := 9883695399010192226293

theorem tailTrace_1169342 : CollatzResearch.WordTrace tailWord_1169342 prefixEnd_1169342 9883695399010192226293 := by
  unfold tailWord_1169342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5331175816210139569895785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28432937686454077706110853 5331175816210139569895785)
  ·
    refine ⟨3998381862157604677421839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5331175816210139569895785 3998381862157604677421839)
    ·
      refine ⟨5997572793236407016132759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3998381862157604677421839 5997572793236407016132759)
      ·
        refine ⟨8996359189854610524199139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5997572793236407016132759 8996359189854610524199139)
        ·
          refine ⟨13494538784781915786298709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8996359189854610524199139 13494538784781915786298709)
          ·
            refine ⟨9883695399010192226293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13494538784781915786298709 9883695399010192226293)
            ·
              rfl

theorem cell21_1169342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 12].length) (baseStart_1169342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169342 prefixEnd_1169342 := by exact prefixLift 1169342
  have htrace : WordTrace (prefixWord ++ tailWord_1169342) baseStart_1169342 baseEnd_1169342 := by
    simpa [prefixWord, tailWord_1169342, baseEnd_1169342] using wordTrace_append hprefix tailTrace_1169342
  have hstable : (prefixWord ++ tailWord_1169342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169342).length < 2 ^ (prefixWord ++ tailWord_1169342).sum := by decide
  have hdescent : baseEnd_1169342 < baseStart_1169342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169463 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 6]
def baseStart_1169463 : Nat := 118140960795 + 1169463 * 2 ^ 59
def prefixEnd_1169463 : Nat := 4983230072969 + 3 ^ 40 * 1169463 * 2
def baseEnd_1169463 : Nat := 266887389621805868592997

theorem tailTrace_1169463 : CollatzResearch.WordTrace tailWord_1169463 prefixEnd_1169463 266887389621805868592997 := by
  unfold tailWord_1169463
  simp only [CollatzResearch.WordTrace]
  refine ⟨42653819762242754224321043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28435879841495169482880695 42653819762242754224321043)
  ·
    refine ⟨63980729643364131336481565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42653819762242754224321043 63980729643364131336481565)
    ·
      refine ⟨23992773616261549251180587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63980729643364131336481565 23992773616261549251180587)
      ·
        refine ⟨35989160424392323876770881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23992773616261549251180587 35989160424392323876770881)
        ·
          refine ⟨26991870318294242907578161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35989160424392323876770881 26991870318294242907578161)
          ·
            refine ⟨20243902738720682180683621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26991870318294242907578161 20243902738720682180683621)
            ·
              refine ⟨3795731763510127908878179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20243902738720682180683621 3795731763510127908878179)
              ·
                refine ⟨5693597645265191863317269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795731763510127908878179 5693597645265191863317269)
                ·
                  refine ⟨266887389621805868592997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5693597645265191863317269 266887389621805868592997)
                  ·
                    rfl

theorem cell21_1169463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_1169463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169463 prefixEnd_1169463 := by exact prefixLift 1169463
  have htrace : WordTrace (prefixWord ++ tailWord_1169463) baseStart_1169463 baseEnd_1169463 := by
    simpa [prefixWord, tailWord_1169463, baseEnd_1169463] using wordTrace_append hprefix tailTrace_1169463
  have hstable : (prefixWord ++ tailWord_1169463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169463).length < 2 ^ (prefixWord ++ tailWord_1169463).sum := by decide
  have hdescent : baseEnd_1169463 < baseStart_1169463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169559 : List Nat := [1, 1, 3, 3, 4, 1, 2, 3, 3]
def baseStart_1169559 : Nat := 118140960795 + 1169559 * 2 ^ 59
def prefixEnd_1169559 : Nat := 4983230072969 + 3 ^ 40 * 1169559 * 2
def baseEnd_1169559 : Nat := 266909298129731034992801

theorem tailTrace_1169559 : CollatzResearch.WordTrace tailWord_1169559 prefixEnd_1169559 266909298129731034992801 := by
  unfold tailWord_1169559
  simp only [CollatzResearch.WordTrace]
  refine ⟨42657321169894962619815731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28438214113263308413210487 42657321169894962619815731)
  ·
    refine ⟨63985981754842443929723597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42657321169894962619815731 63985981754842443929723597)
    ·
      refine ⟨23994743158065916473646349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63985981754842443929723597 23994743158065916473646349)
      ·
        refine ⟨8998028684274718677617381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23994743158065916473646349 8998028684274718677617381)
        ·
          refine ⟨1687130378301509752053259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8998028684274718677617381 1687130378301509752053259)
          ·
            refine ⟨2530695567452264628079889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687130378301509752053259 2530695567452264628079889)
            ·
              refine ⟨1898021675589198471059917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2530695567452264628079889 1898021675589198471059917)
              ·
                refine ⟨711758128345949426647469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898021675589198471059917 711758128345949426647469)
                ·
                  refine ⟨266909298129731034992801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711758128345949426647469 266909298129731034992801)
                  ·
                    rfl

theorem cell21_1169559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 3].length) (baseStart_1169559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169559 prefixEnd_1169559 := by exact prefixLift 1169559
  have htrace : WordTrace (prefixWord ++ tailWord_1169559) baseStart_1169559 baseEnd_1169559 := by
    simpa [prefixWord, tailWord_1169559, baseEnd_1169559] using wordTrace_append hprefix tailTrace_1169559
  have hstable : (prefixWord ++ tailWord_1169559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169559).length < 2 ^ (prefixWord ++ tailWord_1169559).sum := by decide
  have hdescent : baseEnd_1169559 < baseStart_1169559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169604 : List Nat := [2, 3, 3, 1, 2, 3, 2, 5]
def baseStart_1169604 : Nat := 118140960795 + 1169604 * 2 ^ 59
def prefixEnd_1169604 : Nat := 4983230072969 + 3 ^ 40 * 1169604 * 2
def baseEnd_1169604 : Nat := 88973189247606985580903

theorem tailTrace_1169604 : CollatzResearch.WordTrace tailWord_1169604 prefixEnd_1169604 88973189247606985580903 := by
  unfold tailWord_1169604
  simp only [CollatzResearch.WordTrace]
  refine ⟨21329481227365967652601933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28439308303154623536802577 21329481227365967652601933)
  ·
    refine ⟨7998555460262237869725725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21329481227365967652601933 7998555460262237869725725)
    ·
      refine ⟨2999458297598339201147147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7998555460262237869725725 2999458297598339201147147)
      ·
        refine ⟨4499187446397508801720721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2999458297598339201147147 4499187446397508801720721)
        ·
          refine ⟨3374390584798131601290541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4499187446397508801720721 3374390584798131601290541)
          ·
            refine ⟨1265396469299299350483953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3374390584798131601290541 1265396469299299350483953)
            ·
              refine ⟨949047351974474512862965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265396469299299350483953 949047351974474512862965)
              ·
                refine ⟨88973189247606985580903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 949047351974474512862965 88973189247606985580903)
                ·
                  rfl

theorem cell21_1169604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_1169604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169604 prefixEnd_1169604 := by exact prefixLift 1169604
  have htrace : WordTrace (prefixWord ++ tailWord_1169604) baseStart_1169604 baseEnd_1169604 := by
    simpa [prefixWord, tailWord_1169604, baseEnd_1169604] using wordTrace_append hprefix tailTrace_1169604
  have hstable : (prefixWord ++ tailWord_1169604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169604).length < 2 ^ (prefixWord ++ tailWord_1169604).sum := by decide
  have hdescent : baseEnd_1169604 < baseStart_1169604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169635 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 5]
def baseStart_1169635 : Nat := 118140960795 + 1169635 * 2 ^ 59
def prefixEnd_1169635 : Nat := 4983230072969 + 3 ^ 40 * 1169635 * 2
def baseEnd_1169635 : Nat := 266926642365171791725979

theorem tailTrace_1169635 : CollatzResearch.WordTrace tailWord_1169635 prefixEnd_1169635 266926642365171791725979 := by
  unfold tailWord_1169635
  simp only [CollatzResearch.WordTrace]
  refine ⟨42660093117619627599582359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28440062078413085066388239 42660093117619627599582359)
  ·
    refine ⟨63990139676429441399373539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42660093117619627599582359 63990139676429441399373539)
    ·
      refine ⟨95985209514644162099060309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63990139676429441399373539 95985209514644162099060309)
      ·
        refine ⟨1124826673999736274598363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 95985209514644162099060309 1124826673999736274598363)
        ·
          refine ⟨1687240010999604411897545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124826673999736274598363 1687240010999604411897545)
          ·
            refine ⟨1265430008249703308923159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687240010999604411897545 1265430008249703308923159)
            ·
              refine ⟨1898145012374554963384739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265430008249703308923159 1898145012374554963384739)
              ·
                refine ⟨2847217518561832445077109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898145012374554963384739 2847217518561832445077109)
                ·
                  refine ⟨266926642365171791725979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2847217518561832445077109 266926642365171791725979)
                  ·
                    rfl

theorem cell21_1169635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 5].length) (baseStart_1169635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169635 prefixEnd_1169635 := by exact prefixLift 1169635
  have htrace : WordTrace (prefixWord ++ tailWord_1169635) baseStart_1169635 baseEnd_1169635 := by
    simpa [prefixWord, tailWord_1169635, baseEnd_1169635] using wordTrace_append hprefix tailTrace_1169635
  have hstable : (prefixWord ++ tailWord_1169635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169635).length < 2 ^ (prefixWord ++ tailWord_1169635).sum := by decide
  have hdescent : baseEnd_1169635 < baseStart_1169635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169691 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 4]
def baseStart_1169691 : Nat := 118140960795 + 1169691 * 2 ^ 59
def prefixEnd_1169691 : Nat := 4983230072969 + 3 ^ 40 * 1169691 * 2
def baseEnd_1169691 : Nat := 266939422328128138792531

theorem tailTrace_1169691 : CollatzResearch.WordTrace tailWord_1169691 prefixEnd_1169691 266939422328128138792531 := by
  unfold tailWord_1169691
  simp only [CollatzResearch.WordTrace]
  refine ⟨42662135605416749163620927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28441423736944499442413951 42662135605416749163620927)
  ·
    refine ⟨63993203408125123745431391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42662135605416749163620927 63993203408125123745431391)
    ·
      refine ⟨95989805112187685618147087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63993203408125123745431391 95989805112187685618147087)
      ·
        refine ⟨143984707668281528427220631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95989805112187685618147087 143984707668281528427220631)
        ·
          refine ⟨215977061502422292640830947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143984707668281528427220631 215977061502422292640830947)
          ·
            refine ⟨323965592253633438961246421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215977061502422292640830947 323965592253633438961246421)
            ·
              refine ⟨7592943568444533725654213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 323965592253633438961246421 7592943568444533725654213)
              ·
                refine ⟨1423676919083350073560165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7592943568444533725654213 1423676919083350073560165)
                ·
                  refine ⟨266939422328128138792531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1423676919083350073560165 266939422328128138792531)
                  ·
                    rfl

theorem cell21_1169691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 4].length) (baseStart_1169691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169691 prefixEnd_1169691 := by exact prefixLift 1169691
  have htrace : WordTrace (prefixWord ++ tailWord_1169691) baseStart_1169691 baseEnd_1169691 := by
    simpa [prefixWord, tailWord_1169691, baseEnd_1169691] using wordTrace_append hprefix tailTrace_1169691
  have hstable : (prefixWord ++ tailWord_1169691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169691).length < 2 ^ (prefixWord ++ tailWord_1169691).sum := by decide
  have hdescent : baseEnd_1169691 < baseStart_1169691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169863 : List Nat := [1, 1, 4, 1, 1, 6, 2, 2, 3]
def baseStart_1169863 : Nat := 118140960795 + 1169863 * 2 ^ 59
def prefixEnd_1169863 : Nat := 4983230072969 + 3 ^ 40 * 1169863 * 2
def baseEnd_1169863 : Nat := 266978675071494061925513

theorem tailTrace_1169863 : CollatzResearch.WordTrace tailWord_1169863 prefixEnd_1169863 266978675071494061925513 := by
  unfold tailWord_1169863
  simp only [CollatzResearch.WordTrace]
  refine ⟨42668408960793622538882243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28445605973862415025921495 42668408960793622538882243)
  ·
    refine ⟨64002613441190433808323365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42668408960793622538882243 64002613441190433808323365)
    ·
      refine ⟨12000490020223206339060631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64002613441190433808323365 12000490020223206339060631)
      ·
        refine ⟨18000735030334809508590947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12000490020223206339060631 18000735030334809508590947)
        ·
          refine ⟨27001102545502214262886421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18000735030334809508590947 27001102545502214262886421)
          ·
            refine ⟨1265676681820416293572801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27001102545502214262886421 1265676681820416293572801)
            ·
              refine ⟨949257511365312220179601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265676681820416293572801 949257511365312220179601)
              ·
                refine ⟨711943133523984165134701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 949257511365312220179601 711943133523984165134701)
                ·
                  refine ⟨266978675071494061925513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711943133523984165134701 266978675071494061925513)
                  ·
                    rfl

theorem cell21_1169863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 3].length) (baseStart_1169863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169863 prefixEnd_1169863 := by exact prefixLift 1169863
  have htrace : WordTrace (prefixWord ++ tailWord_1169863) baseStart_1169863 baseEnd_1169863 := by
    simpa [prefixWord, tailWord_1169863, baseEnd_1169863] using wordTrace_append hprefix tailTrace_1169863
  have hstable : (prefixWord ++ tailWord_1169863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169863).length < 2 ^ (prefixWord ++ tailWord_1169863).sum := by decide
  have hdescent : baseEnd_1169863 < baseStart_1169863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169888 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_1169888 : Nat := 118140960795 + 1169888 * 2 ^ 59
def prefixEnd_1169888 : Nat := 4983230072969 + 3 ^ 40 * 1169888 * 2
def baseEnd_1169888 : Nat := 266984380412099574008795

theorem tailTrace_1169888 : CollatzResearch.WordTrace tailWord_1169888 prefixEnd_1169888 266984380412099574008795 := by
  unfold tailWord_1169888
  simp only [CollatzResearch.WordTrace]
  refine ⟨21334660392851525904271159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28446213857135367872361545 21334660392851525904271159)
  ·
    refine ⟨32001990589277288856406739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21334660392851525904271159 32001990589277288856406739)
    ·
      refine ⟨48002985883915933284610109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32001990589277288856406739 48002985883915933284610109)
      ·
        refine ⟨18001119706468474981728791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48002985883915933284610109 18001119706468474981728791)
        ·
          refine ⟨27001679559702712472593187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18001119706468474981728791 27001679559702712472593187)
          ·
            refine ⟨40502519339554068708889781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27001679559702712472593187 40502519339554068708889781)
            ·
              refine ⟨3797111188083193941458417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40502519339554068708889781 3797111188083193941458417)
              ·
                refine ⟨2847833391062395456093813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3797111188083193941458417 2847833391062395456093813)
                ·
                  refine ⟨266984380412099574008795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2847833391062395456093813 266984380412099574008795)
                  ·
                    rfl

theorem cell21_1169888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_1169888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169888 prefixEnd_1169888 := by exact prefixLift 1169888
  have htrace : WordTrace (prefixWord ++ tailWord_1169888) baseStart_1169888 baseEnd_1169888 := by
    simpa [prefixWord, tailWord_1169888, baseEnd_1169888] using wordTrace_append hprefix tailTrace_1169888
  have hstable : (prefixWord ++ tailWord_1169888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169888).length < 2 ^ (prefixWord ++ tailWord_1169888).sum := by decide
  have hdescent : baseEnd_1169888 < baseStart_1169888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169891 : List Nat := [1, 1, 1, 6, 3, 1, 3, 5]
def baseStart_1169891 : Nat := 118140960795 + 1169891 * 2 ^ 59
def prefixEnd_1169891 : Nat := 4983230072969 + 3 ^ 40 * 1169891 * 2
def baseEnd_1169891 : Nat := 88995021684324078486263

theorem tailTrace_1169891 : CollatzResearch.WordTrace tailWord_1169891 prefixEnd_1169891 88995021684324078486263 := by
  unfold tailWord_1169891
  simp only [CollatzResearch.WordTrace]
  refine ⟨42669430204692183320901527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28446286803128122213934351 42669430204692183320901527)
  ·
    refine ⟨64004145307038274981352291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42669430204692183320901527 64004145307038274981352291)
    ·
      refine ⟨96006217960557412472028437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64004145307038274981352291 96006217960557412472028437)
      ·
        refine ⟨4500291466901128709626333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96006217960557412472028437 4500291466901128709626333)
        ·
          refine ⟨1687609300087923266109875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4500291466901128709626333 1687609300087923266109875)
          ·
            refine ⟨2531413950131884899164813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687609300087923266109875 2531413950131884899164813)
            ·
              refine ⟨949280231299456837186805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2531413950131884899164813 949280231299456837186805)
              ·
                refine ⟨88995021684324078486263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 949280231299456837186805 88995021684324078486263)
                ·
                  rfl

theorem cell21_1169891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 5].length) (baseStart_1169891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169891 prefixEnd_1169891 := by exact prefixLift 1169891
  have htrace : WordTrace (prefixWord ++ tailWord_1169891) baseStart_1169891 baseEnd_1169891 := by
    simpa [prefixWord, tailWord_1169891, baseEnd_1169891] using wordTrace_append hprefix tailTrace_1169891
  have hstable : (prefixWord ++ tailWord_1169891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169891).length < 2 ^ (prefixWord ++ tailWord_1169891).sum := by decide
  have hdescent : baseEnd_1169891 < baseStart_1169891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169956 : List Nat := [2, 3, 1, 5, 1, 2, 1, 3, 3]
def baseStart_1169956 : Nat := 118140960795 + 1169956 * 2 ^ 59
def prefixEnd_1169956 : Nat := 4983230072969 + 3 ^ 40 * 1169956 * 2
def baseEnd_1169956 : Nat := 266999898938546566875323

theorem tailTrace_1169956 : CollatzResearch.WordTrace tailWord_1169956 prefixEnd_1169956 266999898938546566875323 := by
  unfold tailWord_1169956
  simp only [CollatzResearch.WordTrace]
  refine ⟨21335900474728349711008861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28447867299637799614678481 21335900474728349711008861)
  ·
    refine ⟨8000962678023131141628323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21335900474728349711008861 8000962678023131141628323)
    ·
      refine ⟨12001444017034696712442485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8000962678023131141628323 12001444017034696712442485)
      ·
        refine ⟨1125135376597002816791483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12001444017034696712442485 1125135376597002816791483)
        ·
          refine ⟨1687703064895504225187225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125135376597002816791483 1687703064895504225187225)
          ·
            refine ⟨1265777298671628168890419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687703064895504225187225 1265777298671628168890419)
            ·
              refine ⟨1898665948007442253335629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265777298671628168890419 1898665948007442253335629)
              ·
                refine ⟨711999730502790845000861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898665948007442253335629 711999730502790845000861)
                ·
                  refine ⟨266999898938546566875323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711999730502790845000861 266999898938546566875323)
                  ·
                    rfl

theorem cell21_1169956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_1169956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169956 prefixEnd_1169956 := by exact prefixLift 1169956
  have htrace : WordTrace (prefixWord ++ tailWord_1169956) baseStart_1169956 baseEnd_1169956 := by
    simpa [prefixWord, tailWord_1169956, baseEnd_1169956] using wordTrace_append hprefix tailTrace_1169956
  have hstable : (prefixWord ++ tailWord_1169956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169956).length < 2 ^ (prefixWord ++ tailWord_1169956).sum := by decide
  have hdescent : baseEnd_1169956 < baseStart_1169956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169981 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 5]
def baseStart_1169981 : Nat := 118140960795 + 1169981 * 2 ^ 59
def prefixEnd_1169981 : Nat := 4983230072969 + 3 ^ 40 * 1169981 * 2
def baseEnd_1169981 : Nat := 267005604279152078958605

theorem tailTrace_1169981 : CollatzResearch.WordTrace tailWord_1169981 prefixEnd_1169981 267005604279152078958605 := by
  unfold tailWord_1169981
  simp only [CollatzResearch.WordTrace]
  refine ⟨42672712774366128691677797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28448475182910752461118531 42672712774366128691677797)
  ·
    refine ⟨8001133645193649129689587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42672712774366128691677797 8001133645193649129689587)
    ·
      refine ⟨12001700467790473694534381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8001133645193649129689587 12001700467790473694534381)
      ·
        refine ⟨4500637675421427635450393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12001700467790473694534381 4500637675421427635450393)
        ·
          refine ⟨3375478256566070726587795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4500637675421427635450393 3375478256566070726587795)
          ·
            refine ⟨5063217384849106089881693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375478256566070726587795 5063217384849106089881693)
            ·
              refine ⟨1898706519318414783705635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5063217384849106089881693 1898706519318414783705635)
              ·
                refine ⟨2848059778977622175558453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898706519318414783705635 2848059778977622175558453)
                ·
                  refine ⟨267005604279152078958605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2848059778977622175558453 267005604279152078958605)
                  ·
                    rfl

theorem cell21_1169981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_1169981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1169981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1169981 prefixEnd_1169981 := by exact prefixLift 1169981
  have htrace : WordTrace (prefixWord ++ tailWord_1169981) baseStart_1169981 baseEnd_1169981 := by
    simpa [prefixWord, tailWord_1169981, baseEnd_1169981] using wordTrace_append hprefix tailTrace_1169981
  have hstable : (prefixWord ++ tailWord_1169981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169981).length < 2 ^ (prefixWord ++ tailWord_1169981).sum := by decide
  have hdescent : baseEnd_1169981 < baseStart_1169981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170032 : List Nat := [2, 1, 1, 1, 8, 1, 2, 2, 3]
def baseStart_1170032 : Nat := 118140960795 + 1170032 * 2 ^ 59
def prefixEnd_1170032 : Nat := 4983230072969 + 3 ^ 40 * 1170032 * 2
def baseEnd_1170032 : Nat := 267017243173987323608501

theorem tailTrace_1170032 : CollatzResearch.WordTrace tailWord_1170032 prefixEnd_1170032 267017243173987323608501 := by
  unfold tailWord_1170032
  simp only [CollatzResearch.WordTrace]
  refine ⟨21337286448590682200892175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28449715264787576267856233 21337286448590682200892175)
  ·
    refine ⟨32005929672886023301338263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21337286448590682200892175 32005929672886023301338263)
    ·
      refine ⟨48008894509329034952007395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32005929672886023301338263 48008894509329034952007395)
      ·
        refine ⟨72013341763993552428011093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48008894509329034952007395 72013341763993552428011093)
        ·
          refine ⟨843906348796799442515755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 72013341763993552428011093 843906348796799442515755)
          ·
            refine ⟨1265859523195199163773633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843906348796799442515755 1265859523195199163773633)
            ·
              refine ⟨949394642396399372830225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265859523195199163773633 949394642396399372830225)
              ·
                refine ⟨712045981797299529622669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 949394642396399372830225 712045981797299529622669)
                ·
                  refine ⟨267017243173987323608501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712045981797299529622669 267017243173987323608501)
                  ·
                    rfl

theorem cell21_1170032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 3].length) (baseStart_1170032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170032 prefixEnd_1170032 := by exact prefixLift 1170032
  have htrace : WordTrace (prefixWord ++ tailWord_1170032) baseStart_1170032 baseEnd_1170032 := by
    simpa [prefixWord, tailWord_1170032, baseEnd_1170032] using wordTrace_append hprefix tailTrace_1170032
  have hstable : (prefixWord ++ tailWord_1170032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170032).length < 2 ^ (prefixWord ++ tailWord_1170032).sum := by decide
  have hdescent : baseEnd_1170032 < baseStart_1170032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170125 : List Nat := [1, 6, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1170125 : Nat := 118140960795 + 1170125 * 2 ^ 59
def prefixEnd_1170125 : Nat := 4983230072969 + 3 ^ 40 * 1170125 * 2
def baseEnd_1170125 : Nat := 267038467041039828558311

theorem tailTrace_1170125 : CollatzResearch.WordTrace tailWord_1170125 prefixEnd_1170125 267038467041039828558311 := by
  unfold tailWord_1170125
  simp only [CollatzResearch.WordTrace]
  refine ⟨42677964885844441284919829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28451976590562960856613219 42677964885844441284919829)
  ·
    refine ⟨2000529604023958185230617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42677964885844441284919829 2000529604023958185230617)
    ·
      refine ⟨1500397203017968638922963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2000529604023958185230617 1500397203017968638922963)
      ·
        refine ⟨2250595804526952958384445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1500397203017968638922963 2250595804526952958384445)
        ·
          refine ⟨843973426697607359394167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2250595804526952958384445 843973426697607359394167)
          ·
            refine ⟨1265960140046411039091251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843973426697607359394167 1265960140046411039091251)
            ·
              refine ⟨1898940210069616558636877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265960140046411039091251 1898940210069616558636877)
              ·
                refine ⟨712102578776106209488829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898940210069616558636877 712102578776106209488829)
                ·
                  refine ⟨267038467041039828558311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712102578776106209488829 267038467041039828558311)
                  ·
                    rfl

theorem cell21_1170125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1170125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170125 prefixEnd_1170125 := by exact prefixLift 1170125
  have htrace : WordTrace (prefixWord ++ tailWord_1170125) baseStart_1170125 baseEnd_1170125 := by
    simpa [prefixWord, tailWord_1170125, baseEnd_1170125] using wordTrace_append hprefix tailTrace_1170125
  have hstable : (prefixWord ++ tailWord_1170125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170125).length < 2 ^ (prefixWord ++ tailWord_1170125).sum := by decide
  have hdescent : baseEnd_1170125 < baseStart_1170125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170147 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 6]
def baseStart_1170147 : Nat := 118140960795 + 1170147 * 2 ^ 59
def prefixEnd_1170147 : Nat := 4983230072969 + 3 ^ 40 * 1170147 * 2
def baseEnd_1170147 : Nat := 267043487740772679191599

theorem tailTrace_1170147 : CollatzResearch.WordTrace tailWord_1170147 prefixEnd_1170147 267043487740772679191599 := by
  unfold tailWord_1170147
  simp only [CollatzResearch.WordTrace]
  refine ⟨42678767291764739042220695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28452511527843159361480463 42678767291764739042220695)
  ·
    refine ⟨64018150937647108563331043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42678767291764739042220695 64018150937647108563331043)
    ·
      refine ⟨96027226406470662844996565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64018150937647108563331043 96027226406470662844996565)
      ·
        refine ⟨2250638118901656160429607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 96027226406470662844996565 2250638118901656160429607)
        ·
          refine ⟨3375957178352484240644411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250638118901656160429607 3375957178352484240644411)
          ·
            refine ⟨5063935767528726360966617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375957178352484240644411 5063935767528726360966617)
            ·
              refine ⟨3797951825646544770724963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5063935767528726360966617 3797951825646544770724963)
              ·
                refine ⟨5696927738469817156087445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3797951825646544770724963 5696927738469817156087445)
                ·
                  refine ⟨267043487740772679191599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5696927738469817156087445 267043487740772679191599)
                  ·
                    rfl

theorem cell21_1170147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 6].length) (baseStart_1170147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170147 prefixEnd_1170147 := by exact prefixLift 1170147
  have htrace : WordTrace (prefixWord ++ tailWord_1170147) baseStart_1170147 baseEnd_1170147 := by
    simpa [prefixWord, tailWord_1170147, baseEnd_1170147] using wordTrace_append hprefix tailTrace_1170147
  have hstable : (prefixWord ++ tailWord_1170147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170147).length < 2 ^ (prefixWord ++ tailWord_1170147).sum := by decide
  have hdescent : baseEnd_1170147 < baseStart_1170147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170161 : List Nat := [1, 2, 2, 2, 2, 2, 4, 6]
def baseStart_1170161 : Nat := 118140960795 + 1170161 * 2 ^ 59
def prefixEnd_1170161 : Nat := 4983230072969 + 3 ^ 40 * 1170161 * 2
def baseEnd_1170161 : Nat := 89015560910503921986079

theorem tailTrace_1170161 : CollatzResearch.WordTrace tailWord_1170161 prefixEnd_1170161 89015560910503921986079 := by
  unfold tailWord_1170161
  simp only [CollatzResearch.WordTrace]
  refine ⟨42679277913714019433230337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28452851942476012955486891 42679277913714019433230337)
  ·
    refine ⟨32009458435285514574922753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42679277913714019433230337 32009458435285514574922753)
    ·
      refine ⟨24007093826464135931192065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32009458435285514574922753 24007093826464135931192065)
      ·
        refine ⟨18005320369848101948394049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24007093826464135931192065 18005320369848101948394049)
        ·
          refine ⟨13503990277386076461295537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18005320369848101948394049 13503990277386076461295537)
          ·
            refine ⟨10127992708039557345971653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13503990277386076461295537 10127992708039557345971653)
            ·
              refine ⟨1898998632757417002369685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10127992708039557345971653 1898998632757417002369685)
              ·
                refine ⟨89015560910503921986079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1898998632757417002369685 89015560910503921986079)
                ·
                  rfl

theorem cell21_1170161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 6].length) (baseStart_1170161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170161 prefixEnd_1170161 := by exact prefixLift 1170161
  have htrace : WordTrace (prefixWord ++ tailWord_1170161) baseStart_1170161 baseEnd_1170161 := by
    simpa [prefixWord, tailWord_1170161, baseEnd_1170161] using wordTrace_append hprefix tailTrace_1170161
  have hstable : (prefixWord ++ tailWord_1170161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170161).length < 2 ^ (prefixWord ++ tailWord_1170161).sum := by decide
  have hdescent : baseEnd_1170161 < baseStart_1170161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170175 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 7]
def baseStart_1170175 : Nat := 118140960795 + 1170175 * 2 ^ 59
def prefixEnd_1170175 : Nat := 4983230072969 + 3 ^ 40 * 1170175 * 2
def baseEnd_1170175 : Nat := 267049877722250852724875

theorem tailTrace_1170175 : CollatzResearch.WordTrace tailWord_1170175 prefixEnd_1170175 267049877722250852724875 := by
  unfold tailWord_1170175
  simp only [CollatzResearch.WordTrace]
  refine ⟨42679788535663299824239979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28453192357108866549493319 42679788535663299824239979)
  ·
    refine ⟨64019682803494949736359969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42679788535663299824239979 64019682803494949736359969)
    ·
      refine ⟨48014762102621212302269977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64019682803494949736359969 48014762102621212302269977)
      ·
        refine ⟨36011071576965909226702483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48014762102621212302269977 36011071576965909226702483)
        ·
          refine ⟨54016607365448863840053725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36011071576965909226702483 54016607365448863840053725)
          ·
            refine ⟨20256227762043323940020147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54016607365448863840053725 20256227762043323940020147)
            ·
              refine ⟨30384341643064985910030221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20256227762043323940020147 30384341643064985910030221)
              ·
                refine ⟨11394128116149369716261333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30384341643064985910030221 11394128116149369716261333)
                ·
                  refine ⟨267049877722250852724875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11394128116149369716261333 267049877722250852724875)
                  ·
                    rfl

theorem cell21_1170175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_1170175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170175 prefixEnd_1170175 := by exact prefixLift 1170175
  have htrace : WordTrace (prefixWord ++ tailWord_1170175) baseStart_1170175 baseEnd_1170175 := by
    simpa [prefixWord, tailWord_1170175, baseEnd_1170175] using wordTrace_append hprefix tailTrace_1170175
  have hstable : (prefixWord ++ tailWord_1170175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170175).length < 2 ^ (prefixWord ++ tailWord_1170175).sum := by decide
  have hdescent : baseEnd_1170175 < baseStart_1170175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170178 : List Nat := [3, 4, 1, 1, 1, 2, 2, 7]
def baseStart_1170178 : Nat := 118140960795 + 1170178 * 2 ^ 59
def prefixEnd_1170178 : Nat := 4983230072969 + 3 ^ 40 * 1170178 * 2
def baseEnd_1170178 : Nat := 89016854121041171391623

theorem tailTrace_1170178 : CollatzResearch.WordTrace tailWord_1170178 prefixEnd_1170178 89016854121041171391623 := by
  unfold tailWord_1170178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10669974488663107834149797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28453265303101620891066125 10669974488663107834149797)
  ·
    refine ⟨2000620216624332718903087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10669974488663107834149797 2000620216624332718903087)
    ·
      refine ⟨3000930324936499078354631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2000620216624332718903087 3000930324936499078354631)
      ·
        refine ⟨4501395487404748617531947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000930324936499078354631 4501395487404748617531947)
        ·
          refine ⟨6752093231107122926297921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4501395487404748617531947 6752093231107122926297921)
          ·
            refine ⟨5064069923330342194723441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6752093231107122926297921 5064069923330342194723441)
            ·
              refine ⟨3798052442497756646042581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5064069923330342194723441 3798052442497756646042581)
              ·
                refine ⟨89016854121041171391623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3798052442497756646042581 89016854121041171391623)
                ·
                  rfl

theorem cell21_1170178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_1170178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170178 prefixEnd_1170178 := by exact prefixLift 1170178
  have htrace : WordTrace (prefixWord ++ tailWord_1170178) baseStart_1170178 baseEnd_1170178 := by
    simpa [prefixWord, tailWord_1170178, baseEnd_1170178] using wordTrace_append hprefix tailTrace_1170178
  have hstable : (prefixWord ++ tailWord_1170178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170178).length < 2 ^ (prefixWord ++ tailWord_1170178).sum := by decide
  have hdescent : baseEnd_1170178 < baseStart_1170178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170209 : List Nat := [1, 2, 3, 2, 1, 2, 3, 4, 3]
def baseStart_1170209 : Nat := 118140960795 + 1170209 * 2 ^ 59
def prefixEnd_1170209 : Nat := 4983230072969 + 3 ^ 40 * 1170209 * 2
def baseEnd_1170209 : Nat := 267057636985474349158139

theorem tailTrace_1170209 : CollatzResearch.WordTrace tailWord_1170209 prefixEnd_1170209 267057636985474349158139 := by
  unfold tailWord_1170209
  simp only [CollatzResearch.WordTrace]
  refine ⟨42681028617540123630977681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28454019078360082420651787 42681028617540123630977681)
  ·
    refine ⟨32010771463155092723233261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42681028617540123630977681 32010771463155092723233261)
    ·
      refine ⟨12004039298683159771212473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32010771463155092723233261 12004039298683159771212473)
      ·
        refine ⟨9003029474012369828409355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12004039298683159771212473 9003029474012369828409355)
        ·
          refine ⟨13504544211018554742614033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9003029474012369828409355 13504544211018554742614033)
          ·
            refine ⟨10128408158263916056960525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13504544211018554742614033 10128408158263916056960525)
            ·
              refine ⟨3798153059348968521360197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10128408158263916056960525 3798153059348968521360197)
              ·
                refine ⟨712153698627931597755037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3798153059348968521360197 712153698627931597755037)
                ·
                  refine ⟨267057636985474349158139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712153698627931597755037 267057636985474349158139)
                  ·
                    rfl

theorem cell21_1170209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 3].length) (baseStart_1170209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170209 prefixEnd_1170209 := by exact prefixLift 1170209
  have htrace : WordTrace (prefixWord ++ tailWord_1170209) baseStart_1170209 baseEnd_1170209 := by
    simpa [prefixWord, tailWord_1170209, baseEnd_1170209] using wordTrace_append hprefix tailTrace_1170209
  have hstable : (prefixWord ++ tailWord_1170209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170209).length < 2 ^ (prefixWord ++ tailWord_1170209).sum := by decide
  have hdescent : baseEnd_1170209 < baseStart_1170209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170257 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 4]
def baseStart_1170257 : Nat := 118140960795 + 1170257 * 2 ^ 59
def prefixEnd_1170257 : Nat := 4983230072969 + 3 ^ 40 * 1170257 * 2
def baseEnd_1170257 : Nat := 267068591239436932358041

theorem tailTrace_1170257 : CollatzResearch.WordTrace tailWord_1170257 prefixEnd_1170257 267068591239436932358041 := by
  unfold tailWord_1170257
  simp only [CollatzResearch.WordTrace]
  refine ⟨42682779321366227828725025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28455186214244151885816683 42682779321366227828725025)
  ·
    refine ⟨32012084491024670871543769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42682779321366227828725025 32012084491024670871543769)
    ·
      refine ⟨24009063368268503153657827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32012084491024670871543769 24009063368268503153657827)
      ·
        refine ⟨36013595052402754730486741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24009063368268503153657827 36013595052402754730486741)
        ·
          refine ⟨844068634040689563995783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 36013595052402754730486741 844068634040689563995783)
          ·
            refine ⟨1266102951061034345993675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844068634040689563995783 1266102951061034345993675)
            ·
              refine ⟨1899154426591551518990513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266102951061034345993675 1899154426591551518990513)
              ·
                refine ⟨1424365819943663639242885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899154426591551518990513 1424365819943663639242885)
                ·
                  refine ⟨267068591239436932358041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1424365819943663639242885 267068591239436932358041)
                  ·
                    rfl

theorem cell21_1170257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 4].length) (baseStart_1170257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170257 prefixEnd_1170257 := by exact prefixLift 1170257
  have htrace : WordTrace (prefixWord ++ tailWord_1170257) baseStart_1170257 baseEnd_1170257 := by
    simpa [prefixWord, tailWord_1170257, baseEnd_1170257] using wordTrace_append hprefix tailTrace_1170257
  have hstable : (prefixWord ++ tailWord_1170257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170257).length < 2 ^ (prefixWord ++ tailWord_1170257).sum := by decide
  have hdescent : baseEnd_1170257 < baseStart_1170257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170313 : List Nat := [1, 2, 1, 1, 5, 4, 7]
def baseStart_1170313 : Nat := 118140960795 + 1170313 * 2 ^ 59
def prefixEnd_1170313 : Nat := 4983230072969 + 3 ^ 40 * 1170313 * 2
def baseEnd_1170313 : Nat := 29675707911377031047177

theorem tailTrace_1170313 : CollatzResearch.WordTrace tailWord_1170313 prefixEnd_1170313 29675707911377031047177 := by
  unfold tailWord_1170313
  simp only [CollatzResearch.WordTrace]
  refine ⟨42684821809163349392763593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28456547872775566261842395 42684821809163349392763593)
  ·
    refine ⟨32013616356872512044572695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42684821809163349392763593 32013616356872512044572695)
    ·
      refine ⟨48020424535308768066859043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32013616356872512044572695 48020424535308768066859043)
      ·
        refine ⟨72030636802963152100288565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48020424535308768066859043 72030636802963152100288565)
        ·
          refine ⟨6752872200277795509402053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72030636802963152100288565 6752872200277795509402053)
          ·
            refine ⟨1266163537552086658012885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6752872200277795509402053 1266163537552086658012885)
            ·
              refine ⟨29675707911377031047177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1266163537552086658012885 29675707911377031047177)
              ·
                rfl

theorem cell21_1170313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 7].length) (baseStart_1170313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170313 prefixEnd_1170313 := by exact prefixLift 1170313
  have htrace : WordTrace (prefixWord ++ tailWord_1170313) baseStart_1170313 baseEnd_1170313 := by
    simpa [prefixWord, tailWord_1170313, baseEnd_1170313] using wordTrace_append hprefix tailTrace_1170313
  have hstable : (prefixWord ++ tailWord_1170313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170313).length < 2 ^ (prefixWord ++ tailWord_1170313).sum := by decide
  have hdescent : baseEnd_1170313 < baseStart_1170313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170330 : List Nat := [3, 1, 1, 4, 3, 1, 2, 6]
def baseStart_1170330 : Nat := 118140960795 + 1170330 * 2 ^ 59
def prefixEnd_1170330 : Nat := 4983230072969 + 3 ^ 40 * 1170330 * 2
def baseEnd_1170330 : Nat := 89028416944668342547075

theorem tailTrace_1170330 : CollatzResearch.WordTrace tailWord_1170330 prefixEnd_1170330 89028416944668342547075 := by
  unfold tailWord_1170330
  simp only [CollatzResearch.WordTrace]
  refine ⟨10671360462525440324033111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28456961233401174197421629 10671360462525440324033111)
  ·
    refine ⟨16007040693788160486049667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10671360462525440324033111 16007040693788160486049667)
    ·
      refine ⟨24010561040682240729074501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16007040693788160486049667 24010561040682240729074501)
      ·
        refine ⟨4501980195127920136701469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24010561040682240729074501 4501980195127920136701469)
        ·
          refine ⟨1688242573172970051263051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4501980195127920136701469 1688242573172970051263051)
          ·
            refine ⟨2532363859759455076894577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688242573172970051263051 2532363859759455076894577)
            ·
              refine ⟨1899272894819591307670933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2532363859759455076894577 1899272894819591307670933)
              ·
                refine ⟨89028416944668342547075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1899272894819591307670933 89028416944668342547075)
                ·
                  rfl

theorem cell21_1170330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_1170330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170330 prefixEnd_1170330 := by exact prefixLift 1170330
  have htrace : WordTrace (prefixWord ++ tailWord_1170330) baseStart_1170330 baseEnd_1170330 := by
    simpa [prefixWord, tailWord_1170330, baseEnd_1170330] using wordTrace_append hprefix tailTrace_1170330
  have hstable : (prefixWord ++ tailWord_1170330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170330).length < 2 ^ (prefixWord ++ tailWord_1170330).sum := by decide
  have hdescent : baseEnd_1170330 < baseStart_1170330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170381 : List Nat := [1, 6, 3, 1, 1, 2, 1, 6]
def baseStart_1170381 : Nat := 118140960795 + 1170381 * 2 ^ 59
def prefixEnd_1170381 : Nat := 4983230072969 + 3 ^ 40 * 1170381 * 2
def baseEnd_1170381 : Nat := 89032296576280090763707

theorem tailTrace_1170381 : CollatzResearch.WordTrace tailWord_1170381 prefixEnd_1170381 89032296576280090763707 := by
  unfold tailWord_1170381
  simp only [CollatzResearch.WordTrace]
  refine ⟨42687301972916997006238997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28458201315277998004159331 42687301972916997006238997)
  ·
    refine ⟨2000967279980484234667453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42687301972916997006238997 2000967279980484234667453)
    ·
      refine ⟨750362729992681588000295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2000967279980484234667453 750362729992681588000295)
      ·
        refine ⟨1125544094989022382000443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 750362729992681588000295 1125544094989022382000443)
        ·
          refine ⟨1688316142483533573000665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125544094989022382000443 1688316142483533573000665)
          ·
            refine ⟨1266237106862650179750499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1688316142483533573000665 1266237106862650179750499)
            ·
              refine ⟨1899355660293975269625749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266237106862650179750499 1899355660293975269625749)
              ·
                refine ⟨89032296576280090763707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1899355660293975269625749 89032296576280090763707)
                ·
                  rfl

theorem cell21_1170381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 6].length) (baseStart_1170381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170381 prefixEnd_1170381 := by exact prefixLift 1170381
  have htrace : WordTrace (prefixWord ++ tailWord_1170381) baseStart_1170381 baseEnd_1170381 := by
    simpa [prefixWord, tailWord_1170381, baseEnd_1170381] using wordTrace_append hprefix tailTrace_1170381
  have hstable : (prefixWord ++ tailWord_1170381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170381).length < 2 ^ (prefixWord ++ tailWord_1170381).sum := by decide
  have hdescent : baseEnd_1170381 < baseStart_1170381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170465 : List Nat := [1, 2, 3, 2, 3, 2, 1, 7]
def baseStart_1170465 : Nat := 118140960795 + 1170465 * 2 ^ 59
def prefixEnd_1170465 : Nat := 4983230072969 + 3 ^ 40 * 1170465 * 2
def baseEnd_1170465 : Nat := 89038686557758264296983

theorem tailTrace_1170465 : CollatzResearch.WordTrace tailWord_1170465 prefixEnd_1170465 89038686557758264296983 := by
  unfold tailWord_1170465
  simp only [CollatzResearch.WordTrace]
  refine ⟨42690365704612679352296849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28460243803075119568197899 42690365704612679352296849)
  ·
    refine ⟨32017774278459509514222637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42690365704612679352296849 32017774278459509514222637)
    ·
      refine ⟨12006665354422316067833489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32017774278459509514222637 12006665354422316067833489)
      ·
        refine ⟨9004999015816737050875117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12006665354422316067833489 9004999015816737050875117)
        ·
          refine ⟨3376874630931276394078169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9004999015816737050875117 3376874630931276394078169)
          ·
            refine ⟨2532655973198457295558627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3376874630931276394078169 2532655973198457295558627)
            ·
              refine ⟨3798983959797685943337941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2532655973198457295558627 3798983959797685943337941)
              ·
                refine ⟨89038686557758264296983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3798983959797685943337941 89038686557758264296983)
                ·
                  rfl

theorem cell21_1170465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 7].length) (baseStart_1170465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170465 prefixEnd_1170465 := by exact prefixLift 1170465
  have htrace : WordTrace (prefixWord ++ tailWord_1170465) baseStart_1170465 baseEnd_1170465 := by
    simpa [prefixWord, tailWord_1170465, baseEnd_1170465] using wordTrace_append hprefix tailTrace_1170465
  have hstable : (prefixWord ++ tailWord_1170465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170465).length < 2 ^ (prefixWord ++ tailWord_1170465).sum := by decide
  have hdescent : baseEnd_1170465 < baseStart_1170465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170471 : List Nat := [1, 1, 7, 1, 1, 3, 1, 3, 3]
def baseStart_1170471 : Nat := 118140960795 + 1170471 * 2 ^ 59
def prefixEnd_1170471 : Nat := 4983230072969 + 3 ^ 40 * 1170471 * 2
def baseEnd_1170471 : Nat := 267117428955020115790937

theorem tailTrace_1170471 : CollatzResearch.WordTrace tailWord_1170471 prefixEnd_1170471 267117428955020115790937 := by
  unfold tailWord_1170471
  simp only [CollatzResearch.WordTrace]
  refine ⟨42690584542590942377015267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28460389695060628251343511 42690584542590942377015267)
  ·
    refine ⟨64035876813886413565522901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42690584542590942377015267 64035876813886413565522901)
    ·
      refine ⟨1500840862825462817941943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 64035876813886413565522901 1500840862825462817941943)
      ·
        refine ⟨2251261294238194226912915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1500840862825462817941943 2251261294238194226912915)
        ·
          refine ⟨3376891941357291340369373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2251261294238194226912915 3376891941357291340369373)
          ·
            refine ⟨1266334478008984252638515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3376891941357291340369373 1266334478008984252638515)
            ·
              refine ⟨1899501717013476378957773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266334478008984252638515 1899501717013476378957773)
              ·
                refine ⟨712313143880053642109165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1899501717013476378957773 712313143880053642109165)
                ·
                  refine ⟨267117428955020115790937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712313143880053642109165 267117428955020115790937)
                  ·
                    rfl

theorem cell21_1170471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 3].length) (baseStart_1170471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170471 prefixEnd_1170471 := by exact prefixLift 1170471
  have htrace : WordTrace (prefixWord ++ tailWord_1170471) baseStart_1170471 baseEnd_1170471 := by
    simpa [prefixWord, tailWord_1170471, baseEnd_1170471] using wordTrace_append hprefix tailTrace_1170471
  have hstable : (prefixWord ++ tailWord_1170471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170471).length < 2 ^ (prefixWord ++ tailWord_1170471).sum := by decide
  have hdescent : baseEnd_1170471 < baseStart_1170471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170502 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_1170502 : Nat := 118140960795 + 1170502 * 2 ^ 59
def prefixEnd_1170502 : Nat := 4983230072969 + 3 ^ 40 * 1170502 * 2
def baseEnd_1170502 : Nat := 267124503577370950774207

theorem tailTrace_1170502 : CollatzResearch.WordTrace tailWord_1170502 prefixEnd_1170502 267124503577370950774207 := by
  unfold tailWord_1170502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334116100171207333481055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28461143470319089780929173 1334116100171207333481055)
  ·
    refine ⟨2001174150256811000221583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1334116100171207333481055 2001174150256811000221583)
    ·
      refine ⟨3001761225385216500332375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2001174150256811000221583 3001761225385216500332375)
      ·
        refine ⟨4502641838077824750498563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001761225385216500332375 4502641838077824750498563)
        ·
          refine ⟨6753962757116737125747845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502641838077824750498563 6753962757116737125747845)
          ·
            refine ⟨1266368016959388211077721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6753962757116737125747845 1266368016959388211077721)
            ·
              refine ⟨949776012719541158308291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1266368016959388211077721 949776012719541158308291)
              ·
                refine ⟨1424664019079311737462437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949776012719541158308291 1424664019079311737462437)
                ·
                  refine ⟨267124503577370950774207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1424664019079311737462437 267124503577370950774207)
                  ·
                    rfl

theorem cell21_1170502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_1170502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170502 prefixEnd_1170502 := by exact prefixLift 1170502
  have htrace : WordTrace (prefixWord ++ tailWord_1170502) baseStart_1170502 baseEnd_1170502 := by
    simpa [prefixWord, tailWord_1170502, baseEnd_1170502] using wordTrace_append hprefix tailTrace_1170502
  have hstable : (prefixWord ++ tailWord_1170502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170502).length < 2 ^ (prefixWord ++ tailWord_1170502).sum := by decide
  have hdescent : baseEnd_1170502 < baseStart_1170502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170589 : List Nat := [1, 4, 2, 1, 1, 2, 4, 3, 3]
def baseStart_1170589 : Nat := 118140960795 + 1170589 * 2 ^ 59
def prefixEnd_1170589 : Nat := 4983230072969 + 3 ^ 40 * 1170589 * 2
def baseEnd_1170589 : Nat := 267144358162678132824029

theorem tailTrace_1170589 : CollatzResearch.WordTrace tailWord_1170589 prefixEnd_1170589 267144358162678132824029 := by
  unfold tailWord_1170589
  simp only [CollatzResearch.WordTrace]
  refine ⟨42694888356163448529810821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28463258904108965686540547 42694888356163448529810821)
  ·
    refine ⟨8005291566780646599339529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42694888356163448529810821 8005291566780646599339529)
    ·
      refine ⟨6003968675085484949504647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8005291566780646599339529 6003968675085484949504647)
      ·
        refine ⟨9005953012628227424256971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6003968675085484949504647 9005953012628227424256971)
        ·
          refine ⟨13508929518942341136385457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9005953012628227424256971 13508929518942341136385457)
          ·
            refine ⟨10131697139206755852289093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13508929518942341136385457 10131697139206755852289093)
            ·
              refine ⟨1899693213601266722304205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10131697139206755852289093 1899693213601266722304205)
              ·
                refine ⟨712384955100475020864077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1899693213601266722304205 712384955100475020864077)
                ·
                  refine ⟨267144358162678132824029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712384955100475020864077 267144358162678132824029)
                  ·
                    rfl

theorem cell21_1170589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_1170589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170589 prefixEnd_1170589 := by exact prefixLift 1170589
  have htrace : WordTrace (prefixWord ++ tailWord_1170589) baseStart_1170589 baseEnd_1170589 := by
    simpa [prefixWord, tailWord_1170589, baseEnd_1170589] using wordTrace_append hprefix tailTrace_1170589
  have hstable : (prefixWord ++ tailWord_1170589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170589).length < 2 ^ (prefixWord ++ tailWord_1170589).sum := by decide
  have hdescent : baseEnd_1170589 < baseStart_1170589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170620 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 4]
def baseStart_1170620 : Nat := 118140960795 + 1170620 * 2 ^ 59
def prefixEnd_1170620 : Nat := 4983230072969 + 3 ^ 40 * 1170620 * 2
def baseEnd_1170620 : Nat := 267151432785028967807299

theorem tailTrace_1170620 : CollatzResearch.WordTrace tailWord_1170620 prefixEnd_1170620 267151432785028967807299 := by
  unfold tailWord_1170620
  simp only [CollatzResearch.WordTrace]
  refine ⟨21348009509525570412094657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28464012679367427216126209 21348009509525570412094657)
  ·
    refine ⟨16011007132144177809070993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21348009509525570412094657 16011007132144177809070993)
    ·
      refine ⟨12008255349108133356803245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16011007132144177809070993 12008255349108133356803245)
      ·
        refine ⟨4503095755915550008801217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12008255349108133356803245 4503095755915550008801217)
        ·
          refine ⟨3377321816936662506600913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4503095755915550008801217 3377321816936662506600913)
          ·
            refine ⟨2532991362702496879950685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3377321816936662506600913 2532991362702496879950685)
            ·
              refine ⟨949871761013436329981507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2532991362702496879950685 949871761013436329981507)
              ·
                refine ⟨1424807641520154494972261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949871761013436329981507 1424807641520154494972261)
                ·
                  refine ⟨267151432785028967807299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1424807641520154494972261 267151432785028967807299)
                  ·
                    rfl

theorem cell21_1170620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_1170620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170620 prefixEnd_1170620 := by exact prefixLift 1170620
  have htrace : WordTrace (prefixWord ++ tailWord_1170620) baseStart_1170620 baseEnd_1170620 := by
    simpa [prefixWord, tailWord_1170620, baseEnd_1170620] using wordTrace_append hprefix tailTrace_1170620
  have hstable : (prefixWord ++ tailWord_1170620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170620).length < 2 ^ (prefixWord ++ tailWord_1170620).sum := by decide
  have hdescent : baseEnd_1170620 < baseStart_1170620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170634 : List Nat := [3, 1, 2, 1, 3, 4, 2, 5]
def baseStart_1170634 : Nat := 118140960795 + 1170634 * 2 ^ 59
def prefixEnd_1170634 : Nat := 4983230072969 + 3 ^ 40 * 1170634 * 2
def baseEnd_1170634 : Nat := 89051542591922684857979

theorem tailTrace_1170634 : CollatzResearch.WordTrace tailWord_1170634 prefixEnd_1170634 89051542591922684857979 := by
  unfold tailWord_1170634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10674132410250105303799739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28464353094000280810132637 10674132410250105303799739)
  ·
    refine ⟨16011198615375157955699609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10674132410250105303799739 16011198615375157955699609)
    ·
      refine ⟨12008398961531368466774707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16011198615375157955699609 12008398961531368466774707)
      ·
        refine ⟨18012598442297052700162061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12008398961531368466774707 18012598442297052700162061)
        ·
          refine ⟨6754724415861394762560773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18012598442297052700162061 6754724415861394762560773)
          ·
            refine ⟨1266510827974011517980145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6754724415861394762560773 1266510827974011517980145)
            ·
              refine ⟨949883120980508638485109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1266510827974011517980145 949883120980508638485109)
              ·
                refine ⟨89051542591922684857979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 949883120980508638485109 89051542591922684857979)
                ·
                  rfl

theorem cell21_1170634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_1170634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170634 prefixEnd_1170634 := by exact prefixLift 1170634
  have htrace : WordTrace (prefixWord ++ tailWord_1170634) baseStart_1170634 baseEnd_1170634 := by
    simpa [prefixWord, tailWord_1170634, baseEnd_1170634] using wordTrace_append hprefix tailTrace_1170634
  have hstable : (prefixWord ++ tailWord_1170634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170634).length < 2 ^ (prefixWord ++ tailWord_1170634).sum := by decide
  have hdescent : baseEnd_1170634 < baseStart_1170634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170834 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_1170834 : Nat := 118140960795 + 1170834 * 2 ^ 59
def prefixEnd_1170834 : Nat := 4983230072969 + 3 ^ 40 * 1170834 * 2
def baseEnd_1170834 : Nat := 267200270500612151240195

theorem tailTrace_1170834 : CollatzResearch.WordTrace tailWord_1170834 prefixEnd_1170834 267200270500612151240195 := by
  unfold tailWord_1170834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10675956060068963843119889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28469216160183903581653037 10675956060068963843119889)
  ·
    refine ⟨8006967045051722882339917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10675956060068963843119889 8006967045051722882339917)
    ·
      refine ⟨3002612641894396080877469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8006967045051722882339917 3002612641894396080877469)
      ·
        refine ⟨1125979740710398530329051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3002612641894396080877469 1125979740710398530329051)
        ·
          refine ⟨1688969611065597795493577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125979740710398530329051 1688969611065597795493577)
          ·
            refine ⟨1266727208299198346620183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1688969611065597795493577 1266727208299198346620183)
            ·
              refine ⟨1900090812448797519930275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266727208299198346620183 1900090812448797519930275)
              ·
                refine ⟨2850136218673196279895413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900090812448797519930275 2850136218673196279895413)
                ·
                  refine ⟨267200270500612151240195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2850136218673196279895413 267200270500612151240195)
                  ·
                    rfl

theorem cell21_1170834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_1170834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170834 prefixEnd_1170834 := by exact prefixLift 1170834
  have htrace : WordTrace (prefixWord ++ tailWord_1170834) baseStart_1170834 baseEnd_1170834 := by
    simpa [prefixWord, tailWord_1170834, baseEnd_1170834] using wordTrace_append hprefix tailTrace_1170834
  have hstable : (prefixWord ++ tailWord_1170834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170834).length < 2 ^ (prefixWord ++ tailWord_1170834).sum := by decide
  have hdescent : baseEnd_1170834 < baseStart_1170834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170845 : List Nat := [1, 4, 2, 1, 3, 2, 2, 6]
def baseStart_1170845 : Nat := 118140960795 + 1170845 * 2 ^ 59
def prefixEnd_1170845 : Nat := 4983230072969 + 3 ^ 40 * 1170845 * 2
def baseEnd_1170845 : Nat := 89067593616826192185613

theorem tailTrace_1170845 : CollatzResearch.WordTrace tailWord_1170845 prefixEnd_1170845 89067593616826192185613 := by
  unfold tailWord_1170845
  simp only [CollatzResearch.WordTrace]
  refine ⟨42704225443236004251129989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28469483628824002834086659 42704225443236004251129989)
  ·
    refine ⟨8007042270606750797086873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42704225443236004251129989 8007042270606750797086873)
    ·
      refine ⟨6005281702955063097815155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8007042270606750797086873 6005281702955063097815155)
      ·
        refine ⟨9007922554432594646722733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6005281702955063097815155 9007922554432594646722733)
        ·
          refine ⟨3377970957912222992521025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9007922554432594646722733 3377970957912222992521025)
          ·
            refine ⟨2533478218434167244390769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3377970957912222992521025 2533478218434167244390769)
            ·
              refine ⟨1900108663825625433293077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2533478218434167244390769 1900108663825625433293077)
              ·
                refine ⟨89067593616826192185613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1900108663825625433293077 89067593616826192185613)
                ·
                  rfl

theorem cell21_1170845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 6].length) (baseStart_1170845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170845 prefixEnd_1170845 := by exact prefixLift 1170845
  have htrace : WordTrace (prefixWord ++ tailWord_1170845) baseStart_1170845 baseEnd_1170845 := by
    simpa [prefixWord, tailWord_1170845, baseEnd_1170845] using wordTrace_append hprefix tailTrace_1170845
  have hstable : (prefixWord ++ tailWord_1170845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170845).length < 2 ^ (prefixWord ++ tailWord_1170845).sum := by decide
  have hdescent : baseEnd_1170845 < baseStart_1170845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170890 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_1170890 : Nat := 118140960795 + 1170890 * 2 ^ 59
def prefixEnd_1170890 : Nat := 4983230072969 + 3 ^ 40 * 1170890 * 2
def baseEnd_1170890 : Nat := 267213050463568498306747

theorem tailTrace_1170890 : CollatzResearch.WordTrace tailWord_1170890 prefixEnd_1170890 267213050463568498306747 := by
  unfold tailWord_1170890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10676466682018244234129531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28470577818715317957678749 10676466682018244234129531)
  ·
    refine ⟨16014700023027366351194297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10676466682018244234129531 16014700023027366351194297)
    ·
      refine ⟨12011025017270524763395723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16014700023027366351194297 12011025017270524763395723)
      ·
        refine ⟨18016537525905787145093585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12011025017270524763395723 18016537525905787145093585)
        ·
          refine ⟨13512403144429340358820189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18016537525905787145093585 13512403144429340358820189)
          ·
            refine ⟨5067151179161002634557571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13512403144429340358820189 5067151179161002634557571)
            ·
              refine ⟨7600726768741503951836357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5067151179161002634557571 7600726768741503951836357)
              ·
                refine ⟨1425136269139031990969317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7600726768741503951836357 1425136269139031990969317)
                ·
                  refine ⟨267213050463568498306747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1425136269139031990969317 267213050463568498306747)
                  ·
                    rfl

theorem cell21_1170890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_1170890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170890 prefixEnd_1170890 := by exact prefixLift 1170890
  have htrace : WordTrace (prefixWord ++ tailWord_1170890) baseStart_1170890 baseEnd_1170890 := by
    simpa [prefixWord, tailWord_1170890, baseEnd_1170890] using wordTrace_append hprefix tailTrace_1170890
  have hstable : (prefixWord ++ tailWord_1170890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170890).length < 2 ^ (prefixWord ++ tailWord_1170890).sum := by decide
  have hdescent : baseEnd_1170890 < baseStart_1170890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170904 : List Nat := [2, 1, 2, 2, 2, 1, 5, 6]
def baseStart_1170904 : Nat := 118140960795 + 1170904 * 2 ^ 59
def prefixEnd_1170904 : Nat := 4983230072969 + 3 ^ 40 * 1170904 * 2
def baseEnd_1170904 : Nat := 89072081818102528357795

theorem tailTrace_1170904 : CollatzResearch.WordTrace tailWord_1170904 prefixEnd_1170904 89072081818102528357795 := by
  unfold tailWord_1170904
  simp only [CollatzResearch.WordTrace]
  refine ⟨21353188675011128663763883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28470918233348171551685177 21353188675011128663763883)
  ·
    refine ⟨32029783012516692995645825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21353188675011128663763883 32029783012516692995645825)
    ·
      refine ⟨24022337259387519746734369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32029783012516692995645825 24022337259387519746734369)
      ·
        refine ⟨18016752944540639810050777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24022337259387519746734369 18016752944540639810050777)
        ·
          refine ⟨13512564708405479857538083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18016752944540639810050777 13512564708405479857538083)
          ·
            refine ⟨20268847062608219786307125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13512564708405479857538083 20268847062608219786307125)
            ·
              refine ⟨1900204412119520604966293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20268847062608219786307125 1900204412119520604966293)
              ·
                refine ⟨89072081818102528357795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1900204412119520604966293 89072081818102528357795)
                ·
                  rfl

theorem cell21_1170904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_1170904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170904 prefixEnd_1170904 := by exact prefixLift 1170904
  have htrace : WordTrace (prefixWord ++ tailWord_1170904) baseStart_1170904 baseEnd_1170904 := by
    simpa [prefixWord, tailWord_1170904, baseEnd_1170904] using wordTrace_append hprefix tailTrace_1170904
  have hstable : (prefixWord ++ tailWord_1170904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170904).length < 2 ^ (prefixWord ++ tailWord_1170904).sum := by decide
  have hdescent : baseEnd_1170904 < baseStart_1170904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170952 : List Nat := [2, 1, 3, 2, 1, 1, 4, 4, 3]
def baseStart_1170952 : Nat := 118140960795 + 1170952 * 2 ^ 59
def prefixEnd_1170952 : Nat := 4983230072969 + 3 ^ 40 * 1170952 * 2
def baseEnd_1170952 : Nat := 267227199708270168273287

theorem tailTrace_1170952 : CollatzResearch.WordTrace tailWord_1170952 prefixEnd_1170952 267227199708270168273287 := by
  unfold tailWord_1170952
  simp only [CollatzResearch.WordTrace]
  refine ⟨21354064026924180762637555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28472085369232241016850073 21354064026924180762637555)
  ·
    refine ⟨32031096040386271143956333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21354064026924180762637555 32031096040386271143956333)
    ·
      refine ⟨12011661015144851678983625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32031096040386271143956333 12011661015144851678983625)
      ·
        refine ⟨9008745761358638759237719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12011661015144851678983625 9008745761358638759237719)
        ·
          refine ⟨13513118642037958138856579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9008745761358638759237719 13513118642037958138856579)
          ·
            refine ⟨20269677963056937208284869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13513118642037958138856579 20269677963056937208284869)
            ·
              refine ⟨3800564618073175726553413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20269677963056937208284869 3800564618073175726553413)
              ·
                refine ⟨712605865888720448728765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3800564618073175726553413 712605865888720448728765)
                ·
                  refine ⟨267227199708270168273287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712605865888720448728765 267227199708270168273287)
                  ·
                    rfl

theorem cell21_1170952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 3].length) (baseStart_1170952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1170952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1170952 prefixEnd_1170952 := by exact prefixLift 1170952
  have htrace : WordTrace (prefixWord ++ tailWord_1170952) baseStart_1170952 baseEnd_1170952 := by
    simpa [prefixWord, tailWord_1170952, baseEnd_1170952] using wordTrace_append hprefix tailTrace_1170952
  have hstable : (prefixWord ++ tailWord_1170952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170952).length < 2 ^ (prefixWord ++ tailWord_1170952).sum := by decide
  have hdescent : baseEnd_1170952 < baseStart_1170952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171062 : List Nat := [5, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_1171062 : Nat := 118140960795 + 1171062 * 2 ^ 59
def prefixEnd_1171062 : Nat := 4983230072969 + 3 ^ 40 * 1171062 * 2
def baseEnd_1171062 : Nat := 267252303206934421439729

theorem tailTrace_1171062 : CollatzResearch.WordTrace tailWord_1171062 prefixEnd_1171062 267252303206934421439729 := by
  unfold tailWord_1171062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2669508755215615644486215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28474760055633233541186293 2669508755215615644486215)
  ·
    refine ⟨4004263132823423466729323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2669508755215615644486215 4004263132823423466729323)
    ·
      refine ⟨6006394699235135200093985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4004263132823423466729323 6006394699235135200093985)
      ·
        refine ⟨4504796024426351400070489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6006394699235135200093985 4504796024426351400070489)
        ·
          refine ⟨3378597018319763550052867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4504796024426351400070489 3378597018319763550052867)
          ·
            refine ⟨5067895527479645325079301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3378597018319763550052867 5067895527479645325079301)
            ·
              refine ⟨950230411402433498452369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5067895527479645325079301 950230411402433498452369)
              ·
                refine ⟨712672808551825123839277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950230411402433498452369 712672808551825123839277)
                ·
                  refine ⟨267252303206934421439729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712672808551825123839277 267252303206934421439729)
                  ·
                    rfl

theorem cell21_1171062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_1171062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171062 prefixEnd_1171062 := by exact prefixLift 1171062
  have htrace : WordTrace (prefixWord ++ tailWord_1171062) baseStart_1171062 baseEnd_1171062 := by
    simpa [prefixWord, tailWord_1171062, baseEnd_1171062] using wordTrace_append hprefix tailTrace_1171062
  have hstable : (prefixWord ++ tailWord_1171062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171062).length < 2 ^ (prefixWord ++ tailWord_1171062).sum := by decide
  have hdescent : baseEnd_1171062 < baseStart_1171062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171073 : List Nat := [1, 2, 4, 2, 1, 4, 1, 6]
def baseStart_1171073 : Nat := 118140960795 + 1171073 * 2 ^ 59
def prefixEnd_1171073 : Nat := 4983230072969 + 3 ^ 40 * 1171073 * 2
def baseEnd_1171073 : Nat := 89084937852266948918791

theorem tailTrace_1171073 : CollatzResearch.WordTrace tailWord_1171073 prefixEnd_1171073 89084937852266948918791 := by
  unfold tailWord_1171073
  simp only [CollatzResearch.WordTrace]
  refine ⟨42712541286409999190429873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28475027524273332793619915 42712541286409999190429873)
  ·
    refine ⟨32034405964807499392822405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42712541286409999190429873 32034405964807499392822405)
    ·
      refine ⟨6006451118401406136154201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32034405964807499392822405 6006451118401406136154201)
      ·
        refine ⟨4504838338801054602115651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6006451118401406136154201 4504838338801054602115651)
        ·
          refine ⟨6757257508201581903173477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4504838338801054602115651 6757257508201581903173477)
          ·
            refine ⟨1266985782787796606845027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6757257508201581903173477 1266985782787796606845027)
            ·
              refine ⟨1900478674181694910267541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266985782787796606845027 1900478674181694910267541)
              ·
                refine ⟨89084937852266948918791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1900478674181694910267541 89084937852266948918791)
                ·
                  rfl

theorem cell21_1171073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 6].length) (baseStart_1171073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171073 prefixEnd_1171073 := by exact prefixLift 1171073
  have htrace : WordTrace (prefixWord ++ tailWord_1171073) baseStart_1171073 baseEnd_1171073 := by
    simpa [prefixWord, tailWord_1171073, baseEnd_1171073] using wordTrace_append hprefix tailTrace_1171073
  have hstable : (prefixWord ++ tailWord_1171073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171073).length < 2 ^ (prefixWord ++ tailWord_1171073).sum := by decide
  have hdescent : baseEnd_1171073 < baseStart_1171073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171090 : List Nat := [3, 2, 3, 1, 3, 1, 3, 5]
def baseStart_1171090 : Nat := 118140960795 + 1171090 * 2 ^ 59
def prefixEnd_1171090 : Nat := 4983230072969 + 3 ^ 40 * 1171090 * 2
def baseEnd_1171090 : Nat := 89086231062804198324335

theorem tailTrace_1171090 : CollatzResearch.WordTrace tailWord_1171090 prefixEnd_1171090 89086231062804198324335 := by
  unfold tailWord_1171090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10678290331837102773449681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28475440884898940729199149 10678290331837102773449681)
  ·
    refine ⟨8008717748877827080087261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10678290331837102773449681 8008717748877827080087261)
    ·
      refine ⟨3003269155829185155032723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8008717748877827080087261 3003269155829185155032723)
      ·
        refine ⟨4504903733743777732549085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3003269155829185155032723 4504903733743777732549085)
        ·
          refine ⟨1689338900153916649705907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4504903733743777732549085 1689338900153916649705907)
          ·
            refine ⟨2534008350230874974558861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689338900153916649705907 2534008350230874974558861)
            ·
              refine ⟨950253131336578115459573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2534008350230874974558861 950253131336578115459573)
              ·
                refine ⟨89086231062804198324335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 950253131336578115459573 89086231062804198324335)
                ·
                  rfl

theorem cell21_1171090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_1171090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171090 prefixEnd_1171090 := by exact prefixLift 1171090
  have htrace : WordTrace (prefixWord ++ tailWord_1171090) baseStart_1171090 baseEnd_1171090 := by
    simpa [prefixWord, tailWord_1171090, baseEnd_1171090] using wordTrace_append hprefix tailTrace_1171090
  have hstable : (prefixWord ++ tailWord_1171090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171090).length < 2 ^ (prefixWord ++ tailWord_1171090).sum := by decide
  have hdescent : baseEnd_1171090 < baseStart_1171090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171101 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 6]
def baseStart_1171101 : Nat := 118140960795 + 1171101 * 2 ^ 59
def prefixEnd_1171101 : Nat := 4983230072969 + 3 ^ 40 * 1171101 * 2
def baseEnd_1171101 : Nat := 267261203538279020289649

theorem tailTrace_1171101 : CollatzResearch.WordTrace tailWord_1171101 prefixEnd_1171101 267261203538279020289649 := by
  unfold tailWord_1171101
  simp only [CollatzResearch.WordTrace]
  refine ⟨42713562530308559972449157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28475708353539039981632771 42713562530308559972449157)
  ·
    refine ⟨8008792974432854994834217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42713562530308559972449157 8008792974432854994834217)
    ·
      refine ⟨6006594730824641246125663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8008792974432854994834217 6006594730824641246125663)
      ·
        refine ⟨9009892096236961869188495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6006594730824641246125663 9009892096236961869188495)
        ·
          refine ⟨13514838144355442803782743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9009892096236961869188495 13514838144355442803782743)
          ·
            refine ⟨20272257216533164205674115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13514838144355442803782743 20272257216533164205674115)
            ·
              refine ⟨30408385824799746308511173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20272257216533164205674115 30408385824799746308511173)
              ·
                refine ⟨5701572342149952432845845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30408385824799746308511173 5701572342149952432845845)
                ·
                  refine ⟨267261203538279020289649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5701572342149952432845845 267261203538279020289649)
                  ·
                    rfl

theorem cell21_1171101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_1171101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171101 prefixEnd_1171101 := by exact prefixLift 1171101
  have htrace : WordTrace (prefixWord ++ tailWord_1171101) baseStart_1171101 baseEnd_1171101 := by
    simpa [prefixWord, tailWord_1171101, baseEnd_1171101] using wordTrace_append hprefix tailTrace_1171101
  have hstable : (prefixWord ++ tailWord_1171101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171101).length < 2 ^ (prefixWord ++ tailWord_1171101).sum := by decide
  have hdescent : baseEnd_1171101 < baseStart_1171101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171104 : List Nat := [2, 1, 1, 4, 3, 1, 1, 5, 3]
def baseStart_1171104 : Nat := 118140960795 + 1171104 * 2 ^ 59
def prefixEnd_1171104 : Nat := 4983230072969 + 3 ^ 40 * 1171104 * 2
def baseEnd_1171104 : Nat := 267261888179151681739643

theorem tailTrace_1171104 : CollatzResearch.WordTrace tailWord_1171104 prefixEnd_1171104 267261888179151681739643 := by
  unfold tailWord_1171104
  simp only [CollatzResearch.WordTrace]
  refine ⟨21356835974648845742404183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28475781299531794323205577 21356835974648845742404183)
  ·
    refine ⟨32035253961973268613606275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21356835974648845742404183 32035253961973268613606275)
    ·
      refine ⟨48052880942959902920409413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32035253961973268613606275 48052880942959902920409413)
      ·
        refine ⟨9009915176804981797576765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48052880942959902920409413 9009915176804981797576765)
        ·
          refine ⟨3378718191301868174091287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9009915176804981797576765 3378718191301868174091287)
          ·
            refine ⟨5068077286952802261136931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3378718191301868174091287 5068077286952802261136931)
            ·
              refine ⟨7602115930429203391705397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5068077286952802261136931 7602115930429203391705397)
              ·
                refine ⟨712698368477737817972381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7602115930429203391705397 712698368477737817972381)
                ·
                  refine ⟨267261888179151681739643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712698368477737817972381 267261888179151681739643)
                  ·
                    rfl

theorem cell21_1171104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 3].length) (baseStart_1171104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171104 prefixEnd_1171104 := by exact prefixLift 1171104
  have htrace : WordTrace (prefixWord ++ tailWord_1171104) baseStart_1171104 baseEnd_1171104 := by
    simpa [prefixWord, tailWord_1171104, baseEnd_1171104] using wordTrace_append hprefix tailTrace_1171104
  have hstable : (prefixWord ++ tailWord_1171104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171104).length < 2 ^ (prefixWord ++ tailWord_1171104).sum := by decide
  have hdescent : baseEnd_1171104 < baseStart_1171104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171177 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 4]
def baseStart_1171177 : Nat := 118140960795 + 1171177 * 2 ^ 59
def prefixEnd_1171177 : Nat := 4983230072969 + 3 ^ 40 * 1171177 * 2
def baseEnd_1171177 : Nat := 267278547773719777022827

theorem tailTrace_1171177 : CollatzResearch.WordTrace tailWord_1171177 prefixEnd_1171177 267278547773719777022827 := by
  unfold tailWord_1171177
  simp only [CollatzResearch.WordTrace]
  refine ⟨42716334478033224952215785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28477556318688816634810523 42716334478033224952215785)
  ·
    refine ⟨32037250858524918714161839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42716334478033224952215785 32037250858524918714161839)
    ·
      refine ⟨48055876287787378071242759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32037250858524918714161839 48055876287787378071242759)
      ·
        refine ⟨72083814431681067106864139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48055876287787378071242759 72083814431681067106864139)
        ·
          refine ⟨108125721647521600660296209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72083814431681067106864139 108125721647521600660296209)
          ·
            refine ⟨81094291235641200495222157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108125721647521600660296209 81094291235641200495222157)
            ·
              refine ⟨30410359213365450185708309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81094291235641200495222157 30410359213365450185708309)
              ·
                refine ⟨1425485588126505477455077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30410359213365450185708309 1425485588126505477455077)
                ·
                  refine ⟨267278547773719777022827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1425485588126505477455077 267278547773719777022827)
                  ·
                    rfl

theorem cell21_1171177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_1171177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171177 prefixEnd_1171177 := by exact prefixLift 1171177
  have htrace : WordTrace (prefixWord ++ tailWord_1171177) baseStart_1171177 baseEnd_1171177 := by
    simpa [prefixWord, tailWord_1171177, baseEnd_1171177] using wordTrace_append hprefix tailTrace_1171177
  have hstable : (prefixWord ++ tailWord_1171177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171177).length < 2 ^ (prefixWord ++ tailWord_1171177).sum := by decide
  have hdescent : baseEnd_1171177 < baseStart_1171177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171191 : List Nat := [1, 1, 3, 1, 1, 1, 5, 8]
def baseStart_1171191 : Nat := 118140960795 + 1171191 * 2 ^ 59
def prefixEnd_1171191 : Nat := 4983230072969 + 3 ^ 40 * 1171191 * 2
def baseEnd_1171191 : Nat := 89093914254819621263155

theorem tailTrace_1171191 : CollatzResearch.WordTrace tailWord_1171191 prefixEnd_1171191 89093914254819621263155 := by
  unfold tailWord_1171191
  simp only [CollatzResearch.WordTrace]
  refine ⟨42716845099982505343225427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28477896733321670228816951 42716845099982505343225427)
  ·
    refine ⟨64075267649973758014838141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42716845099982505343225427 64075267649973758014838141)
    ·
      refine ⟨24028225368740159255564303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64075267649973758014838141 24028225368740159255564303)
      ·
        refine ⟨36042338053110238883346455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24028225368740159255564303 36042338053110238883346455)
        ·
          refine ⟨54063507079665358325019683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36042338053110238883346455 54063507079665358325019683)
          ·
            refine ⟨81095260619498037487529525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54063507079665358325019683 81095260619498037487529525)
            ·
              refine ⟨7602680683077941014455893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81095260619498037487529525 7602680683077941014455893)
              ·
                refine ⟨89093914254819621263155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7602680683077941014455893 89093914254819621263155)
                ·
                  rfl

theorem cell21_1171191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 8].length) (baseStart_1171191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171191 prefixEnd_1171191 := by exact prefixLift 1171191
  have htrace : WordTrace (prefixWord ++ tailWord_1171191) baseStart_1171191 baseEnd_1171191 := by
    simpa [prefixWord, tailWord_1171191, baseEnd_1171191] using wordTrace_append hprefix tailTrace_1171191
  have hstable : (prefixWord ++ tailWord_1171191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171191).length < 2 ^ (prefixWord ++ tailWord_1171191).sum := by decide
  have hdescent : baseEnd_1171191 < baseStart_1171191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171284 : List Nat := [2, 4, 1, 1, 3, 2, 8]
def baseStart_1171284 : Nat := 118140960795 + 1171284 * 2 ^ 59
def prefixEnd_1171284 : Nat := 4983230072969 + 3 ^ 40 * 1171284 * 2
def baseEnd_1171284 : Nat := 29700329625723485415475

theorem tailTrace_1171284 : CollatzResearch.WordTrace tailWord_1171284 prefixEnd_1171284 29700329625723485415475 := by
  unfold tailWord_1171284
  simp only [CollatzResearch.WordTrace]
  refine ⟨21360118544322791113180453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28480158059097054817573937 21360118544322791113180453)
  ·
    refine ⟨4005022227060523333721335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21360118544322791113180453 4005022227060523333721335)
    ·
      refine ⟨6007533340590785000582003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4005022227060523333721335 6007533340590785000582003)
      ·
        refine ⟨9011300010886177500873005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6007533340590785000582003 9011300010886177500873005)
        ·
          refine ⟨3379237504082316562827377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9011300010886177500873005 3379237504082316562827377)
          ·
            refine ⟨2534428128061737422120533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3379237504082316562827377 2534428128061737422120533)
            ·
              refine ⟨29700329625723485415475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2534428128061737422120533 29700329625723485415475)
              ·
                rfl

theorem cell21_1171284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 8].length) (baseStart_1171284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171284 prefixEnd_1171284 := by exact prefixLift 1171284
  have htrace : WordTrace (prefixWord ++ tailWord_1171284) baseStart_1171284 baseEnd_1171284 := by
    simpa [prefixWord, tailWord_1171284, baseEnd_1171284] using wordTrace_append hprefix tailTrace_1171284
  have hstable : (prefixWord ++ tailWord_1171284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171284).length < 2 ^ (prefixWord ++ tailWord_1171284).sum := by decide
  have hdescent : baseEnd_1171284 < baseStart_1171284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171287 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 4]
def baseStart_1171287 : Nat := 118140960795 + 1171287 * 2 ^ 59
def prefixEnd_1171287 : Nat := 4983230072969 + 3 ^ 40 * 1171287 * 2
def baseEnd_1171287 : Nat := 267303651272384030189269

theorem tailTrace_1171287 : CollatzResearch.WordTrace tailWord_1171287 prefixEnd_1171287 267303651272384030189269 := by
  unfold tailWord_1171287
  simp only [CollatzResearch.WordTrace]
  refine ⟨42720346507634713738720115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28480231005089809159146743 42720346507634713738720115)
  ·
    refine ⟨64080519761452070608080173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42720346507634713738720115 64080519761452070608080173)
    ·
      refine ⟨24030194910544526478030065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64080519761452070608080173 24030194910544526478030065)
      ·
        refine ⟨18022646182908394858522549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24030194910544526478030065 18022646182908394858522549)
        ·
          refine ⟨1689623079647662017986489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18022646182908394858522549 1689623079647662017986489)
          ·
            refine ⟨1267217309735746513489867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1689623079647662017986489 1267217309735746513489867)
            ·
              refine ⟨1900825964603619770234801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267217309735746513489867 1900825964603619770234801)
              ·
                refine ⟨1425619473452714827676101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1900825964603619770234801 1425619473452714827676101)
                ·
                  refine ⟨267303651272384030189269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1425619473452714827676101 267303651272384030189269)
                  ·
                    rfl

theorem cell21_1171287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 4].length) (baseStart_1171287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171287 prefixEnd_1171287 := by exact prefixLift 1171287
  have htrace : WordTrace (prefixWord ++ tailWord_1171287) baseStart_1171287 baseEnd_1171287 := by
    simpa [prefixWord, tailWord_1171287, baseEnd_1171287] using wordTrace_append hprefix tailTrace_1171287
  have hstable : (prefixWord ++ tailWord_1171287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171287).length < 2 ^ (prefixWord ++ tailWord_1171287).sum := by decide
  have hdescent : baseEnd_1171287 < baseStart_1171287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171332 : List Nat := [2, 3, 2, 1, 1, 1, 5, 3, 3]
def baseStart_1171332 : Nat := 118140960795 + 1171332 * 2 ^ 59
def prefixEnd_1171332 : Nat := 4983230072969 + 3 ^ 40 * 1171332 * 2
def baseEnd_1171332 : Nat := 267313920885473951939177

theorem tailTrace_1171332 : CollatzResearch.WordTrace tailWord_1171332 prefixEnd_1171332 267313920885473951939177 := by
  unfold tailWord_1171332
  simp only [CollatzResearch.WordTrace]
  refine ⟨21360993896235843212054125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28481325194981124282738833 21360993896235843212054125)
  ·
    refine ⟨8010372711088441204520297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21360993896235843212054125 8010372711088441204520297)
    ·
      refine ⟨6007779533316330903390223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8010372711088441204520297 6007779533316330903390223)
      ·
        refine ⟨9011669299974496355085335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6007779533316330903390223 9011669299974496355085335)
        ·
          refine ⟨13517503949961744532628003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9011669299974496355085335 13517503949961744532628003)
          ·
            refine ⟨20276255924942616798942005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13517503949961744532628003 20276255924942616798942005)
            ·
              refine ⟨1900898992963370324900813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20276255924942616798942005 1900898992963370324900813)
              ·
                refine ⟨712837122361263871837805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1900898992963370324900813 712837122361263871837805)
                ·
                  refine ⟨267313920885473951939177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712837122361263871837805 267313920885473951939177)
                  ·
                    rfl

theorem cell21_1171332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_1171332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171332 prefixEnd_1171332 := by exact prefixLift 1171332
  have htrace : WordTrace (prefixWord ++ tailWord_1171332) baseStart_1171332 baseEnd_1171332 := by
    simpa [prefixWord, tailWord_1171332, baseEnd_1171332] using wordTrace_append hprefix tailTrace_1171332
  have hstable : (prefixWord ++ tailWord_1171332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171332).length < 2 ^ (prefixWord ++ tailWord_1171332).sum := by decide
  have hdescent : baseEnd_1171332 < baseStart_1171332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171346 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_1171346 : Nat := 118140960795 + 1171346 * 2 ^ 59
def prefixEnd_1171346 : Nat := 4983230072969 + 3 ^ 40 * 1171346 * 2
def baseEnd_1171346 : Nat := 267317115876213038705815

theorem tailTrace_1171346 : CollatzResearch.WordTrace tailWord_1171346 prefixEnd_1171346 267317115876213038705815 := by
  unfold tailWord_1171346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10680624603605241703779473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28481665609613977876745261 10680624603605241703779473)
  ·
    refine ⟨8010468452703931277834605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10680624603605241703779473 8010468452703931277834605)
    ·
      refine ⟨3003925669763974229187977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8010468452703931277834605 3003925669763974229187977)
      ·
        refine ⟨2252944252322980671890983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3003925669763974229187977 2252944252322980671890983)
        ·
          refine ⟨3379416378484471007836475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2252944252322980671890983 3379416378484471007836475)
          ·
            refine ⟨5069124567726706511754713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3379416378484471007836475 5069124567726706511754713)
            ·
              refine ⟨3801843425795029883816035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5069124567726706511754713 3801843425795029883816035)
              ·
                refine ⟨5702765138692544825724053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3801843425795029883816035 5702765138692544825724053)
                ·
                  refine ⟨267317115876213038705815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5702765138692544825724053 267317115876213038705815)
                  ·
                    rfl

theorem cell21_1171346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_1171346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171346 prefixEnd_1171346 := by exact prefixLift 1171346
  have htrace : WordTrace (prefixWord ++ tailWord_1171346) baseStart_1171346 baseEnd_1171346 := by
    simpa [prefixWord, tailWord_1171346, baseEnd_1171346] using wordTrace_append hprefix tailTrace_1171346
  have hstable : (prefixWord ++ tailWord_1171346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171346).length < 2 ^ (prefixWord ++ tailWord_1171346).sum := by decide
  have hdescent : baseEnd_1171346 < baseStart_1171346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171391 : List Nat := [1, 1, 2, 2, 2, 1, 4, 5, 3]
def baseStart_1171391 : Nat := 118140960795 + 1171391 * 2 ^ 59
def prefixEnd_1171391 : Nat := 4983230072969 + 3 ^ 40 * 1171391 * 2
def baseEnd_1171391 : Nat := 267327385489302960455723

theorem tailTrace_1171391 : CollatzResearch.WordTrace tailWord_1171391 prefixEnd_1171391 267327385489302960455723 := by
  unfold tailWord_1171391
  simp only [CollatzResearch.WordTrace]
  refine ⟨42724139699257939500506027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28482759799505293000337351 42724139699257939500506027)
  ·
    refine ⟨64086209548886909250759041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42724139699257939500506027 64086209548886909250759041)
    ·
      refine ⟨48064657161665181938069281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64086209548886909250759041 48064657161665181938069281)
      ·
        refine ⟨36048492871248886453551961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48064657161665181938069281 36048492871248886453551961)
        ·
          refine ⟨27036369653436664840163971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36048492871248886453551961 27036369653436664840163971)
          ·
            refine ⟨40554554480154997260245957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27036369653436664840163971 40554554480154997260245957)
            ·
              refine ⟨7603978965029061986296117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40554554480154997260245957 7603978965029061986296117)
              ·
                refine ⟨712873027971474561215261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7603978965029061986296117 712873027971474561215261)
                ·
                  refine ⟨267327385489302960455723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712873027971474561215261 267327385489302960455723)
                  ·
                    rfl

theorem cell21_1171391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 3].length) (baseStart_1171391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171391 prefixEnd_1171391 := by exact prefixLift 1171391
  have htrace : WordTrace (prefixWord ++ tailWord_1171391) baseStart_1171391 baseEnd_1171391 := by
    simpa [prefixWord, tailWord_1171391, baseEnd_1171391] using wordTrace_append hprefix tailTrace_1171391
  have hstable : (prefixWord ++ tailWord_1171391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171391).length < 2 ^ (prefixWord ++ tailWord_1171391).sum := by decide
  have hdescent : baseEnd_1171391 < baseStart_1171391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171408 : List Nat := [2, 1, 1, 1, 1, 2, 8, 2, 3]
def baseStart_1171408 : Nat := 118140960795 + 1171408 * 2 ^ 59
def prefixEnd_1171408 : Nat := 4983230072969 + 3 ^ 40 * 1171408 * 2
def baseEnd_1171408 : Nat := 267331265120914708672355

theorem tailTrace_1171408 : CollatzResearch.WordTrace tailWord_1171408 prefixEnd_1171408 267331265120914708672355 := by
  unfold tailWord_1171408
  simp only [CollatzResearch.WordTrace]
  refine ⟨21362379870098175701937439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28483173160130900935916585 21362379870098175701937439)
  ·
    refine ⟨32043569805147263552906159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21362379870098175701937439 32043569805147263552906159)
    ·
      refine ⟨48065354707720895329359239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32043569805147263552906159 48065354707720895329359239)
      ·
        refine ⟨72098032061581342994038859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48065354707720895329359239 72098032061581342994038859)
        ·
          refine ⟨108147048092372014491058289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72098032061581342994038859 108147048092372014491058289)
          ·
            refine ⟨81110286069279010868293717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108147048092372014491058289 81110286069279010868293717)
            ·
              refine ⟨950511164874363408612817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 81110286069279010868293717 950511164874363408612817)
              ·
                refine ⟨712883373655772556459613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950511164874363408612817 712883373655772556459613)
                ·
                  refine ⟨267331265120914708672355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712883373655772556459613 267331265120914708672355)
                  ·
                    rfl

theorem cell21_1171408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 3].length) (baseStart_1171408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171408 prefixEnd_1171408 := by exact prefixLift 1171408
  have htrace : WordTrace (prefixWord ++ tailWord_1171408) baseStart_1171408 baseEnd_1171408 := by
    simpa [prefixWord, tailWord_1171408, baseEnd_1171408] using wordTrace_append hprefix tailTrace_1171408
  have hstable : (prefixWord ++ tailWord_1171408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171408).length < 2 ^ (prefixWord ++ tailWord_1171408).sum := by decide
  have hdescent : baseEnd_1171408 < baseStart_1171408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171467 : List Nat := [1, 1, 1, 1, 6, 1, 1, 6, 3]
def baseStart_1171467 : Nat := 118140960795 + 1171467 * 2 ^ 59
def prefixEnd_1171467 : Nat := 4983230072969 + 3 ^ 40 * 1171467 * 2
def baseEnd_1171467 : Nat := 267344729724743717188901

theorem tailTrace_1171467 : CollatzResearch.WordTrace tailWord_1171467 prefixEnd_1171467 267344729724743717188901 := by
  unfold tailWord_1171467
  simp only [CollatzResearch.WordTrace]
  refine ⟨42726911646982604480272655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28484607764655069653515103 42726911646982604480272655)
  ·
    refine ⟨64090367470473906720408983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42726911646982604480272655 64090367470473906720408983)
    ·
      refine ⟨96135551205710860080613475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64090367470473906720408983 96135551205710860080613475)
      ·
        refine ⟨144203326808566290120920213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96135551205710860080613475 144203326808566290120920213)
        ·
          refine ⟨6759530944151544849418135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 144203326808566290120920213 6759530944151544849418135)
          ·
            refine ⟨10139296416227317274127203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6759530944151544849418135 10139296416227317274127203)
            ·
              refine ⟨15208944624340975911190805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10139296416227317274127203 15208944624340975911190805)
              ·
                refine ⟨712919279265983245837069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15208944624340975911190805 712919279265983245837069)
                ·
                  refine ⟨267344729724743717188901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712919279265983245837069 267344729724743717188901)
                  ·
                    rfl

theorem cell21_1171467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 3].length) (baseStart_1171467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171467 prefixEnd_1171467 := by exact prefixLift 1171467
  have htrace : WordTrace (prefixWord ++ tailWord_1171467) baseStart_1171467 baseEnd_1171467 := by
    simpa [prefixWord, tailWord_1171467, baseEnd_1171467] using wordTrace_append hprefix tailTrace_1171467
  have hstable : (prefixWord ++ tailWord_1171467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171467).length < 2 ^ (prefixWord ++ tailWord_1171467).sum := by decide
  have hdescent : baseEnd_1171467 < baseStart_1171467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171512 : List Nat := [2, 1, 2, 1, 6, 2, 7]
def baseStart_1171512 : Nat := 118140960795 + 1171512 * 2 ^ 59
def prefixEnd_1171512 : Nat := 4983230072969 + 3 ^ 40 * 1171512 * 2
def baseEnd_1171512 : Nat := 29706111037537070993201

theorem tailTrace_1171512 : CollatzResearch.WordTrace tailWord_1171512 prefixEnd_1171512 29706111037537070993201 := by
  unfold tailWord_1171512
  simp only [CollatzResearch.WordTrace]
  refine ⟨21364276465909788582830395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28485701954546384777107193 21364276465909788582830395)
  ·
    refine ⟨32046414698864682874245593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21364276465909788582830395 32046414698864682874245593)
    ·
      refine ⟨24034811024148512155684195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32046414698864682874245593 24034811024148512155684195)
      ·
        refine ⟨36052216536222768233526293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24034811024148512155684195 36052216536222768233526293)
        ·
          refine ⟨1689947650135442260946545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36052216536222768233526293 1689947650135442260946545)
          ·
            refine ⟨1267460737601581695709909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1689947650135442260946545 1267460737601581695709909)
            ·
              refine ⟨29706111037537070993201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1267460737601581695709909 29706111037537070993201)
              ·
                rfl

theorem cell21_1171512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 7].length) (baseStart_1171512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171512 prefixEnd_1171512 := by exact prefixLift 1171512
  have htrace : WordTrace (prefixWord ++ tailWord_1171512) baseStart_1171512 baseEnd_1171512 := by
    simpa [prefixWord, tailWord_1171512, baseEnd_1171512] using wordTrace_append hprefix tailTrace_1171512
  have hstable : (prefixWord ++ tailWord_1171512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171512).length < 2 ^ (prefixWord ++ tailWord_1171512).sum := by decide
  have hdescent : baseEnd_1171512 < baseStart_1171512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171518 : List Nat := [4, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_1171518 : Nat := 118140960795 + 1171518 * 2 ^ 59
def prefixEnd_1171518 : Nat := 4983230072969 + 3 ^ 40 * 1171518 * 2
def baseEnd_1171518 : Nat := 267356368619578961838797

theorem tailTrace_1171518 : CollatzResearch.WordTrace tailWord_1171518 prefixEnd_1171518 267356368619578961838797 := by
  unfold tailWord_1171518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5341096471224730023797401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28485847846531893460252805 5341096471224730023797401)
  ·
    refine ⟨4005822353418547517848051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5341096471224730023797401 4005822353418547517848051)
    ·
      refine ⟨6008733530127821276772077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4005822353418547517848051 6008733530127821276772077)
      ·
        refine ⟨2253275073797932978789529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6008733530127821276772077 2253275073797932978789529)
        ·
          refine ⟨1689956305348449734092147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2253275073797932978789529 1689956305348449734092147)
          ·
            refine ⟨2534934458022674601138221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689956305348449734092147 2534934458022674601138221)
            ·
              refine ⟨950600421758502975426833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2534934458022674601138221 950600421758502975426833)
              ·
                refine ⟨712950316318877231570125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950600421758502975426833 712950316318877231570125)
                ·
                  refine ⟨267356368619578961838797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712950316318877231570125 267356368619578961838797)
                  ·
                    rfl

theorem cell21_1171518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_1171518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171518 prefixEnd_1171518 := by exact prefixLift 1171518
  have htrace : WordTrace (prefixWord ++ tailWord_1171518) baseStart_1171518 baseEnd_1171518 := by
    simpa [prefixWord, tailWord_1171518, baseEnd_1171518] using wordTrace_append hprefix tailTrace_1171518
  have hstable : (prefixWord ++ tailWord_1171518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171518).length < 2 ^ (prefixWord ++ tailWord_1171518).sum := by decide
  have hdescent : baseEnd_1171518 < baseStart_1171518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171574 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1171574 : Nat := 118140960795 + 1171574 * 2 ^ 59
def prefixEnd_1171574 : Nat := 4983230072969 + 3 ^ 40 * 1171574 * 2
def baseEnd_1171574 : Nat := 267369148582535308905349

theorem tailTrace_1171574 : CollatzResearch.WordTrace tailWord_1171574 prefixEnd_1171574 267369148582535308905349 := by
  unfold tailWord_1171574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2670675891099685109651111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28487209505063307836278517 2670675891099685109651111)
  ·
    refine ⟨4006013836649527664476667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2670675891099685109651111 4006013836649527664476667)
    ·
      refine ⟨6009020754974291496715001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4006013836649527664476667 6009020754974291496715001)
      ·
        refine ⟨4506765566230718622536251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6009020754974291496715001 4506765566230718622536251)
        ·
          refine ⟨6760148349346077933804377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4506765566230718622536251 6760148349346077933804377)
          ·
            refine ⟨5070111262009558450353283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6760148349346077933804377 5070111262009558450353283)
            ·
              refine ⟨7605166893014337675529925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5070111262009558450353283 7605166893014337675529925)
              ·
                refine ⟨1425968792440188314161861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7605166893014337675529925 1425968792440188314161861)
                ·
                  refine ⟨267369148582535308905349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1425968792440188314161861 267369148582535308905349)
                  ·
                    rfl

theorem cell21_1171574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1171574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171574 prefixEnd_1171574 := by exact prefixLift 1171574
  have htrace : WordTrace (prefixWord ++ tailWord_1171574) baseStart_1171574 baseEnd_1171574 := by
    simpa [prefixWord, tailWord_1171574, baseEnd_1171574] using wordTrace_append hprefix tailTrace_1171574
  have hstable : (prefixWord ++ tailWord_1171574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171574).length < 2 ^ (prefixWord ++ tailWord_1171574).sum := by decide
  have hdescent : baseEnd_1171574 < baseStart_1171574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171577 : List Nat := [1, 2, 1, 3, 4, 3, 2, 2, 3]
def baseStart_1171577 : Nat := 118140960795 + 1171577 * 2 ^ 59
def prefixEnd_1171577 : Nat := 4983230072969 + 3 ^ 40 * 1171577 * 2
def baseEnd_1171577 : Nat := 267369833223407970355343

theorem tailTrace_1171577 : CollatzResearch.WordTrace tailWord_1171577 prefixEnd_1171577 267369833223407970355343 := by
  unfold tailWord_1171577
  simp only [CollatzResearch.WordTrace]
  refine ⟨42730923676584093266776985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28487282451056062177851323 42730923676584093266776985)
  ·
    refine ⟨32048192757438069950082739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42730923676584093266776985 32048192757438069950082739)
    ·
      refine ⟨48072289136157104925124109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32048192757438069950082739 48072289136157104925124109)
      ·
        refine ⟨18027108426058914346921541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48072289136157104925124109 18027108426058914346921541)
        ·
          refine ⟨3380082829886046440047789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18027108426058914346921541 3380082829886046440047789)
          ·
            refine ⟨1267531061207267415017921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3380082829886046440047789 1267531061207267415017921)
            ·
              refine ⟨950648295905450561263441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267531061207267415017921 950648295905450561263441)
              ·
                refine ⟨712986221929087920947581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950648295905450561263441 712986221929087920947581)
                ·
                  refine ⟨267369833223407970355343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712986221929087920947581 267369833223407970355343)
                  ·
                    rfl

theorem cell21_1171577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 3].length) (baseStart_1171577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171577 prefixEnd_1171577 := by exact prefixLift 1171577
  have htrace : WordTrace (prefixWord ++ tailWord_1171577) baseStart_1171577 baseEnd_1171577 := by
    simpa [prefixWord, tailWord_1171577, baseEnd_1171577] using wordTrace_append hprefix tailTrace_1171577
  have hstable : (prefixWord ++ tailWord_1171577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171577).length < 2 ^ (prefixWord ++ tailWord_1171577).sum := by decide
  have hdescent : baseEnd_1171577 < baseStart_1171577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171670 : List Nat := [5, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1171670 : Nat := 118140960795 + 1171670 * 2 ^ 59
def prefixEnd_1171670 : Nat := 4983230072969 + 3 ^ 40 * 1171670 * 2
def baseEnd_1171670 : Nat := 267391057090460475305153

theorem tailTrace_1171670 : CollatzResearch.WordTrace tailWord_1171670 prefixEnd_1171670 267391057090460475305153 := by
  unfold tailWord_1171670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2670894729077948134369529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28489543776831446766608309 2670894729077948134369529)
  ·
    refine ⟨2003171046808461100777147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2670894729077948134369529 2003171046808461100777147)
    ·
      refine ⟨3004756570212691651165721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2003171046808461100777147 3004756570212691651165721)
      ·
        refine ⟨2253567427659518738374291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3004756570212691651165721 2253567427659518738374291)
        ·
          refine ⟨3380351141489278107561437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2253567427659518738374291 3380351141489278107561437)
          ·
            refine ⟨1267631678058479290335539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3380351141489278107561437 1267631678058479290335539)
            ·
              refine ⟨1901447517087718935503309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267631678058479290335539 1901447517087718935503309)
              ·
                refine ⟨713042818907894600813741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1901447517087718935503309 713042818907894600813741)
                ·
                  refine ⟨267391057090460475305153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713042818907894600813741 267391057090460475305153)
                  ·
                    rfl

theorem cell21_1171670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1171670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171670 prefixEnd_1171670 := by exact prefixLift 1171670
  have htrace : WordTrace (prefixWord ++ tailWord_1171670) baseStart_1171670 baseEnd_1171670 := by
    simpa [prefixWord, tailWord_1171670, baseEnd_1171670] using wordTrace_append hprefix tailTrace_1171670
  have hstable : (prefixWord ++ tailWord_1171670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171670).length < 2 ^ (prefixWord ++ tailWord_1171670).sum := by decide
  have hdescent : baseEnd_1171670 < baseStart_1171670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171692 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_1171692 : Nat := 118140960795 + 1171692 * 2 ^ 59
def prefixEnd_1171692 : Nat := 4983230072969 + 3 ^ 40 * 1171692 * 2
def baseEnd_1171692 : Nat := 267396077790193325938441

theorem tailTrace_1171692 : CollatzResearch.WordTrace tailWord_1171692 prefixEnd_1171692 267396077790193325938441 := by
  unfold tailWord_1171692
  simp only [CollatzResearch.WordTrace]
  refine ⟨21367559035583733953606665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28490078714111645271475553 21367559035583733953606665)
  ·
    refine ⟨16025669276687800465204999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21367559035583733953606665 16025669276687800465204999)
    ·
      refine ⟨24038503915031700697807499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16025669276687800465204999 24038503915031700697807499)
      ·
        refine ⟨36057755872547551046711249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24038503915031700697807499 36057755872547551046711249)
        ·
          refine ⟨27043316904410663285033437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36057755872547551046711249 27043316904410663285033437)
          ·
            refine ⟨10141243839153998731887539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27043316904410663285033437 10141243839153998731887539)
            ·
              refine ⟨15211865758730998097831309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10141243839153998731887539 15211865758730998097831309)
              ·
                refine ⟨5704449659524124286686741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15211865758730998097831309 5704449659524124286686741)
                ·
                  refine ⟨267396077790193325938441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5704449659524124286686741 267396077790193325938441)
                  ·
                    rfl

theorem cell21_1171692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_1171692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171692 prefixEnd_1171692 := by exact prefixLift 1171692
  have htrace : WordTrace (prefixWord ++ tailWord_1171692) baseStart_1171692 baseEnd_1171692 := by
    simpa [prefixWord, tailWord_1171692, baseEnd_1171692] using wordTrace_append hprefix tailTrace_1171692
  have hstable : (prefixWord ++ tailWord_1171692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171692).length < 2 ^ (prefixWord ++ tailWord_1171692).sum := by decide
  have hdescent : baseEnd_1171692 < baseStart_1171692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171695 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 5]
def baseStart_1171695 : Nat := 118140960795 + 1171695 * 2 ^ 59
def prefixEnd_1171695 : Nat := 4983230072969 + 3 ^ 40 * 1171695 * 2
def baseEnd_1171695 : Nat := 267396762431065987388435

theorem tailTrace_1171695 : CollatzResearch.WordTrace tailWord_1171695 prefixEnd_1171695 267396762431065987388435 := by
  unfold tailWord_1171695
  simp only [CollatzResearch.WordTrace]
  refine ⟨42735227490156599419572539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28490151660104399613048359 42735227490156599419572539)
  ·
    refine ⟨64102841235234899129358809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42735227490156599419572539 64102841235234899129358809)
    ·
      refine ⟨48077130926426174347019107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64102841235234899129358809 48077130926426174347019107)
      ·
        refine ⟨72115696389639261520528661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48077130926426174347019107 72115696389639261520528661)
        ·
          refine ⟨3380423268264340383774781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72115696389639261520528661 3380423268264340383774781)
          ·
            refine ⟨1267658725599127643915543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3380423268264340383774781 1267658725599127643915543)
            ·
              refine ⟨1901488088398691465873315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267658725599127643915543 1901488088398691465873315)
              ·
                refine ⟨2852232132598037198809973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901488088398691465873315 2852232132598037198809973)
                ·
                  refine ⟨267396762431065987388435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2852232132598037198809973 267396762431065987388435)
                  ·
                    rfl

theorem cell21_1171695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 5].length) (baseStart_1171695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171695 prefixEnd_1171695 := by exact prefixLift 1171695
  have htrace : WordTrace (prefixWord ++ tailWord_1171695) baseStart_1171695 baseEnd_1171695 := by
    simpa [prefixWord, tailWord_1171695, baseEnd_1171695] using wordTrace_append hprefix tailTrace_1171695
  have hstable : (prefixWord ++ tailWord_1171695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171695).length < 2 ^ (prefixWord ++ tailWord_1171695).sum := by decide
  have hdescent : baseEnd_1171695 < baseStart_1171695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171844 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1171844 : Nat := 118140960795 + 1171844 * 2 ^ 59
def prefixEnd_1171844 : Nat := 4983230072969 + 3 ^ 40 * 1171844 * 2
def baseEnd_1171844 : Nat := 267430766261074839404797

theorem tailTrace_1171844 : CollatzResearch.WordTrace tailWord_1171844 prefixEnd_1171844 267430766261074839404797 := by
  unfold tailWord_1171844
  simp only [CollatzResearch.WordTrace]
  refine ⟨21370330983308398933373293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28493774644411198577831057 21370330983308398933373293)
  ·
    refine ⟨8013874118740649600014985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21370330983308398933373293 8013874118740649600014985)
    ·
      refine ⟨6010405589055487200011239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8013874118740649600014985 6010405589055487200011239)
      ·
        refine ⟨9015608383583230800016859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6010405589055487200011239 9015608383583230800016859)
        ·
          refine ⟨13523412575374846200025289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9015608383583230800016859 13523412575374846200025289)
          ·
            refine ⟨10142559431531134650018967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13523412575374846200025289 10142559431531134650018967)
            ·
              refine ⟨15213839147296701975028451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10142559431531134650018967 15213839147296701975028451)
              ·
                refine ⟨22820758720945052962542677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15213839147296701975028451 22820758720945052962542677)
                ·
                  refine ⟨267430766261074839404797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22820758720945052962542677 267430766261074839404797)
                  ·
                    rfl

theorem cell21_1171844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1171844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171844 prefixEnd_1171844 := by exact prefixLift 1171844
  have htrace : WordTrace (prefixWord ++ tailWord_1171844) baseStart_1171844 baseEnd_1171844 := by
    simpa [prefixWord, tailWord_1171844, baseEnd_1171844] using wordTrace_append hprefix tailTrace_1171844
  have hstable : (prefixWord ++ tailWord_1171844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171844).length < 2 ^ (prefixWord ++ tailWord_1171844).sum := by decide
  have hdescent : baseEnd_1171844 < baseStart_1171844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171875 : List Nat := [1, 1, 1, 4, 1, 5, 2, 6]
def baseStart_1171875 : Nat := 118140960795 + 1171875 * 2 ^ 59
def prefixEnd_1171875 : Nat := 4983230072969 + 3 ^ 40 * 1171875 * 2
def baseEnd_1171875 : Nat := 89145946961141891462689

theorem tailTrace_1171875 : CollatzResearch.WordTrace tailWord_1171875 prefixEnd_1171875 89145946961141891462689 := by
  unfold tailWord_1171875
  simp only [CollatzResearch.WordTrace]
  refine ⟨42741792629504490161125079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28494528419669660107416719 42741792629504490161125079)
  ·
    refine ⟨64112688944256735241687619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42741792629504490161125079 64112688944256735241687619)
    ·
      refine ⟨96169033416385102862531429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64112688944256735241687619 96169033416385102862531429)
      ·
        refine ⟨18031693765572206786724643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96169033416385102862531429 18031693765572206786724643)
        ·
          refine ⟨27047540648358310180086965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18031693765572206786724643 27047540648358310180086965)
          ·
            refine ⟨2535706935783591579383153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27047540648358310180086965 2535706935783591579383153)
            ·
              refine ⟨1901780201837693684537365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2535706935783591579383153 1901780201837693684537365)
              ·
                refine ⟨89145946961141891462689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1901780201837693684537365 89145946961141891462689)
                ·
                  rfl

theorem cell21_1171875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 6].length) (baseStart_1171875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171875 prefixEnd_1171875 := by exact prefixLift 1171875
  have htrace : WordTrace (prefixWord ++ tailWord_1171875) baseStart_1171875 baseEnd_1171875 := by
    simpa [prefixWord, tailWord_1171875, baseEnd_1171875] using wordTrace_append hprefix tailTrace_1171875
  have hstable : (prefixWord ++ tailWord_1171875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171875).length < 2 ^ (prefixWord ++ tailWord_1171875).sum := by decide
  have hdescent : baseEnd_1171875 < baseStart_1171875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171957 : List Nat := [1, 3, 5, 1, 2, 1, 2, 3, 3]
def baseStart_1171957 : Nat := 118140960795 + 1171957 * 2 ^ 59
def prefixEnd_1171957 : Nat := 4983230072969 + 3 ^ 40 * 1171957 * 2
def baseEnd_1171957 : Nat := 267456554400611754021233

theorem tailTrace_1171957 : CollatzResearch.WordTrace tailWord_1171957 prefixEnd_1171957 267456554400611754021233 := by
  unfold tailWord_1171957
  simp only [CollatzResearch.WordTrace]
  refine ⟨42744783415207418165610125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28496522276804945443740083 42744783415207418165610125)
  ·
    refine ⟨16029293780702781812103797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42744783415207418165610125 16029293780702781812103797)
    ·
      refine ⟨1502746291940885794884731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16029293780702781812103797 1502746291940885794884731)
      ·
        refine ⟨2254119437911328692327097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1502746291940885794884731 2254119437911328692327097)
        ·
          refine ⟨1690589578433496519245323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2254119437911328692327097 1690589578433496519245323)
          ·
            refine ⟨2535884367650244778867985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690589578433496519245323 2535884367650244778867985)
            ·
              refine ⟨1901913275737683584150989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2535884367650244778867985 1901913275737683584150989)
              ·
                refine ⟨713217478401631344056621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1901913275737683584150989 713217478401631344056621)
                ·
                  refine ⟨267456554400611754021233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713217478401631344056621 267456554400611754021233)
                  ·
                    rfl

theorem cell21_1171957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_1171957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171957 prefixEnd_1171957 := by exact prefixLift 1171957
  have htrace : WordTrace (prefixWord ++ tailWord_1171957) baseStart_1171957 baseEnd_1171957 := by
    simpa [prefixWord, tailWord_1171957, baseEnd_1171957] using wordTrace_append hprefix tailTrace_1171957
  have hstable : (prefixWord ++ tailWord_1171957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171957).length < 2 ^ (prefixWord ++ tailWord_1171957).sum := by decide
  have hdescent : baseEnd_1171957 < baseStart_1171957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171965 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 7]
def baseStart_1171965 : Nat := 118140960795 + 1171965 * 2 ^ 59
def prefixEnd_1171965 : Nat := 4983230072969 + 3 ^ 40 * 1171965 * 2
def baseEnd_1171965 : Nat := 267458380109605517887883

theorem tailTrace_1171965 : CollatzResearch.WordTrace tailWord_1171965 prefixEnd_1171965 267458380109605517887883 := by
  unfold tailWord_1171965
  simp only [CollatzResearch.WordTrace]
  refine ⟨42745075199178435531901349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28496716799452290354600899 42745075199178435531901349)
  ·
    refine ⟨8014701599845956662231503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42745075199178435531901349 8014701599845956662231503)
    ·
      refine ⟨12022052399768934993347255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8014701599845956662231503 12022052399768934993347255)
      ·
        refine ⟨18033078599653402490020883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12022052399768934993347255 18033078599653402490020883)
        ·
          refine ⟨27049617899480103735031325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18033078599653402490020883 27049617899480103735031325)
          ·
            refine ⟨10143606712305038900636747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27049617899480103735031325 10143606712305038900636747)
            ·
              refine ⟨15215410068457558350955121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10143606712305038900636747 15215410068457558350955121)
              ·
                refine ⟨11411557551343168763216341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15215410068457558350955121 11411557551343168763216341)
                ·
                  refine ⟨267458380109605517887883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11411557551343168763216341 267458380109605517887883)
                  ·
                    rfl

theorem cell21_1171965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_1171965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171965 prefixEnd_1171965 := by exact prefixLift 1171965
  have htrace : WordTrace (prefixWord ++ tailWord_1171965) baseStart_1171965 baseEnd_1171965 := by
    simpa [prefixWord, tailWord_1171965, baseEnd_1171965] using wordTrace_append hprefix tailTrace_1171965
  have hstable : (prefixWord ++ tailWord_1171965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171965).length < 2 ^ (prefixWord ++ tailWord_1171965).sum := by decide
  have hdescent : baseEnd_1171965 < baseStart_1171965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171974 : List Nat := [6, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1171974 : Nat := 118140960795 + 1171974 * 2 ^ 59
def prefixEnd_1171974 : Nat := 4983230072969 + 3 ^ 40 * 1171974 * 2
def baseEnd_1171974 : Nat := 267460434032223502237865

theorem tailTrace_1171974 : CollatzResearch.WordTrace tailWord_1171974 prefixEnd_1171974 267460434032223502237865 := by
  unfold tailWord_1171974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335793858004557189655593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28496935637430553379319317 1335793858004557189655593)
  ·
    refine ⟨1001845393503417892241695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1335793858004557189655593 1001845393503417892241695)
    ·
      refine ⟨1502768090255126838362543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1001845393503417892241695 1502768090255126838362543)
      ·
        refine ⟨2254152135382690257543815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1502768090255126838362543 2254152135382690257543815)
        ·
          refine ⟨3381228203074035386315723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2254152135382690257543815 3381228203074035386315723)
          ·
            refine ⟨5071842304611053079473585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3381228203074035386315723 5071842304611053079473585)
            ·
              refine ⟨3803881728458289809605189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5071842304611053079473585 3803881728458289809605189)
              ·
                refine ⟨713227824085929339300973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3803881728458289809605189 713227824085929339300973)
                ·
                  refine ⟨267460434032223502237865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713227824085929339300973 267460434032223502237865)
                  ·
                    rfl

theorem cell21_1171974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1171974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171974 prefixEnd_1171974 := by exact prefixLift 1171974
  have htrace : WordTrace (prefixWord ++ tailWord_1171974) baseStart_1171974 baseEnd_1171974 := by
    simpa [prefixWord, tailWord_1171974, baseEnd_1171974] using wordTrace_append hprefix tailTrace_1171974
  have hstable : (prefixWord ++ tailWord_1171974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171974).length < 2 ^ (prefixWord ++ tailWord_1171974).sum := by decide
  have hdescent : baseEnd_1171974 < baseStart_1171974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171982 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_1171982 : Nat := 118140960795 + 1171982 * 2 ^ 59
def prefixEnd_1171982 : Nat := 4983230072969 + 3 ^ 40 * 1171982 * 2
def baseEnd_1171982 : Nat := 267462259741217266104515

theorem tailTrace_1171982 : CollatzResearch.WordTrace tailWord_1171982 prefixEnd_1171982 267462259741217266104515 := by
  unfold tailWord_1171982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5343211905014605929408775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28497130160077898290180133 5343211905014605929408775)
  ·
    refine ⟨8014817857521908894113163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5343211905014605929408775 8014817857521908894113163)
    ·
      refine ⟨12022226786282863341169745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8014817857521908894113163 12022226786282863341169745)
      ·
        refine ⟨9016670089712147505877309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12022226786282863341169745 9016670089712147505877309)
        ·
          refine ⟨3381251283642055314703991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9016670089712147505877309 3381251283642055314703991)
          ·
            refine ⟨5071876925463082972055987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3381251283642055314703991 5071876925463082972055987)
            ·
              refine ⟨7607815388194624458083981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5071876925463082972055987 7607815388194624458083981)
              ·
                refine ⟨2852930770572984171781493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7607815388194624458083981 2852930770572984171781493)
                ·
                  refine ⟨267462259741217266104515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2852930770572984171781493 267462259741217266104515)
                  ·
                    rfl

theorem cell21_1171982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_1171982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1171982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1171982 prefixEnd_1171982 := by exact prefixLift 1171982
  have htrace : WordTrace (prefixWord ++ tailWord_1171982) baseStart_1171982 baseEnd_1171982 := by
    simpa [prefixWord, tailWord_1171982, baseEnd_1171982] using wordTrace_append hprefix tailTrace_1171982
  have hstable : (prefixWord ++ tailWord_1171982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171982).length < 2 ^ (prefixWord ++ tailWord_1171982).sum := by decide
  have hdescent : baseEnd_1171982 < baseStart_1171982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172089 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 4]
def baseStart_1172089 : Nat := 118140960795 + 1172089 * 2 ^ 59
def prefixEnd_1172089 : Nat := 4983230072969 + 3 ^ 40 * 1172089 * 2
def baseEnd_1172089 : Nat := 267486678599008857820963

theorem tailTrace_1172089 : CollatzResearch.WordTrace tailWord_1172089 prefixEnd_1172089 267486678599008857820963 := by
  unfold tailWord_1172089
  simp only [CollatzResearch.WordTrace]
  refine ⟨42749597850729204709415321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28499731900486136472943547 42749597850729204709415321)
  ·
    refine ⟨32062198388046903532061491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42749597850729204709415321 32062198388046903532061491)
    ·
      refine ⟨48093297582070355298092237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32062198388046903532061491 48093297582070355298092237)
      ·
        refine ⟨18034986593276383236784589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48093297582070355298092237 18034986593276383236784589)
        ·
          refine ⟨6763119972478643713794221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18034986593276383236784589 6763119972478643713794221)
          ·
            refine ⟨2536169989679491392672833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6763119972478643713794221 2536169989679491392672833)
            ·
              refine ⟨1902127492259618544504625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2536169989679491392672833 1902127492259618544504625)
              ·
                refine ⟨1426595619194713908378469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1902127492259618544504625 1426595619194713908378469)
                ·
                  refine ⟨267486678599008857820963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1426595619194713908378469 267486678599008857820963)
                  ·
                    rfl

theorem cell21_1172089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_1172089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172089 prefixEnd_1172089 := by exact prefixLift 1172089
  have htrace : WordTrace (prefixWord ++ tailWord_1172089) baseStart_1172089 baseEnd_1172089 := by
    simpa [prefixWord, tailWord_1172089, baseEnd_1172089] using wordTrace_append hprefix tailTrace_1172089
  have hstable : (prefixWord ++ tailWord_1172089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172089).length < 2 ^ (prefixWord ++ tailWord_1172089).sum := by decide
  have hdescent : baseEnd_1172089 < baseStart_1172089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172210 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_1172210 : Nat := 118140960795 + 1172210 * 2 ^ 59
def prefixEnd_1172210 : Nat := 4983230072969 + 3 ^ 40 * 1172210 * 2
def baseEnd_1172210 : Nat := 267514292447539536304049

theorem tailTrace_1172210 : CollatzResearch.WordTrace tailWord_1172210 prefixEnd_1172210 267514292447539536304049 := by
  unfold tailWord_1172210
  simp only [CollatzResearch.WordTrace]
  refine ⟨10688502770822710593642521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28502674055527228249713389 10688502770822710593642521)
  ·
    refine ⟨8016377078117032945231891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10688502770822710593642521 8016377078117032945231891)
    ·
      refine ⟨12024565617175549417847837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8016377078117032945231891 12024565617175549417847837)
      ·
        refine ⟨4509212106440831031692939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12024565617175549417847837 4509212106440831031692939)
        ·
          refine ⟨6763818159661246547539409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4509212106440831031692939 6763818159661246547539409)
          ·
            refine ⟨5072863619745934910654557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6763818159661246547539409 5072863619745934910654557)
            ·
              refine ⟨1902323857404725591495459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5072863619745934910654557 1902323857404725591495459)
              ·
                refine ⟨2853485786107088387243189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1902323857404725591495459 2853485786107088387243189)
                ·
                  refine ⟨267514292447539536304049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2853485786107088387243189 267514292447539536304049)
                  ·
                    rfl

theorem cell21_1172210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_1172210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172210 prefixEnd_1172210 := by exact prefixLift 1172210
  have htrace : WordTrace (prefixWord ++ tailWord_1172210) baseStart_1172210 baseEnd_1172210 := by
    simpa [prefixWord, tailWord_1172210, baseEnd_1172210] using wordTrace_append hprefix tailTrace_1172210
  have hstable : (prefixWord ++ tailWord_1172210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172210).length < 2 ^ (prefixWord ++ tailWord_1172210).sum := by decide
  have hdescent : baseEnd_1172210 < baseStart_1172210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172289 : List Nat := [1, 2, 5, 3, 1, 1, 3, 5]
def baseStart_1172289 : Nat := 118140960795 + 1172289 * 2 ^ 59
def prefixEnd_1172289 : Nat := 4983230072969 + 3 ^ 40 * 1172289 * 2
def baseEnd_1172289 : Nat := 89177440441284318162407

theorem tailTrace_1172289 : CollatzResearch.WordTrace tailWord_1172289 prefixEnd_1172289 89177440441284318162407 := by
  unfold tailWord_1172289
  simp only [CollatzResearch.WordTrace]
  refine ⟨42756892450004638866695921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28504594966669759244463947 42756892450004638866695921)
  ·
    refine ⟨32067669337503479150021941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42756892450004638866695921 32067669337503479150021941)
    ·
      refine ⟨3006344000390951170314557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32067669337503479150021941 3006344000390951170314557)
      ·
        refine ⟨1127379000146606688867959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3006344000390951170314557 1127379000146606688867959)
        ·
          refine ⟨1691068500219910033301939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127379000146606688867959 1691068500219910033301939)
          ·
            refine ⟨2536602750329865049952909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691068500219910033301939 2536602750329865049952909)
            ·
              refine ⟨951226031373699393732341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2536602750329865049952909 951226031373699393732341)
              ·
                refine ⟨89177440441284318162407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 951226031373699393732341 89177440441284318162407)
                ·
                  rfl

theorem cell21_1172289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 5].length) (baseStart_1172289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172289 prefixEnd_1172289 := by exact prefixLift 1172289
  have htrace : WordTrace (prefixWord ++ tailWord_1172289) baseStart_1172289 baseEnd_1172289 := by
    simpa [prefixWord, tailWord_1172289, baseEnd_1172289] using wordTrace_append hprefix tailTrace_1172289
  have hstable : (prefixWord ++ tailWord_1172289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172289).length < 2 ^ (prefixWord ++ tailWord_1172289).sum := by decide
  have hdescent : baseEnd_1172289 < baseStart_1172289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172314 : List Nat := [3, 1, 1, 2, 1, 5, 8]
def baseStart_1172314 : Nat := 118140960795 + 1172314 * 2 ^ 59
def prefixEnd_1172314 : Nat := 4983230072969 + 3 ^ 40 * 1172314 * 2
def baseEnd_1172314 : Nat := 29726447407162051841167

theorem tailTrace_1172314 : CollatzResearch.WordTrace tailWord_1172314 prefixEnd_1172314 29726447407162051841167 := by
  unfold tailWord_1172314
  simp only [CollatzResearch.WordTrace]
  refine ⟨10689451068728517034088999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28505202849942712090903997 10689451068728517034088999)
  ·
    refine ⟨16034176603092775551133499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10689451068728517034088999 16034176603092775551133499)
    ·
      refine ⟨24051264904639163326700249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16034176603092775551133499 24051264904639163326700249)
      ·
        refine ⟨18038448678479372495025187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24051264904639163326700249 18038448678479372495025187)
        ·
          refine ⟨27057673017719058742537781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18038448678479372495025187 27057673017719058742537781)
          ·
            refine ⟨2536656845411161757112917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27057673017719058742537781 2536656845411161757112917)
            ·
              refine ⟨29726447407162051841167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2536656845411161757112917 29726447407162051841167)
              ·
                rfl

theorem cell21_1172314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 8].length) (baseStart_1172314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172314 prefixEnd_1172314 := by exact prefixLift 1172314
  have htrace : WordTrace (prefixWord ++ tailWord_1172314) baseStart_1172314 baseEnd_1172314 := by
    simpa [prefixWord, tailWord_1172314, baseEnd_1172314] using wordTrace_append hprefix tailTrace_1172314
  have hstable : (prefixWord ++ tailWord_1172314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172314).length < 2 ^ (prefixWord ++ tailWord_1172314).sum := by decide
  have hdescent : baseEnd_1172314 < baseStart_1172314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172345 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 5]
def baseStart_1172345 : Nat := 118140960795 + 1172345 * 2 ^ 59
def prefixEnd_1172345 : Nat := 4983230072969 + 3 ^ 40 * 1172345 * 2
def baseEnd_1172345 : Nat := 267545101286809301553773

theorem tailTrace_1172345 : CollatzResearch.WordTrace tailWord_1172345 prefixEnd_1172345 267545101286809301553773 := by
  unfold tailWord_1172345
  simp only [CollatzResearch.WordTrace]
  refine ⟨42758934937801760430734489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28505956625201173620489659 42758934937801760430734489)
  ·
    refine ⟨32069201203351320323050867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42758934937801760430734489 32069201203351320323050867)
    ·
      refine ⟨48103801805026980484576301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32069201203351320323050867 48103801805026980484576301)
      ·
        refine ⟨18038925676885117681716113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48103801805026980484576301 18038925676885117681716113)
        ·
          refine ⟨13529194257663838261287085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18038925676885117681716113 13529194257663838261287085)
          ·
            refine ⟨5073447846623939347982657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13529194257663838261287085 5073447846623939347982657)
            ·
              refine ⟨3805085884967954510986993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5073447846623939347982657 3805085884967954510986993)
              ·
                refine ⟨2853814413725965883240245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3805085884967954510986993 2853814413725965883240245)
                ·
                  refine ⟨267545101286809301553773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2853814413725965883240245 267545101286809301553773)
                  ·
                    rfl

theorem cell21_1172345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_1172345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172345 prefixEnd_1172345 := by exact prefixLift 1172345
  have htrace : WordTrace (prefixWord ++ tailWord_1172345) baseStart_1172345 baseEnd_1172345 := by
    simpa [prefixWord, tailWord_1172345, baseEnd_1172345] using wordTrace_append hprefix tailTrace_1172345
  have hstable : (prefixWord ++ tailWord_1172345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172345).length < 2 ^ (prefixWord ++ tailWord_1172345).sum := by decide
  have hdescent : baseEnd_1172345 < baseStart_1172345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172354 : List Nat := [3, 4, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1172354 : Nat := 118140960795 + 1172354 * 2 ^ 59
def prefixEnd_1172354 : Nat := 4983230072969 + 3 ^ 40 * 1172354 * 2
def baseEnd_1172354 : Nat := 267547155209427285903755

theorem tailTrace_1172354 : CollatzResearch.WordTrace tailWord_1172354 prefixEnd_1172354 267547155209427285903755 := by
  unfold tailWord_1172354
  simp only [CollatzResearch.WordTrace]
  refine ⟨10689815798692288741953029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28506175463179436645208077 10689815798692288741953029)
  ·
    refine ⟨2004340462254804139116193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10689815798692288741953029 2004340462254804139116193)
    ·
      refine ⟨1503255346691103104337145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2004340462254804139116193 1503255346691103104337145)
      ·
        refine ⟨1127441510018327328252859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1503255346691103104337145 1127441510018327328252859)
        ·
          refine ⟨1691162265027490992379289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127441510018327328252859 1691162265027490992379289)
          ·
            refine ⟨1268371698770618244284467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1691162265027490992379289 1268371698770618244284467)
            ·
              refine ⟨1902557548155927366426701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268371698770618244284467 1902557548155927366426701)
              ·
                refine ⟨713459080558472762410013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1902557548155927366426701 713459080558472762410013)
                ·
                  refine ⟨267547155209427285903755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713459080558472762410013 267547155209427285903755)
                  ·
                    rfl

theorem cell21_1172354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1172354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172354 prefixEnd_1172354 := by exact prefixLift 1172354
  have htrace : WordTrace (prefixWord ++ tailWord_1172354) baseStart_1172354 baseEnd_1172354 := by
    simpa [prefixWord, tailWord_1172354, baseEnd_1172354] using wordTrace_append hprefix tailTrace_1172354
  have hstable : (prefixWord ++ tailWord_1172354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172354).length < 2 ^ (prefixWord ++ tailWord_1172354).sum := by decide
  have hdescent : baseEnd_1172354 < baseStart_1172354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172562 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_1172562 : Nat := 118140960795 + 1172562 * 2 ^ 59
def prefixEnd_1172562 : Nat := 4983230072969 + 3 ^ 40 * 1172562 * 2
def baseEnd_1172562 : Nat := 267594623643265146436663

theorem tailTrace_1172562 : CollatzResearch.WordTrace tailWord_1172562 prefixEnd_1172562 267594623643265146436663 := by
  unfold tailWord_1172562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10691712394503901622845985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28511233052010404327589293 10691712394503901622845985)
  ·
    refine ⟨8018784295877926217134489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10691712394503901622845985 8018784295877926217134489)
    ·
      refine ⟨6014088221908444662850867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8018784295877926217134489 6014088221908444662850867)
      ·
        refine ⟨9021132332862666994276301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6014088221908444662850867 9021132332862666994276301)
        ·
          refine ⟨3382924624823500122853613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9021132332862666994276301 3382924624823500122853613)
          ·
            refine ⟨1268596734308812546070105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3382924624823500122853613 1268596734308812546070105)
            ·
              refine ⟨951447550731609409552579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268596734308812546070105 951447550731609409552579)
              ·
                refine ⟨1427171326097414114328869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951447550731609409552579 1427171326097414114328869)
                ·
                  refine ⟨267594623643265146436663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1427171326097414114328869 267594623643265146436663)
                  ·
                    rfl

theorem cell21_1172562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_1172562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172562 prefixEnd_1172562 := by exact prefixLift 1172562
  have htrace : WordTrace (prefixWord ++ tailWord_1172562) baseStart_1172562 baseEnd_1172562 := by
    simpa [prefixWord, tailWord_1172562, baseEnd_1172562] using wordTrace_append hprefix tailTrace_1172562
  have hstable : (prefixWord ++ tailWord_1172562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172562).length < 2 ^ (prefixWord ++ tailWord_1172562).sum := by decide
  have hdescent : baseEnd_1172562 < baseStart_1172562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172601 : List Nat := [1, 2, 1, 3, 14]
def baseStart_1172601 : Nat := 118140960795 + 1172601 * 2 ^ 59
def prefixEnd_1172601 : Nat := 4983230072969 + 3 ^ 40 * 1172601 * 2
def baseEnd_1172601 : Nat := 3303747209563083275143

theorem tailTrace_1172601 : CollatzResearch.WordTrace tailWord_1172601 prefixEnd_1172601 3303747209563083275143 := by
  unfold tailWord_1172601
  simp only [CollatzResearch.WordTrace]
  refine ⟨42768272024874316152053657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28512181349916210768035771 42768272024874316152053657)
  ·
    refine ⟨32076204018655737114040243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42768272024874316152053657 32076204018655737114040243)
    ·
      refine ⟨48114306027983605671060365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32076204018655737114040243 48114306027983605671060365)
      ·
        refine ⟨18042864760493852126647637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48114306027983605671060365 18042864760493852126647637)
        ·
          refine ⟨3303747209563083275143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 18042864760493852126647637 3303747209563083275143)
          ·
            rfl

theorem cell21_1172601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 14].length) (baseStart_1172601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172601 prefixEnd_1172601 := by exact prefixLift 1172601
  have htrace : WordTrace (prefixWord ++ tailWord_1172601) baseStart_1172601 baseEnd_1172601 := by
    simpa [prefixWord, tailWord_1172601, baseEnd_1172601] using wordTrace_append hprefix tailTrace_1172601
  have hstable : (prefixWord ++ tailWord_1172601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172601).length < 2 ^ (prefixWord ++ tailWord_1172601).sum := by decide
  have hdescent : baseEnd_1172601 < baseStart_1172601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172604 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 4]
def baseStart_1172604 : Nat := 118140960795 + 1172604 * 2 ^ 59
def prefixEnd_1172604 : Nat := 4983230072969 + 3 ^ 40 * 1172604 * 2
def baseEnd_1172604 : Nat := 267604208615482406736577

theorem tailTrace_1172604 : CollatzResearch.WordTrace tailWord_1172604 prefixEnd_1172604 267604208615482406736577 := by
  unfold tailWord_1172604
  simp only [CollatzResearch.WordTrace]
  refine ⟨21384190721931723832206433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28512254295908965109608577 21384190721931723832206433)
  ·
    refine ⟨16038143041448792874154825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21384190721931723832206433 16038143041448792874154825)
    ·
      refine ⟨12028607281086594655616119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16038143041448792874154825 12028607281086594655616119)
      ·
        refine ⟨18042910921629891983424179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12028607281086594655616119 18042910921629891983424179)
        ·
          refine ⟨27064366382444837975136269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18042910921629891983424179 27064366382444837975136269)
          ·
            refine ⟨10149137393416814240676101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27064366382444837975136269 10149137393416814240676101)
            ·
              refine ⟨1902963261265652670126769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10149137393416814240676101 1902963261265652670126769)
              ·
                refine ⟨1427222445949239502595077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1902963261265652670126769 1427222445949239502595077)
                ·
                  refine ⟨267604208615482406736577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1427222445949239502595077 267604208615482406736577)
                  ·
                    rfl

theorem cell21_1172604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_1172604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172604 prefixEnd_1172604 := by exact prefixLift 1172604
  have htrace : WordTrace (prefixWord ++ tailWord_1172604) baseStart_1172604 baseEnd_1172604 := by
    simpa [prefixWord, tailWord_1172604, baseEnd_1172604] using wordTrace_append hprefix tailTrace_1172604
  have hstable : (prefixWord ++ tailWord_1172604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172604).length < 2 ^ (prefixWord ++ tailWord_1172604).sum := by decide
  have hdescent : baseEnd_1172604 < baseStart_1172604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172663 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 6]
def baseStart_1172663 : Nat := 118140960795 + 1172663 * 2 ^ 59
def prefixEnd_1172663 : Nat := 4983230072969 + 3 ^ 40 * 1172663 * 2
def baseEnd_1172663 : Nat := 267617673219311415253123

theorem tailTrace_1172663 : CollatzResearch.WordTrace tailWord_1172663 prefixEnd_1172663 267617673219311415253123 := by
  unfold tailWord_1172663
  simp only [CollatzResearch.WordTrace]
  refine ⟨42770533350649700740810643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28513688900433133827207095 42770533350649700740810643)
  ·
    refine ⟨64155800025974551111215965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42770533350649700740810643 64155800025974551111215965)
    ·
      refine ⟨24058425009740456666705987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64155800025974551111215965 24058425009740456666705987)
      ·
        refine ⟨36087637514610685000058981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24058425009740456666705987 36087637514610685000058981)
        ·
          refine ⟨6766432033989503437511059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36087637514610685000058981 6766432033989503437511059)
          ·
            refine ⟨10149648050984255156266589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6766432033989503437511059 10149648050984255156266589)
            ·
              refine ⟨3806118019119095683599971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10149648050984255156266589 3806118019119095683599971)
              ·
                refine ⟨5709177028678643525399957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3806118019119095683599971 5709177028678643525399957)
                ·
                  refine ⟨267617673219311415253123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5709177028678643525399957 267617673219311415253123)
                  ·
                    rfl

theorem cell21_1172663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_1172663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172663 prefixEnd_1172663 := by exact prefixLift 1172663
  have htrace : WordTrace (prefixWord ++ tailWord_1172663) baseStart_1172663 baseEnd_1172663 := by
    simpa [prefixWord, tailWord_1172663, baseEnd_1172663] using wordTrace_append hprefix tailTrace_1172663
  have hstable : (prefixWord ++ tailWord_1172663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172663).length < 2 ^ (prefixWord ++ tailWord_1172663).sum := by decide
  have hdescent : baseEnd_1172663 < baseStart_1172663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172677 : List Nat := [1, 3, 1, 1, 1, 1, 3, 10]
def baseStart_1172677 : Nat := 118140960795 + 1172677 * 2 ^ 59
def prefixEnd_1172677 : Nat := 4983230072969 + 3 ^ 40 * 1172677 * 2
def baseEnd_1172677 : Nat := 89206956070016834006587

theorem tailTrace_1172677 : CollatzResearch.WordTrace tailWord_1172677 prefixEnd_1172677 89206956070016834006587 := by
  unfold tailWord_1172677
  simp only [CollatzResearch.WordTrace]
  refine ⟨42771043972598981131820285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28514029315065987421213523 42771043972598981131820285)
  ·
    refine ⟨16039141489724617924432607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42771043972598981131820285 16039141489724617924432607)
    ·
      refine ⟨24058712234586926886648911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16039141489724617924432607 24058712234586926886648911)
      ·
        refine ⟨36088068351880390329973367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24058712234586926886648911 36088068351880390329973367)
        ·
          refine ⟨54132102527820585494960051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36088068351880390329973367 54132102527820585494960051)
          ·
            refine ⟨81198153791730878242440077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54132102527820585494960051 81198153791730878242440077)
            ·
              refine ⟨30449307671899079340915029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81198153791730878242440077 30449307671899079340915029)
              ·
                refine ⟨89206956070016834006587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30449307671899079340915029 89206956070016834006587)
                ·
                  rfl

theorem cell21_1172677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 10].length) (baseStart_1172677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172677 prefixEnd_1172677 := by exact prefixLift 1172677
  have htrace : WordTrace (prefixWord ++ tailWord_1172677) baseStart_1172677 baseEnd_1172677 := by
    simpa [prefixWord, tailWord_1172677, baseEnd_1172677] using wordTrace_append hprefix tailTrace_1172677
  have hstable : (prefixWord ++ tailWord_1172677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172677).length < 2 ^ (prefixWord ++ tailWord_1172677).sum := by decide
  have hdescent : baseEnd_1172677 < baseStart_1172677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172708 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1172708 : Nat := 118140960795 + 1172708 * 2 ^ 59
def prefixEnd_1172708 : Nat := 4983230072969 + 3 ^ 40 * 1172708 * 2
def baseEnd_1172708 : Nat := 267627942832401337003031

theorem tailTrace_1172708 : CollatzResearch.WordTrace tailWord_1172708 prefixEnd_1172708 267627942832401337003031 := by
  unfold tailWord_1172708
  simp only [CollatzResearch.WordTrace]
  refine ⟨21386087317743336713099389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28514783090324448950799185 21386087317743336713099389)
  ·
    refine ⟨8019782744153751267412271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21386087317743336713099389 8019782744153751267412271)
    ·
      refine ⟨12029674116230626901118407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8019782744153751267412271 12029674116230626901118407)
      ·
        refine ⟨18044511174345940351677611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12029674116230626901118407 18044511174345940351677611)
        ·
          refine ⟨27066766761518910527516417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18044511174345940351677611 27066766761518910527516417)
          ·
            refine ⟨20300075071139182895637313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27066766761518910527516417 20300075071139182895637313)
            ·
              refine ⟨15225056303354387171727985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20300075071139182895637313 15225056303354387171727985)
              ·
                refine ⟨11418792227515790378795989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15225056303354387171727985 11418792227515790378795989)
                ·
                  refine ⟨267627942832401337003031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11418792227515790378795989 267627942832401337003031)
                  ·
                    rfl

theorem cell21_1172708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1172708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172708 prefixEnd_1172708 := by exact prefixLift 1172708
  have htrace : WordTrace (prefixWord ++ tailWord_1172708) baseStart_1172708 baseEnd_1172708 := by
    simpa [prefixWord, tailWord_1172708, baseEnd_1172708] using wordTrace_append hprefix tailTrace_1172708
  have hstable : (prefixWord ++ tailWord_1172708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172708).length < 2 ^ (prefixWord ++ tailWord_1172708).sum := by decide
  have hdescent : baseEnd_1172708 < baseStart_1172708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172711 : List Nat := [1, 1, 5, 3, 2, 2, 7]
def baseStart_1172711 : Nat := 118140960795 + 1172711 * 2 ^ 59
def prefixEnd_1172711 : Nat := 4983230072969 + 3 ^ 40 * 1172711 * 2
def baseEnd_1172711 : Nat := 29736514163697110939225

theorem tailTrace_1172711 : CollatzResearch.WordTrace tailWord_1172711 prefixEnd_1172711 29736514163697110939225 := by
  unfold tailWord_1172711
  simp only [CollatzResearch.WordTrace]
  refine ⟨42772284054475804938557987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28514856036317203292371991 42772284054475804938557987)
  ·
    refine ⟨64158426081713707407836981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42772284054475804938557987 64158426081713707407836981)
    ·
      refine ⟨6014852445160660069484717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64158426081713707407836981 6014852445160660069484717)
      ·
        refine ⟨2255569666935247526056769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6014852445160660069484717 2255569666935247526056769)
        ·
          refine ⟨1691677250201435644542577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2255569666935247526056769 1691677250201435644542577)
          ·
            refine ⟨1268757937651076733406933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1691677250201435644542577 1268757937651076733406933)
            ·
              refine ⟨29736514163697110939225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1268757937651076733406933 29736514163697110939225)
              ·
                rfl

theorem cell21_1172711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 7].length) (baseStart_1172711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172711 prefixEnd_1172711 := by exact prefixLift 1172711
  have htrace : WordTrace (prefixWord ++ tailWord_1172711) baseStart_1172711 baseEnd_1172711 := by
    simpa [prefixWord, tailWord_1172711, baseEnd_1172711] using wordTrace_append hprefix tailTrace_1172711
  have hstable : (prefixWord ++ tailWord_1172711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172711).length < 2 ^ (prefixWord ++ tailWord_1172711).sum := by decide
  have hdescent : baseEnd_1172711 < baseStart_1172711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172753 : List Nat := [1, 2, 2, 1, 1, 4, 1, 9]
def baseStart_1172753 : Nat := 118140960795 + 1172753 * 2 ^ 59
def prefixEnd_1172753 : Nat := 4983230072969 + 3 ^ 40 * 1172753 * 2
def baseEnd_1172753 : Nat := 89212737481830419584313

theorem tailTrace_1172753 : CollatzResearch.WordTrace tailWord_1172753 prefixEnd_1172753 89212737481830419584313 := by
  unfold tailWord_1172753
  simp only [CollatzResearch.WordTrace]
  refine ⟨42773815920323646111586913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28515877280215764074391275 42773815920323646111586913)
  ·
    refine ⟨32080361940242734583690185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42773815920323646111586913 32080361940242734583690185)
    ·
      refine ⟨24060271455182050937767639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32080361940242734583690185 24060271455182050937767639)
      ·
        refine ⟨36090407182773076406651459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24060271455182050937767639 36090407182773076406651459)
        ·
          refine ⟨54135610774159614609977189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36090407182773076406651459 54135610774159614609977189)
          ·
            refine ⟨10150427020154927739370723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54135610774159614609977189 10150427020154927739370723)
            ·
              refine ⟨15225640530232391609056085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10150427020154927739370723 15225640530232391609056085)
              ·
                refine ⟨89212737481830419584313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15225640530232391609056085 89212737481830419584313)
                ·
                  rfl

theorem cell21_1172753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 9].length) (baseStart_1172753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172753 prefixEnd_1172753 := by exact prefixLift 1172753
  have htrace : WordTrace (prefixWord ++ tailWord_1172753) baseStart_1172753 baseEnd_1172753 := by
    simpa [prefixWord, tailWord_1172753, baseEnd_1172753] using wordTrace_append hprefix tailTrace_1172753
  have hstable : (prefixWord ++ tailWord_1172753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172753).length < 2 ^ (prefixWord ++ tailWord_1172753).sum := by decide
  have hdescent : baseEnd_1172753 < baseStart_1172753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172770 : List Nat := [3, 3, 1, 1, 4, 9]
def baseStart_1172770 : Nat := 118140960795 + 1172770 * 2 ^ 59
def prefixEnd_1172770 : Nat := 4983230072969 + 3 ^ 40 * 1172770 * 2
def baseEnd_1172770 : Nat := 9912670076929740998873

theorem tailTrace_1172770 : CollatzResearch.WordTrace tailWord_1172770 prefixEnd_1172770 9912670076929740998873 := by
  unfold tailWord_1172770
  simp only [CollatzResearch.WordTrace]
  refine ⟨10693608990315514503738941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28516290640841372009970509 10693608990315514503738941)
  ·
    refine ⟨4010103371368317938902103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10693608990315514503738941 4010103371368317938902103)
    ·
      refine ⟨6015155057052476908353155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4010103371368317938902103 6015155057052476908353155)
      ·
        refine ⟨9022732585578715362529733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6015155057052476908353155 9022732585578715362529733)
        ·
          refine ⟨1691762359796009130474325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9022732585578715362529733 1691762359796009130474325)
          ·
            refine ⟨9912670076929740998873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1691762359796009130474325 9912670076929740998873)
            ·
              rfl

theorem cell21_1172770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 9].length) (baseStart_1172770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172770 prefixEnd_1172770 := by exact prefixLift 1172770
  have htrace : WordTrace (prefixWord ++ tailWord_1172770) baseStart_1172770 baseEnd_1172770 := by
    simpa [prefixWord, tailWord_1172770, baseEnd_1172770] using wordTrace_append hprefix tailTrace_1172770
  have hstable : (prefixWord ++ tailWord_1172770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172770).length < 2 ^ (prefixWord ++ tailWord_1172770).sum := by decide
  have hdescent : baseEnd_1172770 < baseStart_1172770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172776 : List Nat := [2, 1, 5, 1, 2, 3, 2, 2, 3]
def baseStart_1172776 : Nat := 118140960795 + 1172776 * 2 ^ 59
def prefixEnd_1172776 : Nat := 4983230072969 + 3 ^ 40 * 1172776 * 2
def baseEnd_1172776 : Nat := 267643461358848329869559

theorem tailTrace_1172776 : CollatzResearch.WordTrace tailWord_1172776 prefixEnd_1172776 267643461358848329869559 := by
  unfold tailWord_1172776
  simp only [CollatzResearch.WordTrace]
  refine ⟨21387327399620160519837091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28516436532826880693116121 21387327399620160519837091)
  ·
    refine ⟨32080991099430240779755637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21387327399620160519837091 32080991099430240779755637)
    ·
      refine ⟨3007592915571585073102091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32080991099430240779755637 3007592915571585073102091)
      ·
        refine ⟨4511389373357377609653137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007592915571585073102091 4511389373357377609653137)
        ·
          refine ⟨3383542030018033207239853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4511389373357377609653137 3383542030018033207239853)
          ·
            refine ⟨1268828261256762452714945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3383542030018033207239853 1268828261256762452714945)
            ·
              refine ⟨951621195942571839536209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268828261256762452714945 951621195942571839536209)
              ·
                refine ⟨713715896956928879652157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951621195942571839536209 713715896956928879652157)
                ·
                  refine ⟨267643461358848329869559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713715896956928879652157 267643461358848329869559)
                  ·
                    rfl

theorem cell21_1172776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 3].length) (baseStart_1172776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172776 prefixEnd_1172776 := by exact prefixLift 1172776
  have htrace : WordTrace (prefixWord ++ tailWord_1172776) baseStart_1172776 baseEnd_1172776 := by
    simpa [prefixWord, tailWord_1172776, baseEnd_1172776] using wordTrace_append hprefix tailTrace_1172776
  have hstable : (prefixWord ++ tailWord_1172776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172776).length < 2 ^ (prefixWord ++ tailWord_1172776).sum := by decide
  have hdescent : baseEnd_1172776 < baseStart_1172776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172784 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_1172784 : Nat := 118140960795 + 1172784 * 2 ^ 59
def prefixEnd_1172784 : Nat := 4983230072969 + 3 ^ 40 * 1172784 * 2
def baseEnd_1172784 : Nat := 267645287067842093736209

theorem tailTrace_1172784 : CollatzResearch.WordTrace tailWord_1172784 prefixEnd_1172784 267645287067842093736209 := by
  unfold tailWord_1172784
  simp only [CollatzResearch.WordTrace]
  refine ⟨21387473291605669202982703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28516631055474225603976937 21387473291605669202982703)
  ·
    refine ⟨32081209937408503804474055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21387473291605669202982703 32081209937408503804474055)
    ·
      refine ⟨48121814906112755706711083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32081209937408503804474055 48121814906112755706711083)
      ·
        refine ⟨72182722359169133560066625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48121814906112755706711083 72182722359169133560066625)
        ·
          refine ⟨54137041769376850170049969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72182722359169133560066625 54137041769376850170049969)
          ·
            refine ⟨40602781327032637627537477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54137041769376850170049969 40602781327032637627537477)
            ·
              refine ⟨7613021498818619555163277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40602781327032637627537477 7613021498818619555163277)
              ·
                refine ⟨2854883062056982333186229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7613021498818619555163277 2854883062056982333186229)
                ·
                  refine ⟨267645287067842093736209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2854883062056982333186229 267645287067842093736209)
                  ·
                    rfl

theorem cell21_1172784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_1172784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172784 prefixEnd_1172784 := by exact prefixLift 1172784
  have htrace : WordTrace (prefixWord ++ tailWord_1172784) baseStart_1172784 baseEnd_1172784 := by
    simpa [prefixWord, tailWord_1172784, baseEnd_1172784] using wordTrace_append hprefix tailTrace_1172784
  have hstable : (prefixWord ++ tailWord_1172784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172784).length < 2 ^ (prefixWord ++ tailWord_1172784).sum := by decide
  have hdescent : baseEnd_1172784 < baseStart_1172784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172801 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 7]
def baseStart_1172801 : Nat := 118140960795 + 1172801 * 2 ^ 59
def prefixEnd_1172801 : Nat := 4983230072969 + 3 ^ 40 * 1172801 * 2
def baseEnd_1172801 : Nat := 267649166699453841952841

theorem tailTrace_1172801 : CollatzResearch.WordTrace tailWord_1172801 prefixEnd_1172801 267649166699453841952841 := by
  unfold tailWord_1172801
  simp only [CollatzResearch.WordTrace]
  refine ⟨42775566624149750309334257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28517044416099833539556171 42775566624149750309334257)
  ·
    refine ⟨32081674968112312732000693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42775566624149750309334257 32081674968112312732000693)
    ·
      refine ⟨3007657028260529318625065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32081674968112312732000693 3007657028260529318625065)
      ·
        refine ⟨2255742771195396988968799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3007657028260529318625065 2255742771195396988968799)
        ·
          refine ⟨3383614156793095483453199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255742771195396988968799 3383614156793095483453199)
          ·
            refine ⟨5075421235189643225179799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383614156793095483453199 5075421235189643225179799)
            ·
              refine ⟨7613131852784464837769699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5075421235189643225179799 7613131852784464837769699)
              ·
                refine ⟨11419697779176697256654549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7613131852784464837769699 11419697779176697256654549)
                ·
                  refine ⟨267649166699453841952841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11419697779176697256654549 267649166699453841952841)
                  ·
                    rfl

theorem cell21_1172801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_1172801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172801 prefixEnd_1172801 := by exact prefixLift 1172801
  have htrace : WordTrace (prefixWord ++ tailWord_1172801) baseStart_1172801 baseEnd_1172801 := by
    simpa [prefixWord, tailWord_1172801, baseEnd_1172801] using wordTrace_append hprefix tailTrace_1172801
  have hstable : (prefixWord ++ tailWord_1172801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172801).length < 2 ^ (prefixWord ++ tailWord_1172801).sum := by decide
  have hdescent : baseEnd_1172801 < baseStart_1172801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172804 : List Nat := [2, 3, 4, 1, 1, 2, 3, 5]
def baseStart_1172804 : Nat := 118140960795 + 1172804 * 2 ^ 59
def prefixEnd_1172804 : Nat := 4983230072969 + 3 ^ 40 * 1172804 * 2
def baseEnd_1172804 : Nat := 89216617113442167800945

theorem tailTrace_1172804 : CollatzResearch.WordTrace tailWord_1172804 prefixEnd_1172804 89216617113442167800945 := by
  unfold tailWord_1172804
  simp only [CollatzResearch.WordTrace]
  refine ⟨21387838021569440910846733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28517117362092587881128977 21387838021569440910846733)
  ·
    refine ⟨8020439258088540341567525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21387838021569440910846733 8020439258088540341567525)
    ·
      refine ⟨1503832360891601314043911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8020439258088540341567525 1503832360891601314043911)
      ·
        refine ⟨2255748541337401971065867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1503832360891601314043911 2255748541337401971065867)
        ·
          refine ⟨3383622812006102956598801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255748541337401971065867 3383622812006102956598801)
          ·
            refine ⟨2537717109004577217449101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3383622812006102956598801 2537717109004577217449101)
            ·
              refine ⟨951643915876716456543413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2537717109004577217449101 951643915876716456543413)
              ·
                refine ⟨89216617113442167800945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 951643915876716456543413 89216617113442167800945)
                ·
                  rfl

theorem cell21_1172804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_1172804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172804 prefixEnd_1172804 := by exact prefixLift 1172804
  have htrace : WordTrace (prefixWord ++ tailWord_1172804) baseStart_1172804 baseEnd_1172804 := by
    simpa [prefixWord, tailWord_1172804, baseEnd_1172804] using wordTrace_append hprefix tailTrace_1172804
  have hstable : (prefixWord ++ tailWord_1172804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172804).length < 2 ^ (prefixWord ++ tailWord_1172804).sum := by decide
  have hdescent : baseEnd_1172804 < baseStart_1172804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172832 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 4]
def baseStart_1172832 : Nat := 118140960795 + 1172832 * 2 ^ 59
def prefixEnd_1172832 : Nat := 4983230072969 + 3 ^ 40 * 1172832 * 2
def baseEnd_1172832 : Nat := 267656241321804676936111

theorem tailTrace_1172832 : CollatzResearch.WordTrace tailWord_1172832 prefixEnd_1172832 267656241321804676936111 := by
  unfold tailWord_1172832
  simp only [CollatzResearch.WordTrace]
  refine ⟨21388348643518721301856375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28517798191358295069141833 21388348643518721301856375)
  ·
    refine ⟨32082522965278081952784563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21388348643518721301856375 32082522965278081952784563)
    ·
      refine ⟨48123784447917122929176845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32082522965278081952784563 48123784447917122929176845)
      ·
        refine ⟨18046419167968921098441317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48123784447917122929176845 18046419167968921098441317)
        ·
          refine ⟨3383703593994172705957747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18046419167968921098441317 3383703593994172705957747)
          ·
            refine ⟨5075555390991259058936621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383703593994172705957747 5075555390991259058936621)
            ·
              refine ⟨1903333271621722147101233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5075555390991259058936621 1903333271621722147101233)
              ·
                refine ⟨1427499953716291610325925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1903333271621722147101233 1427499953716291610325925)
                ·
                  refine ⟨267656241321804676936111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1427499953716291610325925 267656241321804676936111)
                  ·
                    rfl

theorem cell21_1172832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_1172832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172832 prefixEnd_1172832 := by exact prefixLift 1172832
  have htrace : WordTrace (prefixWord ++ tailWord_1172832) baseStart_1172832 baseEnd_1172832 := by
    simpa [prefixWord, tailWord_1172832, baseEnd_1172832] using wordTrace_append hprefix tailTrace_1172832
  have hstable : (prefixWord ++ tailWord_1172832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172832).length < 2 ^ (prefixWord ++ tailWord_1172832).sum := by decide
  have hdescent : baseEnd_1172832 < baseStart_1172832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172860 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_1172860 : Nat := 118140960795 + 1172860 * 2 ^ 59
def prefixEnd_1172860 : Nat := 4983230072969 + 3 ^ 40 * 1172860 * 2
def baseEnd_1172860 : Nat := 267662631303282850469387

theorem tailTrace_1172860 : CollatzResearch.WordTrace tailWord_1172860 prefixEnd_1172860 267662631303282850469387 := by
  unfold tailWord_1172860
  simp only [CollatzResearch.WordTrace]
  refine ⟨21388859265468001692866017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28518479020624002257154689 21388859265468001692866017)
  ·
    refine ⟨16041644449101001269649513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21388859265468001692866017 16041644449101001269649513)
    ·
      refine ⟨12031233336825750952237135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16041644449101001269649513 12031233336825750952237135)
      ·
        refine ⟨18046850005238626428355703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12031233336825750952237135 18046850005238626428355703)
        ·
          refine ⟨27070275007857939642533555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18046850005238626428355703 27070275007857939642533555)
          ·
            refine ⟨40605412511786909463800333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27070275007857939642533555 40605412511786909463800333)
            ·
              refine ⟨15227029691920091048925125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40605412511786909463800333 15227029691920091048925125)
              ·
                refine ⟨2855068067235017071673461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15227029691920091048925125 2855068067235017071673461)
                ·
                  refine ⟨267662631303282850469387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2855068067235017071673461 267662631303282850469387)
                  ·
                    rfl

theorem cell21_1172860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_1172860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172860 prefixEnd_1172860 := by exact prefixLift 1172860
  have htrace : WordTrace (prefixWord ++ tailWord_1172860) baseStart_1172860 baseEnd_1172860 := by
    simpa [prefixWord, tailWord_1172860, baseEnd_1172860] using wordTrace_append hprefix tailTrace_1172860
  have hstable : (prefixWord ++ tailWord_1172860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172860).length < 2 ^ (prefixWord ++ tailWord_1172860).sum := by decide
  have hdescent : baseEnd_1172860 < baseStart_1172860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172908 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 4]
def baseStart_1172908 : Nat := 118140960795 + 1172908 * 2 ^ 59
def prefixEnd_1172908 : Nat := 4983230072969 + 3 ^ 40 * 1172908 * 2
def baseEnd_1172908 : Nat := 267673585557245433669289

theorem tailTrace_1172908 : CollatzResearch.WordTrace tailWord_1172908 prefixEnd_1172908 267673585557245433669289 := by
  unfold tailWord_1172908
  simp only [CollatzResearch.WordTrace]
  refine ⟨21389734617381053791739689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28519646156508071722319585 21389734617381053791739689)
  ·
    refine ⟨16042300963035790343804767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21389734617381053791739689 16042300963035790343804767)
    ·
      refine ⟨24063451444553685515707151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16042300963035790343804767 24063451444553685515707151)
      ·
        refine ⟨36095177166830528273560727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24063451444553685515707151 36095177166830528273560727)
        ·
          refine ⟨54142765750245792410341091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36095177166830528273560727 54142765750245792410341091)
          ·
            refine ⟨81214148625368688615511637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54142765750245792410341091 81214148625368688615511637)
            ·
              refine ⟨951728304203539319713027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 81214148625368688615511637 951728304203539319713027)
              ·
                refine ⟨1427592456305308979569541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951728304203539319713027 1427592456305308979569541)
                ·
                  refine ⟨267673585557245433669289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1427592456305308979569541 267673585557245433669289)
                  ·
                    rfl

theorem cell21_1172908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_1172908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1172908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1172908 prefixEnd_1172908 := by exact prefixLift 1172908
  have htrace : WordTrace (prefixWord ++ tailWord_1172908) baseStart_1172908 baseEnd_1172908 := by
    simpa [prefixWord, tailWord_1172908, baseEnd_1172908] using wordTrace_append hprefix tailTrace_1172908
  have hstable : (prefixWord ++ tailWord_1172908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172908).length < 2 ^ (prefixWord ++ tailWord_1172908).sum := by decide
  have hdescent : baseEnd_1172908 < baseStart_1172908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173032 : List Nat := [2, 1, 5, 2, 2, 2, 2, 5]
def baseStart_1173032 : Nat := 118140960795 + 1173032 * 2 ^ 59
def prefixEnd_1173032 : Nat := 4983230072969 + 3 ^ 40 * 1173032 * 2
def baseEnd_1173032 : Nat := 89233961348882924534123

theorem tailTrace_1173032 : CollatzResearch.WordTrace tailWord_1173032 prefixEnd_1173032 89233961348882924534123 := by
  unfold tailWord_1173032
  simp only [CollatzResearch.WordTrace]
  refine ⟨21391995943156438380496675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28522661257541917840662233 21391995943156438380496675)
  ·
    refine ⟨32087993914734657570745013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21391995943156438380496675 32087993914734657570745013)
    ·
      refine ⟨3008249429506374147257345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32087993914734657570745013 3008249429506374147257345)
      ·
        refine ⟨2256187072129780610443009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3008249429506374147257345 2256187072129780610443009)
        ·
          refine ⟨1692140304097335457832257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2256187072129780610443009 1692140304097335457832257)
          ·
            refine ⟨1269105228073001593374193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1692140304097335457832257 1269105228073001593374193)
            ·
              refine ⟨951828921054751195030645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269105228073001593374193 951828921054751195030645)
              ·
                refine ⟨89233961348882924534123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 951828921054751195030645 89233961348882924534123)
                ·
                  rfl

theorem cell21_1173032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_1173032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173032 prefixEnd_1173032 := by exact prefixLift 1173032
  have htrace : WordTrace (prefixWord ++ tailWord_1173032) baseStart_1173032 baseEnd_1173032 := by
    simpa [prefixWord, tailWord_1173032, baseEnd_1173032] using wordTrace_append hprefix tailTrace_1173032
  have hstable : (prefixWord ++ tailWord_1173032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173032).length < 2 ^ (prefixWord ++ tailWord_1173032).sum := by decide
  have hdescent : baseEnd_1173032 < baseStart_1173032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173063 : List Nat := [1, 1, 4, 1, 5, 1, 3, 2, 3]
def baseStart_1173063 : Nat := 118140960795 + 1173063 * 2 ^ 59
def prefixEnd_1173063 : Nat := 4983230072969 + 3 ^ 40 * 1173063 * 2
def baseEnd_1173063 : Nat := 267708958668999608585639

theorem tailTrace_1173063 : CollatzResearch.WordTrace tailWord_1173063 prefixEnd_1173063 267708958668999608585639 := by
  unfold tailWord_1173063
  simp only [CollatzResearch.WordTrace]
  refine ⟨42785122549200569055371843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28523415032800379370247895 42785122549200569055371843)
  ·
    refine ⟨64177683823800853583057765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42785122549200569055371843 64177683823800853583057765)
    ·
      refine ⟨12033315716962660046823331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64177683823800853583057765 12033315716962660046823331)
      ·
        refine ⟨18049973575443990070234997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12033315716962660046823331 18049973575443990070234997)
        ·
          refine ⟨1692185022697874069084531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18049973575443990070234997 1692185022697874069084531)
          ·
            refine ⟨2538277534046811103626797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692185022697874069084531 2538277534046811103626797)
            ·
              refine ⟨951854075267554163860049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2538277534046811103626797 951854075267554163860049)
              ·
                refine ⟨713890556450665622895037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951854075267554163860049 713890556450665622895037)
                ·
                  refine ⟨267708958668999608585639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713890556450665622895037 267708958668999608585639)
                  ·
                    rfl

theorem cell21_1173063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 3].length) (baseStart_1173063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173063 prefixEnd_1173063 := by exact prefixLift 1173063
  have htrace : WordTrace (prefixWord ++ tailWord_1173063) baseStart_1173063 baseEnd_1173063 := by
    simpa [prefixWord, tailWord_1173063, baseEnd_1173063] using wordTrace_append hprefix tailTrace_1173063
  have hstable : (prefixWord ++ tailWord_1173063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173063).length < 2 ^ (prefixWord ++ tailWord_1173063).sum := by decide
  have hdescent : baseEnd_1173063 < baseStart_1173063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173074 : List Nat := [3, 2, 2, 1, 2, 3, 2, 6]
def baseStart_1173074 : Nat := 118140960795 + 1173074 * 2 ^ 59
def prefixEnd_1173074 : Nat := 4983230072969 + 3 ^ 40 * 1173074 * 2
def baseEnd_1173074 : Nat := 89237156339622011300761

theorem tailTrace_1173074 : CollatzResearch.WordTrace tailWord_1173074 prefixEnd_1173074 89237156339622011300761 := by
  unfold tailWord_1173074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10696380938040179483505569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28523682501440478622681517 10696380938040179483505569)
  ·
    refine ⟨8022285703530134612629177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10696380938040179483505569 8022285703530134612629177)
    ·
      refine ⟨6016714277647600959471883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8022285703530134612629177 6016714277647600959471883)
      ·
        refine ⟨9025071416471401439207825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6016714277647600959471883 9025071416471401439207825)
        ·
          refine ⟨6768803562353551079405869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9025071416471401439207825 6768803562353551079405869)
          ·
            refine ⟨2538301335882581654777201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6768803562353551079405869 2538301335882581654777201)
            ·
              refine ⟨1903726001911936241082901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2538301335882581654777201 1903726001911936241082901)
              ·
                refine ⟨89237156339622011300761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1903726001911936241082901 89237156339622011300761)
                ·
                  rfl

theorem cell21_1173074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_1173074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173074 prefixEnd_1173074 := by exact prefixLift 1173074
  have htrace : WordTrace (prefixWord ++ tailWord_1173074) baseStart_1173074 baseEnd_1173074 := by
    simpa [prefixWord, tailWord_1173074, baseEnd_1173074] using wordTrace_append hprefix tailTrace_1173074
  have hstable : (prefixWord ++ tailWord_1173074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173074).length < 2 ^ (prefixWord ++ tailWord_1173074).sum := by decide
  have hdescent : baseEnd_1173074 < baseStart_1173074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173181 : List Nat := [1, 4, 1, 2, 1, 2, 1, 6, 3]
def baseStart_1173181 : Nat := 118140960795 + 1173181 * 2 ^ 59
def prefixEnd_1173181 : Nat := 4983230072969 + 3 ^ 40 * 1173181 * 2
def baseEnd_1173181 : Nat := 267735887876657625618731

theorem tailTrace_1173181 : CollatzResearch.WordTrace tailWord_1173181 prefixEnd_1173181 267735887876657625618731 := by
  unfold tailWord_1173181
  simp only [CollatzResearch.WordTrace]
  refine ⟨42789426362773075208167397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28526284241848716805444931 42789426362773075208167397)
  ·
    refine ⟨8023017443019951601531387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42789426362773075208167397 8023017443019951601531387)
    ·
      refine ⟨12034526164529927402297081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8023017443019951601531387 12034526164529927402297081)
      ·
        refine ⟨9025894623397445551722811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12034526164529927402297081 9025894623397445551722811)
        ·
          refine ⟨13538841935096168327584217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9025894623397445551722811 13538841935096168327584217)
          ·
            refine ⟨10154131451322126245688163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13538841935096168327584217 10154131451322126245688163)
            ·
              refine ⟨15231197176983189368532245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10154131451322126245688163 15231197176983189368532245)
              ·
                refine ⟨713962367671087001649949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15231197176983189368532245 713962367671087001649949)
                ·
                  refine ⟨267735887876657625618731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713962367671087001649949 267735887876657625618731)
                  ·
                    rfl

theorem cell21_1173181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_1173181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173181 prefixEnd_1173181 := by exact prefixLift 1173181
  have htrace : WordTrace (prefixWord ++ tailWord_1173181) baseStart_1173181 baseEnd_1173181 := by
    simpa [prefixWord, tailWord_1173181, baseEnd_1173181] using wordTrace_append hprefix tailTrace_1173181
  have hstable : (prefixWord ++ tailWord_1173181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173181).length < 2 ^ (prefixWord ++ tailWord_1173181).sum := by decide
  have hdescent : baseEnd_1173181 < baseStart_1173181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173209 : List Nat := [1, 2, 1, 2, 3, 4, 1, 7]
def baseStart_1173209 : Nat := 118140960795 + 1173209 * 2 ^ 59
def prefixEnd_1173209 : Nat := 4983230072969 + 3 ^ 40 * 1173209 * 2
def baseEnd_1173209 : Nat := 89247425952711933050669

theorem tailTrace_1173209 : CollatzResearch.WordTrace tailWord_1173209 prefixEnd_1173209 89247425952711933050669 := by
  unfold tailWord_1173209
  simp only [CollatzResearch.WordTrace]
  refine ⟨42790447606671635990186681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28526965071114423993457787 42790447606671635990186681)
  ·
    refine ⟨32092835705003726992640011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42790447606671635990186681 32092835705003726992640011)
    ·
      refine ⟨48139253557505590488960017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32092835705003726992640011 48139253557505590488960017)
      ·
        refine ⟨36104440168129192866720013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48139253557505590488960017 36104440168129192866720013)
        ·
          refine ⟨13539165063048447325020005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36104440168129192866720013 13539165063048447325020005)
          ·
            refine ⟨2538593449321583873441251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13539165063048447325020005 2538593449321583873441251)
            ·
              refine ⟨3807890173982375810161877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538593449321583873441251 3807890173982375810161877)
              ·
                refine ⟨89247425952711933050669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3807890173982375810161877 89247425952711933050669)
                ·
                  rfl

theorem cell21_1173209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 7].length) (baseStart_1173209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173209 prefixEnd_1173209 := by exact prefixLift 1173209
  have htrace : WordTrace (prefixWord ++ tailWord_1173209) baseStart_1173209 baseEnd_1173209 := by
    simpa [prefixWord, tailWord_1173209, baseEnd_1173209] using wordTrace_append hprefix tailTrace_1173209
  have hstable : (prefixWord ++ tailWord_1173209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173209).length < 2 ^ (prefixWord ++ tailWord_1173209).sum := by decide
  have hdescent : baseEnd_1173209 < baseStart_1173209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173246 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1173246 : Nat := 118140960795 + 1173246 * 2 ^ 59
def prefixEnd_1173246 : Nat := 4983230072969 + 3 ^ 40 * 1173246 * 2
def baseEnd_1173246 : Nat := 267750721762231957035265

theorem tailTrace_1173246 : CollatzResearch.WordTrace tailWord_1173246 prefixEnd_1173246 267750721762231957035265 := by
  unfold tailWord_1173246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5348974638442198913660449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28527864738358394206189061 5348974638442198913660449)
  ·
    refine ⟨4011730978831649185245337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5348974638442198913660449 4011730978831649185245337)
    ·
      refine ⟨3008798234123736888934003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4011730978831649185245337 3008798234123736888934003)
      ·
        refine ⟨4513197351185605333401005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3008798234123736888934003 4513197351185605333401005)
        ·
          refine ⟨1692449006694602000025377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4513197351185605333401005 1692449006694602000025377)
          ·
            refine ⟨1269336755020951500019033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1692449006694602000025377 1269336755020951500019033)
            ·
              refine ⟨952002566265713625014275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269336755020951500019033 952002566265713625014275)
              ·
                refine ⟨1428003849398570437521413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952002566265713625014275 1428003849398570437521413)
                ·
                  refine ⟨267750721762231957035265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428003849398570437521413 267750721762231957035265)
                  ·
                    rfl

theorem cell21_1173246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1173246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173246 prefixEnd_1173246 := by exact prefixLift 1173246
  have htrace : WordTrace (prefixWord ++ tailWord_1173246) baseStart_1173246 baseEnd_1173246 := by
    simpa [prefixWord, tailWord_1173246, baseEnd_1173246] using wordTrace_append hprefix tailTrace_1173246
  have hstable : (prefixWord ++ tailWord_1173246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173246).length < 2 ^ (prefixWord ++ tailWord_1173246).sum := by decide
  have hdescent : baseEnd_1173246 < baseStart_1173246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173288 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 4]
def baseStart_1173288 : Nat := 118140960795 + 1173288 * 2 ^ 59
def prefixEnd_1173288 : Nat := 4983230072969 + 3 ^ 40 * 1173288 * 2
def baseEnd_1173288 : Nat := 267760306734449217335179

theorem tailTrace_1173288 : CollatzResearch.WordTrace tailWord_1173288 prefixEnd_1173288 267760306734449217335179 := by
  unfold tailWord_1173288
  simp only [CollatzResearch.WordTrace]
  refine ⟨21396664486692716241156259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28528885982256954988208345 21396664486692716241156259)
  ·
    refine ⟨32094996730039074361734389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21396664486692716241156259 32094996730039074361734389)
    ·
      refine ⟨3008905943441163221412599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32094996730039074361734389 3008905943441163221412599)
      ·
        refine ⟨4513358915161744832118899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3008905943441163221412599 4513358915161744832118899)
        ·
          refine ⟨6770038372742617248178349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4513358915161744832118899 6770038372742617248178349)
          ·
            refine ⟨2538764389778481468066881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6770038372742617248178349 2538764389778481468066881)
            ·
              refine ⟨1904073292333861101050161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2538764389778481468066881 1904073292333861101050161)
              ·
                refine ⟨1428054969250395825787621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1904073292333861101050161 1428054969250395825787621)
                ·
                  refine ⟨267760306734449217335179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428054969250395825787621 267760306734449217335179)
                  ·
                    rfl

theorem cell21_1173288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_1173288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173288 prefixEnd_1173288 := by exact prefixLift 1173288
  have htrace : WordTrace (prefixWord ++ tailWord_1173288) baseStart_1173288 baseEnd_1173288 := by
    simpa [prefixWord, tailWord_1173288, baseEnd_1173288] using wordTrace_append hprefix tailTrace_1173288
  have hstable : (prefixWord ++ tailWord_1173288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173288).length < 2 ^ (prefixWord ++ tailWord_1173288).sum := by decide
  have hdescent : baseEnd_1173288 < baseStart_1173288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173333 : List Nat := [1, 3, 2, 2, 2, 2, 1, 5, 3]
def baseStart_1173333 : Nat := 118140960795 + 1173333 * 2 ^ 59
def prefixEnd_1173333 : Nat := 4983230072969 + 3 ^ 40 * 1173333 * 2
def baseEnd_1173333 : Nat := 267770576347539139085087

theorem tailTrace_1173333 : CollatzResearch.WordTrace tailWord_1173333 prefixEnd_1173333 267770576347539139085087 := by
  unfold tailWord_1173333
  simp only [CollatzResearch.WordTrace]
  refine ⟨42794970258222405167700653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28529980172148270111800435 42794970258222405167700653)
  ·
    refine ⟨16048113846833401937887745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42794970258222405167700653 16048113846833401937887745)
    ·
      refine ⟨12036085385125051453415809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16048113846833401937887745 12036085385125051453415809)
      ·
        refine ⟨9027064038843788590061857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12036085385125051453415809 9027064038843788590061857)
        ·
          refine ⟨6770298029132841442546393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9027064038843788590061857 6770298029132841442546393)
          ·
            refine ⟨5077723521849631081909795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6770298029132841442546393 5077723521849631081909795)
            ·
              refine ⟨7616585282774446622864693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077723521849631081909795 7616585282774446622864693)
              ·
                refine ⟨714054870260104370893565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7616585282774446622864693 714054870260104370893565)
                ·
                  refine ⟨267770576347539139085087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714054870260104370893565 267770576347539139085087)
                  ·
                    rfl

theorem cell21_1173333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_1173333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173333 prefixEnd_1173333 := by exact prefixLift 1173333
  have htrace : WordTrace (prefixWord ++ tailWord_1173333) baseStart_1173333 baseEnd_1173333 := by
    simpa [prefixWord, tailWord_1173333, baseEnd_1173333] using wordTrace_append hprefix tailTrace_1173333
  have hstable : (prefixWord ++ tailWord_1173333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173333).length < 2 ^ (prefixWord ++ tailWord_1173333).sum := by decide
  have hdescent : baseEnd_1173333 < baseStart_1173333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173347 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 6]
def baseStart_1173347 : Nat := 118140960795 + 1173347 * 2 ^ 59
def prefixEnd_1173347 : Nat := 4983230072969 + 3 ^ 40 * 1173347 * 2
def baseEnd_1173347 : Nat := 267773771338278225851725

theorem tailTrace_1173347 : CollatzResearch.WordTrace tailWord_1173347 prefixEnd_1173347 267773771338278225851725 := by
  unfold tailWord_1173347
  simp only [CollatzResearch.WordTrace]
  refine ⟨42795480880171685558710295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28530320586781123705806863 42795480880171685558710295)
  ·
    refine ⟨64193221320257528338065443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42795480880171685558710295 64193221320257528338065443)
    ·
      refine ⟨96289831980386292507098165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64193221320257528338065443 96289831980386292507098165)
      ·
        refine ⟨9027171748161214922540453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96289831980386292507098165 9027171748161214922540453)
        ·
          refine ⟨1692594702780227797976335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9027171748161214922540453 1692594702780227797976335)
          ·
            refine ⟨2538892054170341696964503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692594702780227797976335 2538892054170341696964503)
            ·
              refine ⟨3808338081255512545446755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538892054170341696964503 3808338081255512545446755)
              ·
                refine ⟨5712507121883268818170133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808338081255512545446755 5712507121883268818170133)
                ·
                  refine ⟨267773771338278225851725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5712507121883268818170133 267773771338278225851725)
                  ·
                    rfl

theorem cell21_1173347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 6].length) (baseStart_1173347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173347 prefixEnd_1173347 := by exact prefixLift 1173347
  have htrace : WordTrace (prefixWord ++ tailWord_1173347) baseStart_1173347 baseEnd_1173347 := by
    simpa [prefixWord, tailWord_1173347, baseEnd_1173347] using wordTrace_append hprefix tailTrace_1173347
  have hstable : (prefixWord ++ tailWord_1173347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173347).length < 2 ^ (prefixWord ++ tailWord_1173347).sum := by decide
  have hdescent : baseEnd_1173347 < baseStart_1173347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173437 : List Nat := [1, 4, 1, 2, 3, 1, 2, 7]
def baseStart_1173437 : Nat := 118140960795 + 1173437 * 2 ^ 59
def prefixEnd_1173437 : Nat := 4983230072969 + 3 ^ 40 * 1173437 * 2
def baseEnd_1173437 : Nat := 89264770188152689783847

theorem tailTrace_1173437 : CollatzResearch.WordTrace tailWord_1173437 prefixEnd_1173437 89264770188152689783847 := by
  unfold tailWord_1173437
  simp only [CollatzResearch.WordTrace]
  refine ⟨42798763449845630929486565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28532508966563753952991043 42798763449845630929486565)
  ·
    refine ⟨8024768146846055799278731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42798763449845630929486565 8024768146846055799278731)
    ·
      refine ⟨12037152220269083698918097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8024768146846055799278731 12037152220269083698918097)
      ·
        refine ⟨9027864165201812774188573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12037152220269083698918097 9027864165201812774188573)
        ·
          refine ⟨3385449061950679790320715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9027864165201812774188573 3385449061950679790320715)
          ·
            refine ⟨5078173592926019685481073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385449061950679790320715 5078173592926019685481073)
            ·
              refine ⟨3808630194694514764110805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5078173592926019685481073 3808630194694514764110805)
              ·
                refine ⟨89264770188152689783847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3808630194694514764110805 89264770188152689783847)
                ·
                  rfl

theorem cell21_1173437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 7].length) (baseStart_1173437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173437 prefixEnd_1173437 := by exact prefixLift 1173437
  have htrace : WordTrace (prefixWord ++ tailWord_1173437) baseStart_1173437 baseEnd_1173437 := by
    simpa [prefixWord, tailWord_1173437, baseEnd_1173437] using wordTrace_append hprefix tailTrace_1173437
  have hstable : (prefixWord ++ tailWord_1173437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173437).length < 2 ^ (prefixWord ++ tailWord_1173437).sum := by decide
  have hdescent : baseEnd_1173437 < baseStart_1173437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173496 : List Nat := [2, 1, 2, 1, 1, 3, 2, 9]
def baseStart_1173496 : Nat := 118140960795 + 1173496 * 2 ^ 59
def prefixEnd_1173496 : Nat := 4983230072969 + 3 ^ 40 * 1173496 * 2
def baseEnd_1173496 : Nat := 89269258389429025956029

theorem tailTrace_1173496 : CollatzResearch.WordTrace tailWord_1173496 prefixEnd_1173496 89269258389429025956029 := by
  unfold tailWord_1173496
  simp only [CollatzResearch.WordTrace]
  refine ⟨21400457678315942002942171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28533943571087922670589561 21400457678315942002942171)
  ·
    refine ⟨32100686517473913004413257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21400457678315942002942171 32100686517473913004413257)
    ·
      refine ⟨24075514888105434753309943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32100686517473913004413257 24075514888105434753309943)
      ·
        refine ⟨36113272332158152129964915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24075514888105434753309943 36113272332158152129964915)
        ·
          refine ⟨54169908498237228194947373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36113272332158152129964915 54169908498237228194947373)
          ·
            refine ⟨20313715686838960573105265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54169908498237228194947373 20313715686838960573105265)
            ·
              refine ⟨15235286765129220429828949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20313715686838960573105265 15235286765129220429828949)
              ·
                refine ⟨89269258389429025956029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15235286765129220429828949 89269258389429025956029)
                ·
                  rfl

theorem cell21_1173496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_1173496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173496 prefixEnd_1173496 := by exact prefixLift 1173496
  have htrace : WordTrace (prefixWord ++ tailWord_1173496) baseStart_1173496 baseEnd_1173496 := by
    simpa [prefixWord, tailWord_1173496, baseEnd_1173496] using wordTrace_append hprefix tailTrace_1173496
  have hstable : (prefixWord ++ tailWord_1173496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173496).length < 2 ^ (prefixWord ++ tailWord_1173496).sum := by decide
  have hdescent : baseEnd_1173496 < baseStart_1173496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173502 : List Nat := [4, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_1173502 : Nat := 118140960795 + 1173502 * 2 ^ 59
def prefixEnd_1173502 : Nat := 4983230072969 + 3 ^ 40 * 1173502 * 2
def baseEnd_1173502 : Nat := 267809144450032400768075

theorem tailTrace_1173502 : CollatzResearch.WordTrace tailWord_1173502 prefixEnd_1173502 267809144450032400768075 := by
  unfold tailWord_1173502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350141774326268378825345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28534089463073431353735173 5350141774326268378825345)
  ·
    refine ⟨4012606330744701284119009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5350141774326268378825345 4012606330744701284119009)
    ·
      refine ⟨3009454748058525963089257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4012606330744701284119009 3009454748058525963089257)
      ·
        refine ⟨2257091061043894472316943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3009454748058525963089257 2257091061043894472316943)
        ·
          refine ⟨3385636591565841708475415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257091061043894472316943 3385636591565841708475415)
          ·
            refine ⟨5078454887348762562713123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385636591565841708475415 5078454887348762562713123)
            ·
              refine ⟨7617682331023143844069685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5078454887348762562713123 7617682331023143844069685)
              ·
                refine ⟨714157718533419735381533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7617682331023143844069685 714157718533419735381533)
                ·
                  refine ⟨267809144450032400768075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714157718533419735381533 267809144450032400768075)
                  ·
                    rfl

theorem cell21_1173502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_1173502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173502 prefixEnd_1173502 := by exact prefixLift 1173502
  have htrace : WordTrace (prefixWord ++ tailWord_1173502) baseStart_1173502 baseEnd_1173502 := by
    simpa [prefixWord, tailWord_1173502, baseEnd_1173502] using wordTrace_append hprefix tailTrace_1173502
  have hstable : (prefixWord ++ tailWord_1173502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173502).length < 2 ^ (prefixWord ++ tailWord_1173502).sum := by decide
  have hdescent : baseEnd_1173502 < baseStart_1173502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173589 : List Nat := [1, 3, 2, 2, 1, 4, 2, 6]
def baseStart_1173589 : Nat := 118140960795 + 1173589 * 2 ^ 59
def prefixEnd_1173589 : Nat := 4983230072969 + 3 ^ 40 * 1173589 * 2
def baseEnd_1173589 : Nat := 89276333011779860939299

theorem tailTrace_1173589 : CollatzResearch.WordTrace tailWord_1173589 prefixEnd_1173589 89276333011779860939299 := by
  unfold tailWord_1173589
  simp only [CollatzResearch.WordTrace]
  refine ⟨42804307345294960889019821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28536204896863307259346547 42804307345294960889019821)
  ·
    refine ⟨16051615254485610333382433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42804307345294960889019821 16051615254485610333382433)
    ·
      refine ⟨12038711440864207750036825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16051615254485610333382433 12038711440864207750036825)
      ·
        refine ⟨9029033580648155812527619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12038711440864207750036825 9029033580648155812527619)
        ·
          refine ⟨13543550370972233718791429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9029033580648155812527619 13543550370972233718791429)
          ·
            refine ⟨2539415694557293822273393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13543550370972233718791429 2539415694557293822273393)
            ·
              refine ⟨1904561770917970366705045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2539415694557293822273393 1904561770917970366705045)
              ·
                refine ⟨89276333011779860939299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1904561770917970366705045 89276333011779860939299)
                ·
                  rfl

theorem cell21_1173589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 6].length) (baseStart_1173589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173589 prefixEnd_1173589 := by exact prefixLift 1173589
  have htrace : WordTrace (prefixWord ++ tailWord_1173589) baseStart_1173589 baseEnd_1173589 := by
    simpa [prefixWord, tailWord_1173589, baseEnd_1173589] using wordTrace_append hprefix tailTrace_1173589
  have hstable : (prefixWord ++ tailWord_1173589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173589).length < 2 ^ (prefixWord ++ tailWord_1173589).sum := by decide
  have hdescent : baseEnd_1173589 < baseStart_1173589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173592 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 4]
def baseStart_1173592 : Nat := 118140960795 + 1173592 * 2 ^ 59
def prefixEnd_1173592 : Nat := 4983230072969 + 3 ^ 40 * 1173592 * 2
def baseEnd_1173592 : Nat := 267829683676212244267891

theorem tailTrace_1173592 : CollatzResearch.WordTrace tailWord_1173592 prefixEnd_1173592 267829683676212244267891 := by
  unfold tailWord_1173592
  simp only [CollatzResearch.WordTrace]
  refine ⟨21402208382142046200689515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28536277842856061600919353 21402208382142046200689515)
  ·
    refine ⟨32103312573213069301034273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21402208382142046200689515 32103312573213069301034273)
    ·
      refine ⟨24077484429909801975775705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32103312573213069301034273 24077484429909801975775705)
      ·
        refine ⟨18058113322432351481831779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24077484429909801975775705 18058113322432351481831779)
        ·
          refine ⟨27087169983648527222747669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18058113322432351481831779 27087169983648527222747669)
          ·
            refine ⟨1269711092983524713566297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27087169983648527222747669 1269711092983524713566297)
            ·
              refine ⟨952283319737643535174723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269711092983524713566297 952283319737643535174723)
              ·
                refine ⟨1428424979606465302762085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952283319737643535174723 1428424979606465302762085)
                ·
                  refine ⟨267829683676212244267891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428424979606465302762085 267829683676212244267891)
                  ·
                    rfl

theorem cell21_1173592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_1173592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173592 prefixEnd_1173592 := by exact prefixLift 1173592
  have htrace : WordTrace (prefixWord ++ tailWord_1173592) baseStart_1173592 baseEnd_1173592 := by
    simpa [prefixWord, tailWord_1173592, baseEnd_1173592] using wordTrace_append hprefix tailTrace_1173592
  have hstable : (prefixWord ++ tailWord_1173592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173592).length < 2 ^ (prefixWord ++ tailWord_1173592).sum := by decide
  have hdescent : baseEnd_1173592 < baseStart_1173592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173603 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 5]
def baseStart_1173603 : Nat := 118140960795 + 1173603 * 2 ^ 59
def prefixEnd_1173603 : Nat := 4983230072969 + 3 ^ 40 * 1173603 * 2
def baseEnd_1173603 : Nat := 267832194026078669584535

theorem tailTrace_1173603 : CollatzResearch.WordTrace tailWord_1173603 prefixEnd_1173603 267832194026078669584535 := by
  unfold tailWord_1173603
  simp only [CollatzResearch.WordTrace]
  refine ⟨42804817967244241280029463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28536545311496160853352975 42804817967244241280029463)
  ·
    refine ⟨64207226950866361920044195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42804817967244241280029463 64207226950866361920044195)
    ·
      refine ⟨96310840426299542880066293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64207226950866361920044195 96310840426299542880066293)
      ·
        refine ⟨9029141289965582145006215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96310840426299542880066293 9029141289965582145006215)
        ·
          refine ⟨13543711934948373217509323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9029141289965582145006215 13543711934948373217509323)
          ·
            refine ⟨20315567902422559826263985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13543711934948373217509323 20315567902422559826263985)
            ·
              refine ⟨15236675926816919869697989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20315567902422559826263985 15236675926816919869697989)
              ·
                refine ⟨2856876736278172475568373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15236675926816919869697989 2856876736278172475568373)
                ·
                  refine ⟨267832194026078669584535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2856876736278172475568373 267832194026078669584535)
                  ·
                    rfl

theorem cell21_1173603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_1173603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173603 prefixEnd_1173603 := by exact prefixLift 1173603
  have htrace : WordTrace (prefixWord ++ tailWord_1173603) baseStart_1173603 baseEnd_1173603 := by
    simpa [prefixWord, tailWord_1173603, baseEnd_1173603] using wordTrace_append hprefix tailTrace_1173603
  have hstable : (prefixWord ++ tailWord_1173603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173603).length < 2 ^ (prefixWord ++ tailWord_1173603).sum := by decide
  have hdescent : baseEnd_1173603 < baseStart_1173603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173637 : List Nat := [1, 3, 1, 1, 5, 2, 1, 4, 3]
def baseStart_1173637 : Nat := 118140960795 + 1173637 * 2 ^ 59
def prefixEnd_1173637 : Nat := 4983230072969 + 3 ^ 40 * 1173637 * 2
def baseEnd_1173637 : Nat := 267839953289302166017799

theorem tailTrace_1173637 : CollatzResearch.WordTrace tailWord_1173637 prefixEnd_1173637 267839953289302166017799 := by
  unfold tailWord_1173637
  simp only [CollatzResearch.WordTrace]
  refine ⟨42806058049121065086767165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28537372032747376724511443 42806058049121065086767165)
  ·
    refine ⟨16052271768420399407537687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42806058049121065086767165 16052271768420399407537687)
    ·
      refine ⟨24078407652630599111306531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16052271768420399407537687 24078407652630599111306531)
      ·
        refine ⟨36117611478945898666959797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24078407652630599111306531 36117611478945898666959797)
        ·
          refine ⟨3386026076151178000027481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36117611478945898666959797 3386026076151178000027481)
          ·
            refine ⟨2539519557113383500020611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3386026076151178000027481 2539519557113383500020611)
            ·
              refine ⟨3809279335670075250030917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539519557113383500020611 3809279335670075250030917)
              ·
                refine ⟨714239875438139109380797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3809279335670075250030917 714239875438139109380797)
                ·
                  refine ⟨267839953289302166017799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714239875438139109380797 267839953289302166017799)
                  ·
                    rfl

theorem cell21_1173637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_1173637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173637 prefixEnd_1173637 := by exact prefixLift 1173637
  have htrace : WordTrace (prefixWord ++ tailWord_1173637) baseStart_1173637 baseEnd_1173637 := by
    simpa [prefixWord, tailWord_1173637, baseEnd_1173637] using wordTrace_append hprefix tailTrace_1173637
  have hstable : (prefixWord ++ tailWord_1173637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173637).length < 2 ^ (prefixWord ++ tailWord_1173637).sum := by decide
  have hdescent : baseEnd_1173637 < baseStart_1173637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173685 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 4]
def baseStart_1173685 : Nat := 118140960795 + 1173685 * 2 ^ 59
def prefixEnd_1173685 : Nat := 4983230072969 + 3 ^ 40 * 1173685 * 2
def baseEnd_1173685 : Nat := 267850907543264749217701

theorem tailTrace_1173685 : CollatzResearch.WordTrace tailWord_1173685 prefixEnd_1173685 267850907543264749217701 := by
  unfold tailWord_1173685
  simp only [CollatzResearch.WordTrace]
  refine ⟨42807808752947169284514509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28538539168631446189676339 42807808752947169284514509)
  ·
    refine ⟨16052928282355188481692941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42807808752947169284514509 16052928282355188481692941)
    ·
      refine ⟨6019848105883195680634853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16052928282355188481692941 6019848105883195680634853)
      ·
        refine ⟨1128721519853099190119035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6019848105883195680634853 1128721519853099190119035)
        ·
          refine ⟨1693082279779648785178553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128721519853099190119035 1693082279779648785178553)
          ·
            refine ⟨1269811709834736588883915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1693082279779648785178553 1269811709834736588883915)
            ·
              refine ⟨1904717564752104883325873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269811709834736588883915 1904717564752104883325873)
              ·
                refine ⟨1428538173564078662494405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1904717564752104883325873 1428538173564078662494405)
                ·
                  refine ⟨267850907543264749217701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428538173564078662494405 267850907543264749217701)
                  ·
                    rfl

theorem cell21_1173685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_1173685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173685 prefixEnd_1173685 := by exact prefixLift 1173685
  have htrace : WordTrace (prefixWord ++ tailWord_1173685) baseStart_1173685 baseEnd_1173685 := by
    simpa [prefixWord, tailWord_1173685, baseEnd_1173685] using wordTrace_append hprefix tailTrace_1173685
  have hstable : (prefixWord ++ tailWord_1173685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173685).length < 2 ^ (prefixWord ++ tailWord_1173685).sum := by decide
  have hdescent : baseEnd_1173685 < baseStart_1173685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173696 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 5]
def baseStart_1173696 : Nat := 118140960795 + 1173696 * 2 ^ 59
def prefixEnd_1173696 : Nat := 4983230072969 + 3 ^ 40 * 1173696 * 2
def baseEnd_1173696 : Nat := 267853417893131174534345

theorem tailTrace_1173696 : CollatzResearch.WordTrace tailWord_1173696 prefixEnd_1173696 267853417893131174534345 := by
  unfold tailWord_1173696
  simp only [CollatzResearch.WordTrace]
  refine ⟨21404104977953659081582471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28538806637271545442109961 21404104977953659081582471)
  ·
    refine ⟨32106157466930488622373707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21404104977953659081582471 32106157466930488622373707)
    ·
      refine ⟨48159236200395732933560561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32106157466930488622373707 48159236200395732933560561)
      ·
        refine ⟨36119427150296799700170421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48159236200395732933560561 36119427150296799700170421)
        ·
          refine ⟨3386196295340324971890977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36119427150296799700170421 3386196295340324971890977)
          ·
            refine ⟨2539647221505243728918233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3386196295340324971890977 2539647221505243728918233)
            ·
              refine ⟨1904735416128932796688675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2539647221505243728918233 1904735416128932796688675)
              ·
                refine ⟨2857103124193399195033013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1904735416128932796688675 2857103124193399195033013)
                ·
                  refine ⟨267853417893131174534345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2857103124193399195033013 267853417893131174534345)
                  ·
                    rfl

theorem cell21_1173696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_1173696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173696 prefixEnd_1173696 := by exact prefixLift 1173696
  have htrace : WordTrace (prefixWord ++ tailWord_1173696) baseStart_1173696 baseEnd_1173696 := by
    simpa [prefixWord, tailWord_1173696, baseEnd_1173696] using wordTrace_append hprefix tailTrace_1173696
  have hstable : (prefixWord ++ tailWord_1173696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173696).length < 2 ^ (prefixWord ++ tailWord_1173696).sum := by decide
  have hdescent : baseEnd_1173696 < baseStart_1173696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173800 : List Nat := [2, 1, 5, 1, 12]
def baseStart_1173800 : Nat := 118140960795 + 1173800 * 2 ^ 59
def prefixEnd_1173800 : Nat := 4983230072969 + 3 ^ 40 * 1173800 * 2
def baseEnd_1173800 : Nat := 3307125334691976602479

theorem tailTrace_1173800 : CollatzResearch.WordTrace tailWord_1173800 prefixEnd_1173800 3307125334691976602479 := by
  unfold tailWord_1173800
  simp only [CollatzResearch.WordTrace]
  refine ⟨21406001573765271962475427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28541335431687029283300569 21406001573765271962475427)
  ·
    refine ⟨32109002360647907943713141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21406001573765271962475427 32109002360647907943713141)
    ·
      refine ⟨3010218971310741369723107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32109002360647907943713141 3010218971310741369723107)
      ·
        refine ⟨4515328456966112054584661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3010218971310741369723107 4515328456966112054584661)
        ·
          refine ⟨3307125334691976602479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4515328456966112054584661 3307125334691976602479)
          ·
            rfl

theorem cell21_1173800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 12].length) (baseStart_1173800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173800 prefixEnd_1173800 := by exact prefixLift 1173800
  have htrace : WordTrace (prefixWord ++ tailWord_1173800) baseStart_1173800 baseEnd_1173800 := by
    simpa [prefixWord, tailWord_1173800, baseEnd_1173800] using wordTrace_append hprefix tailTrace_1173800
  have hstable : (prefixWord ++ tailWord_1173800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173800).length < 2 ^ (prefixWord ++ tailWord_1173800).sum := by decide
  have hdescent : baseEnd_1173800 < baseStart_1173800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173817 : List Nat := [1, 2, 1, 6, 1, 1, 3, 6]
def baseStart_1173817 : Nat := 118140960795 + 1173817 * 2 ^ 59
def prefixEnd_1173817 : Nat := 4983230072969 + 3 ^ 40 * 1173817 * 2
def baseEnd_1173817 : Nat := 89293677247220617672477

theorem tailTrace_1173817 : CollatzResearch.WordTrace tailWord_1173817 prefixEnd_1173817 89293677247220617672477 := by
  unfold tailWord_1173817
  simp only [CollatzResearch.WordTrace]
  refine ⟨42812623188468955828319705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28541748792312637218879803 42812623188468955828319705)
  ·
    refine ⟨32109467391351716871239779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42812623188468955828319705 32109467391351716871239779)
    ·
      refine ⟨48164201087027575306859669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32109467391351716871239779 48164201087027575306859669)
      ·
        refine ⟨2257696925954417592509047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48164201087027575306859669 2257696925954417592509047)
        ·
          refine ⟨3386545388931626388763571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257696925954417592509047 3386545388931626388763571)
          ·
            refine ⟨5079818083397439583145357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3386545388931626388763571 5079818083397439583145357)
            ·
              refine ⟨1904931781274039843679509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5079818083397439583145357 1904931781274039843679509)
              ·
                refine ⟨89293677247220617672477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1904931781274039843679509 89293677247220617672477)
                ·
                  rfl

theorem cell21_1173817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 6].length) (baseStart_1173817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173817 prefixEnd_1173817 := by exact prefixLift 1173817
  have htrace : WordTrace (prefixWord ++ tailWord_1173817) baseStart_1173817 baseEnd_1173817 := by
    simpa [prefixWord, tailWord_1173817, baseEnd_1173817] using wordTrace_append hprefix tailTrace_1173817
  have hstable : (prefixWord ++ tailWord_1173817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173817).length < 2 ^ (prefixWord ++ tailWord_1173817).sum := by decide
  have hdescent : baseEnd_1173817 < baseStart_1173817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173831 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 5]
def baseStart_1173831 : Nat := 118140960795 + 1173831 * 2 ^ 59
def prefixEnd_1173831 : Nat := 4983230072969 + 3 ^ 40 * 1173831 * 2
def baseEnd_1173831 : Nat := 267884226732400939784069

theorem tailTrace_1173831 : CollatzResearch.WordTrace tailWord_1173831 prefixEnd_1173831 267884226732400939784069 := by
  unfold tailWord_1173831
  simp only [CollatzResearch.WordTrace]
  refine ⟨42813133810418236219329347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28542089206945490812886231 42813133810418236219329347)
  ·
    refine ⟨64219700715627354328994021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42813133810418236219329347 64219700715627354328994021)
    ·
      refine ⟨12041193884180128936686379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64219700715627354328994021 12041193884180128936686379)
      ·
        refine ⟨18061790826270193405029569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12041193884180128936686379 18061790826270193405029569)
        ·
          refine ⟨13546343119702645053772177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18061790826270193405029569 13546343119702645053772177)
          ·
            refine ⟨10159757339776983790329133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13546343119702645053772177 10159757339776983790329133)
            ·
              refine ⟨3809909002416368921373425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10159757339776983790329133 3809909002416368921373425)
              ·
                refine ⟨2857431751812276691030069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3809909002416368921373425 2857431751812276691030069)
                ·
                  refine ⟨267884226732400939784069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2857431751812276691030069 267884226732400939784069)
                  ·
                    rfl

theorem cell21_1173831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_1173831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173831 prefixEnd_1173831 := by exact prefixLift 1173831
  have htrace : WordTrace (prefixWord ++ tailWord_1173831) baseStart_1173831 baseEnd_1173831 := by
    simpa [prefixWord, tailWord_1173831, baseEnd_1173831] using wordTrace_append hprefix tailTrace_1173831
  have hstable : (prefixWord ++ tailWord_1173831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173831).length < 2 ^ (prefixWord ++ tailWord_1173831).sum := by decide
  have hdescent : baseEnd_1173831 < baseStart_1173831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173854 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1173854 : Nat := 118140960795 + 1173854 * 2 ^ 59
def prefixEnd_1173854 : Nat := 4983230072969 + 3 ^ 40 * 1173854 * 2
def baseEnd_1173854 : Nat := 267889475645758010900689

theorem tailTrace_1173854 : CollatzResearch.WordTrace tailWord_1173854 prefixEnd_1173854 267889475645758010900689 := by
  unfold tailWord_1173854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5351746586166863893427077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28542648459556607431611077 5351746586166863893427077)
  ·
    refine ⟨1003452484906286980017577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5351746586166863893427077 1003452484906286980017577)
    ·
      refine ⟨752589363679715235013183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1003452484906286980017577 752589363679715235013183)
      ·
        refine ⟨1128884045519572852519775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752589363679715235013183 1128884045519572852519775)
        ·
          refine ⟨1693326068279359278779663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128884045519572852519775 1693326068279359278779663)
          ·
            refine ⟨2539989102419038918169495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693326068279359278779663 2539989102419038918169495)
            ·
              refine ⟨3809983653628558377254243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539989102419038918169495 3809983653628558377254243)
              ·
                refine ⟨5714975480442837565881365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3809983653628558377254243 5714975480442837565881365)
                ·
                  refine ⟨267889475645758010900689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5714975480442837565881365 267889475645758010900689)
                  ·
                    rfl

theorem cell21_1173854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1173854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173854 prefixEnd_1173854 := by exact prefixLift 1173854
  have htrace : WordTrace (prefixWord ++ tailWord_1173854) baseStart_1173854 baseEnd_1173854 := by
    simpa [prefixWord, tailWord_1173854, baseEnd_1173854] using wordTrace_append hprefix tailTrace_1173854
  have hstable : (prefixWord ++ tailWord_1173854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173854).length < 2 ^ (prefixWord ++ tailWord_1173854).sum := by decide
  have hdescent : baseEnd_1173854 < baseStart_1173854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173924 : List Nat := [2, 3, 1, 2, 1, 1, 2, 6, 3]
def baseStart_1173924 : Nat := 118140960795 + 1173924 * 2 ^ 59
def prefixEnd_1173924 : Nat := 4983230072969 + 3 ^ 40 * 1173924 * 2
def baseEnd_1173924 : Nat := 267905450599453444733879

theorem tailTrace_1173924 : CollatzResearch.WordTrace tailWord_1173924 prefixEnd_1173924 267905450599453444733879 := by
  unfold tailWord_1173924
  simp only [CollatzResearch.WordTrace]
  refine ⟨21408262899540656551232413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28544350532720875401643217 21408262899540656551232413)
  ·
    refine ⟨8028098587327746206712155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21408262899540656551232413 8028098587327746206712155)
    ·
      refine ⟨12042147880991619310068233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8028098587327746206712155 12042147880991619310068233)
      ·
        refine ⟨9031610910743714482551175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12042147880991619310068233 9031610910743714482551175)
        ·
          refine ⟨13547416366115571723826763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9031610910743714482551175 13547416366115571723826763)
          ·
            refine ⟨20321124549173357585740145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13547416366115571723826763 20321124549173357585740145)
            ·
              refine ⟨15240843411880018189305109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20321124549173357585740145 15240843411880018189305109)
              ·
                refine ⟨714414534931875852623677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15240843411880018189305109 714414534931875852623677)
                ·
                  refine ⟨267905450599453444733879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714414534931875852623677 267905450599453444733879)
                  ·
                    rfl

theorem cell21_1173924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_1173924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173924 prefixEnd_1173924 := by exact prefixLift 1173924
  have htrace : WordTrace (prefixWord ++ tailWord_1173924) baseStart_1173924 baseEnd_1173924 := by
    simpa [prefixWord, tailWord_1173924, baseEnd_1173924] using wordTrace_append hprefix tailTrace_1173924
  have hstable : (prefixWord ++ tailWord_1173924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173924).length < 2 ^ (prefixWord ++ tailWord_1173924).sum := by decide
  have hdescent : baseEnd_1173924 < baseStart_1173924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173938 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_1173938 : Nat := 118140960795 + 1173938 * 2 ^ 59
def prefixEnd_1173938 : Nat := 4983230072969 + 3 ^ 40 * 1173938 * 2
def baseEnd_1173938 : Nat := 267908645590192531500517

theorem tailTrace_1173938 : CollatzResearch.WordTrace tailWord_1173938 prefixEnd_1173938 267908645590192531500517 := by
  unfold tailWord_1173938
  simp only [CollatzResearch.WordTrace]
  refine ⟨10704259105257648373368617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28544690947353728995649645 10704259105257648373368617)
  ·
    refine ⟨8028194328943236280026463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10704259105257648373368617 8028194328943236280026463)
    ·
      refine ⟨12042291493414854420039695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8028194328943236280026463 12042291493414854420039695)
      ·
        refine ⟨18063437240122281630059543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12042291493414854420039695 18063437240122281630059543)
        ·
          refine ⟨27095155860183422445089315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18063437240122281630059543 27095155860183422445089315)
          ·
            refine ⟨40642733790275133667633973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27095155860183422445089315 40642733790275133667633973)
            ·
              refine ⟨3810256292838293781340685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40642733790275133667633973 3810256292838293781340685)
              ·
                refine ⟨1428846109814360168002757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3810256292838293781340685 1428846109814360168002757)
                ·
                  refine ⟨267908645590192531500517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428846109814360168002757 267908645590192531500517)
                  ·
                    rfl

theorem cell21_1173938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_1173938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1173938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1173938 prefixEnd_1173938 := by exact prefixLift 1173938
  have htrace : WordTrace (prefixWord ++ tailWord_1173938) baseStart_1173938 baseEnd_1173938 := by
    simpa [prefixWord, tailWord_1173938, baseEnd_1173938] using wordTrace_append hprefix tailTrace_1173938
  have hstable : (prefixWord ++ tailWord_1173938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173938).length < 2 ^ (prefixWord ++ tailWord_1173938).sum := by decide
  have hdescent : baseEnd_1173938 < baseStart_1173938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174017 : List Nat := [1, 2, 4, 1, 3, 2, 2, 3, 3]
def baseStart_1174017 : Nat := 118140960795 + 1174017 * 2 ^ 59
def prefixEnd_1174017 : Nat := 4983230072969 + 3 ^ 40 * 1174017 * 2
def baseEnd_1174017 : Nat := 267926674466505949683689

theorem tailTrace_1174017 : CollatzResearch.WordTrace tailWord_1174017 prefixEnd_1174017 267926674466505949683689 := by
  unfold tailWord_1174017
  simp only [CollatzResearch.WordTrace]
  refine ⟨42819917787744389985600305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28546611858496259990400203 42819917787744389985600305)
  ·
    refine ⟨32114938340808292489200229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42819917787744389985600305 32114938340808292489200229)
    ·
      refine ⟨6021550938901554841725043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32114938340808292489200229 6021550938901554841725043)
      ·
        refine ⟨9032326408352332262587565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6021550938901554841725043 9032326408352332262587565)
        ·
          refine ⟨3387122403132124598470337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9032326408352332262587565 3387122403132124598470337)
          ·
            refine ⟨2540341802349093448852753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3387122403132124598470337 2540341802349093448852753)
            ·
              refine ⟨1905256351761820086639565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2540341802349093448852753 1905256351761820086639565)
              ·
                refine ⟨714471131910682532489837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1905256351761820086639565 714471131910682532489837)
                ·
                  refine ⟨267926674466505949683689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714471131910682532489837 267926674466505949683689)
                  ·
                    rfl

theorem cell21_1174017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 3].length) (baseStart_1174017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174017 prefixEnd_1174017 := by exact prefixLift 1174017
  have htrace : WordTrace (prefixWord ++ tailWord_1174017) baseStart_1174017 baseEnd_1174017 := by
    simpa [prefixWord, tailWord_1174017, baseEnd_1174017] using wordTrace_append hprefix tailTrace_1174017
  have hstable : (prefixWord ++ tailWord_1174017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174017).length < 2 ^ (prefixWord ++ tailWord_1174017).sum := by decide
  have hdescent : baseEnd_1174017 < baseStart_1174017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174028 : List Nat := [2, 2, 1, 2, 4, 2, 8]
def baseStart_1174028 : Nat := 118140960795 + 1174028 * 2 ^ 59
def prefixEnd_1174028 : Nat := 4983230072969 + 3 ^ 40 * 1174028 * 2
def baseEnd_1174028 : Nat := 29769909424041375000037

theorem tailTrace_1174028 : CollatzResearch.WordTrace tailWord_1174028 prefixEnd_1174028 29769909424041375000037 := by
  unfold tailWord_1174028
  simp only [CollatzResearch.WordTrace]
  refine ⟨21410159495352269432125369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28546879327136359242833825 21410159495352269432125369)
  ·
    refine ⟨16057619621514202074094027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21410159495352269432125369 16057619621514202074094027)
    ·
      refine ⟨24086429432271303111141041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16057619621514202074094027 24086429432271303111141041)
      ·
        refine ⟨18064822074203477333355781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24086429432271303111141041 18064822074203477333355781)
        ·
          refine ⟨3387154138913152000004209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18064822074203477333355781 3387154138913152000004209)
          ·
            refine ⟨2540365604184864000003157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3387154138913152000004209 2540365604184864000003157)
            ·
              refine ⟨29769909424041375000037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2540365604184864000003157 29769909424041375000037)
              ·
                rfl

theorem cell21_1174028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 8].length) (baseStart_1174028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174028 prefixEnd_1174028 := by exact prefixLift 1174028
  have htrace : WordTrace (prefixWord ++ tailWord_1174028) baseStart_1174028 baseEnd_1174028 := by
    simpa [prefixWord, tailWord_1174028, baseEnd_1174028] using wordTrace_append hprefix tailTrace_1174028
  have hstable : (prefixWord ++ tailWord_1174028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174028).length < 2 ^ (prefixWord ++ tailWord_1174028).sum := by decide
  have hdescent : baseEnd_1174028 < baseStart_1174028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174048 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 4]
def baseStart_1174048 : Nat := 118140960795 + 1174048 * 2 ^ 59
def prefixEnd_1174048 : Nat := 4983230072969 + 3 ^ 40 * 1174048 * 2
def baseEnd_1174048 : Nat := 267933749088856784666959

theorem tailTrace_1174048 : CollatzResearch.WordTrace tailWord_1174048 prefixEnd_1174048 267933749088856784666959 := by
  unfold tailWord_1174048
  simp only [CollatzResearch.WordTrace]
  refine ⟨21410524225316041139989399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28547365633754721519985865 21410524225316041139989399)
  ·
    refine ⟨32115786337974061709984099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21410524225316041139989399 32115786337974061709984099)
    ·
      refine ⟨48173679506961092564976149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32115786337974061709984099 48173679506961092564976149)
      ·
        refine ⟨2258141226888801213983257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48173679506961092564976149 2258141226888801213983257)
        ·
          refine ⟨1693605920166600910487443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2258141226888801213983257 1693605920166600910487443)
          ·
            refine ⟨2540408880249901365731165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693605920166600910487443 2540408880249901365731165)
            ·
              refine ⟨952653330093713012149187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2540408880249901365731165 952653330093713012149187)
              ·
                refine ⟨1428979995140569518223781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952653330093713012149187 1428979995140569518223781)
                ·
                  refine ⟨267933749088856784666959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428979995140569518223781 267933749088856784666959)
                  ·
                    rfl

theorem cell21_1174048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_1174048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174048 prefixEnd_1174048 := by exact prefixLift 1174048
  have htrace : WordTrace (prefixWord ++ tailWord_1174048) baseStart_1174048 baseEnd_1174048 := by
    simpa [prefixWord, tailWord_1174048, baseEnd_1174048] using wordTrace_append hprefix tailTrace_1174048
  have hstable : (prefixWord ++ tailWord_1174048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174048).length < 2 ^ (prefixWord ++ tailWord_1174048).sum := by decide
  have hdescent : baseEnd_1174048 < baseStart_1174048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174068 : List Nat := [2, 5, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1174068 : Nat := 118140960795 + 1174068 * 2 ^ 59
def prefixEnd_1174068 : Nat := 4983230072969 + 3 ^ 40 * 1174068 * 2
def baseEnd_1174068 : Nat := 267938313361341194333585

theorem tailTrace_1174068 : CollatzResearch.WordTrace tailWord_1174068 prefixEnd_1174068 267938313361341194333585 := by
  unfold tailWord_1174068
  simp only [CollatzResearch.WordTrace]
  refine ⟨21410888955279812847853429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28547851940373083797137905 21410888955279812847853429)
  ·
    refine ⟨2007270839557482454486259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21410888955279812847853429 2007270839557482454486259)
    ·
      refine ⟨3010906259336223681729389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2007270839557482454486259 3010906259336223681729389)
      ·
        refine ⟨1129089847251083880648521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3010906259336223681729389 1129089847251083880648521)
        ·
          refine ⟨846817385438312910486391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1129089847251083880648521 846817385438312910486391)
          ·
            refine ⟨1270226078157469365729587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846817385438312910486391 1270226078157469365729587)
            ·
              refine ⟨1905339117236204048594381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270226078157469365729587 1905339117236204048594381)
              ·
                refine ⟨714502168963576518222893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1905339117236204048594381 714502168963576518222893)
                ·
                  refine ⟨267938313361341194333585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714502168963576518222893 267938313361341194333585)
                  ·
                    rfl

theorem cell21_1174068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1174068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174068 prefixEnd_1174068 := by exact prefixLift 1174068
  have htrace : WordTrace (prefixWord ++ tailWord_1174068) baseStart_1174068 baseEnd_1174068 := by
    simpa [prefixWord, tailWord_1174068, baseEnd_1174068] using wordTrace_append hprefix tailTrace_1174068
  have hstable : (prefixWord ++ tailWord_1174068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174068).length < 2 ^ (prefixWord ++ tailWord_1174068).sum := by decide
  have hdescent : baseEnd_1174068 < baseStart_1174068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174073 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 8]
def baseStart_1174073 : Nat := 118140960795 + 1174073 * 2 ^ 59
def prefixEnd_1174073 : Nat := 4983230072969 + 3 ^ 40 * 1174073 * 2
def baseEnd_1174073 : Nat := 267939454429462296750241

theorem tailTrace_1174073 : CollatzResearch.WordTrace tailWord_1174073 prefixEnd_1174073 267939454429462296750241 := by
  unfold tailWord_1174073
  simp only [CollatzResearch.WordTrace]
  refine ⟨42821960275541511549638873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28547973517027674366425915 42821960275541511549638873)
  ·
    refine ⟨32116470206656133662229155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42821960275541511549638873 32116470206656133662229155)
    ·
      refine ⟨48174705309984200493343733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32116470206656133662229155 48174705309984200493343733)
      ·
        refine ⟨4516378622811018796250975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48174705309984200493343733 4516378622811018796250975)
        ·
          refine ⟨6774567934216528194376463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4516378622811018796250975 6774567934216528194376463)
          ·
            refine ⟨10161851901324792291564695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6774567934216528194376463 10161851901324792291564695)
            ·
              refine ⟨15242777851987188437347043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10161851901324792291564695 15242777851987188437347043)
              ·
                refine ⟨22864166777980782656020565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15242777851987188437347043 22864166777980782656020565)
                ·
                  refine ⟨267939454429462296750241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22864166777980782656020565 267939454429462296750241)
                  ·
                    rfl

theorem cell21_1174073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_1174073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174073 prefixEnd_1174073 := by exact prefixLift 1174073
  have htrace : WordTrace (prefixWord ++ tailWord_1174073) baseStart_1174073 baseEnd_1174073 := by
    simpa [prefixWord, tailWord_1174073, baseEnd_1174073] using wordTrace_append hprefix tailTrace_1174073
  have hstable : (prefixWord ++ tailWord_1174073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174073).length < 2 ^ (prefixWord ++ tailWord_1174073).sum := by decide
  have hdescent : baseEnd_1174073 < baseStart_1174073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174093 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1174093 : Nat := 118140960795 + 1174093 * 2 ^ 59
def prefixEnd_1174093 : Nat := 4983230072969 + 3 ^ 40 * 1174093 * 2
def baseEnd_1174093 : Nat := 267944018701946706416867

theorem tailTrace_1174093 : CollatzResearch.WordTrace tailWord_1174093 prefixEnd_1174093 267944018701946706416867 := by
  unfold tailWord_1174093
  simp only [CollatzResearch.WordTrace]
  refine ⟨42822689735469054965366933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28548459823646036643577955 42822689735469054965366933)
  ·
    refine ⟨2007313581350111951501575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42822689735469054965366933 2007313581350111951501575)
    ·
      refine ⟨3010970372025167927252363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2007313581350111951501575 3010970372025167927252363)
      ·
        refine ⟨4516455558037751890878545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3010970372025167927252363 4516455558037751890878545)
        ·
          refine ⟨3387341668528313918158909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4516455558037751890878545 3387341668528313918158909)
          ·
            refine ⟨1270253125698117719309591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3387341668528313918158909 1270253125698117719309591)
            ·
              refine ⟨1905379688547176578964387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270253125698117719309591 1905379688547176578964387)
              ·
                refine ⟨2858069532820764868446581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905379688547176578964387 2858069532820764868446581)
                ·
                  refine ⟨267944018701946706416867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2858069532820764868446581 267944018701946706416867)
                  ·
                    rfl

theorem cell21_1174093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1174093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174093 prefixEnd_1174093 := by exact prefixLift 1174093
  have htrace : WordTrace (prefixWord ++ tailWord_1174093) baseStart_1174093 baseEnd_1174093 := by
    simpa [prefixWord, tailWord_1174093, baseEnd_1174093] using wordTrace_append hprefix tailTrace_1174093
  have hstable : (prefixWord ++ tailWord_1174093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174093).length < 2 ^ (prefixWord ++ tailWord_1174093).sum := by decide
  have hdescent : baseEnd_1174093 < baseStart_1174093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174194 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_1174194 : Nat := 118140960795 + 1174194 * 2 ^ 59
def prefixEnd_1174194 : Nat := 4983230072969 + 3 ^ 40 * 1174194 * 2
def baseEnd_1174194 : Nat := 267967068277992975233327

theorem tailTrace_1174194 : CollatzResearch.WordTrace tailWord_1174194 prefixEnd_1174194 267967068277992975233327 := by
  unfold tailWord_1174194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706593377025787303698409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28550915672068766143195757 10706593377025787303698409)
  ·
    refine ⟨8029945032769340477773807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10706593377025787303698409 8029945032769340477773807)
    ·
      refine ⟨12044917549154010716660711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8029945032769340477773807 12044917549154010716660711)
      ·
        refine ⟨18067376323731016074991067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12044917549154010716660711 18067376323731016074991067)
        ·
          refine ⟨27101064485596524112486601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18067376323731016074991067 27101064485596524112486601)
          ·
            refine ⟨20325798364197393084364951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27101064485596524112486601 20325798364197393084364951)
            ·
              refine ⟨30488697546296089626547427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20325798364197393084364951 30488697546296089626547427)
              ·
                refine ⟨45733046319444134439821141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30488697546296089626547427 45733046319444134439821141)
                ·
                  refine ⟨267967068277992975233327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45733046319444134439821141 267967068277992975233327)
                  ·
                    rfl

theorem cell21_1174194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_1174194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174194 prefixEnd_1174194 := by exact prefixLift 1174194
  have htrace : WordTrace (prefixWord ++ tailWord_1174194) baseStart_1174194 baseEnd_1174194 := by
    simpa [prefixWord, tailWord_1174194, baseEnd_1174194] using wordTrace_append hprefix tailTrace_1174194
  have hstable : (prefixWord ++ tailWord_1174194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174194).length < 2 ^ (prefixWord ++ tailWord_1174194).sum := by decide
  have hdescent : baseEnd_1174194 < baseStart_1174194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174245 : List Nat := [1, 3, 1, 4, 1, 4, 1, 3, 3]
def baseStart_1174245 : Nat := 118140960795 + 1174245 * 2 ^ 59
def prefixEnd_1174245 : Nat := 4983230072969 + 3 ^ 40 * 1174245 * 2
def baseEnd_1174245 : Nat := 267978707172828219883223

theorem tailTrace_1174245 : CollatzResearch.WordTrace tailWord_1174245 prefixEnd_1174245 267978707172828219883223 := by
  unfold tailWord_1174245
  simp only [CollatzResearch.WordTrace]
  refine ⟨42828233630918384924900189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28552155753945589949933459 42828233630918384924900189)
  ·
    refine ⟨16060587611594394346837571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42828233630918384924900189 16060587611594394346837571)
    ·
      refine ⟨24090881417391591520256357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16060587611594394346837571 24090881417391591520256357)
      ·
        refine ⟨4517040265760923410048067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24090881417391591520256357 4517040265760923410048067)
        ·
          refine ⟨6775560398641385115072101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517040265760923410048067 6775560398641385115072101)
          ·
            refine ⟨1270417574745259709076019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6775560398641385115072101 1270417574745259709076019)
            ·
              refine ⟨1905626362117889563614029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270417574745259709076019 1905626362117889563614029)
              ·
                refine ⟨714609885794208586355261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1905626362117889563614029 714609885794208586355261)
                ·
                  refine ⟨267978707172828219883223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714609885794208586355261 267978707172828219883223)
                  ·
                    rfl

theorem cell21_1174245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_1174245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174245 prefixEnd_1174245 := by exact prefixLift 1174245
  have htrace : WordTrace (prefixWord ++ tailWord_1174245) baseStart_1174245 baseEnd_1174245 := by
    simpa [prefixWord, tailWord_1174245, baseEnd_1174245] using wordTrace_append hprefix tailTrace_1174245
  have hstable : (prefixWord ++ tailWord_1174245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174245).length < 2 ^ (prefixWord ++ tailWord_1174245).sum := by decide
  have hdescent : baseEnd_1174245 < baseStart_1174245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174408 : List Nat := [2, 1, 3, 3, 2, 2, 1, 7]
def baseStart_1174408 : Nat := 118140960795 + 1174408 * 2 ^ 59
def prefixEnd_1174408 : Nat := 4983230072969 + 3 ^ 40 * 1174408 * 2
def baseEnd_1174408 : Nat := 89338635331192052888741

theorem tailTrace_1174408 : CollatzResearch.WordTrace tailWord_1174408 prefixEnd_1174408 89338635331192052888741 := by
  unfold tailWord_1174408
  simp only [CollatzResearch.WordTrace]
  refine ⟨21417089364663931881541939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28556119152885242508722585 21417089364663931881541939)
  ·
    refine ⟨32125634046995897822312909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21417089364663931881541939 32125634046995897822312909)
    ·
      refine ⟨12047112767623461683367341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32125634046995897822312909 12047112767623461683367341)
      ·
        refine ⟨4517667287858798131262753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12047112767623461683367341 4517667287858798131262753)
        ·
          refine ⟨3388250465894098598447065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4517667287858798131262753 3388250465894098598447065)
          ·
            refine ⟨2541187849420573948835299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3388250465894098598447065 2541187849420573948835299)
            ·
              refine ⟨3811781774130860923252949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2541187849420573948835299 3811781774130860923252949)
              ·
                refine ⟨89338635331192052888741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3811781774130860923252949 89338635331192052888741)
                ·
                  rfl

theorem cell21_1174408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_1174408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174408 prefixEnd_1174408 := by exact prefixLift 1174408
  have htrace : WordTrace (prefixWord ++ tailWord_1174408) baseStart_1174408 baseEnd_1174408 := by
    simpa [prefixWord, tailWord_1174408, baseEnd_1174408] using wordTrace_append hprefix tailTrace_1174408
  have hstable : (prefixWord ++ tailWord_1174408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174408).length < 2 ^ (prefixWord ++ tailWord_1174408).sum := by decide
  have hdescent : baseEnd_1174408 < baseStart_1174408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174445 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1174445 : Nat := 118140960795 + 1174445 * 2 ^ 59
def prefixEnd_1174445 : Nat := 4983230072969 + 3 ^ 40 * 1174445 * 2
def baseEnd_1174445 : Nat := 268024349897672316549481

theorem tailTrace_1174445 : CollatzResearch.WordTrace tailWord_1174445 prefixEnd_1174445 268024349897672316549481 := by
  unfold tailWord_1174445
  simp only [CollatzResearch.WordTrace]
  refine ⟨42835528230193819082180789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28557018820129212721453859 42835528230193819082180789)
  ·
    refine ⟨4015830771580670538954449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42835528230193819082180789 4015830771580670538954449)
    ·
      refine ⟨3011873078685502904215837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4015830771580670538954449 3011873078685502904215837)
      ·
        refine ⟨1129452404507063589080939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3011873078685502904215837 1129452404507063589080939)
        ·
          refine ⟨1694178606760595383621409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129452404507063589080939 1694178606760595383621409)
          ·
            refine ⟨1270633955070446537716057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1694178606760595383621409 1270633955070446537716057)
            ·
              refine ⟨952975466302834903287043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1270633955070446537716057 952975466302834903287043)
              ·
                refine ⟨1429463199454252354930565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952975466302834903287043 1429463199454252354930565)
                ·
                  refine ⟨268024349897672316549481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1429463199454252354930565 268024349897672316549481)
                  ·
                    rfl

theorem cell21_1174445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1174445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174445 prefixEnd_1174445 := by exact prefixLift 1174445
  have htrace : WordTrace (prefixWord ++ tailWord_1174445) baseStart_1174445 baseEnd_1174445 := by
    simpa [prefixWord, tailWord_1174445, baseEnd_1174445] using wordTrace_append hprefix tailTrace_1174445
  have hstable : (prefixWord ++ tailWord_1174445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174445).length < 2 ^ (prefixWord ++ tailWord_1174445).sum := by decide
  have hdescent : baseEnd_1174445 < baseStart_1174445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174512 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_1174512 : Nat := 118140960795 + 1174512 * 2 ^ 59
def prefixEnd_1174512 : Nat := 4983230072969 + 3 ^ 40 * 1174512 * 2
def baseEnd_1174512 : Nat := 268039640210495088932677

theorem tailTrace_1174512 : CollatzResearch.WordTrace tailWord_1174512 prefixEnd_1174512 268039640210495088932677 := by
  unfold tailWord_1174512
  simp only [CollatzResearch.WordTrace]
  refine ⟨21418985960475544762434895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28558647947300726349913193 21418985960475544762434895)
  ·
    refine ⟨32128478940713317143652343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21418985960475544762434895 32128478940713317143652343)
    ·
      refine ⟨48192718411069975715478515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32128478940713317143652343 48192718411069975715478515)
      ·
        refine ⟨72289077616604963573217773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48192718411069975715478515 72289077616604963573217773)
        ·
          refine ⟨27108404106226861339956665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72289077616604963573217773 27108404106226861339956665)
          ·
            refine ⟨20331303079670146004967499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27108404106226861339956665 20331303079670146004967499)
            ·
              refine ⟨30496954619505219007451249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20331303079670146004967499 30496954619505219007451249)
              ·
                refine ⟨22872715964628914255588437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30496954619505219007451249 22872715964628914255588437)
                ·
                  refine ⟨268039640210495088932677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22872715964628914255588437 268039640210495088932677)
                  ·
                    rfl

theorem cell21_1174512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_1174512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174512 prefixEnd_1174512 := by exact prefixLift 1174512
  have htrace : WordTrace (prefixWord ++ tailWord_1174512) baseStart_1174512 baseEnd_1174512 := by
    simpa [prefixWord, tailWord_1174512, baseEnd_1174512] using wordTrace_append hprefix tailTrace_1174512
  have hstable : (prefixWord ++ tailWord_1174512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174512).length < 2 ^ (prefixWord ++ tailWord_1174512).sum := by decide
  have hdescent : baseEnd_1174512 < baseStart_1174512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174614 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1174614 : Nat := 118140960795 + 1174614 * 2 ^ 59
def prefixEnd_1174614 : Nat := 4983230072969 + 3 ^ 40 * 1174614 * 2
def baseEnd_1174614 : Nat := 268062918000165578232469

theorem tailTrace_1174614 : CollatzResearch.WordTrace tailWord_1174614 prefixEnd_1174614 268062918000165578232469 := by
  unfold tailWord_1174614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2677605760411347559067681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28561128111054373963388597 2677605760411347559067681)
  ·
    refine ⟨2008204320308510669300761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2677605760411347559067681 2008204320308510669300761)
    ·
      refine ⟨1506153240231383001975571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2008204320308510669300761 1506153240231383001975571)
      ·
        refine ⟨2259229860347074502963357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506153240231383001975571 2259229860347074502963357)
        ·
          refine ⟨847211197630152938611259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2259229860347074502963357 847211197630152938611259)
          ·
            refine ⟨1270816796445229407916889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847211197630152938611259 1270816796445229407916889)
            ·
              refine ⟨953112597333922055937667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1270816796445229407916889 953112597333922055937667)
              ·
                refine ⟨1429668896000883083906501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953112597333922055937667 1429668896000883083906501)
                ·
                  refine ⟨268062918000165578232469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1429668896000883083906501 268062918000165578232469)
                  ·
                    rfl

theorem cell21_1174614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1174614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174614 prefixEnd_1174614 := by exact prefixLift 1174614
  have htrace : WordTrace (prefixWord ++ tailWord_1174614) baseStart_1174614 baseEnd_1174614 := by
    simpa [prefixWord, tailWord_1174614, baseEnd_1174614] using wordTrace_append hprefix tailTrace_1174614
  have hstable : (prefixWord ++ tailWord_1174614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174614).length < 2 ^ (prefixWord ++ tailWord_1174614).sum := by decide
  have hdescent : baseEnd_1174614 < baseStart_1174614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174701 : List Nat := [1, 5, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1174701 : Nat := 118140960795 + 1174701 * 2 ^ 59
def prefixEnd_1174701 : Nat := 4983230072969 + 3 ^ 40 * 1174701 * 2
def baseEnd_1174701 : Nat := 268082772585472760282291

theorem tailTrace_1174701 : CollatzResearch.WordTrace tailWord_1174701 prefixEnd_1174701 268082772585472760282291 := by
  unfold tailWord_1174701
  simp only [CollatzResearch.WordTrace]
  refine ⟨42844865317266374803499957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28563243544844249868999971 42844865317266374803499957)
  ·
    refine ⟨4016706123493722637828121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42844865317266374803499957 4016706123493722637828121)
    ·
      refine ⟨3012529592620291978371091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4016706123493722637828121 3012529592620291978371091)
      ·
        refine ⟨4518794388930437967556637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012529592620291978371091 4518794388930437967556637)
        ·
          refine ⟨1694547895848914237833739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4518794388930437967556637 1694547895848914237833739)
          ·
            refine ⟨2541821843773371356750609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1694547895848914237833739 2541821843773371356750609)
            ·
              refine ⟨1906366382830028517562957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2541821843773371356750609 1906366382830028517562957)
              ·
                refine ⟨714887393561260694086109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1906366382830028517562957 714887393561260694086109)
                ·
                  refine ⟨268082772585472760282291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714887393561260694086109 268082772585472760282291)
                  ·
                    rfl

theorem cell21_1174701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1174701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174701 prefixEnd_1174701 := by exact prefixLift 1174701
  have htrace : WordTrace (prefixWord ++ tailWord_1174701) baseStart_1174701 baseEnd_1174701 := by
    simpa [prefixWord, tailWord_1174701, baseEnd_1174701] using wordTrace_append hprefix tailTrace_1174701
  have hstable : (prefixWord ++ tailWord_1174701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174701).length < 2 ^ (prefixWord ++ tailWord_1174701).sum := by decide
  have hdescent : baseEnd_1174701 < baseStart_1174701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174771 : List Nat := [1, 1, 1, 2, 2, 7, 7]
def baseStart_1174771 : Nat := 118140960795 + 1174771 * 2 ^ 59
def prefixEnd_1174771 : Nat := 4983230072969 + 3 ^ 40 * 1174771 * 2
def baseEnd_1174771 : Nat := 29788749726574243790609

theorem tailTrace_1174771 : CollatzResearch.WordTrace tailWord_1174771 prefixEnd_1174771 29788749726574243790609 := by
  unfold tailWord_1174771
  simp only [CollatzResearch.WordTrace]
  refine ⟨42847418427012776758548167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28564945618008517839032111 42847418427012776758548167)
  ·
    refine ⟨64271127640519165137822251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42847418427012776758548167 64271127640519165137822251)
    ·
      refine ⟨96406691460778747706733377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64271127640519165137822251 96406691460778747706733377)
      ·
        refine ⟨72305018595584060780050033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96406691460778747706733377 72305018595584060780050033)
        ·
          refine ⟨54228763946688045585037525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72305018595584060780050033 54228763946688045585037525)
          ·
            refine ⟨1270986655000501068399317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 54228763946688045585037525 1270986655000501068399317)
            ·
              refine ⟨29788749726574243790609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1270986655000501068399317 29788749726574243790609)
              ·
                rfl

theorem cell21_1174771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 7].length) (baseStart_1174771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174771 prefixEnd_1174771 := by exact prefixLift 1174771
  have htrace : WordTrace (prefixWord ++ tailWord_1174771) baseStart_1174771 baseEnd_1174771 := by
    simpa [prefixWord, tailWord_1174771, baseEnd_1174771] using wordTrace_append hprefix tailTrace_1174771
  have hstable : (prefixWord ++ tailWord_1174771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174771).length < 2 ^ (prefixWord ++ tailWord_1174771).sum := by decide
  have hdescent : baseEnd_1174771 < baseStart_1174771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174788 : List Nat := [2, 3, 2, 2, 2, 2, 2, 6]
def baseStart_1174788 : Nat := 118140960795 + 1174788 * 2 ^ 59
def prefixEnd_1174788 : Nat := 4983230072969 + 3 ^ 40 * 1174788 * 2
def baseEnd_1174788 : Nat := 89367542390259980777371

theorem tailTrace_1174788 : CollatzResearch.WordTrace tailWord_1174788 prefixEnd_1174788 89367542390259980777371 := by
  unfold tailWord_1174788
  simp only [CollatzResearch.WordTrace]
  refine ⟨21424019233975594330958509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28565358978634125774611345 21424019233975594330958509)
  ·
    refine ⟨8034007212740847874109441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21424019233975594330958509 8034007212740847874109441)
    ·
      refine ⟨6025505409555635905582081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8034007212740847874109441 6025505409555635905582081)
      ·
        refine ⟨4519129057166726929186561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6025505409555635905582081 4519129057166726929186561)
        ·
          refine ⟨3389346792875045196889921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4519129057166726929186561 3389346792875045196889921)
          ·
            refine ⟨2542010094656283897667441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3389346792875045196889921 2542010094656283897667441)
            ·
              refine ⟨1906507570992212923250581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542010094656283897667441 1906507570992212923250581)
              ·
                refine ⟨89367542390259980777371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1906507570992212923250581 89367542390259980777371)
                ·
                  rfl

theorem cell21_1174788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_1174788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174788 prefixEnd_1174788 := by exact prefixLift 1174788
  have htrace : WordTrace (prefixWord ++ tailWord_1174788) baseStart_1174788 baseEnd_1174788 := by
    simpa [prefixWord, tailWord_1174788, baseEnd_1174788] using wordTrace_append hprefix tailTrace_1174788
  have hstable : (prefixWord ++ tailWord_1174788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174788).length < 2 ^ (prefixWord ++ tailWord_1174788).sum := by decide
  have hdescent : baseEnd_1174788 < baseStart_1174788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174833 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 4]
def baseStart_1174833 : Nat := 118140960795 + 1174833 * 2 ^ 59
def prefixEnd_1174833 : Nat := 4983230072969 + 3 ^ 40 * 1174833 * 2
def baseEnd_1174833 : Nat := 268112896783869864082021

theorem tailTrace_1174833 : CollatzResearch.WordTrace tailWord_1174833 prefixEnd_1174833 268112896783869864082021 := by
  unfold tailWord_1174833
  simp only [CollatzResearch.WordTrace]
  refine ⟨42849679752788161347305153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28566453168525440898203435 42849679752788161347305153)
  ·
    refine ⟨32137259814591121010478865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42849679752788161347305153 32137259814591121010478865)
    ·
      refine ⟨24102944860943340757859149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32137259814591121010478865 24102944860943340757859149)
      ·
        refine ⟨9038604322853752784197181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24102944860943340757859149 9038604322853752784197181)
        ·
          refine ⟨3389476621070157294073943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9038604322853752784197181 3389476621070157294073943)
          ·
            refine ⟨5084214931605235941110915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389476621070157294073943 5084214931605235941110915)
            ·
              refine ⟨7626322397407853911666373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084214931605235941110915 7626322397407853911666373)
              ·
                refine ⟨1429935449513972608437445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7626322397407853911666373 1429935449513972608437445)
                ·
                  refine ⟨268112896783869864082021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1429935449513972608437445 268112896783869864082021)
                  ·
                    rfl

theorem cell21_1174833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_1174833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174833 prefixEnd_1174833 := by exact prefixLift 1174833
  have htrace : WordTrace (prefixWord ++ tailWord_1174833) baseStart_1174833 baseEnd_1174833 := by
    simpa [prefixWord, tailWord_1174833, baseEnd_1174833] using wordTrace_append hprefix tailTrace_1174833
  have hstable : (prefixWord ++ tailWord_1174833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174833).length < 2 ^ (prefixWord ++ tailWord_1174833).sum := by decide
  have hdescent : baseEnd_1174833 < baseStart_1174833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174836 : List Nat := [2, 5, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1174836 : Nat := 118140960795 + 1174836 * 2 ^ 59
def prefixEnd_1174836 : Nat := 4983230072969 + 3 ^ 40 * 1174836 * 2
def baseEnd_1174836 : Nat := 268113581424742525532015

theorem tailTrace_1174836 : CollatzResearch.WordTrace tailWord_1174836 prefixEnd_1174836 268113581424742525532015 := by
  unfold tailWord_1174836
  simp only [CollatzResearch.WordTrace]
  refine ⟨21424894585888646429832181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28566526114518195239776241 21424894585888646429832181)
  ·
    refine ⟨2008583867427060602796767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21424894585888646429832181 2008583867427060602796767)
    ·
      refine ⟨3012875801140590904195151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2008583867427060602796767 3012875801140590904195151)
      ·
        refine ⟨4519313701710886356292727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012875801140590904195151 4519313701710886356292727)
        ·
          refine ⟨6778970552566329534439091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4519313701710886356292727 6778970552566329534439091)
          ·
            refine ⟨10168455828849494301658637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6778970552566329534439091 10168455828849494301658637)
            ·
              refine ⟨3813170935818560363121989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10168455828849494301658637 3813170935818560363121989)
              ·
                refine ⟨714969550465980068085373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3813170935818560363121989 714969550465980068085373)
                ·
                  refine ⟨268113581424742525532015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714969550465980068085373 268113581424742525532015)
                  ·
                    rfl

theorem cell21_1174836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1174836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174836 prefixEnd_1174836 := by exact prefixLift 1174836
  have htrace : WordTrace (prefixWord ++ tailWord_1174836) baseStart_1174836 baseEnd_1174836 := by
    simpa [prefixWord, tailWord_1174836, baseEnd_1174836] using wordTrace_append hprefix tailTrace_1174836
  have hstable : (prefixWord ++ tailWord_1174836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174836).length < 2 ^ (prefixWord ++ tailWord_1174836).sum := by decide
  have hdescent : baseEnd_1174836 < baseStart_1174836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174847 : List Nat := [1, 1, 2, 2, 4, 2, 3, 6]
def baseStart_1174847 : Nat := 118140960795 + 1174847 * 2 ^ 59
def prefixEnd_1174847 : Nat := 4983230072969 + 3 ^ 40 * 1174847 * 2
def baseEnd_1174847 : Nat := 89372030591536316949553

theorem tailTrace_1174847 : CollatzResearch.WordTrace tailWord_1174847 prefixEnd_1174847 89372030591536316949553 := by
  unfold tailWord_1174847
  simp only [CollatzResearch.WordTrace]
  refine ⟨42850190374737441738314795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28566793583158294492209863 42850190374737441738314795)
  ·
    refine ⟨64275285562106162607472193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42850190374737441738314795 64275285562106162607472193)
    ·
      refine ⟨48206464171579621955604145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64275285562106162607472193 48206464171579621955604145)
      ·
        refine ⟨36154848128684716466703109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48206464171579621955604145 36154848128684716466703109)
        ·
          refine ⟨6779034024128384337506833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36154848128684716466703109 6779034024128384337506833)
          ·
            refine ⟨5084275518096288253130125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6779034024128384337506833 5084275518096288253130125)
            ·
              refine ⟨1906603319286108094923797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5084275518096288253130125 1906603319286108094923797)
              ·
                refine ⟨89372030591536316949553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1906603319286108094923797 89372030591536316949553)
                ·
                  rfl

theorem cell21_1174847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 6].length) (baseStart_1174847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1174847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1174847 prefixEnd_1174847 := by exact prefixLift 1174847
  have htrace : WordTrace (prefixWord ++ tailWord_1174847) baseStart_1174847 baseEnd_1174847 := by
    simpa [prefixWord, tailWord_1174847, baseEnd_1174847] using wordTrace_append hprefix tailTrace_1174847
  have hstable : (prefixWord ++ tailWord_1174847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174847).length < 2 ^ (prefixWord ++ tailWord_1174847).sum := by decide
  have hdescent : baseEnd_1174847 < baseStart_1174847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175005 : List Nat := [1, 4, 3, 1, 1, 4, 2, 2, 3]
def baseStart_1175005 : Nat := 118140960795 + 1175005 * 2 ^ 59
def prefixEnd_1175005 : Nat := 4983230072969 + 3 ^ 40 * 1175005 * 2
def baseEnd_1175005 : Nat := 268152149527235787215003

theorem tailTrace_1175005 : CollatzResearch.WordTrace tailWord_1175005 prefixEnd_1175005 268152149527235787215003 := by
  unfold tailWord_1175005
  simp only [CollatzResearch.WordTrace]
  refine ⟨42855953108165034722566469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28570635405443356481710979 42855953108165034722566469)
  ·
    refine ⟨8035491207780944010481213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42855953108165034722566469 8035491207780944010481213)
    ·
      refine ⟨3013309202917854003930455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8035491207780944010481213 3013309202917854003930455)
      ·
        refine ⟨4519963804376781005895683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3013309202917854003930455 4519963804376781005895683)
        ·
          refine ⟨6779945706565171508843525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4519963804376781005895683 6779945706565171508843525)
          ·
            refine ⟨1271239819980969657908161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6779945706565171508843525 1271239819980969657908161)
            ·
              refine ⟨953429864985727243431121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271239819980969657908161 953429864985727243431121)
              ·
                refine ⟨715072398739295432573341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953429864985727243431121 715072398739295432573341)
                ·
                  refine ⟨268152149527235787215003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 715072398739295432573341 268152149527235787215003)
                  ·
                    rfl

theorem cell21_1175005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_1175005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175005 prefixEnd_1175005 := by exact prefixLift 1175005
  have htrace : WordTrace (prefixWord ++ tailWord_1175005) baseStart_1175005 baseEnd_1175005 := by
    simpa [prefixWord, tailWord_1175005, baseEnd_1175005] using wordTrace_append hprefix tailTrace_1175005
  have hstable : (prefixWord ++ tailWord_1175005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175005).length < 2 ^ (prefixWord ++ tailWord_1175005).sum := by decide
  have hdescent : baseEnd_1175005 < baseStart_1175005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175030 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1175030 : Nat := 118140960795 + 1175030 * 2 ^ 59
def prefixEnd_1175030 : Nat := 4983230072969 + 3 ^ 40 * 1175030 * 2
def baseEnd_1175030 : Nat := 268157854867841299298285

theorem tailTrace_1175030 : CollatzResearch.WordTrace tailWord_1175030 prefixEnd_1175030 268157854867841299298285 := by
  unfold tailWord_1175030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678554058317153999514159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28571243288716309328151029 2678554058317153999514159)
  ·
    refine ⟨4017831087475730999271239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2678554058317153999514159 4017831087475730999271239)
    ·
      refine ⟨6026746631213596498906859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4017831087475730999271239 6026746631213596498906859)
      ·
        refine ⟨9040119946820394748360289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6026746631213596498906859 9040119946820394748360289)
        ·
          refine ⟨6780089960115296061270217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9040119946820394748360289 6780089960115296061270217)
          ·
            refine ⟨5085067470086472045952663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6780089960115296061270217 5085067470086472045952663)
            ·
              refine ⟨7627601205129708068928995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5085067470086472045952663 7627601205129708068928995)
              ·
                refine ⟨11441401807694562103393493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7627601205129708068928995 11441401807694562103393493)
                ·
                  refine ⟨268157854867841299298285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11441401807694562103393493 268157854867841299298285)
                  ·
                    rfl

theorem cell21_1175030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1175030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175030 prefixEnd_1175030 := by exact prefixLift 1175030
  have htrace : WordTrace (prefixWord ++ tailWord_1175030) baseStart_1175030 baseEnd_1175030 := by
    simpa [prefixWord, tailWord_1175030, baseEnd_1175030] using wordTrace_append hprefix tailTrace_1175030
  have hstable : (prefixWord ++ tailWord_1175030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175030).length < 2 ^ (prefixWord ++ tailWord_1175030).sum := by decide
  have hdescent : baseEnd_1175030 < baseStart_1175030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175047 : List Nat := [1, 1, 4, 3, 2, 1, 1, 5, 3]
def baseStart_1175047 : Nat := 118140960795 + 1175047 * 2 ^ 59
def prefixEnd_1175047 : Nat := 4983230072969 + 3 ^ 40 * 1175047 * 2
def baseEnd_1175047 : Nat := 268161734499453047514917

theorem tailTrace_1175047 : CollatzResearch.WordTrace tailWord_1175047 prefixEnd_1175047 268161734499453047514917 := by
  unfold tailWord_1175047
  simp only [CollatzResearch.WordTrace]
  refine ⟨42857484974012875895595395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28571656649341917263730263 42857484974012875895595395)
  ·
    refine ⟨64286227461019313843393093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42857484974012875895595395 64286227461019313843393093)
    ·
      refine ⟨12053667648941121345636205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64286227461019313843393093 12053667648941121345636205)
      ·
        refine ⟨4520125368352920504613577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12053667648941121345636205 4520125368352920504613577)
        ·
          refine ⟨3390094026264690378460183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4520125368352920504613577 3390094026264690378460183)
          ·
            refine ⟨5085141039397035567690275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390094026264690378460183 5085141039397035567690275)
            ·
              refine ⟨7627711559095553351535413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5085141039397035567690275 7627711559095553351535413)
              ·
                refine ⟨715097958665208126706445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7627711559095553351535413 715097958665208126706445)
                ·
                  refine ⟨268161734499453047514917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 715097958665208126706445 268161734499453047514917)
                  ·
                    rfl

theorem cell21_1175047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 3].length) (baseStart_1175047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175047 prefixEnd_1175047 := by exact prefixLift 1175047
  have htrace : WordTrace (prefixWord ++ tailWord_1175047) baseStart_1175047 baseEnd_1175047 := by
    simpa [prefixWord, tailWord_1175047, baseEnd_1175047] using wordTrace_append hprefix tailTrace_1175047
  have hstable : (prefixWord ++ tailWord_1175047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175047).length < 2 ^ (prefixWord ++ tailWord_1175047).sum := by decide
  have hdescent : baseEnd_1175047 < baseStart_1175047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175053 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1175053 : Nat := 118140960795 + 1175053 * 2 ^ 59
def prefixEnd_1175053 : Nat := 4983230072969 + 3 ^ 40 * 1175053 * 2
def baseEnd_1175053 : Nat := 268163103781198370414905

theorem tailTrace_1175053 : CollatzResearch.WordTrace tailWord_1175053 prefixEnd_1175053 268163103781198370414905 := by
  unfold tailWord_1175053
  simp only [CollatzResearch.WordTrace]
  refine ⟨42857703811991138920313813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28571802541327425946875875 42857703811991138920313813)
  ·
    refine ⟨1004477433093542318444855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 42857703811991138920313813 1004477433093542318444855)
    ·
      refine ⟨1506716149640313477667283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004477433093542318444855 1506716149640313477667283)
      ·
        refine ⟨2260074224460470216500925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506716149640313477667283 2260074224460470216500925)
        ·
          refine ⟨847527834172676331187847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2260074224460470216500925 847527834172676331187847)
          ·
            refine ⟨1271291751259014496781771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847527834172676331187847 1271291751259014496781771)
            ·
              refine ⟨1906937626888521745172657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271291751259014496781771 1906937626888521745172657)
              ·
                refine ⟨1430203220166391308879493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906937626888521745172657 1430203220166391308879493)
                ·
                  refine ⟨268163103781198370414905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1430203220166391308879493 268163103781198370414905)
                  ·
                    rfl

theorem cell21_1175053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1175053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175053 prefixEnd_1175053 := by exact prefixLift 1175053
  have htrace : WordTrace (prefixWord ++ tailWord_1175053) baseStart_1175053 baseEnd_1175053 := by
    simpa [prefixWord, tailWord_1175053, baseEnd_1175053] using wordTrace_append hprefix tailTrace_1175053
  have hstable : (prefixWord ++ tailWord_1175053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175053).length < 2 ^ (prefixWord ++ tailWord_1175053).sum := by decide
  have hdescent : baseEnd_1175053 < baseStart_1175053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175061 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 4]
def baseStart_1175061 : Nat := 118140960795 + 1175061 * 2 ^ 59
def prefixEnd_1175061 : Nat := 4983230072969 + 3 ^ 40 * 1175061 * 2
def baseEnd_1175061 : Nat := 268164929490192134281555

theorem tailTrace_1175061 : CollatzResearch.WordTrace tailWord_1175061 prefixEnd_1175061 268164929490192134281555 := by
  unfold tailWord_1175061
  simp only [CollatzResearch.WordTrace]
  refine ⟨42857995595962156286605037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28571997063974770857736691 42857995595962156286605037)
  ·
    refine ⟨16071748348485808607476889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42857995595962156286605037 16071748348485808607476889)
    ·
      refine ⟨12053811261364356455607667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16071748348485808607476889 12053811261364356455607667)
      ·
        refine ⟨18080716892046534683411501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12053811261364356455607667 18080716892046534683411501)
        ·
          refine ⟨6780268834517450506279313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18080716892046534683411501 6780268834517450506279313)
          ·
            refine ⟨5085201625888087879709485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6780268834517450506279313 5085201625888087879709485)
            ·
              refine ⟨1906950609708032954891057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5085201625888087879709485 1906950609708032954891057)
              ·
                refine ⟨1430212957281024716168293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906950609708032954891057 1430212957281024716168293)
                ·
                  refine ⟨268164929490192134281555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1430212957281024716168293 268164929490192134281555)
                  ·
                    rfl

theorem cell21_1175061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_1175061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175061 prefixEnd_1175061 := by exact prefixLift 1175061
  have htrace : WordTrace (prefixWord ++ tailWord_1175061) baseStart_1175061 baseEnd_1175061 := by
    simpa [prefixWord, tailWord_1175061, baseEnd_1175061] using wordTrace_append hprefix tailTrace_1175061
  have hstable : (prefixWord ++ tailWord_1175061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175061).length < 2 ^ (prefixWord ++ tailWord_1175061).sum := by decide
  have hdescent : baseEnd_1175061 < baseStart_1175061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175120 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 4]
def baseStart_1175120 : Nat := 118140960795 + 1175120 * 2 ^ 59
def prefixEnd_1175120 : Nat := 4983230072969 + 3 ^ 40 * 1175120 * 2
def baseEnd_1175120 : Nat := 268178394094021142798101

theorem tailTrace_1175120 : CollatzResearch.WordTrace tailWord_1175120 prefixEnd_1175120 268178394094021142798101 := by
  unfold tailWord_1175120
  simp only [CollatzResearch.WordTrace]
  refine ⟨21430073751374204681501407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28573431668498939575335209 21430073751374204681501407)
  ·
    refine ⟨32145110627061307022252111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21430073751374204681501407 32145110627061307022252111)
    ·
      refine ⟨48217665940591960533378167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32145110627061307022252111 48217665940591960533378167)
      ·
        refine ⟨72326498910887940800067251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48217665940591960533378167 72326498910887940800067251)
        ·
          refine ⟨108489748366331911200100877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72326498910887940800067251 108489748366331911200100877)
          ·
            refine ⟨40683655637374466700037829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108489748366331911200100877 40683655637374466700037829)
            ·
              refine ⟨7628185432007712506257093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40683655637374466700037829 7628185432007712506257093)
              ·
                refine ⟨1430284768501446094923205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7628185432007712506257093 1430284768501446094923205)
                ·
                  refine ⟨268178394094021142798101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1430284768501446094923205 268178394094021142798101)
                  ·
                    rfl

theorem cell21_1175120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_1175120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175120 prefixEnd_1175120 := by exact prefixLift 1175120
  have htrace : WordTrace (prefixWord ++ tailWord_1175120) baseStart_1175120 baseEnd_1175120 := by
    simpa [prefixWord, tailWord_1175120, baseEnd_1175120] using wordTrace_append hprefix tailTrace_1175120
  have hstable : (prefixWord ++ tailWord_1175120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175120).length < 2 ^ (prefixWord ++ tailWord_1175120).sum := by decide
  have hdescent : baseEnd_1175120 < baseStart_1175120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175126 : List Nat := [5, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1175126 : Nat := 118140960795 + 1175126 * 2 ^ 59
def prefixEnd_1175126 : Nat := 4983230072969 + 3 ^ 40 * 1175126 * 2
def baseEnd_1175126 : Nat := 89393254458588821899363

theorem tailTrace_1175126 : CollatzResearch.WordTrace tailWord_1175126 prefixEnd_1175126 89393254458588821899363 := by
  unfold tailWord_1175126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678772896295417024232577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28573577560484448258480821 2678772896295417024232577)
  ·
    refine ⟨2009079672221562768174433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2678772896295417024232577 2009079672221562768174433)
    ·
      refine ⟨1506809754166172076130825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2009079672221562768174433 1506809754166172076130825)
      ·
        refine ⟨1130107315624629057098119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1506809754166172076130825 1130107315624629057098119)
        ·
          refine ⟨1695160973436943585647179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130107315624629057098119 1695160973436943585647179)
          ·
            refine ⟨2542741460155415378470769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695160973436943585647179 2542741460155415378470769)
            ·
              refine ⟨1907056095116561533853077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542741460155415378470769 1907056095116561533853077)
              ·
                refine ⟨89393254458588821899363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1907056095116561533853077 89393254458588821899363)
                ·
                  rfl

theorem cell21_1175126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1175126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175126 prefixEnd_1175126 := by exact prefixLift 1175126
  have htrace : WordTrace (prefixWord ++ tailWord_1175126) baseStart_1175126 baseEnd_1175126 := by
    simpa [prefixWord, tailWord_1175126, baseEnd_1175126] using wordTrace_append hprefix tailTrace_1175126
  have hstable : (prefixWord ++ tailWord_1175126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175126).length < 2 ^ (prefixWord ++ tailWord_1175126).sum := by decide
  have hdescent : baseEnd_1175126 < baseStart_1175126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175199 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 5]
def baseStart_1175199 : Nat := 118140960795 + 1175199 * 2 ^ 59
def prefixEnd_1175199 : Nat := 4983230072969 + 3 ^ 40 * 1175199 * 2
def baseEnd_1175199 : Nat := 268196422970334560981273

theorem tailTrace_1175199 : CollatzResearch.WordTrace tailWord_1175199 prefixEnd_1175199 268196422970334560981273 := by
  unfold tailWord_1175199
  simp only [CollatzResearch.WordTrace]
  refine ⟨42863028869462205855128651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28575352579641470570085767 42863028869462205855128651)
  ·
    refine ⟨64294543304193308782692977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42863028869462205855128651 64294543304193308782692977)
    ·
      refine ⟨48220907478144981587019733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64294543304193308782692977 48220907478144981587019733)
      ·
        refine ⟨1130177519019023005945775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 48220907478144981587019733 1130177519019023005945775)
        ·
          refine ⟨1695266278528534508918663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130177519019023005945775 1695266278528534508918663)
          ·
            refine ⟨2542899417792801763377995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695266278528534508918663 2542899417792801763377995)
            ·
              refine ⟨3814349126689202645066993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542899417792801763377995 3814349126689202645066993)
              ·
                refine ⟨2860761845016901983800245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3814349126689202645066993 2860761845016901983800245)
                ·
                  refine ⟨268196422970334560981273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2860761845016901983800245 268196422970334560981273)
                  ·
                    rfl

theorem cell21_1175199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 5].length) (baseStart_1175199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175199 prefixEnd_1175199 := by exact prefixLift 1175199
  have htrace : WordTrace (prefixWord ++ tailWord_1175199) baseStart_1175199 baseEnd_1175199 := by
    simpa [prefixWord, tailWord_1175199, baseEnd_1175199] using wordTrace_append hprefix tailTrace_1175199
  have hstable : (prefixWord ++ tailWord_1175199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175199).length < 2 ^ (prefixWord ++ tailWord_1175199).sum := by decide
  have hdescent : baseEnd_1175199 < baseStart_1175199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175230 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_1175230 : Nat := 118140960795 + 1175230 * 2 ^ 59
def prefixEnd_1175230 : Nat := 4983230072969 + 3 ^ 40 * 1175230 * 2
def baseEnd_1175230 : Nat := 268203497592685395964543

theorem tailTrace_1175230 : CollatzResearch.WordTrace tailWord_1175230 prefixEnd_1175230 268203497592685395964543 := by
  unfold tailWord_1175230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5358019941543737268688393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28576106354899932099671429 5358019941543737268688393)
  ·
    refine ⟨4018514956157802951516295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5358019941543737268688393 4018514956157802951516295)
    ·
      refine ⟨6027772434236704427274443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4018514956157802951516295 6027772434236704427274443)
      ·
        refine ⟨9041658651355056640911665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6027772434236704427274443 9041658651355056640911665)
        ·
          refine ⟨6781243988516292480683749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9041658651355056640911665 6781243988516292480683749)
          ·
            refine ⟨1271483247846804840128203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6781243988516292480683749 1271483247846804840128203)
            ·
              refine ⟨1907224871770207260192305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271483247846804840128203 1907224871770207260192305)
              ·
                refine ⟨1430418653827655445144229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1907224871770207260192305 1430418653827655445144229)
                ·
                  refine ⟨268203497592685395964543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1430418653827655445144229 268203497592685395964543)
                  ·
                    rfl

theorem cell21_1175230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_1175230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175230 prefixEnd_1175230 := by exact prefixLift 1175230
  have htrace : WordTrace (prefixWord ++ tailWord_1175230) baseStart_1175230 baseEnd_1175230 := by
    simpa [prefixWord, tailWord_1175230, baseEnd_1175230] using wordTrace_append hprefix tailTrace_1175230
  have hstable : (prefixWord ++ tailWord_1175230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175230).length < 2 ^ (prefixWord ++ tailWord_1175230).sum := by decide
  have hdescent : baseEnd_1175230 < baseStart_1175230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175272 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_1175272 : Nat := 118140960795 + 1175272 * 2 ^ 59
def prefixEnd_1175272 : Nat := 4983230072969 + 3 ^ 40 * 1175272 * 2
def baseEnd_1175272 : Nat := 268213082564902656264457

theorem tailTrace_1175272 : CollatzResearch.WordTrace tailWord_1175272 prefixEnd_1175272 268213082564902656264457 := by
  unfold tailWord_1175272
  simp only [CollatzResearch.WordTrace]
  refine ⟨21432845699098869661268035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28577127598798492881690713 21432845699098869661268035)
  ·
    refine ⟨32149268548648304491902053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21432845699098869661268035 32149268548648304491902053)
    ·
      refine ⟨6027987852871557092231635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32149268548648304491902053 6027987852871557092231635)
      ·
        refine ⟨9041981779307335638347453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6027987852871557092231635 9041981779307335638347453)
        ·
          refine ⟨3390743167240250864380295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9041981779307335638347453 3390743167240250864380295)
          ·
            refine ⟨5086114750860376296570443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390743167240250864380295 5086114750860376296570443)
            ·
              refine ⟨7629172126290564444855665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086114750860376296570443 7629172126290564444855665)
              ·
                refine ⟨5721879094717923333641749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7629172126290564444855665 5721879094717923333641749)
                ·
                  refine ⟨268213082564902656264457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5721879094717923333641749 268213082564902656264457)
                  ·
                    rfl

theorem cell21_1175272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_1175272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175272 prefixEnd_1175272 := by exact prefixLift 1175272
  have htrace : WordTrace (prefixWord ++ tailWord_1175272) baseStart_1175272 baseEnd_1175272 := by
    simpa [prefixWord, tailWord_1175272, baseEnd_1175272] using wordTrace_append hprefix tailTrace_1175272
  have hstable : (prefixWord ++ tailWord_1175272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175272).length < 2 ^ (prefixWord ++ tailWord_1175272).sum := by decide
  have hdescent : baseEnd_1175272 < baseStart_1175272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175306 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_1175306 : Nat := 118140960795 + 1175306 * 2 ^ 59
def prefixEnd_1175306 : Nat := 4983230072969 + 3 ^ 40 * 1175306 * 2
def baseEnd_1175306 : Nat := 268220841828126152697721

theorem tailTrace_1175306 : CollatzResearch.WordTrace tailWord_1175306 prefixEnd_1175306 268220841828126152697721 := by
  unfold tailWord_1175306
  simp only [CollatzResearch.WordTrace]
  refine ⟨10716732870018640782318443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28577954320049708752849181 10716732870018640782318443)
  ·
    refine ⟨16075099305027961173477665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10716732870018640782318443 16075099305027961173477665)
    ·
      refine ⟨12056324478770970880108249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16075099305027961173477665 12056324478770970880108249)
      ·
        refine ⟨9042243359078228160081187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12056324478770970880108249 9042243359078228160081187)
        ·
          refine ⟨13563365038617342240121781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9042243359078228160081187 13563365038617342240121781)
          ·
            refine ⟨1271565472370375835011417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13563365038617342240121781 1271565472370375835011417)
            ·
              refine ⟨953674104277781876258563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271565472370375835011417 953674104277781876258563)
              ·
                refine ⟨1430511156416672814387845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953674104277781876258563 1430511156416672814387845)
                ·
                  refine ⟨268220841828126152697721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1430511156416672814387845 268220841828126152697721)
                  ·
                    rfl

theorem cell21_1175306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_1175306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175306 prefixEnd_1175306 := by exact prefixLift 1175306
  have htrace : WordTrace (prefixWord ++ tailWord_1175306) baseStart_1175306 baseEnd_1175306 := by
    simpa [prefixWord, tailWord_1175306, baseEnd_1175306] using wordTrace_append hprefix tailTrace_1175306
  have hstable : (prefixWord ++ tailWord_1175306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175306).length < 2 ^ (prefixWord ++ tailWord_1175306).sum := by decide
  have hdescent : baseEnd_1175306 < baseStart_1175306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175331 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 8]
def baseStart_1175331 : Nat := 118140960795 + 1175331 * 2 ^ 59
def prefixEnd_1175331 : Nat := 4983230072969 + 3 ^ 40 * 1175331 * 2
def baseEnd_1175331 : Nat := 268226547168731664781003

theorem tailTrace_1175331 : CollatzResearch.WordTrace tailWord_1175331 prefixEnd_1175331 268226547168731664781003 := by
  unfold tailWord_1175331
  simp only [CollatzResearch.WordTrace]
  refine ⟨42867843304983992398933847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28578562203322661599289231 42867843304983992398933847)
  ·
    refine ⟨64301764957475988598400771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42867843304983992398933847 64301764957475988598400771)
    ·
      refine ⟨96452647436213982897601157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64301764957475988598400771 96452647436213982897601157)
      ·
        refine ⟨18084871394290121793300217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96452647436213982897601157 18084871394290121793300217)
        ·
          refine ⟨13563653545717591344975163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18084871394290121793300217 13563653545717591344975163)
          ·
            refine ⟨20345480318576387017462745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13563653545717591344975163 20345480318576387017462745)
            ·
              refine ⟨15259110238932290263097059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20345480318576387017462745 15259110238932290263097059)
              ·
                refine ⟨22888665358398435394645589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15259110238932290263097059 22888665358398435394645589)
                ·
                  refine ⟨268226547168731664781003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22888665358398435394645589 268226547168731664781003)
                  ·
                    rfl

theorem cell21_1175331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_1175331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175331 prefixEnd_1175331 := by exact prefixLift 1175331
  have htrace : WordTrace (prefixWord ++ tailWord_1175331) baseStart_1175331 baseEnd_1175331 := by
    simpa [prefixWord, tailWord_1175331, baseEnd_1175331] using wordTrace_append hprefix tailTrace_1175331
  have hstable : (prefixWord ++ tailWord_1175331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175331).length < 2 ^ (prefixWord ++ tailWord_1175331).sum := by decide
  have hdescent : baseEnd_1175331 < baseStart_1175331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175444 : List Nat := [2, 4, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1175444 : Nat := 118140960795 + 1175444 * 2 ^ 59
def prefixEnd_1175444 : Nat := 4983230072969 + 3 ^ 40 * 1175444 * 2
def baseEnd_1175444 : Nat := 268252335308268579397439

theorem tailTrace_1175444 : CollatzResearch.WordTrace tailWord_1175444 prefixEnd_1175444 268252335308268579397439 := by
  unfold tailWord_1175444
  simp only [CollatzResearch.WordTrace]
  refine ⟨21435982376787306348898693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28581309835716408465198257 21435982376787306348898693)
  ·
    refine ⟨4019246695647619940418505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21435982376787306348898693 4019246695647619940418505)
    ·
      refine ⟨3014435021735714955313879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4019246695647619940418505 3014435021735714955313879)
      ·
        refine ⟨4521652532603572432970819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3014435021735714955313879 4521652532603572432970819)
        ·
          refine ⟨6782478798905358649456229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4521652532603572432970819 6782478798905358649456229)
          ·
            refine ⟨1271714774794754746773043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6782478798905358649456229 1271714774794754746773043)
            ·
              refine ⟨1907572162192132120159565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271714774794754746773043 1907572162192132120159565)
              ·
                refine ⟨715339560822049545059837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1907572162192132120159565 715339560822049545059837)
                ·
                  refine ⟨268252335308268579397439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 715339560822049545059837 268252335308268579397439)
                  ·
                    rfl

theorem cell21_1175444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1175444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175444 prefixEnd_1175444 := by exact prefixLift 1175444
  have htrace : WordTrace (prefixWord ++ tailWord_1175444) baseStart_1175444 baseEnd_1175444 := by
    simpa [prefixWord, tailWord_1175444, baseEnd_1175444] using wordTrace_append hprefix tailTrace_1175444
  have hstable : (prefixWord ++ tailWord_1175444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175444).length < 2 ^ (prefixWord ++ tailWord_1175444).sum := by decide
  have hdescent : baseEnd_1175444 < baseStart_1175444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175455 : List Nat := [1, 1, 2, 5, 3, 2, 7]
def baseStart_1175455 : Nat := 118140960795 + 1175455 * 2 ^ 59
def prefixEnd_1175455 : Nat := 4983230072969 + 3 ^ 40 * 1175455 * 2
def baseEnd_1175455 : Nat := 29806093962015000523787

theorem tailTrace_1175455 : CollatzResearch.WordTrace tailWord_1175455 prefixEnd_1175455 29806093962015000523787 := by
  unfold tailWord_1175455
  simp only [CollatzResearch.WordTrace]
  refine ⟨42872365956534761576447819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28581577304356507717631879 42872365956534761576447819)
  ·
    refine ⟨64308548934802142364671729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42872365956534761576447819 64308548934802142364671729)
    ·
      refine ⟨48231411701101606773503797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64308548934802142364671729 48231411701101606773503797)
      ·
        refine ⟨4521694846978275635015981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48231411701101606773503797 4521694846978275635015981)
        ·
          refine ⟨1695635567616853363130993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4521694846978275635015981 1695635567616853363130993)
          ·
            refine ⟨1271726675712640022348245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1695635567616853363130993 1271726675712640022348245)
            ·
              refine ⟨29806093962015000523787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1271726675712640022348245 29806093962015000523787)
              ·
                rfl

theorem cell21_1175455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 7].length) (baseStart_1175455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175455 prefixEnd_1175455 := by exact prefixLift 1175455
  have htrace : WordTrace (prefixWord ++ tailWord_1175455) baseStart_1175455 baseEnd_1175455 := by
    simpa [prefixWord, tailWord_1175455, baseEnd_1175455] using wordTrace_append hprefix tailTrace_1175455
  have hstable : (prefixWord ++ tailWord_1175455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175455).length < 2 ^ (prefixWord ++ tailWord_1175455).sum := by decide
  have hdescent : baseEnd_1175455 < baseStart_1175455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175514 : List Nat := [3, 1, 1, 2, 5, 9]
def baseStart_1175514 : Nat := 118140960795 + 1175514 * 2 ^ 59
def prefixEnd_1175514 : Nat := 4983230072969 + 3 ^ 40 * 1175514 * 2
def baseEnd_1175514 : Nat := 9935863343035704193727

theorem tailTrace_1175514 : CollatzResearch.WordTrace tailWord_1175514 prefixEnd_1175514 9935863343035704193727 := by
  unfold tailWord_1175514
  simp only [CollatzResearch.WordTrace]
  refine ⟨10718629465830253663211399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28583011908880676435230397 10718629465830253663211399)
  ·
    refine ⟨16077944198745380494817099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10718629465830253663211399 16077944198745380494817099)
    ·
      refine ⟨24116916298118070742225649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16077944198745380494817099 24116916298118070742225649)
      ·
        refine ⟨18087687223588553056669237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24116916298118070742225649 18087687223588553056669237)
        ·
          refine ⟨1695720677211426849062741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18087687223588553056669237 1695720677211426849062741)
          ·
            refine ⟨9935863343035704193727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1695720677211426849062741 9935863343035704193727)
            ·
              rfl

theorem cell21_1175514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 9].length) (baseStart_1175514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175514 prefixEnd_1175514 := by exact prefixLift 1175514
  have htrace : WordTrace (prefixWord ++ tailWord_1175514) baseStart_1175514 baseEnd_1175514 := by
    simpa [prefixWord, tailWord_1175514, baseEnd_1175514] using wordTrace_append hprefix tailTrace_1175514
  have hstable : (prefixWord ++ tailWord_1175514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175514).length < 2 ^ (prefixWord ++ tailWord_1175514).sum := by decide
  have hdescent : baseEnd_1175514 < baseStart_1175514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175545 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 5]
def baseStart_1175545 : Nat := 118140960795 + 1175545 * 2 ^ 59
def prefixEnd_1175545 : Nat := 4983230072969 + 3 ^ 40 * 1175545 * 2
def baseEnd_1175545 : Nat := 268275384884314848213899

theorem tailTrace_1175545 : CollatzResearch.WordTrace tailWord_1175545 prefixEnd_1175545 268275384884314848213899 := by
  unfold tailWord_1175545
  simp only [CollatzResearch.WordTrace]
  refine ⟨42875648526208706947224089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28583765684139137964816059 42875648526208706947224089)
  ·
    refine ⟨32156736394656530210418067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42875648526208706947224089 32156736394656530210418067)
    ·
      refine ⟨48235104591984795315627101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32156736394656530210418067 48235104591984795315627101)
      ·
        refine ⟨18088164221994298243360163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48235104591984795315627101 18088164221994298243360163)
        ·
          refine ⟨27132246332991447365040245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18088164221994298243360163 27132246332991447365040245)
          ·
            refine ⟨2543648093717948190472523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27132246332991447365040245 2543648093717948190472523)
            ·
              refine ⟨3815472140576922285708785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543648093717948190472523 3815472140576922285708785)
              ·
                refine ⟨2861604105432691714281589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3815472140576922285708785 2861604105432691714281589)
                ·
                  refine ⟨268275384884314848213899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2861604105432691714281589 268275384884314848213899)
                  ·
                    rfl

theorem cell21_1175545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_1175545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175545 prefixEnd_1175545 := by exact prefixLift 1175545
  have htrace : WordTrace (prefixWord ++ tailWord_1175545) baseStart_1175545 baseEnd_1175545 := by
    simpa [prefixWord, tailWord_1175545, baseEnd_1175545] using wordTrace_append hprefix tailTrace_1175545
  have hstable : (prefixWord ++ tailWord_1175545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175545).length < 2 ^ (prefixWord ++ tailWord_1175545).sum := by decide
  have hdescent : baseEnd_1175545 < baseStart_1175545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175565 : List Nat := [1, 7, 1, 2, 1, 1, 8]
def baseStart_1175565 : Nat := 118140960795 + 1175565 * 2 ^ 59
def prefixEnd_1175565 : Nat := 4983230072969 + 3 ^ 40 * 1175565 * 2
def baseEnd_1175565 : Nat := 29808883239644361986725

theorem tailTrace_1175565 : CollatzResearch.WordTrace tailWord_1175565 prefixEnd_1175565 29808883239644361986725 := by
  unfold tailWord_1175565
  simp only [CollatzResearch.WordTrace]
  refine ⟨42876377986136250362952149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28584251990757500241968099 42876377986136250362952149)
  ·
    refine ⟨1004915109050068367881691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 42876377986136250362952149 1004915109050068367881691)
    ·
      refine ⟨1507372663575102551822537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004915109050068367881691 1507372663575102551822537)
      ·
        refine ⟨1130529497681326913866903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1507372663575102551822537 1130529497681326913866903)
        ·
          refine ⟨1695794246521990370800355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130529497681326913866903 1695794246521990370800355)
          ·
            refine ⟨2543691369782985556200533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695794246521990370800355 2543691369782985556200533)
            ·
              refine ⟨29808883239644361986725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2543691369782985556200533 29808883239644361986725)
              ·
                rfl

theorem cell21_1175565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 8].length) (baseStart_1175565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175565 prefixEnd_1175565 := by exact prefixLift 1175565
  have htrace : WordTrace (prefixWord ++ tailWord_1175565) baseStart_1175565 baseEnd_1175565 := by
    simpa [prefixWord, tailWord_1175565, baseEnd_1175565] using wordTrace_append hprefix tailTrace_1175565
  have hstable : (prefixWord ++ tailWord_1175565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175565).length < 2 ^ (prefixWord ++ tailWord_1175565).sum := by decide
  have hdescent : baseEnd_1175565 < baseStart_1175565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175666 : List Nat := [3, 2, 1, 2, 2, 2, 2, 7]
def baseStart_1175666 : Nat := 118140960795 + 1175666 * 2 ^ 59
def prefixEnd_1175666 : Nat := 4983230072969 + 3 ^ 40 * 1175666 * 2
def baseEnd_1175666 : Nat := 89434332910948508898995

theorem tailTrace_1175666 : CollatzResearch.WordTrace tailWord_1175666 prefixEnd_1175666 89434332910948508898995 := by
  unfold tailWord_1175666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10720015439692586153094713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28586707839180229741585901 10720015439692586153094713)
  ·
    refine ⟨8040011579769439614821035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10720015439692586153094713 8040011579769439614821035)
    ·
      refine ⟨12060017369654159422231553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8040011579769439614821035 12060017369654159422231553)
      ·
        refine ⟨9045013027240619566673665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12060017369654159422231553 9045013027240619566673665)
        ·
          refine ⟨6783759770430464675005249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9045013027240619566673665 6783759770430464675005249)
          ·
            refine ⟨5087819827822848506253937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6783759770430464675005249 5087819827822848506253937)
            ·
              refine ⟨3815864870867136379690453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5087819827822848506253937 3815864870867136379690453)
              ·
                refine ⟨89434332910948508898995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3815864870867136379690453 89434332910948508898995)
                ·
                  rfl

theorem cell21_1175666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_1175666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175666 prefixEnd_1175666 := by exact prefixLift 1175666
  have htrace : WordTrace (prefixWord ++ tailWord_1175666) baseStart_1175666 baseEnd_1175666 := by
    simpa [prefixWord, tailWord_1175666, baseEnd_1175666] using wordTrace_append hprefix tailTrace_1175666
  have hstable : (prefixWord ++ tailWord_1175666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175666).length < 2 ^ (prefixWord ++ tailWord_1175666).sum := by decide
  have hdescent : baseEnd_1175666 < baseStart_1175666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175714 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1175714 : Nat := 118140960795 + 1175714 * 2 ^ 59
def prefixEnd_1175714 : Nat := 4983230072969 + 3 ^ 40 * 1175714 * 2
def baseEnd_1175714 : Nat := 268313952986808109896887

theorem tailTrace_1175714 : CollatzResearch.WordTrace tailWord_1175714 prefixEnd_1175714 268313952986808109896887 := by
  unfold tailWord_1175714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10720453115649112202531549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28587874975064299206750797 10720453115649112202531549)
  ·
    refine ⟨4020169918368417075949331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10720453115649112202531549 4020169918368417075949331)
    ·
      refine ⟨6030254877552625613923997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4020169918368417075949331 6030254877552625613923997)
      ·
        refine ⟨2261345579082234605221499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6030254877552625613923997 2261345579082234605221499)
        ·
          refine ⟨3392018368623351907832249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2261345579082234605221499 3392018368623351907832249)
          ·
            refine ⟨2544013776467513930874187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3392018368623351907832249 2544013776467513930874187)
            ·
              refine ⟨3816020664701270896311281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2544013776467513930874187 3816020664701270896311281)
              ·
                refine ⟨2862015498525953172233461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3816020664701270896311281 2862015498525953172233461)
                ·
                  refine ⟨268313952986808109896887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2862015498525953172233461 268313952986808109896887)
                  ·
                    rfl

theorem cell21_1175714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1175714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175714 prefixEnd_1175714 := by exact prefixLift 1175714
  have htrace : WordTrace (prefixWord ++ tailWord_1175714) baseStart_1175714 baseEnd_1175714 := by
    simpa [prefixWord, tailWord_1175714, baseEnd_1175714] using wordTrace_append hprefix tailTrace_1175714
  have hstable : (prefixWord ++ tailWord_1175714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175714).length < 2 ^ (prefixWord ++ tailWord_1175714).sum := by decide
  have hdescent : baseEnd_1175714 < baseStart_1175714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175745 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 6]
def baseStart_1175745 : Nat := 118140960795 + 1175745 * 2 ^ 59
def prefixEnd_1175745 : Nat := 4983230072969 + 3 ^ 40 * 1175745 * 2
def baseEnd_1175745 : Nat := 268321027609158944880157

theorem tailTrace_1175745 : CollatzResearch.WordTrace tailWord_1175745 prefixEnd_1175745 268321027609158944880157 := by
  unfold tailWord_1175745
  simp only [CollatzResearch.WordTrace]
  refine ⟨42882943125484141104504689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28588628750322760736336459 42882943125484141104504689)
  ·
    refine ⟨32162207344113105828378517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42882943125484141104504689 32162207344113105828378517)
    ·
      refine ⟨1507603469255301835705243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32162207344113105828378517 1507603469255301835705243)
      ·
        refine ⟨2261405203882952753557865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507603469255301835705243 2261405203882952753557865)
        ·
          refine ⟨1696053902912214565168399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2261405203882952753557865 1696053902912214565168399)
          ·
            refine ⟨2544080854368321847752599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696053902912214565168399 2544080854368321847752599)
            ·
              refine ⟨3816121281552482771628899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2544080854368321847752599 3816121281552482771628899)
              ·
                refine ⟨5724181922328724157443349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3816121281552482771628899 5724181922328724157443349)
                ·
                  refine ⟨268321027609158944880157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5724181922328724157443349 268321027609158944880157)
                  ·
                    rfl

theorem cell21_1175745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_1175745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175745 prefixEnd_1175745 := by exact prefixLift 1175745
  have htrace : WordTrace (prefixWord ++ tailWord_1175745) baseStart_1175745 baseEnd_1175745 := by
    simpa [prefixWord, tailWord_1175745, baseEnd_1175745] using wordTrace_append hprefix tailTrace_1175745
  have hstable : (prefixWord ++ tailWord_1175745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175745).length < 2 ^ (prefixWord ++ tailWord_1175745).sum := by decide
  have hdescent : baseEnd_1175745 < baseStart_1175745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175832 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_1175832 : Nat := 118140960795 + 1175832 * 2 ^ 59
def prefixEnd_1175832 : Nat := 4983230072969 + 3 ^ 40 * 1175832 * 2
def baseEnd_1175832 : Nat := 268340882194466126929979

theorem tailTrace_1175832 : CollatzResearch.WordTrace tailWord_1175832 prefixEnd_1175832 268340882194466126929979 := by
  unfold tailWord_1175832
  simp only [CollatzResearch.WordTrace]
  refine ⟨21443058138084477481460875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28590744184112636641947833 21443058138084477481460875)
  ·
    refine ⟨32164587207126716222191313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21443058138084477481460875 32164587207126716222191313)
    ·
      refine ⟨24123440405345037166643485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32164587207126716222191313 24123440405345037166643485)
      ·
        refine ⟨9046290152004388937491307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24123440405345037166643485 9046290152004388937491307)
        ·
          refine ⟨13569435228006583406236961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9046290152004388937491307 13569435228006583406236961)
          ·
            refine ⟨10177076421004937554677721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13569435228006583406236961 10177076421004937554677721)
            ·
              refine ⟨7632807315753703166008291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10177076421004937554677721 7632807315753703166008291)
              ·
                refine ⟨11449210973630554749012437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7632807315753703166008291 11449210973630554749012437)
                ·
                  refine ⟨268340882194466126929979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11449210973630554749012437 268340882194466126929979)
                  ·
                    rfl

theorem cell21_1175832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_1175832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175832 prefixEnd_1175832 := by exact prefixLift 1175832
  have htrace : WordTrace (prefixWord ++ tailWord_1175832) baseStart_1175832 baseEnd_1175832 := by
    simpa [prefixWord, tailWord_1175832, baseEnd_1175832] using wordTrace_append hprefix tailTrace_1175832
  have hstable : (prefixWord ++ tailWord_1175832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175832).length < 2 ^ (prefixWord ++ tailWord_1175832).sum := by decide
  have hdescent : baseEnd_1175832 < baseStart_1175832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175866 : List Nat := [3, 1, 1, 1, 4, 3, 1, 4, 3]
def baseStart_1175866 : Nat := 118140960795 + 1175866 * 2 ^ 59
def prefixEnd_1175866 : Nat := 4983230072969 + 3 ^ 40 * 1175866 * 2
def baseEnd_1175866 : Nat := 268348641457689623363243

theorem tailTrace_1175866 : CollatzResearch.WordTrace tailWord_1175866 prefixEnd_1175866 268348641457689623363243 := by
  unfold tailWord_1175866
  simp only [CollatzResearch.WordTrace]
  refine ⟨10721839089511444692414863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28591570905363852513106301 10721839089511444692414863)
  ·
    refine ⟨16082758634267167038622295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10721839089511444692414863 16082758634267167038622295)
    ·
      refine ⟨24124137951400750557933443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16082758634267167038622295 24124137951400750557933443)
      ·
        refine ⟨36186206927101125836900165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24124137951400750557933443 36186206927101125836900165)
        ·
          refine ⟨6784913798831461094418781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36186206927101125836900165 6784913798831461094418781)
          ·
            refine ⟨2544342674561797910407043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6784913798831461094418781 2544342674561797910407043)
            ·
              refine ⟨3816514011842696865610565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2544342674561797910407043 3816514011842696865610565)
              ·
                refine ⟨715596377220505662301981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3816514011842696865610565 715596377220505662301981)
                ·
                  refine ⟨268348641457689623363243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 715596377220505662301981 268348641457689623363243)
                  ·
                    rfl

theorem cell21_1175866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_1175866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175866 prefixEnd_1175866 := by exact prefixLift 1175866
  have htrace : WordTrace (prefixWord ++ tailWord_1175866) baseStart_1175866 baseEnd_1175866 := by
    simpa [prefixWord, tailWord_1175866, baseEnd_1175866] using wordTrace_append hprefix tailTrace_1175866
  have hstable : (prefixWord ++ tailWord_1175866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175866).length < 2 ^ (prefixWord ++ tailWord_1175866).sum := by decide
  have hdescent : baseEnd_1175866 < baseStart_1175866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175900 : List Nat := [2, 2, 4, 3, 1, 1, 2, 3, 3]
def baseStart_1175900 : Nat := 118140960795 + 1175900 * 2 ^ 59
def prefixEnd_1175900 : Nat := 4983230072969 + 3 ^ 40 * 1175900 * 2
def baseEnd_1175900 : Nat := 268356400720913119796507

theorem tailTrace_1175900 : CollatzResearch.WordTrace tailWord_1175900 prefixEnd_1175900 268356400720913119796507 := by
  unfold tailWord_1175900
  simp only [CollatzResearch.WordTrace]
  refine ⟨21444298219961301288198577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28592397626615068384264769 21444298219961301288198577)
  ·
    refine ⟨16083223664970975966148933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21444298219961301288198577 16083223664970975966148933)
    ·
      refine ⟨3015604437182057993652925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16083223664970975966148933 3015604437182057993652925)
      ·
        refine ⟨1130851663943271747619847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3015604437182057993652925 1130851663943271747619847)
        ·
          refine ⟨1696277495914907621429771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130851663943271747619847 1696277495914907621429771)
          ·
            refine ⟨2544416243872361432144657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696277495914907621429771 2544416243872361432144657)
            ·
              refine ⟨1908312182904271074108493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2544416243872361432144657 1908312182904271074108493)
              ·
                refine ⟨715617068589101652790685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1908312182904271074108493 715617068589101652790685)
                ·
                  refine ⟨268356400720913119796507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 715617068589101652790685 268356400720913119796507)
                  ·
                    rfl

theorem cell21_1175900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_1175900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175900 prefixEnd_1175900 := by exact prefixLift 1175900
  have htrace : WordTrace (prefixWord ++ tailWord_1175900) baseStart_1175900 baseEnd_1175900 := by
    simpa [prefixWord, tailWord_1175900, baseEnd_1175900] using wordTrace_append hprefix tailTrace_1175900
  have hstable : (prefixWord ++ tailWord_1175900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175900).length < 2 ^ (prefixWord ++ tailWord_1175900).sum := by decide
  have hdescent : baseEnd_1175900 < baseStart_1175900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175908 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_1175908 : Nat := 118140960795 + 1175908 * 2 ^ 59
def prefixEnd_1175908 : Nat := 4983230072969 + 3 ^ 40 * 1175908 * 2
def baseEnd_1175908 : Nat := 268358226429906883663157

theorem tailTrace_1175908 : CollatzResearch.WordTrace tailWord_1175908 prefixEnd_1175908 268358226429906883663157 := by
  unfold tailWord_1175908
  simp only [CollatzResearch.WordTrace]
  refine ⟨21444444111946809971344189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28592592149262413295125585 21444444111946809971344189)
  ·
    refine ⟨8041666541980053739254071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21444444111946809971344189 8041666541980053739254071)
    ·
      refine ⟨12062499812970080608881107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8041666541980053739254071 12062499812970080608881107)
      ·
        refine ⟨18093749719455120913321661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12062499812970080608881107 18093749719455120913321661)
        ·
          refine ⟨6785156144795670342495623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18093749719455120913321661 6785156144795670342495623)
          ·
            refine ⟨10177734217193505513743435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6785156144795670342495623 10177734217193505513743435)
            ·
              refine ⟨15266601325790258270615153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10177734217193505513743435 15266601325790258270615153)
              ·
                refine ⟨11449950994342693702961365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15266601325790258270615153 11449950994342693702961365)
                ·
                  refine ⟨268358226429906883663157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11449950994342693702961365 268358226429906883663157)
                  ·
                    rfl

theorem cell21_1175908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_1175908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175908 prefixEnd_1175908 := by exact prefixLift 1175908
  have htrace : WordTrace (prefixWord ++ tailWord_1175908) baseStart_1175908 baseEnd_1175908 := by
    simpa [prefixWord, tailWord_1175908, baseEnd_1175908] using wordTrace_append hprefix tailTrace_1175908
  have hstable : (prefixWord ++ tailWord_1175908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175908).length < 2 ^ (prefixWord ++ tailWord_1175908).sum := by decide
  have hdescent : baseEnd_1175908 < baseStart_1175908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175925 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 5]
def baseStart_1175925 : Nat := 118140960795 + 1175925 * 2 ^ 59
def prefixEnd_1175925 : Nat := 4983230072969 + 3 ^ 40 * 1175925 * 2
def baseEnd_1175925 : Nat := 268362106061518631879789

theorem tailTrace_1175925 : CollatzResearch.WordTrace tailWord_1175925 prefixEnd_1175925 268362106061518631879789 := by
  unfold tailWord_1175925
  simp only [CollatzResearch.WordTrace]
  refine ⟨42889508264832031846057229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28593005509888021230704819 42889508264832031846057229)
  ·
    refine ⟨16083565599312011942271461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42889508264832031846057229 16083565599312011942271461)
    ·
      refine ⟨3015668549871002239175899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16083565599312011942271461 3015668549871002239175899)
      ·
        refine ⟨4523502824806503358763849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015668549871002239175899 4523502824806503358763849)
        ·
          refine ⟨3392627118604877519072887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4523502824806503358763849 3392627118604877519072887)
          ·
            refine ⟨5088940677907316278609331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3392627118604877519072887 5088940677907316278609331)
            ·
              refine ⟨7633411016860974417913997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5088940677907316278609331 7633411016860974417913997)
              ·
                refine ⟨2862529131322865406717749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7633411016860974417913997 2862529131322865406717749)
                ·
                  refine ⟨268362106061518631879789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2862529131322865406717749 268362106061518631879789)
                  ·
                    rfl

theorem cell21_1175925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_1175925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175925 prefixEnd_1175925 := by exact prefixLift 1175925
  have htrace : WordTrace (prefixWord ++ tailWord_1175925) baseStart_1175925 baseEnd_1175925 := by
    simpa [prefixWord, tailWord_1175925, baseEnd_1175925] using wordTrace_append hprefix tailTrace_1175925
  have hstable : (prefixWord ++ tailWord_1175925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175925).length < 2 ^ (prefixWord ++ tailWord_1175925).sum := by decide
  have hdescent : baseEnd_1175925 < baseStart_1175925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175976 : List Nat := [2, 1, 6, 1, 1, 2, 3, 2, 3]
def baseStart_1175976 : Nat := 118140960795 + 1175976 * 2 ^ 59
def prefixEnd_1175976 : Nat := 4983230072969 + 3 ^ 40 * 1175976 * 2
def baseEnd_1175976 : Nat := 268373744956353876529685

theorem tailTrace_1175976 : CollatzResearch.WordTrace tailWord_1175976 prefixEnd_1175976 268373744956353876529685 := by
  unfold tailWord_1175976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21445684193823633778081891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28594245591764845037442521 21445684193823633778081891)
  ·
    refine ⟨32168526290735450667122837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21445684193823633778081891 32168526290735450667122837)
    ·
      refine ⟨1507899669878224250021383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32168526290735450667122837 1507899669878224250021383)
      ·
        refine ⟨2261849504817336375032075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507899669878224250021383 2261849504817336375032075)
        ·
          refine ⟨3392774257226004562548113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2261849504817336375032075 3392774257226004562548113)
          ·
            refine ⟨2544580692919503421911085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3392774257226004562548113 2544580692919503421911085)
            ·
              refine ⟨954217759844813783216657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2544580692919503421911085 954217759844813783216657)
              ·
                refine ⟨715663319883610337412493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954217759844813783216657 715663319883610337412493)
                ·
                  refine ⟨268373744956353876529685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 715663319883610337412493 268373744956353876529685)
                  ·
                    rfl

theorem cell21_1175976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 3].length) (baseStart_1175976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1175976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1175976 prefixEnd_1175976 := by exact prefixLift 1175976
  have htrace : WordTrace (prefixWord ++ tailWord_1175976) baseStart_1175976 baseEnd_1175976 := by
    simpa [prefixWord, tailWord_1175976, baseEnd_1175976] using wordTrace_append hprefix tailTrace_1175976
  have hstable : (prefixWord ++ tailWord_1175976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175976).length < 2 ^ (prefixWord ++ tailWord_1175976).sum := by decide
  have hdescent : baseEnd_1175976 < baseStart_1175976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176046 : List Nat := [4, 1, 2, 1, 2, 2, 3, 6]
def baseStart_1176046 : Nat := 118140960795 + 1176046 * 2 ^ 59
def prefixEnd_1176046 : Nat := 4983230072969 + 3 ^ 40 * 1176046 * 2
def baseEnd_1176046 : Nat := 89463239970016436787625

theorem tailTrace_1176046 : CollatzResearch.WordTrace tailWord_1176046 prefixEnd_1176046 89463239970016436787625 := by
  unfold tailWord_1176046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5361740187174208688901499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28595947664929113007474661 5361740187174208688901499)
  ·
    refine ⟨8042610280761313033352249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5361740187174208688901499 8042610280761313033352249)
    ·
      refine ⟨6031957710570984775014187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8042610280761313033352249 6031957710570984775014187)
      ·
        refine ⟨9047936565856477162521281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6031957710570984775014187 9047936565856477162521281)
        ·
          refine ⟨6785952424392357871890961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9047936565856477162521281 6785952424392357871890961)
          ·
            refine ⟨5089464318294268403918221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6785952424392357871890961 5089464318294268403918221)
            ·
              refine ⟨1908549119360350651469333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5089464318294268403918221 1908549119360350651469333)
              ·
                refine ⟨89463239970016436787625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1908549119360350651469333 89463239970016436787625)
                ·
                  rfl

theorem cell21_1176046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_1176046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176046 prefixEnd_1176046 := by exact prefixLift 1176046
  have htrace : WordTrace (prefixWord ++ tailWord_1176046) baseStart_1176046 baseEnd_1176046 := by
    simpa [prefixWord, tailWord_1176046, baseEnd_1176046] using wordTrace_append hprefix tailTrace_1176046
  have hstable : (prefixWord ++ tailWord_1176046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176046).length < 2 ^ (prefixWord ++ tailWord_1176046).sum := by decide
  have hdescent : baseEnd_1176046 < baseStart_1176046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176122 : List Nat := [3, 1, 1, 1, 3, 3, 4, 5]
def baseStart_1176122 : Nat := 118140960795 + 1176122 * 2 ^ 59
def prefixEnd_1176122 : Nat := 4983230072969 + 3 ^ 40 * 1176122 * 2
def baseEnd_1176122 : Nat := 89469021381830022365351

theorem tailTrace_1176122 : CollatzResearch.WordTrace tailWord_1176122 prefixEnd_1176122 89469021381830022365351 := by
  unfold tailWord_1176122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10724173361279583622744655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28597795630078889660652413 10724173361279583622744655)
  ·
    refine ⟨16086260041919375434116983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10724173361279583622744655 16086260041919375434116983)
    ·
      refine ⟨24129390062879063151175475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16086260041919375434116983 24129390062879063151175475)
      ·
        refine ⟨36194085094318594726763213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24129390062879063151175475 36194085094318594726763213)
        ·
          refine ⟨13572781910369473022536205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36194085094318594726763213 13572781910369473022536205)
          ·
            refine ⟨5089793216388552383451077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13572781910369473022536205 5089793216388552383451077)
            ·
              refine ⟨954336228072853571897077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5089793216388552383451077 954336228072853571897077)
              ·
                refine ⟨89469021381830022365351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 954336228072853571897077 89469021381830022365351)
                ·
                  rfl

theorem cell21_1176122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_1176122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176122 prefixEnd_1176122 := by exact prefixLift 1176122
  have htrace : WordTrace (prefixWord ++ tailWord_1176122) baseStart_1176122 baseEnd_1176122 := by
    simpa [prefixWord, tailWord_1176122, baseEnd_1176122] using wordTrace_append hprefix tailTrace_1176122
  have hstable : (prefixWord ++ tailWord_1176122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176122).length < 2 ^ (prefixWord ++ tailWord_1176122).sum := by decide
  have hdescent : baseEnd_1176122 < baseStart_1176122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176260 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 4]
def baseStart_1176260 : Nat := 118140960795 + 1176260 * 2 ^ 59
def prefixEnd_1176260 : Nat := 4983230072969 + 3 ^ 40 * 1176260 * 2
def baseEnd_1176260 : Nat := 268438557625632493795771

theorem tailTrace_1176260 : CollatzResearch.WordTrace tailWord_1176260 prefixEnd_1176260 268438557625632493795771 := by
  unfold tailWord_1176260
  simp only [CollatzResearch.WordTrace]
  refine ⟨21450863359309192029751117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28601151145745589373001489 21450863359309192029751117)
  ·
    refine ⟨8044073759740947011156669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21450863359309192029751117 8044073759740947011156669)
    ·
      refine ⟨3016527659902855129183751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8044073759740947011156669 3016527659902855129183751)
      ·
        refine ⟨4524791489854282693775627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3016527659902855129183751 4524791489854282693775627)
        ·
          refine ⟨6787187234781424040663441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524791489854282693775627 6787187234781424040663441)
          ·
            refine ⟨5090390426086068030497581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6787187234781424040663441 5090390426086068030497581)
            ·
              refine ⟨1908896409782275511436593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5090390426086068030497581 1908896409782275511436593)
              ·
                refine ⟨1431672307336706633577445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1908896409782275511436593 1431672307336706633577445)
                ·
                  refine ⟨268438557625632493795771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1431672307336706633577445 268438557625632493795771)
                  ·
                    rfl

theorem cell21_1176260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_1176260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176260 prefixEnd_1176260 := by exact prefixLift 1176260
  have htrace : WordTrace (prefixWord ++ tailWord_1176260) baseStart_1176260 baseEnd_1176260 := by
    simpa [prefixWord, tailWord_1176260, baseEnd_1176260] using wordTrace_append hprefix tailTrace_1176260
  have hstable : (prefixWord ++ tailWord_1176260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176260).length < 2 ^ (prefixWord ++ tailWord_1176260).sum := by decide
  have hdescent : baseEnd_1176260 < baseStart_1176260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176291 : List Nat := [1, 1, 1, 7, 1, 3, 2, 5]
def baseStart_1176291 : Nat := 118140960795 + 1176291 * 2 ^ 59
def prefixEnd_1176291 : Nat := 4983230072969 + 3 ^ 40 * 1176291 * 2
def baseEnd_1176291 : Nat := 89481877415994442926347

theorem tailTrace_1176291 : CollatzResearch.WordTrace tailWord_1176291 prefixEnd_1176291 89481877415994442926347 := by
  unfold tailWord_1176291
  simp only [CollatzResearch.WordTrace]
  refine ⟨42902857381506076353880727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28601904921004050902587151 42902857381506076353880727)
  ·
    refine ⟨64354286072259114530821091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42902857381506076353880727 64354286072259114530821091)
    ·
      refine ⟨96531429108388671796231637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64354286072259114530821091 96531429108388671796231637)
      ·
        refine ⟨2262455369727859495224179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 96531429108388671796231637 2262455369727859495224179)
        ·
          refine ⟨3393683054591789242836269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2262455369727859495224179 3393683054591789242836269)
          ·
            refine ⟨1272631145471920966063601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3393683054591789242836269 1272631145471920966063601)
            ·
              refine ⟨954473359103940724547701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1272631145471920966063601 954473359103940724547701)
              ·
                refine ⟨89481877415994442926347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 954473359103940724547701 89481877415994442926347)
                ·
                  rfl

theorem cell21_1176291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 5].length) (baseStart_1176291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176291 prefixEnd_1176291 := by exact prefixLift 1176291
  have htrace : WordTrace (prefixWord ++ tailWord_1176291) baseStart_1176291 baseEnd_1176291 := by
    simpa [prefixWord, tailWord_1176291, baseEnd_1176291] using wordTrace_append hprefix tailTrace_1176291
  have hstable : (prefixWord ++ tailWord_1176291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176291).length < 2 ^ (prefixWord ++ tailWord_1176291).sum := by decide
  have hdescent : baseEnd_1176291 < baseStart_1176291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176308 : List Nat := [2, 6, 1, 1, 2, 2, 7]
def baseStart_1176308 : Nat := 118140960795 + 1176308 * 2 ^ 59
def prefixEnd_1176308 : Nat := 4983230072969 + 3 ^ 40 * 1176308 * 2
def baseEnd_1176308 : Nat := 29827723542177230777297

theorem tailTrace_1176308 : CollatzResearch.WordTrace tailWord_1176308 prefixEnd_1176308 29827723542177230777297 := by
  unfold tailWord_1176308
  simp only [CollatzResearch.WordTrace]
  refine ⟨21451738711222244128624789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28602318281629658838166385 21451738711222244128624789)
  ·
    refine ⟨1005550252088542693529287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21451738711222244128624789 1005550252088542693529287)
    ·
      refine ⟨1508325378132814040293931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005550252088542693529287 1508325378132814040293931)
      ·
        refine ⟨2262488067199221060440897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1508325378132814040293931 2262488067199221060440897)
        ·
          refine ⟨1696866050399415795330673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2262488067199221060440897 1696866050399415795330673)
          ·
            refine ⟨1272649537799561846498005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1696866050399415795330673 1272649537799561846498005)
            ·
              refine ⟨29827723542177230777297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1272649537799561846498005 29827723542177230777297)
              ·
                rfl

theorem cell21_1176308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 7].length) (baseStart_1176308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176308 prefixEnd_1176308 := by exact prefixLift 1176308
  have htrace : WordTrace (prefixWord ++ tailWord_1176308) baseStart_1176308 baseEnd_1176308 := by
    simpa [prefixWord, tailWord_1176308, baseEnd_1176308] using wordTrace_append hprefix tailTrace_1176308
  have hstable : (prefixWord ++ tailWord_1176308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176308).length < 2 ^ (prefixWord ++ tailWord_1176308).sum := by decide
  have hdescent : baseEnd_1176308 < baseStart_1176308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176322 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1176322 : Nat := 118140960795 + 1176322 * 2 ^ 59
def prefixEnd_1176322 : Nat := 4983230072969 + 3 ^ 40 * 1176322 * 2
def baseEnd_1176322 : Nat := 268452706870334163762311

theorem tailTrace_1176322 : CollatzResearch.WordTrace tailWord_1176322 prefixEnd_1176322 268452706870334163762311 := by
  unfold tailWord_1176322
  simp only [CollatzResearch.WordTrace]
  refine ⟨10725997011098442162064805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28602658696262512432172813 10725997011098442162064805)
  ·
    refine ⟨2011124439580957905387151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10725997011098442162064805 2011124439580957905387151)
    ·
      refine ⟨3016686659371436858080727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2011124439580957905387151 3016686659371436858080727)
      ·
        refine ⟨4525029989057155287121091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3016686659371436858080727 4525029989057155287121091)
        ·
          refine ⟨6787544983585732930681637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4525029989057155287121091 6787544983585732930681637)
          ·
            refine ⟨1272664684422324924502807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6787544983585732930681637 1272664684422324924502807)
            ·
              refine ⟨1908997026633487386754211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272664684422324924502807 1908997026633487386754211)
              ·
                refine ⟨2863495539950231080131317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1908997026633487386754211 2863495539950231080131317)
                ·
                  refine ⟨268452706870334163762311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2863495539950231080131317 268452706870334163762311)
                  ·
                    rfl

theorem cell21_1176322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1176322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176322 prefixEnd_1176322 := by exact prefixLift 1176322
  have htrace : WordTrace (prefixWord ++ tailWord_1176322) baseStart_1176322 baseEnd_1176322 := by
    simpa [prefixWord, tailWord_1176322, baseEnd_1176322] using wordTrace_append hprefix tailTrace_1176322
  have hstable : (prefixWord ++ tailWord_1176322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176322).length < 2 ^ (prefixWord ++ tailWord_1176322).sum := by decide
  have hdescent : baseEnd_1176322 < baseStart_1176322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176446 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_1176446 : Nat := 118140960795 + 1176446 * 2 ^ 59
def prefixEnd_1176446 : Nat := 4983230072969 + 3 ^ 40 * 1176446 * 2
def baseEnd_1176446 : Nat := 268481005359737503695391

theorem tailTrace_1176446 : CollatzResearch.WordTrace tailWord_1176446 prefixEnd_1176446 268481005359737503695391 := by
  unfold tailWord_1176446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5363563836993067228221649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28605673797296358550515461 5363563836993067228221649)
  ·
    refine ⟨4022672877744800421166237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5363563836993067228221649 4022672877744800421166237)
    ·
      refine ⟨1508502329154300157937339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4022672877744800421166237 1508502329154300157937339)
      ·
        refine ⟨2262753493731450236906009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1508502329154300157937339 2262753493731450236906009)
        ·
          refine ⟨1697065120298587677679507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2262753493731450236906009 1697065120298587677679507)
          ·
            refine ⟨2545597680447881516519261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697065120298587677679507 2545597680447881516519261)
            ·
              refine ⟨954599130167955568694723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2545597680447881516519261 954599130167955568694723)
              ·
                refine ⟨1431898695251933353042085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954599130167955568694723 1431898695251933353042085)
                ·
                  refine ⟨268481005359737503695391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1431898695251933353042085 268481005359737503695391)
                  ·
                    rfl

theorem cell21_1176446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_1176446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176446 prefixEnd_1176446 := by exact prefixLift 1176446
  have htrace : WordTrace (prefixWord ++ tailWord_1176446) baseStart_1176446 baseEnd_1176446 := by
    simpa [prefixWord, tailWord_1176446, baseEnd_1176446] using wordTrace_append hprefix tailTrace_1176446
  have hstable : (prefixWord ++ tailWord_1176446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176446).length < 2 ^ (prefixWord ++ tailWord_1176446).sum := by decide
  have hdescent : baseEnd_1176446 < baseStart_1176446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176499 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 5]
def baseStart_1176499 : Nat := 118140960795 + 1176499 * 2 ^ 59
def prefixEnd_1176499 : Nat := 4983230072969 + 3 ^ 40 * 1176499 * 2
def baseEnd_1176499 : Nat := 268493100681821189311949

theorem tailTrace_1176499 : CollatzResearch.WordTrace tailWord_1176499 prefixEnd_1176499 268493100681821189311949 := by
  unfold tailWord_1176499
  simp only [CollatzResearch.WordTrace]
  refine ⟨42910443764752527877452551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28606962509835018584968367 42910443764752527877452551)
  ·
    refine ⟨64365665647128791816178827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42910443764752527877452551 64365665647128791816178827)
    ·
      refine ⟨96548498470693187724268241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64365665647128791816178827 96548498470693187724268241)
      ·
        refine ⟨72411373853019890793201181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96548498470693187724268241 72411373853019890793201181)
        ·
          refine ⟨27154265194882459047450443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72411373853019890793201181 27154265194882459047450443)
          ·
            refine ⟨40731397792323688571175665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27154265194882459047450443 40731397792323688571175665)
            ·
              refine ⟨30548548344242766428381749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40731397792323688571175665 30548548344242766428381749)
              ·
                refine ⟨2863926407272759352660789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30548548344242766428381749 2863926407272759352660789)
                ·
                  refine ⟨268493100681821189311949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2863926407272759352660789 268493100681821189311949)
                  ·
                    rfl

theorem cell21_1176499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_1176499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176499 prefixEnd_1176499 := by exact prefixLift 1176499
  have htrace : WordTrace (prefixWord ++ tailWord_1176499) baseStart_1176499 baseEnd_1176499 := by
    simpa [prefixWord, tailWord_1176499, baseEnd_1176499] using wordTrace_append hprefix tailTrace_1176499
  have hstable : (prefixWord ++ tailWord_1176499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176499).length < 2 ^ (prefixWord ++ tailWord_1176499).sum := by decide
  have hdescent : baseEnd_1176499 < baseStart_1176499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176547 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 4]
def baseStart_1176547 : Nat := 118140960795 + 1176547 * 2 ^ 59
def prefixEnd_1176547 : Nat := 4983230072969 + 3 ^ 40 * 1176547 * 2
def baseEnd_1176547 : Nat := 268504054935783772511851

theorem tailTrace_1176547 : CollatzResearch.WordTrace tailWord_1176547 prefixEnd_1176547 268504054935783772511851 := by
  unfold tailWord_1176547
  simp only [CollatzResearch.WordTrace]
  refine ⟨42912194468578632075199895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28608129645719088050133263 42912194468578632075199895)
  ·
    refine ⟨64368291702867948112799843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42912194468578632075199895 64368291702867948112799843)
    ·
      refine ⟨96552437554301922169199765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64368291702867948112799843 96552437554301922169199765)
      ·
        refine ⟨4525895510357902601681239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96552437554301922169199765 4525895510357902601681239)
        ·
          refine ⟨6788843265536853902521859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4525895510357902601681239 6788843265536853902521859)
          ·
            refine ⟨10183264898305280853782789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6788843265536853902521859 10183264898305280853782789)
            ·
              refine ⟨1909362168432240160084273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10183264898305280853782789 1909362168432240160084273)
              ·
                refine ⟨1432021626324180120063205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909362168432240160084273 1432021626324180120063205)
                ·
                  refine ⟨268504054935783772511851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1432021626324180120063205 268504054935783772511851)
                  ·
                    rfl

theorem cell21_1176547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 4].length) (baseStart_1176547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176547 prefixEnd_1176547 := by exact prefixLift 1176547
  have htrace : WordTrace (prefixWord ++ tailWord_1176547) baseStart_1176547 baseEnd_1176547 := by
    simpa [prefixWord, tailWord_1176547, baseEnd_1176547] using wordTrace_append hprefix tailTrace_1176547
  have hstable : (prefixWord ++ tailWord_1176547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176547).length < 2 ^ (prefixWord ++ tailWord_1176547).sum := by decide
  have hdescent : baseEnd_1176547 < baseStart_1176547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176561 : List Nat := [1, 2, 2, 2, 4, 1, 3, 6]
def baseStart_1176561 : Nat := 118140960795 + 1176561 * 2 ^ 59
def prefixEnd_1176561 : Nat := 4983230072969 + 3 ^ 40 * 1176561 * 2
def baseEnd_1176561 : Nat := 89502416642174286426163

theorem tailTrace_1176561 : CollatzResearch.WordTrace tailWord_1176561 prefixEnd_1176561 89502416642174286426163 := by
  unfold tailWord_1176561
  simp only [CollatzResearch.WordTrace]
  refine ⟨42912705090527912466209537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28608470060351941644139691 42912705090527912466209537)
  ·
    refine ⟨32184528817895934349657153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42912705090527912466209537 32184528817895934349657153)
    ·
      refine ⟨24138396613421950762242865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32184528817895934349657153 24138396613421950762242865)
      ·
        refine ⟨18103797460066463071682149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24138396613421950762242865 18103797460066463071682149)
        ·
          refine ⟨3394462023762461825940403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18103797460066463071682149 3394462023762461825940403)
          ·
            refine ⟨5091693035643692738910605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394462023762461825940403 5091693035643692738910605)
            ·
              refine ⟨1909384888366384777091477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5091693035643692738910605 1909384888366384777091477)
              ·
                refine ⟨89502416642174286426163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1909384888366384777091477 89502416642174286426163)
                ·
                  rfl

theorem cell21_1176561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 6].length) (baseStart_1176561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176561 prefixEnd_1176561 := by exact prefixLift 1176561
  have htrace : WordTrace (prefixWord ++ tailWord_1176561) baseStart_1176561 baseEnd_1176561 := by
    simpa [prefixWord, tailWord_1176561, baseEnd_1176561] using wordTrace_append hprefix tailTrace_1176561
  have hstable : (prefixWord ++ tailWord_1176561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176561).length < 2 ^ (prefixWord ++ tailWord_1176561).sum := by decide
  have hdescent : baseEnd_1176561 < baseStart_1176561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176609 : List Nat := [1, 2, 3, 2, 3, 1, 2, 4, 3]
def baseStart_1176609 : Nat := 118140960795 + 1176609 * 2 ^ 59
def prefixEnd_1176609 : Nat := 4983230072969 + 3 ^ 40 * 1176609 * 2
def baseEnd_1176609 : Nat := 268518204180485442478391

theorem tailTrace_1176609 : CollatzResearch.WordTrace tailWord_1176609 prefixEnd_1176609 268518204180485442478391 := by
  unfold tailWord_1176609
  simp only [CollatzResearch.WordTrace]
  refine ⟨42914455794354016663956881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28609637196236011109304587 42914455794354016663956881)
  ·
    refine ⟨32185841845765512497967661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42914455794354016663956881 32185841845765512497967661)
    ·
      refine ⟨12069690692162067186737873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32185841845765512497967661 12069690692162067186737873)
      ·
        refine ⟨9052268019121550390053405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12069690692162067186737873 9052268019121550390053405)
        ·
          refine ⟨3394600507170581396270027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9052268019121550390053405 3394600507170581396270027)
          ·
            refine ⟨5091900760755872094405041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394600507170581396270027 5091900760755872094405041)
            ·
              refine ⟨3818925570566904070803781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5091900760755872094405041 3818925570566904070803781)
              ·
                refine ⟨716048544481294513275709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3818925570566904070803781 716048544481294513275709)
                ·
                  refine ⟨268518204180485442478391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716048544481294513275709 268518204180485442478391)
                  ·
                    rfl

theorem cell21_1176609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 3].length) (baseStart_1176609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176609 prefixEnd_1176609 := by exact prefixLift 1176609
  have htrace : WordTrace (prefixWord ++ tailWord_1176609) baseStart_1176609 baseEnd_1176609 := by
    simpa [prefixWord, tailWord_1176609, baseEnd_1176609] using wordTrace_append hprefix tailTrace_1176609
  have hstable : (prefixWord ++ tailWord_1176609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176609).length < 2 ^ (prefixWord ++ tailWord_1176609).sum := by decide
  have hdescent : baseEnd_1176609 < baseStart_1176609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176620 : List Nat := [2, 2, 1, 1, 1, 2, 4, 8]
def baseStart_1176620 : Nat := 118140960795 + 1176620 * 2 ^ 59
def prefixEnd_1176620 : Nat := 4983230072969 + 3 ^ 40 * 1176620 * 2
def baseEnd_1176620 : Nat := 89506904843450622598345

theorem tailTrace_1176620 : CollatzResearch.WordTrace tailWord_1176620 prefixEnd_1176620 89506904843450622598345 := by
  unfold tailWord_1176620
  simp only [CollatzResearch.WordTrace]
  refine ⟨21457428498657082771303657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28609904664876110361738209 21457428498657082771303657)
  ·
    refine ⟨16093071373992812078477743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21457428498657082771303657 16093071373992812078477743)
    ·
      refine ⟨24139607060989218117716615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16093071373992812078477743 24139607060989218117716615)
      ·
        refine ⟨36209410591483827176574923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24139607060989218117716615 36209410591483827176574923)
        ·
          refine ⟨54314115887225740764862385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36209410591483827176574923 54314115887225740764862385)
          ·
            refine ⟨40735586915419305573646789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54314115887225740764862385 40735586915419305573646789)
            ·
              refine ⟨7637922546641119795058773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40735586915419305573646789 7637922546641119795058773)
              ·
                refine ⟨89506904843450622598345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7637922546641119795058773 89506904843450622598345)
                ·
                  rfl

theorem cell21_1176620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_1176620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176620 prefixEnd_1176620 := by exact prefixLift 1176620
  have htrace : WordTrace (prefixWord ++ tailWord_1176620) baseStart_1176620 baseEnd_1176620 := by
    simpa [prefixWord, tailWord_1176620, baseEnd_1176620] using wordTrace_append hprefix tailTrace_1176620
  have hstable : (prefixWord ++ tailWord_1176620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176620).length < 2 ^ (prefixWord ++ tailWord_1176620).sum := by decide
  have hdescent : baseEnd_1176620 < baseStart_1176620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176637 : List Nat := [1, 4, 1, 3, 1, 3, 1, 7]
def baseStart_1176637 : Nat := 118140960795 + 1176637 * 2 ^ 59
def prefixEnd_1176637 : Nat := 4983230072969 + 3 ^ 40 * 1176637 * 2
def baseEnd_1176637 : Nat := 89508198053987872003889

theorem tailTrace_1176637 : CollatzResearch.WordTrace tailWord_1176637 prefixEnd_1176637 89508198053987872003889 := by
  unfold tailWord_1176637
  simp only [CollatzResearch.WordTrace]
  refine ⟨42915477038252577445976165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28610318025501718297317443 42915477038252577445976165)
  ·
    refine ⟨8046651944672358271120531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42915477038252577445976165 8046651944672358271120531)
    ·
      refine ⟨12069977917008537406680797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8046651944672358271120531 12069977917008537406680797)
      ·
        refine ⟨4526241718878201527505299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12069977917008537406680797 4526241718878201527505299)
        ·
          refine ⟨6789362578317302291257949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526241718878201527505299 6789362578317302291257949)
          ·
            refine ⟨2546010966868988359221731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6789362578317302291257949 2546010966868988359221731)
            ·
              refine ⟨3819016450303482538832597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2546010966868988359221731 3819016450303482538832597)
              ·
                refine ⟨89508198053987872003889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3819016450303482538832597 89508198053987872003889)
                ·
                  rfl

theorem cell21_1176637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 7].length) (baseStart_1176637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176637 prefixEnd_1176637 := by exact prefixLift 1176637
  have htrace : WordTrace (prefixWord ++ tailWord_1176637) baseStart_1176637 baseEnd_1176637 := by
    simpa [prefixWord, tailWord_1176637, baseEnd_1176637] using wordTrace_append hprefix tailTrace_1176637
  have hstable : (prefixWord ++ tailWord_1176637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176637).length < 2 ^ (prefixWord ++ tailWord_1176637).sum := by decide
  have hdescent : baseEnd_1176637 < baseStart_1176637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176696 : List Nat := [2, 1, 2, 1, 1, 1, 6, 7]
def baseStart_1176696 : Nat := 118140960795 + 1176696 * 2 ^ 59
def prefixEnd_1176696 : Nat := 4983230072969 + 3 ^ 40 * 1176696 * 2
def baseEnd_1176696 : Nat := 89512686255264208176071

theorem tailTrace_1176696 : CollatzResearch.WordTrace tailWord_1176696 prefixEnd_1176696 89512686255264208176071 := by
  unfold tailWord_1176696
  simp only [CollatzResearch.WordTrace]
  refine ⟨21458814472519415261186971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28611752630025887014915961 21458814472519415261186971)
  ·
    refine ⟨32188221708779122891780457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21458814472519415261186971 32188221708779122891780457)
    ·
      refine ⟨24141166281584342168835343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32188221708779122891780457 24141166281584342168835343)
      ·
        refine ⟨36211749422376513253253015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24141166281584342168835343 36211749422376513253253015)
        ·
          refine ⟨54317624133564769879879523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36211749422376513253253015 54317624133564769879879523)
          ·
            refine ⟨81476436200347154819819285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54317624133564769879879523 81476436200347154819819285)
            ·
              refine ⟨3819207946891272882179029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81476436200347154819819285 3819207946891272882179029)
              ·
                refine ⟨89512686255264208176071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3819207946891272882179029 89512686255264208176071)
                ·
                  rfl

theorem cell21_1176696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_1176696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176696 prefixEnd_1176696 := by exact prefixLift 1176696
  have htrace : WordTrace (prefixWord ++ tailWord_1176696) baseStart_1176696 baseEnd_1176696 := by
    simpa [prefixWord, tailWord_1176696, baseEnd_1176696] using wordTrace_append hprefix tailTrace_1176696
  have hstable : (prefixWord ++ tailWord_1176696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176696).length < 2 ^ (prefixWord ++ tailWord_1176696).sum := by decide
  have hdescent : baseEnd_1176696 < baseStart_1176696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176730 : List Nat := [3, 1, 1, 5, 1, 3, 1, 6]
def baseStart_1176730 : Nat := 118140960795 + 1176730 * 2 ^ 59
def prefixEnd_1176730 : Nat := 4983230072969 + 3 ^ 40 * 1176730 * 2
def baseEnd_1176730 : Nat := 89515272676338706987159

theorem tailTrace_1176730 : CollatzResearch.WordTrace tailWord_1176730 prefixEnd_1176730 89515272676338706987159 := by
  unfold tailWord_1176730
  simp only [CollatzResearch.WordTrace]
  refine ⟨10729717256728913582277911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28612579351277102886074429 10729717256728913582277911)
  ·
    refine ⟨16094575885093370373416867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10729717256728913582277911 16094575885093370373416867)
    ·
      refine ⟨24141863827640055560125301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16094575885093370373416867 24141863827640055560125301)
      ·
        refine ⟨2263299733841255208761747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24141863827640055560125301 2263299733841255208761747)
        ·
          refine ⟨3394949600761882813142621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263299733841255208761747 3394949600761882813142621)
          ·
            refine ⟨1273106100285706054928483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3394949600761882813142621 1273106100285706054928483)
            ·
              refine ⟨1909659150428559082392725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273106100285706054928483 1909659150428559082392725)
              ·
                refine ⟨89515272676338706987159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1909659150428559082392725 89515272676338706987159)
                ·
                  rfl

theorem cell21_1176730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_1176730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176730 prefixEnd_1176730 := by exact prefixLift 1176730
  have htrace : WordTrace (prefixWord ++ tailWord_1176730) baseStart_1176730 baseEnd_1176730 := by
    simpa [prefixWord, tailWord_1176730, baseEnd_1176730] using wordTrace_append hprefix tailTrace_1176730
  have hstable : (prefixWord ++ tailWord_1176730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176730).length < 2 ^ (prefixWord ++ tailWord_1176730).sum := by decide
  have hdescent : baseEnd_1176730 < baseStart_1176730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176761 : List Nat := [1, 2, 1, 4, 1, 4, 2, 3, 3]
def baseStart_1176761 : Nat := 118140960795 + 1176761 * 2 ^ 59
def prefixEnd_1176761 : Nat := 4983230072969 + 3 ^ 40 * 1176761 * 2
def baseEnd_1176761 : Nat := 268552892651366955944747

theorem tailTrace_1176761 : CollatzResearch.WordTrace tailWord_1176761 prefixEnd_1176761 268552892651366955944747 := by
  unfold tailWord_1176761
  simp only [CollatzResearch.WordTrace]
  refine ⟨42919999689803346623490137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28613333126535564415660091 42919999689803346623490137)
  ·
    refine ⟨32189999767352509967617603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42919999689803346623490137 32189999767352509967617603)
    ·
      refine ⟨48284999651028764951426405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32189999767352509967617603 48284999651028764951426405)
      ·
        refine ⟨9053437434567893428392451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48284999651028764951426405 9053437434567893428392451)
        ·
          refine ⟨13580156151851840142588677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9053437434567893428392451 13580156151851840142588677)
          ·
            refine ⟨2546279278472220026735377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13580156151851840142588677 2546279278472220026735377)
            ·
              refine ⟨1909709458854165020051533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2546279278472220026735377 1909709458854165020051533)
              ·
                refine ⟨716141047070311882519325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1909709458854165020051533 716141047070311882519325)
                ·
                  refine ⟨268552892651366955944747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716141047070311882519325 268552892651366955944747)
                  ·
                    rfl

theorem cell21_1176761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 3].length) (baseStart_1176761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176761 prefixEnd_1176761 := by exact prefixLift 1176761
  have htrace : WordTrace (prefixWord ++ tailWord_1176761) baseStart_1176761 baseEnd_1176761 := by
    simpa [prefixWord, tailWord_1176761, baseEnd_1176761] using wordTrace_append hprefix tailTrace_1176761
  have hstable : (prefixWord ++ tailWord_1176761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176761).length < 2 ^ (prefixWord ++ tailWord_1176761).sum := by decide
  have hdescent : baseEnd_1176761 < baseStart_1176761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176792 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 4]
def baseStart_1176792 : Nat := 118140960795 + 1176792 * 2 ^ 59
def prefixEnd_1176792 : Nat := 4983230072969 + 3 ^ 40 * 1176792 * 2
def baseEnd_1176792 : Nat := 268559967273717790928017

theorem tailTrace_1176792 : CollatzResearch.WordTrace tailWord_1176792 prefixEnd_1176792 268559967273717790928017 := by
  unfold tailWord_1176792
  simp only [CollatzResearch.WordTrace]
  refine ⟨21460565176345519458934315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28614086901794025945245753 21460565176345519458934315)
  ·
    refine ⟨32190847764518279188401473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21460565176345519458934315 32190847764518279188401473)
    ·
      refine ⟨24143135823388709391301105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32190847764518279188401473 24143135823388709391301105)
      ·
        refine ⟨18107351867541532043475829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24143135823388709391301105 18107351867541532043475829)
        ·
          refine ⟨1697564237582018629075859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18107351867541532043475829 1697564237582018629075859)
          ·
            refine ⟨2546346356373027943613789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697564237582018629075859 2546346356373027943613789)
            ·
              refine ⟨954879883639885478855171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2546346356373027943613789 954879883639885478855171)
              ·
                refine ⟨1432319825459828218282757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954879883639885478855171 1432319825459828218282757)
                ·
                  refine ⟨268559967273717790928017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1432319825459828218282757 268559967273717790928017)
                  ·
                    rfl

theorem cell21_1176792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_1176792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176792 prefixEnd_1176792 := by exact prefixLift 1176792
  have htrace : WordTrace (prefixWord ++ tailWord_1176792) baseStart_1176792 baseEnd_1176792 := by
    simpa [prefixWord, tailWord_1176792, baseEnd_1176792] using wordTrace_append hprefix tailTrace_1176792
  have hstable : (prefixWord ++ tailWord_1176792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176792).length < 2 ^ (prefixWord ++ tailWord_1176792).sum := by decide
  have hdescent : baseEnd_1176792 < baseStart_1176792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176837 : List Nat := [1, 3, 1, 1, 2, 1, 7, 2, 3]
def baseStart_1176837 : Nat := 118140960795 + 1176837 * 2 ^ 59
def prefixEnd_1176837 : Nat := 4983230072969 + 3 ^ 40 * 1176837 * 2
def baseEnd_1176837 : Nat := 268570236886807712677925

theorem tailTrace_1176837 : CollatzResearch.WordTrace tailWord_1176837 prefixEnd_1176837 268570236886807712677925 := by
  unfold tailWord_1176837
  simp only [CollatzResearch.WordTrace]
  refine ⟨42922771637528011603256765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28615181091685341068837843 42922771637528011603256765)
  ·
    refine ⟨16096039364073004351221287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42922771637528011603256765 16096039364073004351221287)
    ·
      refine ⟨24144059046109506526831931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16096039364073004351221287 24144059046109506526831931)
      ·
        refine ⟨36216088569164259790247897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24144059046109506526831931 36216088569164259790247897)
        ·
          refine ⟨27162066426873194842685923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36216088569164259790247897 27162066426873194842685923)
          ·
            refine ⟨40743099640309792264028885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27162066426873194842685923 40743099640309792264028885)
            ·
              refine ⟨954916397819760756188177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 40743099640309792264028885 954916397819760756188177)
              ·
                refine ⟨716187298364820567141133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954916397819760756188177 716187298364820567141133)
                ·
                  refine ⟨268570236886807712677925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716187298364820567141133 268570236886807712677925)
                  ·
                    rfl

theorem cell21_1176837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_1176837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176837 prefixEnd_1176837 := by exact prefixLift 1176837
  have htrace : WordTrace (prefixWord ++ tailWord_1176837) baseStart_1176837 baseEnd_1176837 := by
    simpa [prefixWord, tailWord_1176837, baseEnd_1176837] using wordTrace_append hprefix tailTrace_1176837
  have hstable : (prefixWord ++ tailWord_1176837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176837).length < 2 ^ (prefixWord ++ tailWord_1176837).sum := by decide
  have hdescent : baseEnd_1176837 < baseStart_1176837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176896 : List Nat := [2, 1, 1, 2, 2, 1, 5, 4, 3]
def baseStart_1176896 : Nat := 118140960795 + 1176896 * 2 ^ 59
def prefixEnd_1176896 : Nat := 4983230072969 + 3 ^ 40 * 1176896 * 2
def baseEnd_1176896 : Nat := 268583701490636721194471

theorem tailTrace_1176896 : CollatzResearch.WordTrace tailWord_1176896 prefixEnd_1176896 268583701490636721194471 := by
  unfold tailWord_1176896
  simp only [CollatzResearch.WordTrace]
  refine ⟨21462461772157132339827271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28616615696209509786436361 21462461772157132339827271)
  ·
    refine ⟨32193692658235698509740907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21462461772157132339827271 32193692658235698509740907)
    ·
      refine ⟨48290538987353547764611361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32193692658235698509740907 48290538987353547764611361)
      ·
        refine ⟨36217904240515160823458521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48290538987353547764611361 36217904240515160823458521)
        ·
          refine ⟨27163428180386370617593891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36217904240515160823458521 27163428180386370617593891)
          ·
            refine ⟨40745142270579555926390837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27163428180386370617593891 40745142270579555926390837)
            ·
              refine ⟨3819857087866833368099141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40745142270579555926390837 3819857087866833368099141)
              ·
                refine ⟨716223203975031256518589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3819857087866833368099141 716223203975031256518589)
                ·
                  refine ⟨268583701490636721194471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716223203975031256518589 268583701490636721194471)
                  ·
                    rfl

theorem cell21_1176896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 3].length) (baseStart_1176896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176896 prefixEnd_1176896 := by exact prefixLift 1176896
  have htrace : WordTrace (prefixWord ++ tailWord_1176896) baseStart_1176896 baseEnd_1176896 := by
    simpa [prefixWord, tailWord_1176896, baseEnd_1176896] using wordTrace_append hprefix tailTrace_1176896
  have hstable : (prefixWord ++ tailWord_1176896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176896).length < 2 ^ (prefixWord ++ tailWord_1176896).sum := by decide
  have hdescent : baseEnd_1176896 < baseStart_1176896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176910 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_1176910 : Nat := 118140960795 + 1176910 * 2 ^ 59
def prefixEnd_1176910 : Nat := 4983230072969 + 3 ^ 40 * 1176910 * 2
def baseEnd_1176910 : Nat := 268586896481375807961109

theorem tailTrace_1176910 : CollatzResearch.WordTrace tailWord_1176910 prefixEnd_1176910 268586896481375807961109 := by
  unfold tailWord_1176910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5365679270782943133833023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28616956110842363380442789 5365679270782943133833023)
  ·
    refine ⟨8048518906174414700749535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5365679270782943133833023 8048518906174414700749535)
    ·
      refine ⟨12072778359261622051124303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8048518906174414700749535 12072778359261622051124303)
      ·
        refine ⟨18109167538892433076686455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12072778359261622051124303 18109167538892433076686455)
        ·
          refine ⟨27163751308338649615029683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18109167538892433076686455 27163751308338649615029683)
          ·
            refine ⟨40745626962507974422544525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27163751308338649615029683 40745626962507974422544525)
            ·
              refine ⟨15279610110940490408454197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40745626962507974422544525 15279610110940490408454197)
              ·
                refine ⟨1432463447900670975792581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15279610110940490408454197 1432463447900670975792581)
                ·
                  refine ⟨268586896481375807961109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1432463447900670975792581 268586896481375807961109)
                  ·
                    rfl

theorem cell21_1176910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_1176910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176910 prefixEnd_1176910 := by exact prefixLift 1176910
  have htrace : WordTrace (prefixWord ++ tailWord_1176910) baseStart_1176910 baseEnd_1176910 := by
    simpa [prefixWord, tailWord_1176910, baseEnd_1176910] using wordTrace_append hprefix tailTrace_1176910
  have hstable : (prefixWord ++ tailWord_1176910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176910).length < 2 ^ (prefixWord ++ tailWord_1176910).sum := by decide
  have hdescent : baseEnd_1176910 < baseStart_1176910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176955 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 5]
def baseStart_1176955 : Nat := 118140960795 + 1176955 * 2 ^ 59
def prefixEnd_1176955 : Nat := 4983230072969 + 3 ^ 40 * 1176955 * 2
def baseEnd_1176955 : Nat := 268597166094465729711017

theorem tailTrace_1176955 : CollatzResearch.WordTrace tailWord_1176955 prefixEnd_1176955 268597166094465729711017 := by
  unfold tailWord_1176955
  simp only [CollatzResearch.WordTrace]
  refine ⟨42927075451100517756052319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28618050300733678504034879 42927075451100517756052319)
  ·
    refine ⟨64390613176650776634078479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42927075451100517756052319 64390613176650776634078479)
    ·
      refine ⟨96585919764976164951117719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64390613176650776634078479 96585919764976164951117719)
      ·
        refine ⟨144878879647464247426676579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96585919764976164951117719 144878879647464247426676579)
        ·
          refine ⟨217318319471196371140014869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144878879647464247426676579 217318319471196371140014869)
          ·
            refine ⟨10186796225212329897188197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 217318319471196371140014869 10186796225212329897188197)
            ·
              refine ⟨1910024292227311855722787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10186796225212329897188197 1910024292227311855722787)
              ·
                refine ⟨2865036438340967783584181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910024292227311855722787 2865036438340967783584181)
                ·
                  refine ⟨268597166094465729711017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2865036438340967783584181 268597166094465729711017)
                  ·
                    rfl

theorem cell21_1176955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 5].length) (baseStart_1176955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176955 prefixEnd_1176955 := by exact prefixLift 1176955
  have htrace : WordTrace (prefixWord ++ tailWord_1176955) baseStart_1176955 baseEnd_1176955 := by
    simpa [prefixWord, tailWord_1176955, baseEnd_1176955] using wordTrace_append hprefix tailTrace_1176955
  have hstable : (prefixWord ++ tailWord_1176955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176955).length < 2 ^ (prefixWord ++ tailWord_1176955).sum := by decide
  have hdescent : baseEnd_1176955 < baseStart_1176955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176989 : List Nat := [1, 4, 2, 1, 3, 1, 3, 3, 3]
def baseStart_1176989 : Nat := 118140960795 + 1176989 * 2 ^ 59
def prefixEnd_1176989 : Nat := 4983230072969 + 3 ^ 40 * 1176989 * 2
def baseEnd_1176989 : Nat := 268604925357689226144281

theorem tailTrace_1176989 : CollatzResearch.WordTrace tailWord_1176989 prefixEnd_1176989 268604925357689226144281 := by
  unfold tailWord_1176989
  simp only [CollatzResearch.WordTrace]
  refine ⟨42928315532977341562790021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28618877021984894375193347 42928315532977341562790021)
  ·
    refine ⟨8049059162433251543023129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42928315532977341562790021 8049059162433251543023129)
    ·
      refine ⟨6036794371824938657267347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8049059162433251543023129 6036794371824938657267347)
      ·
        refine ⟨9055191557737407985901021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6036794371824938657267347 9055191557737407985901021)
        ·
          refine ⟨3395696834151527994712883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9055191557737407985901021 3395696834151527994712883)
          ·
            refine ⟨5093545251227291992069325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395696834151527994712883 5093545251227291992069325)
            ·
              refine ⟨1910079469210234497025997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5093545251227291992069325 1910079469210234497025997)
              ·
                refine ⟨716279800953837936384749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1910079469210234497025997 716279800953837936384749)
                ·
                  refine ⟨268604925357689226144281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716279800953837936384749 268604925357689226144281)
                  ·
                    rfl

theorem cell21_1176989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_1176989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1176989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1176989 prefixEnd_1176989 := by exact prefixLift 1176989
  have htrace : WordTrace (prefixWord ++ tailWord_1176989) baseStart_1176989 baseEnd_1176989 := by
    simpa [prefixWord, tailWord_1176989, baseEnd_1176989] using wordTrace_append hprefix tailTrace_1176989
  have hstable : (prefixWord ++ tailWord_1176989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176989).length < 2 ^ (prefixWord ++ tailWord_1176989).sum := by decide
  have hdescent : baseEnd_1176989 < baseStart_1176989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177017 : List Nat := [1, 2, 1, 4, 4, 1, 2, 6]
def baseStart_1177017 : Nat := 118140960795 + 1177017 * 2 ^ 59
def prefixEnd_1177017 : Nat := 4983230072969 + 3 ^ 40 * 1177017 * 2
def baseEnd_1177017 : Nat := 89537105113055799892519

theorem tailTrace_1177017 : CollatzResearch.WordTrace tailWord_1177017 prefixEnd_1177017 89537105113055799892519 := by
  unfold tailWord_1177017
  simp only [CollatzResearch.WordTrace]
  refine ⟨42929336776875902344809305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28619557851250601563206203 42929336776875902344809305)
  ·
    refine ⟨32197002582656926758606979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42929336776875902344809305 32197002582656926758606979)
    ·
      refine ⟨48295503873985390137910469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32197002582656926758606979 48295503873985390137910469)
      ·
        refine ⟨9055406976372260650858213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48295503873985390137910469 9055406976372260650858213)
        ·
          refine ⟨1697888808069798872035915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9055406976372260650858213 1697888808069798872035915)
          ·
            refine ⟨2546833212104698308053873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697888808069798872035915 2546833212104698308053873)
            ·
              refine ⟨1910124909078523731040405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2546833212104698308053873 1910124909078523731040405)
              ·
                refine ⟨89537105113055799892519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1910124909078523731040405 89537105113055799892519)
                ·
                  rfl

theorem cell21_1177017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 6].length) (baseStart_1177017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177017 prefixEnd_1177017 := by exact prefixLift 1177017
  have htrace : WordTrace (prefixWord ++ tailWord_1177017) baseStart_1177017 baseEnd_1177017 := by
    simpa [prefixWord, tailWord_1177017, baseEnd_1177017] using wordTrace_append hprefix tailTrace_1177017
  have hstable : (prefixWord ++ tailWord_1177017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177017).length < 2 ^ (prefixWord ++ tailWord_1177017).sum := by decide
  have hdescent : baseEnd_1177017 < baseStart_1177017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177211 : List Nat := [1, 1, 1, 1, 1, 4, 3, 9]
def baseStart_1177211 : Nat := 118140960795 + 1177211 * 2 ^ 59
def prefixEnd_1177211 : Nat := 4983230072969 + 3 ^ 40 * 1177211 * 2
def baseEnd_1177211 : Nat := 89551862927422057814609

theorem tailTrace_1177211 : CollatzResearch.WordTrace tailWord_1177211 prefixEnd_1177211 89551862927422057814609 := by
  unfold tailWord_1177211
  simp only [CollatzResearch.WordTrace]
  refine ⟨42936412538173073477371487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28624275025448715651580991 42936412538173073477371487)
  ·
    refine ⟨64404618807259610216057231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42936412538173073477371487 64404618807259610216057231)
    ·
      refine ⟨96606928210889415324085847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64404618807259610216057231 96606928210889415324085847)
      ·
        refine ⟨144910392316334122986128771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96606928210889415324085847 144910392316334122986128771)
        ·
          refine ⟨217365588474501184479193157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144910392316334122986128771 217365588474501184479193157)
          ·
            refine ⟨40756047838968972089848717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217365588474501184479193157 40756047838968972089848717)
            ·
              refine ⟨15283517939613364533693269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40756047838968972089848717 15283517939613364533693269)
              ·
                refine ⟨89551862927422057814609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15283517939613364533693269 89551862927422057814609)
                ·
                  rfl

theorem cell21_1177211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 9].length) (baseStart_1177211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177211 prefixEnd_1177211 := by exact prefixLift 1177211
  have htrace : WordTrace (prefixWord ++ tailWord_1177211) baseStart_1177211 baseEnd_1177211 := by
    simpa [prefixWord, tailWord_1177211, baseEnd_1177211] using wordTrace_append hprefix tailTrace_1177211
  have hstable : (prefixWord ++ tailWord_1177211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177211).length < 2 ^ (prefixWord ++ tailWord_1177211).sum := by decide
  have hdescent : baseEnd_1177211 < baseStart_1177211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177276 : List Nat := [2, 2, 2, 3, 1, 2, 1, 5, 3]
def baseStart_1177276 : Nat := 118140960795 + 1177276 * 2 ^ 59
def prefixEnd_1177276 : Nat := 4983230072969 + 3 ^ 40 * 1177276 * 2
def baseEnd_1177276 : Nat := 268670422667840504860361

theorem tailTrace_1177276 : CollatzResearch.WordTrace tailWord_1177276 prefixEnd_1177276 268670422667840504860361 := by
  unfold tailWord_1177276
  simp only [CollatzResearch.WordTrace]
  refine ⟨21469391641468794789243841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28625855521958393052325121 21469391641468794789243841)
  ·
    refine ⟨16102043731101596091932881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21469391641468794789243841 16102043731101596091932881)
    ·
      refine ⟨12076532798326197068949661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16102043731101596091932881 12076532798326197068949661)
      ·
        refine ⟨4528699799372323900856123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12076532798326197068949661 4528699799372323900856123)
        ·
          refine ⟨6793049699058485851284185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528699799372323900856123 6793049699058485851284185)
          ·
            refine ⟨5094787274293864388463139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6793049699058485851284185 5094787274293864388463139)
            ·
              refine ⟨7642180911440796582694709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5094787274293864388463139 7642180911440796582694709)
              ·
                refine ⟨716454460447574679627629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7642180911440796582694709 716454460447574679627629)
                ·
                  refine ⟨268670422667840504860361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716454460447574679627629 268670422667840504860361)
                  ·
                    rfl

theorem cell21_1177276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_1177276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177276 prefixEnd_1177276 := by exact prefixLift 1177276
  have htrace : WordTrace (prefixWord ++ tailWord_1177276) baseStart_1177276 baseEnd_1177276 := by
    simpa [prefixWord, tailWord_1177276, baseEnd_1177276] using wordTrace_append hprefix tailTrace_1177276
  have hstable : (prefixWord ++ tailWord_1177276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177276).length < 2 ^ (prefixWord ++ tailWord_1177276).sum := by decide
  have hdescent : baseEnd_1177276 < baseStart_1177276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177282 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1177282 : Nat := 118140960795 + 1177282 * 2 ^ 59
def prefixEnd_1177282 : Nat := 4983230072969 + 3 ^ 40 * 1177282 * 2
def baseEnd_1177282 : Nat := 268671791949585827760349

theorem tailTrace_1177282 : CollatzResearch.WordTrace tailWord_1177282 prefixEnd_1177282 268671791949585827760349 := by
  unfold tailWord_1177282
  simp only [CollatzResearch.WordTrace]
  refine ⟨10734750530228963150801525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28626001413943901735470733 10734750530228963150801525)
  ·
    refine ⟨1006382862208965295387643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10734750530228963150801525 1006382862208965295387643)
    ·
      refine ⟨1509574293313447943081465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1006382862208965295387643 1509574293313447943081465)
      ·
        refine ⟨1132180719985085957311099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1509574293313447943081465 1132180719985085957311099)
        ·
          refine ⟨1698271079977628935966649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132180719985085957311099 1698271079977628935966649)
          ·
            refine ⟨1273703309983221701974987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1698271079977628935966649 1273703309983221701974987)
            ·
              refine ⟨1910554964974832552962481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273703309983221701974987 1910554964974832552962481)
              ·
                refine ⟨1432916223731124414721861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1910554964974832552962481 1432916223731124414721861)
                ·
                  refine ⟨268671791949585827760349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1432916223731124414721861 268671791949585827760349)
                  ·
                    rfl

theorem cell21_1177282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1177282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177282 prefixEnd_1177282 := by exact prefixLift 1177282
  have htrace : WordTrace (prefixWord ++ tailWord_1177282) baseStart_1177282 baseEnd_1177282 := by
    simpa [prefixWord, tailWord_1177282, baseEnd_1177282] using wordTrace_append hprefix tailTrace_1177282
  have hstable : (prefixWord ++ tailWord_1177282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177282).length < 2 ^ (prefixWord ++ tailWord_1177282).sum := by decide
  have hdescent : baseEnd_1177282 < baseStart_1177282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177287 : List Nat := [1, 1, 4, 1, 1, 1, 12]
def baseStart_1177287 : Nat := 118140960795 + 1177287 * 2 ^ 59
def prefixEnd_1177287 : Nat := 4983230072969 + 3 ^ 40 * 1177287 * 2
def baseEnd_1177287 : Nat := 29852548113078547797445

theorem tailTrace_1177287 : CollatzResearch.WordTrace tailWord_1177287 prefixEnd_1177287 29852548113078547797445 := by
  unfold tailWord_1177287
  simp only [CollatzResearch.WordTrace]
  refine ⟨42939184485897738457138115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28626122990598492304758743 42939184485897738457138115)
  ·
    refine ⟨64408776728846607685707173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42939184485897738457138115 64408776728846607685707173)
    ·
      refine ⟨12076645636658738941070095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64408776728846607685707173 12076645636658738941070095)
      ·
        refine ⟨18114968454988108411605143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12076645636658738941070095 18114968454988108411605143)
        ·
          refine ⟨27172452682482162617407715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18114968454988108411605143 27172452682482162617407715)
          ·
            refine ⟨40758679023723243926111573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27172452682482162617407715 40758679023723243926111573)
            ·
              refine ⟨29852548113078547797445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 40758679023723243926111573 29852548113078547797445)
              ·
                rfl

theorem cell21_1177287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 12].length) (baseStart_1177287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177287 prefixEnd_1177287 := by exact prefixLift 1177287
  have htrace : WordTrace (prefixWord ++ tailWord_1177287) baseStart_1177287 baseEnd_1177287 := by
    simpa [prefixWord, tailWord_1177287, baseEnd_1177287] using wordTrace_append hprefix tailTrace_1177287
  have hstable : (prefixWord ++ tailWord_1177287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177287).length < 2 ^ (prefixWord ++ tailWord_1177287).sum := by decide
  have hdescent : baseEnd_1177287 < baseStart_1177287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177290 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_1177290 : Nat := 118140960795 + 1177290 * 2 ^ 59
def prefixEnd_1177290 : Nat := 4983230072969 + 3 ^ 40 * 1177290 * 2
def baseEnd_1177290 : Nat := 268673617658579591626999

theorem tailTrace_1177290 : CollatzResearch.WordTrace tailWord_1177290 prefixEnd_1177290 268673617658579591626999 := by
  unfold tailWord_1177290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10734823476221717492374331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28626195936591246646331549 10734823476221717492374331)
  ·
    refine ⟨16102235214332576238561497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10734823476221717492374331 16102235214332576238561497)
    ·
      refine ⟨12076676410749432178921123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16102235214332576238561497 12076676410749432178921123)
      ·
        refine ⟨18115014616124148268381685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12076676410749432178921123 18115014616124148268381685)
        ·
          refine ⟨1698282620261638900160783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18115014616124148268381685 1698282620261638900160783)
          ·
            refine ⟨2547423930392458350241175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698282620261638900160783 2547423930392458350241175)
            ·
              refine ⟨3821135895588687525361763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547423930392458350241175 3821135895588687525361763)
              ·
                refine ⟨5731703843383031288042645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3821135895588687525361763 5731703843383031288042645)
                ·
                  refine ⟨268673617658579591626999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5731703843383031288042645 268673617658579591626999)
                  ·
                    rfl

theorem cell21_1177290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_1177290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177290 prefixEnd_1177290 := by exact prefixLift 1177290
  have htrace : WordTrace (prefixWord ++ tailWord_1177290) baseStart_1177290 baseEnd_1177290 := by
    simpa [prefixWord, tailWord_1177290, baseEnd_1177290] using wordTrace_append hprefix tailTrace_1177290
  have hstable : (prefixWord ++ tailWord_1177290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177290).length < 2 ^ (prefixWord ++ tailWord_1177290).sum := by decide
  have hdescent : baseEnd_1177290 < baseStart_1177290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177293 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1177293 : Nat := 118140960795 + 1177293 * 2 ^ 59
def prefixEnd_1177293 : Nat := 4983230072969 + 3 ^ 40 * 1177293 * 2
def baseEnd_1177293 : Nat := 268674302299452253076993

theorem tailTrace_1177293 : CollatzResearch.WordTrace tailWord_1177293 prefixEnd_1177293 268674302299452253076993 := by
  unfold tailWord_1177293
  simp only [CollatzResearch.WordTrace]
  refine ⟨42939403323876001481856533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28626268882584000987904355 42939403323876001481856533)
  ·
    refine ⟨2012784530806687569462025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42939403323876001481856533 2012784530806687569462025)
    ·
      refine ⟨1509588398105015677096519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2012784530806687569462025 1509588398105015677096519)
      ·
        refine ⟨2264382597157523515644779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509588398105015677096519 2264382597157523515644779)
        ·
          refine ⟨3396573895736285273467169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2264382597157523515644779 3396573895736285273467169)
          ·
            refine ⟨2547430421802213955100377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3396573895736285273467169 2547430421802213955100377)
            ·
              refine ⟨1910572816351660466325283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2547430421802213955100377 1910572816351660466325283)
              ·
                refine ⟨2865859224527490699487925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910572816351660466325283 2865859224527490699487925)
                ·
                  refine ⟨268674302299452253076993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2865859224527490699487925 268674302299452253076993)
                  ·
                    rfl

theorem cell21_1177293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1177293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177293 prefixEnd_1177293 := by exact prefixLift 1177293
  have htrace : WordTrace (prefixWord ++ tailWord_1177293) baseStart_1177293 baseEnd_1177293 := by
    simpa [prefixWord, tailWord_1177293, baseEnd_1177293] using wordTrace_append hprefix tailTrace_1177293
  have hstable : (prefixWord ++ tailWord_1177293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177293).length < 2 ^ (prefixWord ++ tailWord_1177293).sum := by decide
  have hdescent : baseEnd_1177293 < baseStart_1177293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177380 : List Nat := [2, 3, 1, 3, 2, 1, 2, 7]
def baseStart_1177380 : Nat := 118140960795 + 1177380 * 2 ^ 59
def prefixEnd_1177380 : Nat := 4983230072969 + 3 ^ 40 * 1177380 * 2
def baseEnd_1177380 : Nat := 89564718961586478375605

theorem tailTrace_1177380 : CollatzResearch.WordTrace tailWord_1177380 prefixEnd_1177380 89564718961586478375605 := by
  unfold tailWord_1177380
  simp only [CollatzResearch.WordTrace]
  refine ⟨21471288237280407670136797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28628384316373876893515729 21471288237280407670136797)
  ·
    refine ⟨8051733088980152876301299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21471288237280407670136797 8051733088980152876301299)
    ·
      refine ⟨12077599633470229314451949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8051733088980152876301299 12077599633470229314451949)
      ·
        refine ⟨4529099862551335992919481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12077599633470229314451949 4529099862551335992919481)
        ·
          refine ⟨3396824896913501994689611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4529099862551335992919481 3396824896913501994689611)
          ·
            refine ⟨5095237345370252992034417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396824896913501994689611 5095237345370252992034417)
            ·
              refine ⟨3821428009027689744025813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5095237345370252992034417 3821428009027689744025813)
              ·
                refine ⟨89564718961586478375605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3821428009027689744025813 89564718961586478375605)
                ·
                  rfl

theorem cell21_1177380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_1177380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177380 prefixEnd_1177380 := by exact prefixLift 1177380
  have htrace : WordTrace (prefixWord ++ tailWord_1177380) baseStart_1177380 baseEnd_1177380 := by
    simpa [prefixWord, tailWord_1177380, baseEnd_1177380] using wordTrace_append hprefix tailTrace_1177380
  have hstable : (prefixWord ++ tailWord_1177380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177380).length < 2 ^ (prefixWord ++ tailWord_1177380).sum := by decide
  have hdescent : baseEnd_1177380 < baseStart_1177380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177414 : List Nat := [6, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1177414 : Nat := 118140960795 + 1177414 * 2 ^ 59
def prefixEnd_1177414 : Nat := 4983230072969 + 3 ^ 40 * 1177414 * 2
def baseEnd_1177414 : Nat := 89567305382660977186693

theorem tailTrace_1177414 : CollatzResearch.WordTrace tailWord_1177414 prefixEnd_1177414 89567305382660977186693 := by
  unfold tailWord_1177414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341994267388676223344103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28629211037625092764674197 1341994267388676223344103)
  ·
    refine ⟨2012991401083014335016155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1341994267388676223344103 2012991401083014335016155)
    ·
      refine ⟨3019487101624521502524233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2012991401083014335016155 3019487101624521502524233)
      ·
        refine ⟨2264615326218391126893175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3019487101624521502524233 2264615326218391126893175)
        ·
          refine ⟨3396922989327586690339763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2264615326218391126893175 3396922989327586690339763)
          ·
            refine ⟨5095384483991380035509645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396922989327586690339763 5095384483991380035509645)
            ·
              refine ⟨1910769181496767513316117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5095384483991380035509645 1910769181496767513316117)
              ·
                refine ⟨89567305382660977186693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1910769181496767513316117 89567305382660977186693)
                ·
                  rfl

theorem cell21_1177414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1177414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177414 prefixEnd_1177414 := by exact prefixLift 1177414
  have htrace : WordTrace (prefixWord ++ tailWord_1177414) baseStart_1177414 baseEnd_1177414 := by
    simpa [prefixWord, tailWord_1177414, baseEnd_1177414] using wordTrace_append hprefix tailTrace_1177414
  have hstable : (prefixWord ++ tailWord_1177414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177414).length < 2 ^ (prefixWord ++ tailWord_1177414).sum := by decide
  have hdescent : baseEnd_1177414 < baseStart_1177414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177490 : List Nat := [3, 2, 3, 2, 1, 3, 2, 5]
def baseStart_1177490 : Nat := 118140960795 + 1177490 * 2 ^ 59
def prefixEnd_1177490 : Nat := 4983230072969 + 3 ^ 40 * 1177490 * 2
def baseEnd_1177490 : Nat := 89573086794474562764419

theorem tailTrace_1177490 : CollatzResearch.WordTrace tailWord_1177490 prefixEnd_1177490 89573086794474562764419 := by
  unfold tailWord_1177490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10736647126040576031694481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28631059002774869417851949 10736647126040576031694481)
  ·
    refine ⟨8052485344530432023770861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10736647126040576031694481 8052485344530432023770861)
    ·
      refine ⟨3019682004198912008914073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8052485344530432023770861 3019682004198912008914073)
      ·
        refine ⟨2264761503149184006685555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3019682004198912008914073 2264761503149184006685555)
        ·
          refine ⟨3397142254723776010028333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2264761503149184006685555 3397142254723776010028333)
          ·
            refine ⟨1273928345521416003760625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3397142254723776010028333 1273928345521416003760625)
            ·
              refine ⟨955446259141062002820469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273928345521416003760625 955446259141062002820469)
              ·
                refine ⟨89573086794474562764419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 955446259141062002820469 89573086794474562764419)
                ·
                  rfl

theorem cell21_1177490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_1177490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177490 prefixEnd_1177490 := by exact prefixLift 1177490
  have htrace : WordTrace (prefixWord ++ tailWord_1177490) baseStart_1177490 baseEnd_1177490 := by
    simpa [prefixWord, tailWord_1177490, baseEnd_1177490] using wordTrace_append hprefix tailTrace_1177490
  have hstable : (prefixWord ++ tailWord_1177490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177490).length < 2 ^ (prefixWord ++ tailWord_1177490).sum := by decide
  have hdescent : baseEnd_1177490 < baseStart_1177490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177501 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1177501 : Nat := 118140960795 + 1177501 * 2 ^ 59
def prefixEnd_1177501 : Nat := 4983230072969 + 3 ^ 40 * 1177501 * 2
def baseEnd_1177501 : Nat := 268721770733290113609901

theorem tailTrace_1177501 : CollatzResearch.WordTrace tailWord_1177501 prefixEnd_1177501 268721770733290113609901 := by
  unfold tailWord_1177501
  simp only [CollatzResearch.WordTrace]
  refine ⟨42946989707122453005428357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28631326471414968670285571 42946989707122453005428357)
  ·
    refine ⟨8052560570085459938517817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42946989707122453005428357 8052560570085459938517817)
    ·
      refine ⟨6039420427564094953888363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8052560570085459938517817 6039420427564094953888363)
      ·
        refine ⟨9059130641346142430832545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6039420427564094953888363 9059130641346142430832545)
        ·
          refine ⟨6794347981009606823124409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9059130641346142430832545 6794347981009606823124409)
          ·
            refine ⟨5095760985757205117343307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6794347981009606823124409 5095760985757205117343307)
            ·
              refine ⟨7643641478635807676014961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5095760985757205117343307 7643641478635807676014961)
              ·
                refine ⟨5732731108976855757011221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7643641478635807676014961 5732731108976855757011221)
                ·
                  refine ⟨268721770733290113609901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5732731108976855757011221 268721770733290113609901)
                  ·
                    rfl

theorem cell21_1177501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1177501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177501 prefixEnd_1177501 := by exact prefixLift 1177501
  have htrace : WordTrace (prefixWord ++ tailWord_1177501) baseStart_1177501 baseEnd_1177501 := by
    simpa [prefixWord, tailWord_1177501, baseEnd_1177501] using wordTrace_append hprefix tailTrace_1177501
  have hstable : (prefixWord ++ tailWord_1177501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177501).length < 2 ^ (prefixWord ++ tailWord_1177501).sum := by decide
  have hdescent : baseEnd_1177501 < baseStart_1177501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177521 : List Nat := [1, 2, 2, 4, 2, 2, 3, 2, 3]
def baseStart_1177521 : Nat := 118140960795 + 1177521 * 2 ^ 59
def prefixEnd_1177521 : Nat := 4983230072969 + 3 ^ 40 * 1177521 * 2
def baseEnd_1177521 : Nat := 268726335005774523276527

theorem tailTrace_1177521 : CollatzResearch.WordTrace tailWord_1177521 prefixEnd_1177521 268726335005774523276527 := by
  unfold tailWord_1177521
  simp only [CollatzResearch.WordTrace]
  refine ⟨42947719167049996421156417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28631812778033330947437611 42947719167049996421156417)
  ·
    refine ⟨32210789375287497315867313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42947719167049996421156417 32210789375287497315867313)
    ·
      refine ⟨24158092031465622986900485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32210789375287497315867313 24158092031465622986900485)
      ·
        refine ⟨4529642255899804310043841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24158092031465622986900485 4529642255899804310043841)
        ·
          refine ⟨3397231691924853232532881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4529642255899804310043841 3397231691924853232532881)
          ·
            refine ⟨2547923768943639924399661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3397231691924853232532881 2547923768943639924399661)
            ·
              refine ⟨955471413353864971649873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2547923768943639924399661 955471413353864971649873)
              ·
                refine ⟨716603560015398728737405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955471413353864971649873 716603560015398728737405)
                ·
                  refine ⟨268726335005774523276527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716603560015398728737405 268726335005774523276527)
                  ·
                    rfl

theorem cell21_1177521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 3].length) (baseStart_1177521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177521 prefixEnd_1177521 := by exact prefixLift 1177521
  have htrace : WordTrace (prefixWord ++ tailWord_1177521) baseStart_1177521 baseEnd_1177521 := by
    simpa [prefixWord, tailWord_1177521, baseEnd_1177521] using wordTrace_append hprefix tailTrace_1177521
  have hstable : (prefixWord ++ tailWord_1177521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177521).length < 2 ^ (prefixWord ++ tailWord_1177521).sum := by decide
  have hdescent : baseEnd_1177521 < baseStart_1177521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177546 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_1177546 : Nat := 118140960795 + 1177546 * 2 ^ 59
def prefixEnd_1177546 : Nat := 4983230072969 + 3 ^ 40 * 1177546 * 2
def baseEnd_1177546 : Nat := 268732040346380035359809

theorem tailTrace_1177546 : CollatzResearch.WordTrace tailWord_1177546 prefixEnd_1177546 268732040346380035359809 := by
  unfold tailWord_1177546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10737157747989856422704123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28632420661306283793877661 10737157747989856422704123)
  ·
    refine ⟨16105736621984784634056185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10737157747989856422704123 16105736621984784634056185)
    ·
      refine ⟨12079302466488588475542139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16105736621984784634056185 12079302466488588475542139)
      ·
        refine ⟨18118953699732882713313209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12079302466488588475542139 18118953699732882713313209)
        ·
          refine ⟨13589215274799662034984907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18118953699732882713313209 13589215274799662034984907)
          ·
            refine ⟨20383822912199493052477361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13589215274799662034984907 20383822912199493052477361)
            ·
              refine ⟨15287867184149619789358021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20383822912199493052477361 15287867184149619789358021)
              ·
                refine ⟨2866475097028053710504629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15287867184149619789358021 2866475097028053710504629)
                ·
                  refine ⟨268732040346380035359809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2866475097028053710504629 268732040346380035359809)
                  ·
                    rfl

theorem cell21_1177546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_1177546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177546 prefixEnd_1177546 := by exact prefixLift 1177546
  have htrace : WordTrace (prefixWord ++ tailWord_1177546) baseStart_1177546 baseEnd_1177546 := by
    simpa [prefixWord, tailWord_1177546, baseEnd_1177546] using wordTrace_append hprefix tailTrace_1177546
  have hstable : (prefixWord ++ tailWord_1177546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177546).length < 2 ^ (prefixWord ++ tailWord_1177546).sum := by decide
  have hdescent : baseEnd_1177546 < baseStart_1177546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177608 : List Nat := [2, 1, 3, 2, 1, 2, 5, 5]
def baseStart_1177608 : Nat := 118140960795 + 1177608 * 2 ^ 59
def prefixEnd_1177608 : Nat := 4983230072969 + 3 ^ 40 * 1177608 * 2
def baseEnd_1177608 : Nat := 89582063197027235108783

theorem tailTrace_1177608 : CollatzResearch.WordTrace tailWord_1177608 prefixEnd_1177608 89582063197027235108783 := by
  unfold tailWord_1177608
  simp only [CollatzResearch.WordTrace]
  refine ⟨21475446158867405139786739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28633928211823206853048985 21475446158867405139786739)
  ·
    refine ⟨32213169238301107709680109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21475446158867405139786739 32213169238301107709680109)
    ·
      refine ⟨12079938464362915391130041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32213169238301107709680109 12079938464362915391130041)
      ·
        refine ⟨9059953848272186543347531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12079938464362915391130041 9059953848272186543347531)
        ·
          refine ⟨13589930772408279815021297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9059953848272186543347531 13589930772408279815021297)
          ·
            refine ⟨10192448079306209861265973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13589930772408279815021297 10192448079306209861265973)
            ·
              refine ⟨955542007434957174493685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10192448079306209861265973 955542007434957174493685)
              ·
                refine ⟨89582063197027235108783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 955542007434957174493685 89582063197027235108783)
                ·
                  rfl

theorem cell21_1177608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_1177608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177608 prefixEnd_1177608 := by exact prefixLift 1177608
  have htrace : WordTrace (prefixWord ++ tailWord_1177608) baseStart_1177608 baseEnd_1177608 := by
    simpa [prefixWord, tailWord_1177608, baseEnd_1177608] using wordTrace_append hprefix tailTrace_1177608
  have hstable : (prefixWord ++ tailWord_1177608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177608).length < 2 ^ (prefixWord ++ tailWord_1177608).sum := by decide
  have hdescent : baseEnd_1177608 < baseStart_1177608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177653 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 4]
def baseStart_1177653 : Nat := 118140960795 + 1177653 * 2 ^ 59
def prefixEnd_1177653 : Nat := 4983230072969 + 3 ^ 40 * 1177653 * 2
def baseEnd_1177653 : Nat := 268756459204171627076257

theorem tailTrace_1177653 : CollatzResearch.WordTrace tailWord_1177653 prefixEnd_1177653 268756459204171627076257 := by
  unfold tailWord_1177653
  simp only [CollatzResearch.WordTrace]
  refine ⟨42952533602571782964961613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28635022401714521976641075 42952533602571782964961613)
  ·
    refine ⟨16107200100964418611860605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42952533602571782964961613 16107200100964418611860605)
    ·
      refine ⟨6040200037861656979447727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16107200100964418611860605 6040200037861656979447727)
      ·
        refine ⟨9060300056792485469171591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6040200037861656979447727 9060300056792485469171591)
        ·
          refine ⟨13590450085188728203757387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9060300056792485469171591 13590450085188728203757387)
          ·
            refine ⟨20385675127783092305636081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13590450085188728203757387 20385675127783092305636081)
            ·
              refine ⟨15289256345837319229227061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20385675127783092305636081 15289256345837319229227061)
              ·
                refine ⟨1433367782422248677740037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15289256345837319229227061 1433367782422248677740037)
                ·
                  refine ⟨268756459204171627076257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1433367782422248677740037 268756459204171627076257)
                  ·
                    rfl

theorem cell21_1177653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_1177653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177653 prefixEnd_1177653 := by exact prefixLift 1177653
  have htrace : WordTrace (prefixWord ++ tailWord_1177653) baseStart_1177653 baseEnd_1177653 := by
    simpa [prefixWord, tailWord_1177653, baseEnd_1177653] using wordTrace_append hprefix tailTrace_1177653
  have hstable : (prefixWord ++ tailWord_1177653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177653).length < 2 ^ (prefixWord ++ tailWord_1177653).sum := by decide
  have hdescent : baseEnd_1177653 < baseStart_1177653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177670 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1177670 : Nat := 118140960795 + 1177670 * 2 ^ 59
def prefixEnd_1177670 : Nat := 4983230072969 + 3 ^ 40 * 1177670 * 2
def baseEnd_1177670 : Nat := 268760338835783375292889

theorem tailTrace_1177670 : CollatzResearch.WordTrace tailWord_1177670 prefixEnd_1177670 268760338835783375292889 := by
  unfold tailWord_1177670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1342286051359693589635327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28635435762340129912220309 1342286051359693589635327)
  ·
    refine ⟨2013429077039540384452991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1342286051359693589635327 2013429077039540384452991)
    ·
      refine ⟨3020143615559310576679487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013429077039540384452991 3020143615559310576679487)
      ·
        refine ⟨4530215423338965865019231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3020143615559310576679487 4530215423338965865019231)
        ·
          refine ⟨6795323135008448797528847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4530215423338965865019231 6795323135008448797528847)
          ·
            refine ⟨10192984702512673196293271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6795323135008448797528847 10192984702512673196293271)
            ·
              refine ⟨15289477053769009794439907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10192984702512673196293271 15289477053769009794439907)
              ·
                refine ⟨22934215580653514691659861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15289477053769009794439907 22934215580653514691659861)
                ·
                  refine ⟨268760338835783375292889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22934215580653514691659861 268760338835783375292889)
                  ·
                    rfl

theorem cell21_1177670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1177670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177670 prefixEnd_1177670 := by exact prefixLift 1177670
  have htrace : WordTrace (prefixWord ++ tailWord_1177670) baseStart_1177670 baseEnd_1177670 := by
    simpa [prefixWord, tailWord_1177670, baseEnd_1177670] using wordTrace_append hprefix tailTrace_1177670
  have hstable : (prefixWord ++ tailWord_1177670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177670).length < 2 ^ (prefixWord ++ tailWord_1177670).sum := by decide
  have hdescent : baseEnd_1177670 < baseStart_1177670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
