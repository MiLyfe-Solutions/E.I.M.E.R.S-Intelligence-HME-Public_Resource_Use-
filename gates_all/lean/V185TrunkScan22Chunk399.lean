import V185TrunkScan22Chunk398

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3558840 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 1, 5]
def baseStart_3558840 : Nat := 118140960795 + 3558840 * 2 ^ 59
def prefixEnd_3558840 : Nat := 4983230072969 + 3 ^ 40 * 3558840 * 2
def baseEnd_3558840 : Nat := 1218263661631307503888799

theorem tailTrace_3558840 : CollatzResearch.WordTrace tailWord_3558840 prefixEnd_3558840 1218263661631307503888799 := by
  unfold tailWord_3558840
  simp only [CollatzResearch.WordTrace]
  refine ⟨64900779213468978163780987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86534372284625304218374649 64900779213468978163780987)
  ·
    refine ⟨97351168820203467245671481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64900779213468978163780987 97351168820203467245671481)
    ·
      refine ⟨73013376615152600434253611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97351168820203467245671481 73013376615152600434253611)
      ·
        refine ⟨109520064922728900651380417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73013376615152600434253611 109520064922728900651380417)
        ·
          refine ⟨82140048692046675488535313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109520064922728900651380417 82140048692046675488535313)
          ·
            refine ⟨61605036519035006616401485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82140048692046675488535313 61605036519035006616401485)
            ·
              refine ⟨23101888694638127481150557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61605036519035006616401485 23101888694638127481150557)
              ·
                refine ⟨8663208260489297805431459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23101888694638127481150557 8663208260489297805431459)
                ·
                  refine ⟨12994812390733946708147189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8663208260489297805431459 12994812390733946708147189)
                  ·
                    refine ⟨1218263661631307503888799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12994812390733946708147189 1218263661631307503888799)
                    ·
                      rfl

theorem cell22_3558840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_3558840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558840 prefixEnd_3558840 := by exact prefixLift 3558840
  have htrace : WordTrace (prefixWord ++ tailWord_3558840) baseStart_3558840 baseEnd_3558840 := by
    simpa [prefixWord, tailWord_3558840, baseEnd_3558840] using wordTrace_append hprefix tailTrace_3558840
  have hstable : (prefixWord ++ tailWord_3558840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558840).length < 2 ^ (prefixWord ++ tailWord_3558840).sum := by decide
  have hdescent : baseEnd_3558840 < baseStart_3558840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558855 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 1, 6]
def baseStart_3558855 : Nat := 118140960795 + 3558855 * 2 ^ 59
def prefixEnd_3558855 : Nat := 4983230072969 + 3 ^ 40 * 3558855 * 2
def baseEnd_3558855 : Nat := 1218268796437852464763753

theorem tailTrace_3558855 : CollatzResearch.WordTrace tailWord_3558855 prefixEnd_3558855 1218268796437852464763753 := by
  unfold tailWord_3558855
  simp only [CollatzResearch.WordTrace]
  refine ⟨129802105521883613889358019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86534737014589075926238679 129802105521883613889358019)
  ·
    refine ⟨194703158282825420834037029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129802105521883613889358019 194703158282825420834037029)
    ·
      refine ⟨36506842178029766406381943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194703158282825420834037029 36506842178029766406381943)
      ·
        refine ⟨54760263267044649609572915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36506842178029766406381943 54760263267044649609572915)
        ·
          refine ⟨82140394900566974414359373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54760263267044649609572915 82140394900566974414359373)
          ·
            refine ⟨30802648087712615405384765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82140394900566974414359373 30802648087712615405384765)
            ·
              refine ⟨11550993032892230777019287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30802648087712615405384765 11550993032892230777019287)
              ·
                refine ⟨17326489549338346165528931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11550993032892230777019287 17326489549338346165528931)
                ·
                  refine ⟨25989734324007519248293397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17326489549338346165528931 25989734324007519248293397)
                  ·
                    refine ⟨1218268796437852464763753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25989734324007519248293397 1218268796437852464763753)
                    ·
                      rfl

theorem cell22_3558855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_3558855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558855 prefixEnd_3558855 := by exact prefixLift 3558855
  have htrace : WordTrace (prefixWord ++ tailWord_3558855) baseStart_3558855 baseEnd_3558855 := by
    simpa [prefixWord, tailWord_3558855, baseEnd_3558855] using wordTrace_append hprefix tailTrace_3558855
  have hstable : (prefixWord ++ tailWord_3558855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558855).length < 2 ^ (prefixWord ++ tailWord_3558855).sum := by decide
  have hdescent : baseEnd_3558855 < baseStart_3558855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558874 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 2, 3]
def baseStart_3558874 : Nat := 118140960795 + 3558874 * 2 ^ 59
def prefixEnd_3558874 : Nat := 4983230072969 + 3 ^ 40 * 3558874 * 2
def baseEnd_3558874 : Nat := 1218275300526142748538695

theorem tailTrace_3558874 : CollatzResearch.WordTrace tailWord_3558874 prefixEnd_3558874 1218275300526142748538695 := by
  unfold tailWord_3558874
  simp only [CollatzResearch.WordTrace]
  refine ⟨32450699627203695033574919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86535199005876520089533117 32450699627203695033574919)
  ·
    refine ⟨48676049440805542550362379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32450699627203695033574919 48676049440805542550362379)
    ·
      refine ⟨73014074161208313825543569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48676049440805542550362379 73014074161208313825543569)
      ·
        refine ⟨54760555620906235369157677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73014074161208313825543569 54760555620906235369157677)
        ·
          refine ⟨20535208357839838263434129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54760555620906235369157677 20535208357839838263434129)
          ·
            refine ⟨15401406268379878697575597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20535208357839838263434129 15401406268379878697575597)
            ·
              refine ⟨5775527350642454511590849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15401406268379878697575597 5775527350642454511590849)
              ·
                refine ⟨4331645512981840883693137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5775527350642454511590849 4331645512981840883693137)
                ·
                  refine ⟨3248734134736380662769853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4331645512981840883693137 3248734134736380662769853)
                  ·
                    refine ⟨1218275300526142748538695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248734134736380662769853 1218275300526142748538695)
                    ·
                      rfl

theorem cell22_3558874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_3558874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558874 prefixEnd_3558874 := by exact prefixLift 3558874
  have htrace : WordTrace (prefixWord ++ tailWord_3558874) baseStart_3558874 baseEnd_3558874 := by
    simpa [prefixWord, tailWord_3558874, baseEnd_3558874] using wordTrace_append hprefix tailTrace_3558874
  have hstable : (prefixWord ++ tailWord_3558874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558874).length < 2 ^ (prefixWord ++ tailWord_3558874).sum := by decide
  have hdescent : baseEnd_3558874 < baseStart_3558874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558910 : List Nat := [4, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_3558910 : Nat := 118140960795 + 3558910 * 2 ^ 59
def prefixEnd_3558910 : Nat := 4983230072969 + 3 ^ 40 * 3558910 * 2
def baseEnd_3558910 : Nat := 406095874687283551546195

theorem tailTrace_3558910 : CollatzResearch.WordTrace tailWord_3558910 prefixEnd_3558910 406095874687283551546195 := by
  unfold tailWord_3558910
  simp only [CollatzResearch.WordTrace]
  refine ⟨16225513942085544785326273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86536074357789572188406789 16225513942085544785326273)
  ·
    refine ⟨12169135456564158588994705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16225513942085544785326273 12169135456564158588994705)
    ·
      refine ⟨9126851592423118941746029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12169135456564158588994705 9126851592423118941746029)
      ·
        refine ⟨3422569347158669603154761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9126851592423118941746029 3422569347158669603154761)
        ·
          refine ⟨2566927010369002202366071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3422569347158669603154761 2566927010369002202366071)
          ·
            refine ⟨3850390515553503303549107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566927010369002202366071 3850390515553503303549107)
            ·
              refine ⟨5775585773330254955323661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850390515553503303549107 5775585773330254955323661)
              ·
                refine ⟨2165844664998845608246373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5775585773330254955323661 2165844664998845608246373)
                ·
                  refine ⟨406095874687283551546195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2165844664998845608246373 406095874687283551546195)
                  ·
                    rfl

theorem cell22_3558910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_3558910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558910 prefixEnd_3558910 := by exact prefixLift 3558910
  have htrace : WordTrace (prefixWord ++ tailWord_3558910) baseStart_3558910 baseEnd_3558910 := by
    simpa [prefixWord, tailWord_3558910, baseEnd_3558910] using wordTrace_append hprefix tailTrace_3558910
  have hstable : (prefixWord ++ tailWord_3558910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558910).length < 2 ^ (prefixWord ++ tailWord_3558910).sum := by decide
  have hdescent : baseEnd_3558910 < baseStart_3558910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558936 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 3, 3]
def baseStart_3558936 : Nat := 118140960795 + 3558936 * 2 ^ 59
def prefixEnd_3558936 : Nat := 4983230072969 + 3 ^ 40 * 3558936 * 2
def baseEnd_3558936 : Nat := 1218296524393195253488505

theorem tailTrace_3558936 : CollatzResearch.WordTrace tailWord_3558936 prefixEnd_3558936 1218296524393195253488505 := by
  unfold tailWord_3558936
  simp only [CollatzResearch.WordTrace]
  refine ⟨64902529917295082361528331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86536706556393443148704441 64902529917295082361528331)
  ·
    refine ⟨97353794875942623542292497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64902529917295082361528331 97353794875942623542292497)
    ·
      refine ⟨73015346156956967656719373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97353794875942623542292497 73015346156956967656719373)
      ·
        refine ⟨27380754808858862871269765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73015346156956967656719373 27380754808858862871269765)
        ·
          refine ⟨5133891526661036788363081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27380754808858862871269765 5133891526661036788363081)
          ·
            refine ⟨3850418644995777591272311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5133891526661036788363081 3850418644995777591272311)
            ·
              refine ⟨5775627967493666386908467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850418644995777591272311 5775627967493666386908467)
              ·
                refine ⟨8663441951240499580362701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5775627967493666386908467 8663441951240499580362701)
                ·
                  refine ⟨3248790731715187342636013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8663441951240499580362701 3248790731715187342636013)
                  ·
                    refine ⟨1218296524393195253488505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248790731715187342636013 1218296524393195253488505)
                    ·
                      rfl

theorem cell22_3558936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_3558936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558936 prefixEnd_3558936 := by exact prefixLift 3558936
  have htrace : WordTrace (prefixWord ++ tailWord_3558936) baseStart_3558936 baseEnd_3558936 := by
    simpa [prefixWord, tailWord_3558936, baseEnd_3558936] using wordTrace_append hprefix tailTrace_3558936
  have hstable : (prefixWord ++ tailWord_3558936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558936).length < 2 ^ (prefixWord ++ tailWord_3558936).sum := by decide
  have hdescent : baseEnd_3558936 < baseStart_3558936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558960 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 8]
def baseStart_3558960 : Nat := 118140960795 + 3558960 * 2 ^ 59
def prefixEnd_3558960 : Nat := 4983230072969 + 3 ^ 40 * 3558960 * 2
def baseEnd_3558960 : Nat := 406101580027889063629477

theorem tailTrace_3558960 : CollatzResearch.WordTrace tailWord_3558960 prefixEnd_3558960 406101580027889063629477 := by
  unfold tailWord_3558960
  simp only [CollatzResearch.WordTrace]
  refine ⟨64902967593251608410965167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86537290124335477881286889 64902967593251608410965167)
  ·
    refine ⟨97354451389877412616447751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64902967593251608410965167 97354451389877412616447751)
    ·
      refine ⟨146031677084816118924671627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97354451389877412616447751 146031677084816118924671627)
      ·
        refine ⟨219047515627224178387007441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146031677084816118924671627 219047515627224178387007441)
        ·
          refine ⟨164285636720418133790255581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219047515627224178387007441 164285636720418133790255581)
          ·
            refine ⟨61607113770156800171345843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164285636720418133790255581 61607113770156800171345843)
            ·
              refine ⟨92410670655235200257018765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61607113770156800171345843 92410670655235200257018765)
              ·
                refine ⟨34654001495713200096382037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92410670655235200257018765 34654001495713200096382037)
                ·
                  refine ⟨406101580027889063629477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34654001495713200096382037 406101580027889063629477)
                  ·
                    rfl

theorem cell22_3558960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_3558960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558960 prefixEnd_3558960 := by exact prefixLift 3558960
  have htrace : WordTrace (prefixWord ++ tailWord_3558960) baseStart_3558960 baseEnd_3558960 := by
    simpa [prefixWord, tailWord_3558960, baseEnd_3558960] using wordTrace_append hprefix tailTrace_3558960
  have hstable : (prefixWord ++ tailWord_3558960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558960).length < 2 ^ (prefixWord ++ tailWord_3558960).sum := by decide
  have hdescent : baseEnd_3558960 < baseStart_3558960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558998 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_3558998 : Nat := 118140960795 + 3558998 * 2 ^ 59
def prefixEnd_3558998 : Nat := 4983230072969 + 3 ^ 40 * 3558998 * 2
def baseEnd_3558998 : Nat := 1218317748260247758438315

theorem tailTrace_3558998 : CollatzResearch.WordTrace tailWord_3558998 prefixEnd_3558998 1218317748260247758438315 := by
  unfold tailWord_3558998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8112957572522846831988353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86538214106910366207875765 8112957572522846831988353)
  ·
    refine ⟨6084718179392135123991265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8112957572522846831988353 6084718179392135123991265)
    ·
      refine ⟨4563538634544101342993449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6084718179392135123991265 4563538634544101342993449)
      ·
        refine ⟨3422653975908076007245087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4563538634544101342993449 3422653975908076007245087)
        ·
          refine ⟨5133980963862114010867631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422653975908076007245087 5133980963862114010867631)
          ·
            refine ⟨7700971445793171016301447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5133980963862114010867631 7700971445793171016301447)
            ·
              refine ⟨11551457168689756524452171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7700971445793171016301447 11551457168689756524452171)
              ·
                refine ⟨17327185753034634786678257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11551457168689756524452171 17327185753034634786678257)
                ·
                  refine ⟨12995389314775976090008693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17327185753034634786678257 12995389314775976090008693)
                  ·
                    refine ⟨1218317748260247758438315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12995389314775976090008693 1218317748260247758438315)
                    ·
                      rfl

theorem cell22_3558998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_3558998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3558998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3558998 prefixEnd_3558998 := by exact prefixLift 3558998
  have htrace : WordTrace (prefixWord ++ tailWord_3558998) baseStart_3558998 baseEnd_3558998 := by
    simpa [prefixWord, tailWord_3558998, baseEnd_3558998] using wordTrace_append hprefix tailTrace_3558998
  have hstable : (prefixWord ++ tailWord_3558998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558998).length < 2 ^ (prefixWord ++ tailWord_3558998).sum := by decide
  have hdescent : baseEnd_3558998 < baseStart_3558998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559009 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 2, 3]
def baseStart_3559009 : Nat := 118140960795 + 3559009 * 2 ^ 59
def prefixEnd_3559009 : Nat := 4983230072969 + 3 ^ 40 * 3559009 * 2
def baseEnd_3559009 : Nat := 1218321513785047396413281

theorem tailTrace_3559009 : CollatzResearch.WordTrace tailWord_3559009 prefixEnd_3559009 1218321513785047396413281 := by
  unfold tailWord_3559009
  simp only [CollatzResearch.WordTrace]
  refine ⟨129807722363325698190464081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86538481575550465460309387 129807722363325698190464081)
  ·
    refine ⟨97355791772494273642848061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129807722363325698190464081 97355791772494273642848061)
    ·
      refine ⟨36508421914685352616068023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97355791772494273642848061 36508421914685352616068023)
      ·
        refine ⟨54762632872028028924102035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36508421914685352616068023 54762632872028028924102035)
        ·
          refine ⟨82143949308042043386153053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54762632872028028924102035 82143949308042043386153053)
          ·
            refine ⟨30803980990515766269807395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82143949308042043386153053 30803980990515766269807395)
            ·
              refine ⟨46205971485773649404711093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30803980990515766269807395 46205971485773649404711093)
              ·
                refine ⟨4331809826791279631691665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46205971485773649404711093 4331809826791279631691665)
                ·
                  refine ⟨3248857370093459723768749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4331809826791279631691665 3248857370093459723768749)
                  ·
                    refine ⟨1218321513785047396413281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248857370093459723768749 1218321513785047396413281)
                    ·
                      rfl

theorem cell22_3559009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_3559009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559009 prefixEnd_3559009 := by exact prefixLift 3559009
  have htrace : WordTrace (prefixWord ++ tailWord_3559009) baseStart_3559009 baseEnd_3559009 := by
    simpa [prefixWord, tailWord_3559009, baseEnd_3559009] using wordTrace_append hprefix tailTrace_3559009
  have hstable : (prefixWord ++ tailWord_3559009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559009).length < 2 ^ (prefixWord ++ tailWord_3559009).sum := by decide
  have hdescent : baseEnd_3559009 < baseStart_3559009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559024 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 2, 4]
def baseStart_3559024 : Nat := 118140960795 + 3559024 * 2 ^ 59
def prefixEnd_3559024 : Nat := 4983230072969 + 3 ^ 40 * 3559024 * 2
def baseEnd_3559024 : Nat := 1218326648591592357288235

theorem tailTrace_3559024 : CollatzResearch.WordTrace tailWord_3559024 prefixEnd_3559024 1218326648591592357288235 := by
  unfold tailWord_3559024
  simp only [CollatzResearch.WordTrace]
  refine ⟨64904134729135677876130063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86538846305514237168173417 64904134729135677876130063)
  ·
    refine ⟨97356202093703516814195095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64904134729135677876130063 97356202093703516814195095)
    ·
      refine ⟨146034303140555275221292643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97356202093703516814195095 146034303140555275221292643)
      ·
        refine ⟨219051454710832912831938965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146034303140555275221292643 219051454710832912831938965)
        ·
          refine ⟨10268036939570292788997139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 219051454710832912831938965 10268036939570292788997139)
          ·
            refine ⟨15402055409355439183495709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10268036939570292788997139 15402055409355439183495709)
            ·
              refine ⟨5775770778508289693810891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15402055409355439183495709 5775770778508289693810891)
              ·
                refine ⟨8663656167762434540716337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5775770778508289693810891 8663656167762434540716337)
                ·
                  refine ⟨6497742125821825905537253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8663656167762434540716337 6497742125821825905537253)
                  ·
                    refine ⟨1218326648591592357288235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6497742125821825905537253 1218326648591592357288235)
                    ·
                      rfl

theorem cell22_3559024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_3559024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559024 prefixEnd_3559024 := by exact prefixLift 3559024
  have htrace : WordTrace (prefixWord ++ tailWord_3559024) baseStart_3559024 baseEnd_3559024 := by
    simpa [prefixWord, tailWord_3559024, baseEnd_3559024] using wordTrace_append hprefix tailTrace_3559024
  have hstable : (prefixWord ++ tailWord_3559024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559024).length < 2 ^ (prefixWord ++ tailWord_3559024).sum := by decide
  have hdescent : baseEnd_3559024 < baseStart_3559024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559060 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3559060 : Nat := 118140960795 + 3559060 * 2 ^ 59
def prefixEnd_3559060 : Nat := 4983230072969 + 3 ^ 40 * 3559060 * 2
def baseEnd_3559060 : Nat := 1218338972127300263388125

theorem tailTrace_3559060 : CollatzResearch.WordTrace tailWord_3559060 prefixEnd_3559060 1218338972127300263388125 := by
  unfold tailWord_3559060
  simp only [CollatzResearch.WordTrace]
  refine ⟨64904791243070466950285317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86539721657427289267047089 64904791243070466950285317)
  ·
    refine ⟨12169648358075712553178497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64904791243070466950285317 12169648358075712553178497)
    ·
      refine ⟨9127236268556784414883873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12169648358075712553178497 9127236268556784414883873)
      ·
        refine ⟨6845427201417588311162905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9127236268556784414883873 6845427201417588311162905)
        ·
          refine ⟨5134070401063191233372179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6845427201417588311162905 5134070401063191233372179)
          ·
            refine ⟨7701105601594786850058269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5134070401063191233372179 7701105601594786850058269)
            ·
              refine ⟨2887914600598045068771851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7701105601594786850058269 2887914600598045068771851)
              ·
                refine ⟨4331871900897067603157777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887914600598045068771851 4331871900897067603157777)
                ·
                  refine ⟨3248903925672800702368333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4331871900897067603157777 3248903925672800702368333)
                  ·
                    refine ⟨1218338972127300263388125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248903925672800702368333 1218338972127300263388125)
                    ·
                      rfl

theorem cell22_3559060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3559060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559060 prefixEnd_3559060 := by exact prefixLift 3559060
  have htrace : WordTrace (prefixWord ++ tailWord_3559060) baseStart_3559060 baseEnd_3559060 := by
    simpa [prefixWord, tailWord_3559060, baseEnd_3559060] using wordTrace_append hprefix tailTrace_3559060
  have hstable : (prefixWord ++ tailWord_3559060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559060).length < 2 ^ (prefixWord ++ tailWord_3559060).sum := by decide
  have hdescent : baseEnd_3559060 < baseStart_3559060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559144 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 3, 5]
def baseStart_3559144 : Nat := 118140960795 + 3559144 * 2 ^ 59
def prefixEnd_3559144 : Nat := 4983230072969 + 3 ^ 40 * 3559144 * 2
def baseEnd_3559144 : Nat := 1218367727043952044287867

theorem tailTrace_3559144 : CollatzResearch.WordTrace tailWord_3559144 prefixEnd_3559144 1218367727043952044287867 := by
  unfold tailWord_3559144
  simp only [CollatzResearch.WordTrace]
  refine ⟨64906323108918308123314243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86541764145224410831085657 64906323108918308123314243)
  ·
    refine ⟨97359484663377462184971365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64906323108918308123314243 97359484663377462184971365)
    ·
      refine ⟨18254903374383274159682131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97359484663377462184971365 18254903374383274159682131)
      ·
        refine ⟨27382355061574911239523197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18254903374383274159682131 27382355061574911239523197)
        ·
          refine ⟨10268383148090591714821199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27382355061574911239523197 10268383148090591714821199)
          ·
            refine ⟨15402574722135887572231799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10268383148090591714821199 15402574722135887572231799)
            ·
              refine ⟨23103862083203831358347699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15402574722135887572231799 23103862083203831358347699)
              ·
                refine ⟨34655793124805747037521549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23103862083203831358347699 34655793124805747037521549)
                ·
                  refine ⟨12995922421802155139070581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34655793124805747037521549 12995922421802155139070581)
                  ·
                    refine ⟨1218367727043952044287867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12995922421802155139070581 1218367727043952044287867)
                    ·
                      rfl

theorem cell22_3559144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_3559144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559144 prefixEnd_3559144 := by exact prefixLift 3559144
  have htrace : WordTrace (prefixWord ++ tailWord_3559144) baseStart_3559144 baseEnd_3559144 := by
    simpa [prefixWord, tailWord_3559144, baseEnd_3559144] using wordTrace_append hprefix tailTrace_3559144
  have hstable : (prefixWord ++ tailWord_3559144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559144).length < 2 ^ (prefixWord ++ tailWord_3559144).sum := by decide
  have hdescent : baseEnd_3559144 < baseStart_3559144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559159 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 2, 4]
def baseStart_3559159 : Nat := 118140960795 + 3559159 * 2 ^ 59
def prefixEnd_3559159 : Nat := 4983230072969 + 3 ^ 40 * 3559159 * 2
def baseEnd_3559159 : Nat := 1218372861850497005162821

theorem tailTrace_3559159 : CollatzResearch.WordTrace tailWord_3559159 prefixEnd_3559159 1218372861850497005162821 := by
  unfold tailWord_3559159
  simp only [CollatzResearch.WordTrace]
  refine ⟨129813193312782273808424531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86542128875188182538949687 129813193312782273808424531)
  ·
    refine ⟨194719789969173410712636797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129813193312782273808424531 194719789969173410712636797)
    ·
      refine ⟨73019921238440029017238799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194719789969173410712636797 73019921238440029017238799)
      ·
        refine ⟨109529881857660043525858199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73019921238440029017238799 109529881857660043525858199)
        ·
          refine ⟨164294822786490065288787299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109529881857660043525858199 164294822786490065288787299)
          ·
            refine ⟨246442234179735097933180949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164294822786490065288787299 246442234179735097933180949)
            ·
              refine ⟨11551979727175082715617857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 246442234179735097933180949 11551979727175082715617857)
              ·
                refine ⟨8663984795381312036713393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11551979727175082715617857 8663984795381312036713393)
                ·
                  refine ⟨6497988596535984027535045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8663984795381312036713393 6497988596535984027535045)
                  ·
                    refine ⟨1218372861850497005162821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6497988596535984027535045 1218372861850497005162821)
                    ·
                      rfl

theorem cell22_3559159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_3559159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559159 prefixEnd_3559159 := by exact prefixLift 3559159
  have htrace : WordTrace (prefixWord ++ tailWord_3559159) baseStart_3559159 baseEnd_3559159 := by
    simpa [prefixWord, tailWord_3559159, baseEnd_3559159] using wordTrace_append hprefix tailTrace_3559159
  have hstable : (prefixWord ++ tailWord_3559159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559159).length < 2 ^ (prefixWord ++ tailWord_3559159).sum := by decide
  have hdescent : baseEnd_3559159 < baseStart_3559159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559191 : List Nat := [1, 1, 3, 4, 2, 2, 3, 6]
def baseStart_3559191 : Nat := 118140960795 + 3559191 * 2 ^ 59
def prefixEnd_3559191 : Nat := 4983230072969 + 3 ^ 40 * 3559191 * 2
def baseEnd_3559191 : Nat := 135375979567162176484747

theorem tailTrace_3559191 : CollatzResearch.WordTrace tailWord_3559191 prefixEnd_3559191 135375979567162176484747 := by
  unfold tailWord_3559191
  simp only [CollatzResearch.WordTrace]
  refine ⟨129814360448666343273589427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86542906965777562182392951 129814360448666343273589427)
  ·
    refine ⟨194721540672999514910384141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129814360448666343273589427 194721540672999514910384141)
    ·
      refine ⟨73020577752374818091394053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194721540672999514910384141 73020577752374818091394053)
      ·
        refine ⟨13691358328570278392136385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73020577752374818091394053 13691358328570278392136385)
        ·
          refine ⟨10268518746427708794102289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13691358328570278392136385 10268518746427708794102289)
          ·
            refine ⟨7701389059820781595576717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10268518746427708794102289 7701389059820781595576717)
            ·
              refine ⟨2888020897432793098341269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7701389059820781595576717 2888020897432793098341269)
              ·
                refine ⟨135375979567162176484747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2888020897432793098341269 135375979567162176484747)
                ·
                  rfl

theorem cell22_3559191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 6].length) (baseStart_3559191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559191 prefixEnd_3559191 := by exact prefixLift 3559191
  have htrace : WordTrace (prefixWord ++ tailWord_3559191) baseStart_3559191 baseEnd_3559191 := by
    simpa [prefixWord, tailWord_3559191, baseEnd_3559191] using wordTrace_append hprefix tailTrace_3559191
  have hstable : (prefixWord ++ tailWord_3559191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559191).length < 2 ^ (prefixWord ++ tailWord_3559191).sum := by decide
  have hdescent : baseEnd_3559191 < baseStart_3559191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559274 : List Nat := [3, 1, 3, 4, 1, 1, 3, 2, 1, 3]
def baseStart_3559274 : Nat := 118140960795 + 3559274 * 2 ^ 59
def prefixEnd_3559274 : Nat := 4983230072969 + 3 ^ 40 * 3559274 * 2
def baseEnd_3559274 : Nat := 1218412228700675038537469

theorem tailTrace_3559274 : CollatzResearch.WordTrace tailWord_3559274 prefixEnd_3559274 1218412228700675038537469 := by
  unfold tailWord_3559274
  simp only [CollatzResearch.WordTrace]
  refine ⟨32454346926841412112215219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86544925138243765632573917 32454346926841412112215219)
  ·
    refine ⟨48681520390262118168322829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32454346926841412112215219 48681520390262118168322829)
    ·
      refine ⟨18255570146348294313121061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48681520390262118168322829 18255570146348294313121061)
      ·
        refine ⟨3422919402440305183710199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18255570146348294313121061 3422919402440305183710199)
        ·
          refine ⟨5134379103660457775565299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422919402440305183710199 5134379103660457775565299)
          ·
            refine ⟨7701568655490686663347949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5134379103660457775565299 7701568655490686663347949)
            ·
              refine ⟨2888088245809007498755481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7701568655490686663347949 2888088245809007498755481)
              ·
                refine ⟨2166066184356755624066611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888088245809007498755481 2166066184356755624066611)
                ·
                  refine ⟨3249099276535133436099917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166066184356755624066611 3249099276535133436099917)
                  ·
                    refine ⟨1218412228700675038537469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249099276535133436099917 1218412228700675038537469)
                    ·
                      rfl

theorem cell22_3559274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_3559274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559274 prefixEnd_3559274 := by exact prefixLift 3559274
  have htrace : WordTrace (prefixWord ++ tailWord_3559274) baseStart_3559274 baseEnd_3559274 := by
    simpa [prefixWord, tailWord_3559274, baseEnd_3559274] using wordTrace_append hprefix tailTrace_3559274
  have hstable : (prefixWord ++ tailWord_3559274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559274).length < 2 ^ (prefixWord ++ tailWord_3559274).sum := by decide
  have hdescent : baseEnd_3559274 < baseStart_3559274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559358 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_3559358 : Nat := 118140960795 + 3559358 * 2 ^ 59
def prefixEnd_3559358 : Nat := 4983230072969 + 3 ^ 40 * 3559358 * 2
def baseEnd_3559358 : Nat := 1218440983617326819437211

theorem tailTrace_3559358 : CollatzResearch.WordTrace tailWord_3559358 prefixEnd_3559358 1218440983617326819437211 := by
  unfold tailWord_3559358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16227556429882666349364841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86546967626040887196612485 16227556429882666349364841)
  ·
    refine ⟨12170667322411999762023631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16227556429882666349364841 12170667322411999762023631)
    ·
      refine ⟨18256000983617999643035447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12170667322411999762023631 18256000983617999643035447)
      ·
        refine ⟨27384001475426999464553171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18256000983617999643035447 27384001475426999464553171)
        ·
          refine ⟨41076002213140499196829757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27384001475426999464553171 41076002213140499196829757)
          ·
            refine ⟨15403500829927687198811159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41076002213140499196829757 15403500829927687198811159)
            ·
              refine ⟨23105251244891530798216739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15403500829927687198811159 23105251244891530798216739)
              ·
                refine ⟨34657876867337296197325109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23105251244891530798216739 34657876867337296197325109)
                ·
                  refine ⟨3249175956312871518499229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34657876867337296197325109 3249175956312871518499229)
                  ·
                    refine ⟨1218440983617326819437211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249175956312871518499229 1218440983617326819437211)
                    ·
                      rfl

theorem cell22_3559358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_3559358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559358 prefixEnd_3559358 := by exact prefixLift 3559358
  have htrace : WordTrace (prefixWord ++ tailWord_3559358) baseStart_3559358 baseEnd_3559358 := by
    simpa [prefixWord, tailWord_3559358, baseEnd_3559358] using wordTrace_append hprefix tailTrace_3559358
  have hstable : (prefixWord ++ tailWord_3559358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559358).length < 2 ^ (prefixWord ++ tailWord_3559358).sum := by decide
  have hdescent : baseEnd_3559358 < baseStart_3559358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559375 : List Nat := [1, 1, 2, 1, 1, 5, 4, 3, 1, 3]
def baseStart_3559375 : Nat := 118140960795 + 3559375 * 2 ^ 59
def prefixEnd_3559375 : Nat := 4983230072969 + 3 ^ 40 * 3559375 * 2
def baseEnd_3559375 : Nat := 1218446803064744441762159

theorem tailTrace_3559375 : CollatzResearch.WordTrace tailWord_3559375 prefixEnd_3559375 1218446803064744441762159 := by
  unfold tailWord_3559375
  simp only [CollatzResearch.WordTrace]
  refine ⟨129821071479999742698287579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86547380986666495132191719 129821071479999742698287579)
  ·
    refine ⟨194731607219999614047431369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129821071479999742698287579 194731607219999614047431369)
    ·
      refine ⟨146048705414999710535573527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194731607219999614047431369 146048705414999710535573527)
      ·
        refine ⟨219073058122499565803360291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146048705414999710535573527 219073058122499565803360291)
        ·
          refine ⟨328609587183749348705040437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219073058122499565803360291 328609587183749348705040437)
          ·
            refine ⟨30807148798476501441097541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 328609587183749348705040437 30807148798476501441097541)
            ·
              refine ⟨5776340399714344020205789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30807148798476501441097541 5776340399714344020205789)
              ·
                refine ⟨2166127649892879007577171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5776340399714344020205789 2166127649892879007577171)
                ·
                  refine ⟨3249191474839318511365757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166127649892879007577171 3249191474839318511365757)
                  ·
                    refine ⟨1218446803064744441762159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249191474839318511365757 1218446803064744441762159)
                    ·
                      rfl

theorem cell22_3559375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 1, 3].length) (baseStart_3559375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559375 prefixEnd_3559375 := by exact prefixLift 3559375
  have htrace : WordTrace (prefixWord ++ tailWord_3559375) baseStart_3559375 baseEnd_3559375 := by
    simpa [prefixWord, tailWord_3559375, baseEnd_3559375] using wordTrace_append hprefix tailTrace_3559375
  have hstable : (prefixWord ++ tailWord_3559375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559375).length < 2 ^ (prefixWord ++ tailWord_3559375).sum := by decide
  have hdescent : baseEnd_3559375 < baseStart_3559375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559416 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 6]
def baseStart_3559416 : Nat := 118140960795 + 3559416 * 2 ^ 59
def prefixEnd_3559416 : Nat := 4983230072969 + 3 ^ 40 * 3559416 * 2
def baseEnd_3559416 : Nat := 406153612734211333829011

theorem tailTrace_3559416 : CollatzResearch.WordTrace tailWord_3559416 prefixEnd_3559416 406153612734211333829011 := by
  unfold tailWord_3559416
  simp only [CollatzResearch.WordTrace]
  refine ⟨64911283436425603350265051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86548377915234137800353401 64911283436425603350265051)
  ·
    refine ⟨97366925154638405025397577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64911283436425603350265051 97366925154638405025397577)
    ·
      refine ⟨73025193865978803769048183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97366925154638405025397577 73025193865978803769048183)
      ·
        refine ⟨109537790798968205653572275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73025193865978803769048183 109537790798968205653572275)
        ·
          refine ⟨164306686198452308480358413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109537790798968205653572275 164306686198452308480358413)
          ·
            refine ⟨61615007324419615680134405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164306686198452308480358413 61615007324419615680134405)
            ·
              refine ⟨11552813873328677940025201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61615007324419615680134405 11552813873328677940025201)
              ·
                refine ⟨8664610404996508455018901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11552813873328677940025201 8664610404996508455018901)
                ·
                  refine ⟨406153612734211333829011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8664610404996508455018901 406153612734211333829011)
                  ·
                    rfl

theorem cell22_3559416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_3559416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559416 prefixEnd_3559416 := by exact prefixLift 3559416
  have htrace : WordTrace (prefixWord ++ tailWord_3559416) baseStart_3559416 baseEnd_3559416 := by
    simpa [prefixWord, tailWord_3559416, baseEnd_3559416] using wordTrace_append hprefix tailTrace_3559416
  have hstable : (prefixWord ++ tailWord_3559416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559416).length < 2 ^ (prefixWord ++ tailWord_3559416).sum := by decide
  have hdescent : baseEnd_3559416 < baseStart_3559416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559448 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 4, 3]
def baseStart_3559448 : Nat := 118140960795 + 3559448 * 2 ^ 59
def prefixEnd_3559448 : Nat := 4983230072969 + 3 ^ 40 * 3559448 * 2
def baseEnd_3559448 : Nat := 1218471792456596584686935

theorem tailTrace_3559448 : CollatzResearch.WordTrace tailWord_3559448 prefixEnd_3559448 1218471792456596584686935 := by
  unfold tailWord_3559448
  simp only [CollatzResearch.WordTrace]
  refine ⟨64911867004367638082847499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86549156005823517443796665 64911867004367638082847499)
  ·
    refine ⟨97367800506551457124271249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64911867004367638082847499 97367800506551457124271249)
    ·
      refine ⟨73025850379913592843203437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97367800506551457124271249 73025850379913592843203437)
      ·
        refine ⟨27384693892467597316201289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73025850379913592843203437 27384693892467597316201289)
        ·
          refine ⟨20538520419350697987150967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27384693892467597316201289 20538520419350697987150967)
          ·
            refine ⟨30807780629026046980726451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20538520419350697987150967 30807780629026046980726451)
            ·
              refine ⟨46211670943539070471089677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30807780629026046980726451 46211670943539070471089677)
              ·
                refine ⟨17329376603827151426658629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46211670943539070471089677 17329376603827151426658629)
                ·
                  refine ⟨3249258113217590892498493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17329376603827151426658629 3249258113217590892498493)
                  ·
                    refine ⟨1218471792456596584686935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249258113217590892498493 1218471792456596584686935)
                    ·
                      rfl

theorem cell22_3559448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_3559448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559448 prefixEnd_3559448 := by exact prefixLift 3559448
  have htrace : WordTrace (prefixWord ++ tailWord_3559448) baseStart_3559448 baseEnd_3559448 := by
    simpa [prefixWord, tailWord_3559448, baseEnd_3559448] using wordTrace_append hprefix tailTrace_3559448
  have hstable : (prefixWord ++ tailWord_3559448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559448).length < 2 ^ (prefixWord ++ tailWord_3559448).sum := by decide
  have hdescent : baseEnd_3559448 < baseStart_3559448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559461 : List Nat := [1, 3, 1, 2, 2, 3, 1, 9]
def baseStart_3559461 : Nat := 118140960795 + 3559461 * 2 ^ 59
def prefixEnd_3559461 : Nat := 4983230072969 + 3 ^ 40 * 3559461 * 2
def baseEnd_3559461 : Nat := 135386249180252098234655

theorem tailTrace_3559461 : CollatzResearch.WordTrace tailWord_3559461 prefixEnd_3559461 135386249180252098234655 := by
  unfold tailWord_3559461
  simp only [CollatzResearch.WordTrace]
  refine ⟨129824208157688179385918237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86549472105125452923945491 129824208157688179385918237)
  ·
    refine ⟨48684078059133067269719339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129824208157688179385918237 48684078059133067269719339)
    ·
      refine ⟨73026117088699600904579009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48684078059133067269719339 73026117088699600904579009)
      ·
        refine ⟨54769587816524700678434257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73026117088699600904579009 54769587816524700678434257)
        ·
          refine ⟨41077190862393525508825693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54769587816524700678434257 41077190862393525508825693)
          ·
            refine ⟨15403946573397572065809635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41077190862393525508825693 15403946573397572065809635)
            ·
              refine ⟨23105919860096358098714453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15403946573397572065809635 23105919860096358098714453)
              ·
                refine ⟨135386249180252098234655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23105919860096358098714453 135386249180252098234655)
                ·
                  rfl

theorem cell22_3559461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 9].length) (baseStart_3559461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559461 prefixEnd_3559461 := by exact prefixLift 3559461
  have htrace : WordTrace (prefixWord ++ tailWord_3559461) baseStart_3559461 baseEnd_3559461 := by
    simpa [prefixWord, tailWord_3559461, baseEnd_3559461] using wordTrace_append hprefix tailTrace_3559461
  have hstable : (prefixWord ++ tailWord_3559461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559461).length < 2 ^ (prefixWord ++ tailWord_3559461).sum := by decide
  have hdescent : baseEnd_3559461 < baseStart_3559461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559478 : List Nat := [5, 1, 2, 1, 1, 1, 1, 10]
def baseStart_3559478 : Nat := 118140960795 + 3559478 * 2 ^ 59
def prefixEnd_3559478 : Nat := 4983230072969 + 3 ^ 40 * 3559478 * 2
def baseEnd_3559478 : Nat := 135386895785520722937427

theorem tailTrace_3559478 : CollatzResearch.WordTrace tailWord_3559478 prefixEnd_3559478 135386895785520722937427 := by
  unfold tailWord_3559478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8114051762414161955580443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86549885465751060859524725 8114051762414161955580443)
  ·
    refine ⟨12171077643621242933370665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8114051762414161955580443 12171077643621242933370665)
    ·
      refine ⟨9128308232715932200027999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12171077643621242933370665 9128308232715932200027999)
      ·
        refine ⟨13692462349073898300041999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9128308232715932200027999 13692462349073898300041999)
        ·
          refine ⟨20538693523610847450062999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13692462349073898300041999 20538693523610847450062999)
          ·
            refine ⟨30808040285416271175094499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20538693523610847450062999 30808040285416271175094499)
            ·
              refine ⟨46212060428124406762641749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30808040285416271175094499 46212060428124406762641749)
              ·
                refine ⟨135386895785520722937427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46212060428124406762641749 135386895785520722937427)
                ·
                  rfl

theorem cell22_3559478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_3559478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559478 prefixEnd_3559478 := by exact prefixLift 3559478
  have htrace : WordTrace (prefixWord ++ tailWord_3559478) baseStart_3559478 baseEnd_3559478 := by
    simpa [prefixWord, tailWord_3559478, baseEnd_3559478] using wordTrace_append hprefix tailTrace_3559478
  have hstable : (prefixWord ++ tailWord_3559478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559478).length < 2 ^ (prefixWord ++ tailWord_3559478).sum := by decide
  have hdescent : baseEnd_3559478 < baseStart_3559478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559480 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 2, 4]
def baseStart_3559480 : Nat := 118140960795 + 3559480 * 2 ^ 59
def prefixEnd_3559480 : Nat := 4983230072969 + 3 ^ 40 * 3559480 * 2
def baseEnd_3559480 : Nat := 1218482746710559167886837

theorem tailTrace_3559480 : CollatzResearch.WordTrace tailWord_3559480 prefixEnd_3559480 1218482746710559167886837 := by
  unfold tailWord_3559480
  simp only [CollatzResearch.WordTrace]
  refine ⟨64912450572309672815429947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86549934096412897087239929 64912450572309672815429947)
  ·
    refine ⟨97368675858464509223144921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64912450572309672815429947 97368675858464509223144921)
    ·
      refine ⟨73026506893848381917358691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97368675858464509223144921 73026506893848381917358691)
      ·
        refine ⟨109539760340772572876038037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73026506893848381917358691 109539760340772572876038037)
        ·
          refine ⟨5134676265973714353564283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109539760340772572876038037 5134676265973714353564283)
          ·
            refine ⟨7702014398960571530346425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5134676265973714353564283 7702014398960571530346425)
            ·
              refine ⟨5776510799220428647759819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7702014398960571530346425 5776510799220428647759819)
              ·
                refine ⟨8664766198830642971639729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776510799220428647759819 8664766198830642971639729)
                ·
                  refine ⟨6498574649122982228729797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8664766198830642971639729 6498574649122982228729797)
                  ·
                    refine ⟨1218482746710559167886837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6498574649122982228729797 1218482746710559167886837)
                    ·
                      rfl

theorem cell22_3559480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_3559480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559480 prefixEnd_3559480 := by exact prefixLift 3559480
  have htrace : WordTrace (prefixWord ++ tailWord_3559480) baseStart_3559480 baseEnd_3559480 := by
    simpa [prefixWord, tailWord_3559480, baseEnd_3559480] using wordTrace_append hprefix tailTrace_3559480
  have hstable : (prefixWord ++ tailWord_3559480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559480).length < 2 ^ (prefixWord ++ tailWord_3559480).sum := by decide
  have hdescent : baseEnd_3559480 < baseStart_3559480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559523 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 5]
def baseStart_3559523 : Nat := 118140960795 + 3559523 * 2 ^ 59
def prefixEnd_3559523 : Nat := 4983230072969 + 3 ^ 40 * 3559523 * 2
def baseEnd_3559523 : Nat := 406165822163107129687235

theorem tailTrace_3559523 : CollatzResearch.WordTrace tailWord_3559523 prefixEnd_3559523 406165822163107129687235 := by
  unfold tailWord_3559523
  simp only [CollatzResearch.WordTrace]
  refine ⟨129826469483463563974675223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86550979655642375983116815 129826469483463563974675223)
  ·
    refine ⟨194739704225195345962012835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129826469483463563974675223 194739704225195345962012835)
    ·
      refine ⟨292109556337793018943019253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194739704225195345962012835 292109556337793018943019253)
      ·
        refine ⟨27385270906668095525908055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292109556337793018943019253 27385270906668095525908055)
        ·
          refine ⟨41077906360002143288862083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27385270906668095525908055 41077906360002143288862083)
          ·
            refine ⟨61616859540003214933293125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41077906360002143288862083 61616859540003214933293125)
            ·
              refine ⟨11553161163750602799992461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61616859540003214933293125 11553161163750602799992461)
              ·
                refine ⟨4332435436406476049997173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11553161163750602799992461 4332435436406476049997173)
                ·
                  refine ⟨406165822163107129687235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4332435436406476049997173 406165822163107129687235)
                  ·
                    rfl

theorem cell22_3559523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 5].length) (baseStart_3559523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559523 prefixEnd_3559523 := by exact prefixLift 3559523
  have htrace : WordTrace (prefixWord ++ tailWord_3559523) baseStart_3559523 baseEnd_3559523 := by
    simpa [prefixWord, tailWord_3559523, baseEnd_3559523] using wordTrace_append hprefix tailTrace_3559523
  have hstable : (prefixWord ++ tailWord_3559523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559523).length < 2 ^ (prefixWord ++ tailWord_3559523).sum := by decide
  have hdescent : baseEnd_3559523 < baseStart_3559523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559568 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 6]
def baseStart_3559568 : Nat := 118140960795 + 3559568 * 2 ^ 59
def prefixEnd_3559568 : Nat := 4983230072969 + 3 ^ 40 * 3559568 * 2
def baseEnd_3559568 : Nat := 406170956969652090562189

theorem tailTrace_3559568 : CollatzResearch.WordTrace tailWord_3559568 prefixEnd_3559568 406170956969652090562189 := by
  unfold tailWord_3559568
  simp only [CollatzResearch.WordTrace]
  refine ⟨64914055384150268330031679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86552073845533691106708905 64914055384150268330031679)
  ·
    refine ⟨97371083076225402495047519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64914055384150268330031679 97371083076225402495047519)
    ·
      refine ⟨146056624614338103742571279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97371083076225402495047519 146056624614338103742571279)
      ·
        refine ⟨219084936921507155613856919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146056624614338103742571279 219084936921507155613856919)
        ·
          refine ⟨328627405382260733420785379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219084936921507155613856919 328627405382260733420785379)
          ·
            refine ⟨492941108073391100131178069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328627405382260733420785379 492941108073391100131178069)
            ·
              refine ⟨5776653610235051954662243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 492941108073391100131178069 5776653610235051954662243)
              ·
                refine ⟨8664980415352577931993365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776653610235051954662243 8664980415352577931993365)
                ·
                  refine ⟨406170956969652090562189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8664980415352577931993365 406170956969652090562189)
                  ·
                    rfl

theorem cell22_3559568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_3559568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559568 prefixEnd_3559568 := by exact prefixLift 3559568
  have htrace : WordTrace (prefixWord ++ tailWord_3559568) baseStart_3559568 baseEnd_3559568 := by
    simpa [prefixWord, tailWord_3559568, baseEnd_3559568] using wordTrace_append hprefix tailTrace_3559568
  have hstable : (prefixWord ++ tailWord_3559568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559568).length < 2 ^ (prefixWord ++ tailWord_3559568).sum := by decide
  have hdescent : baseEnd_3559568 < baseStart_3559568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559630 : List Nat := [4, 1, 1, 1, 4, 2, 2, 7]
def baseStart_3559630 : Nat := 118140960795 + 3559630 * 2 ^ 59
def prefixEnd_3559630 : Nat := 4983230072969 + 3 ^ 40 * 3559630 * 2
def baseEnd_3559630 : Nat := 135392677197334308515153

theorem tailTrace_3559630 : CollatzResearch.WordTrace tailWord_3559630 prefixEnd_3559630 135392677197334308515153 := by
  unfold tailWord_3559630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16228796511759490156102543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86553581396050614165880229 16228796511759490156102543)
  ·
    refine ⟨24343194767639235234153815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16228796511759490156102543 24343194767639235234153815)
    ·
      refine ⟨36514792151458852851230723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24343194767639235234153815 36514792151458852851230723)
      ·
        refine ⟨54772188227188279276846085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36514792151458852851230723 54772188227188279276846085)
        ·
          refine ⟨10269785292597802364408641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54772188227188279276846085 10269785292597802364408641)
          ·
            refine ⟨7702338969448351773306481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10269785292597802364408641 7702338969448351773306481)
            ·
              refine ⟨5776754227086263829979861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7702338969448351773306481 5776754227086263829979861)
              ·
                refine ⟨135392677197334308515153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5776754227086263829979861 135392677197334308515153)
                ·
                  rfl

theorem cell22_3559630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_3559630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559630 prefixEnd_3559630 := by exact prefixLift 3559630
  have htrace : WordTrace (prefixWord ++ tailWord_3559630) baseStart_3559630 baseEnd_3559630 := by
    simpa [prefixWord, tailWord_3559630, baseEnd_3559630] using wordTrace_append hprefix tailTrace_3559630
  have hstable : (prefixWord ++ tailWord_3559630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559630).length < 2 ^ (prefixWord ++ tailWord_3559630).sum := by decide
  have hdescent : baseEnd_3559630 < baseStart_3559630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559634 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_3559634 : Nat := 118140960795 + 3559634 * 2 ^ 59
def prefixEnd_3559634 : Nat := 4983230072969 + 3 ^ 40 * 3559634 * 2
def baseEnd_3559634 : Nat := 1218535464057754099536365

theorem tailTrace_3559634 : CollatzResearch.WordTrace tailWord_3559634 prefixEnd_3559634 1218535464057754099536365 := by
  unfold tailWord_3559634
  simp only [CollatzResearch.WordTrace]
  refine ⟨32457629496515357482991489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86553678657374286621310637 32457629496515357482991489)
  ·
    refine ⟨24343222122386518112243617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32457629496515357482991489 24343222122386518112243617)
    ·
      refine ⟨18257416591789888584182713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24343222122386518112243617 18257416591789888584182713)
      ·
        refine ⟨13693062443842416438137035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18257416591789888584182713 13693062443842416438137035)
        ·
          refine ⟨20539593665763624657205553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13693062443842416438137035 20539593665763624657205553)
          ·
            refine ⟨15404695249322718492904165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20539593665763624657205553 15404695249322718492904165)
            ·
              refine ⟨2888380359248009717419531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15404695249322718492904165 2888380359248009717419531)
              ·
                refine ⟨4332570538872014576129297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888380359248009717419531 4332570538872014576129297)
                ·
                  refine ⟨3249427904154010932096973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4332570538872014576129297 3249427904154010932096973)
                  ·
                    refine ⟨1218535464057754099536365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249427904154010932096973 1218535464057754099536365)
                    ·
                      rfl

theorem cell22_3559634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_3559634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559634 prefixEnd_3559634 := by exact prefixLift 3559634
  have htrace : WordTrace (prefixWord ++ tailWord_3559634) baseStart_3559634 baseEnd_3559634 := by
    simpa [prefixWord, tailWord_3559634, baseEnd_3559634] using wordTrace_append hprefix tailTrace_3559634
  have hstable : (prefixWord ++ tailWord_3559634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559634).length < 2 ^ (prefixWord ++ tailWord_3559634).sum := by decide
  have hdescent : baseEnd_3559634 < baseStart_3559634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559726 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_3559726 : Nat := 118140960795 + 3559726 * 2 ^ 59
def prefixEnd_3559726 : Nat := 4983230072969 + 3 ^ 40 * 3559726 * 2
def baseEnd_3559726 : Nat := 406188985845965508745361

theorem tailTrace_3559726 : CollatzResearch.WordTrace tailWord_3559726 prefixEnd_3559726 406188985845965508745361 := by
  unfold tailWord_3559726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16229234187716016205539379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86555915667818753096210021 16229234187716016205539379)
  ·
    refine ⟨24343851281574024308309069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16229234187716016205539379 24343851281574024308309069)
    ·
      refine ⟨9128944230590259115615901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24343851281574024308309069 9128944230590259115615901)
      ·
        refine ⟨3423354086471347168355963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9128944230590259115615901 3423354086471347168355963)
        ·
          refine ⟨5135031129707020752533945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423354086471347168355963 5135031129707020752533945)
          ·
            refine ⟨3851273347280265564400459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5135031129707020752533945 3851273347280265564400459)
            ·
              refine ⟨5776910020920398346600689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851273347280265564400459 5776910020920398346600689)
              ·
                refine ⟨4332682515690298759950517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5776910020920398346600689 4332682515690298759950517)
                ·
                  refine ⟨406188985845965508745361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4332682515690298759950517 406188985845965508745361)
                  ·
                    rfl

theorem cell22_3559726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_3559726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559726 prefixEnd_3559726 := by exact prefixLift 3559726
  have htrace : WordTrace (prefixWord ++ tailWord_3559726) baseStart_3559726 baseEnd_3559726 := by
    simpa [prefixWord, tailWord_3559726, baseEnd_3559726] using wordTrace_append hprefix tailTrace_3559726
  have hstable : (prefixWord ++ tailWord_3559726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559726).length < 2 ^ (prefixWord ++ tailWord_3559726).sum := by decide
  have hdescent : baseEnd_3559726 < baseStart_3559726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559737 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 6]
def baseStart_3559737 : Nat := 118140960795 + 3559737 * 2 ^ 59
def prefixEnd_3559737 : Nat := 4983230072969 + 3 ^ 40 * 3559737 * 2
def baseEnd_3559737 : Nat := 406190241020898721403683

theorem tailTrace_3559737 : CollatzResearch.WordTrace tailWord_3559737 prefixEnd_3559737 406190241020898721403683 := by
  unfold tailWord_3559737
  simp only [CollatzResearch.WordTrace]
  refine ⟨129834274704688278522965465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86556183136458852348643643 129834274704688278522965465)
  ·
    refine ⟨97375706028516208892224099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129834274704688278522965465 97375706028516208892224099)
    ·
      refine ⟨146063559042774313338336149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97375706028516208892224099 146063559042774313338336149)
      ·
        refine ⟨6846729330130045937734507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146063559042774313338336149 6846729330130045937734507)
        ·
          refine ⟨10270093995195068906601761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6846729330130045937734507 10270093995195068906601761)
          ·
            refine ⟨7702570496396301679951321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10270093995195068906601761 7702570496396301679951321)
            ·
              refine ⟨5776927872297226259963491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7702570496396301679951321 5776927872297226259963491)
              ·
                refine ⟨8665391808445839389945237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776927872297226259963491 8665391808445839389945237)
                ·
                  refine ⟨406190241020898721403683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8665391808445839389945237 406190241020898721403683)
                  ·
                    rfl

theorem cell22_3559737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_3559737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559737 prefixEnd_3559737 := by exact prefixLift 3559737
  have htrace : WordTrace (prefixWord ++ tailWord_3559737) baseStart_3559737 baseEnd_3559737 := by
    simpa [prefixWord, tailWord_3559737, baseEnd_3559737] using wordTrace_append hprefix tailTrace_3559737
  have hstable : (prefixWord ++ tailWord_3559737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559737).length < 2 ^ (prefixWord ++ tailWord_3559737).sum := by decide
  have hdescent : baseEnd_3559737 < baseStart_3559737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559752 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 2, 3]
def baseStart_3559752 : Nat := 118140960795 + 3559752 * 2 ^ 59
def prefixEnd_3559752 : Nat := 4983230072969 + 3 ^ 40 * 3559752 * 2
def baseEnd_3559752 : Nat := 1218575857869241125086003

theorem tailTrace_3559752 : CollatzResearch.WordTrace tailWord_3559752 prefixEnd_3559752 1218575857869241125086003 := by
  unfold tailWord_3559752
  simp only [CollatzResearch.WordTrace]
  refine ⟨64917410899816968042380755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86556547866422624056507673 64917410899816968042380755)
  ·
    refine ⟨97376116349725452063571133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64917410899816968042380755 97376116349725452063571133)
    ·
      refine ⟨36516043631147044523839175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97376116349725452063571133 36516043631147044523839175)
      ·
        refine ⟨54774065446720566785758763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36516043631147044523839175 54774065446720566785758763)
        ·
          refine ⟨82161098170080850178638145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54774065446720566785758763 82161098170080850178638145)
          ·
            refine ⟨61620823627560637633978609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82161098170080850178638145 61620823627560637633978609)
            ·
              refine ⟨46215617720670478225483957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61620823627560637633978609 46215617720670478225483957)
              ·
                refine ⟨4332714161312857333639121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46215617720670478225483957 4332714161312857333639121)
                ·
                  refine ⟨3249535620984643000229341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4332714161312857333639121 3249535620984643000229341)
                  ·
                    refine ⟨1218575857869241125086003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249535620984643000229341 1218575857869241125086003)
                    ·
                      rfl

theorem cell22_3559752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_3559752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559752 prefixEnd_3559752 := by exact prefixLift 3559752
  have htrace : WordTrace (prefixWord ++ tailWord_3559752) baseStart_3559752 baseEnd_3559752 := by
    simpa [prefixWord, tailWord_3559752, baseEnd_3559752] using wordTrace_append hprefix tailTrace_3559752
  have hstable : (prefixWord ++ tailWord_3559752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559752).length < 2 ^ (prefixWord ++ tailWord_3559752).sum := by decide
  have hdescent : baseEnd_3559752 < baseStart_3559752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559842 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3559842 : Nat := 118140960795 + 3559842 * 2 ^ 59
def prefixEnd_3559842 : Nat := 4983230072969 + 3 ^ 40 * 3559842 * 2
def baseEnd_3559842 : Nat := 1218606666708510890335727

theorem tailTrace_3559842 : CollatzResearch.WordTrace tailWord_3559842 prefixEnd_3559842 1218606666708510890335727 := by
  unfold tailWord_3559842
  simp only [CollatzResearch.WordTrace]
  refine ⟨32459526092326970363884445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86558736246205254303691853 32459526092326970363884445)
  ·
    refine ⟨12172322284622613886456667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32459526092326970363884445 12172322284622613886456667)
    ·
      refine ⟨18258483426933920829685001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12172322284622613886456667 18258483426933920829685001)
      ·
        refine ⟨13693862570200440622263751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18258483426933920829685001 13693862570200440622263751)
        ·
          refine ⟨20540793855300660933395627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13693862570200440622263751 20540793855300660933395627)
          ·
            refine ⟨30811190782950991400093441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20540793855300660933395627 30811190782950991400093441)
            ·
              refine ⟨23108393087213243550070081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30811190782950991400093441 23108393087213243550070081)
              ·
                refine ⟨17331294815409932662552561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23108393087213243550070081 17331294815409932662552561)
                ·
                  refine ⟨12998471111557449496914421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17331294815409932662552561 12998471111557449496914421)
                  ·
                    refine ⟨1218606666708510890335727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12998471111557449496914421 1218606666708510890335727)
                    ·
                      rfl

theorem cell22_3559842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3559842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559842 prefixEnd_3559842 := by exact prefixLift 3559842
  have htrace : WordTrace (prefixWord ++ tailWord_3559842) baseStart_3559842 baseEnd_3559842 := by
    simpa [prefixWord, tailWord_3559842, baseEnd_3559842] using wordTrace_append hprefix tailTrace_3559842
  have hstable : (prefixWord ++ tailWord_3559842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559842).length < 2 ^ (prefixWord ++ tailWord_3559842).sum := by decide
  have hdescent : baseEnd_3559842 < baseStart_3559842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559848 : List Nat := [2, 1, 6, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3559848 : Nat := 118140960795 + 3559848 * 2 ^ 59
def prefixEnd_3559848 : Nat := 4983230072969 + 3 ^ 40 * 3559848 * 2
def baseEnd_3559848 : Nat := 1218608720631128874685709

theorem tailTrace_3559848 : CollatzResearch.WordTrace tailWord_3559848 prefixEnd_3559848 1218608720631128874685709 := by
  unfold tailWord_3559848
  simp only [CollatzResearch.WordTrace]
  refine ⟨64919161603643072240128099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86558882138190762986837465 64919161603643072240128099)
  ·
    refine ⟨97378742405464608360192149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64919161603643072240128099 97378742405464608360192149)
    ·
      refine ⟨4564628550256153516884007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97378742405464608360192149 4564628550256153516884007)
      ·
        refine ⟨6846942825384230275326011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4564628550256153516884007 6846942825384230275326011)
        ·
          refine ⟨10270414238076345412989017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6846942825384230275326011 10270414238076345412989017)
          ·
            refine ⟨7702810678557259059741763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10270414238076345412989017 7702810678557259059741763)
            ·
              refine ⟨11554216017835888589612645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7702810678557259059741763 11554216017835888589612645)
              ·
                refine ⟨2166415503344229110552371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11554216017835888589612645 2166415503344229110552371)
                ·
                  refine ⟨3249623255016343665828557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166415503344229110552371 3249623255016343665828557)
                  ·
                    refine ⟨1218608720631128874685709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249623255016343665828557 1218608720631128874685709)
                    ·
                      rfl

theorem cell22_3559848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3559848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559848 prefixEnd_3559848 := by exact prefixLift 3559848
  have htrace : WordTrace (prefixWord ++ tailWord_3559848) baseStart_3559848 baseEnd_3559848 := by
    simpa [prefixWord, tailWord_3559848, baseEnd_3559848] using wordTrace_append hprefix tailTrace_3559848
  have hstable : (prefixWord ++ tailWord_3559848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559848).length < 2 ^ (prefixWord ++ tailWord_3559848).sum := by decide
  have hdescent : baseEnd_3559848 < baseStart_3559848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559857 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 3, 4]
def baseStart_3559857 : Nat := 118140960795 + 3559857 * 2 ^ 59
def prefixEnd_3559857 : Nat := 4983230072969 + 3 ^ 40 * 3559857 * 2
def baseEnd_3559857 : Nat := 1218611801515055851210681

theorem tailTrace_3559857 : CollatzResearch.WordTrace tailWord_3559857 prefixEnd_3559857 1218611801515055851210681 := by
  unfold tailWord_3559857
  simp only [CollatzResearch.WordTrace]
  refine ⟨129838651464253539017333825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86559100976169026011555883 129838651464253539017333825)
  ·
    refine ⟨97378988598190154263000369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129838651464253539017333825 97378988598190154263000369)
    ·
      refine ⟨73034241448642615697250277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97378988598190154263000369 73034241448642615697250277)
      ·
        refine ⟨13693920271620490443234427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73034241448642615697250277 13693920271620490443234427)
        ·
          refine ⟨20540880407430735664851641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13693920271620490443234427 20540880407430735664851641)
          ·
            refine ⟨15405660305573051748638731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20540880407430735664851641 15405660305573051748638731)
            ·
              refine ⟨23108490458359577622958097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15405660305573051748638731 23108490458359577622958097)
              ·
                refine ⟨17331367843769683217218573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23108490458359577622958097 17331367843769683217218573)
                ·
                  refine ⟨6499262941413631206456965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17331367843769683217218573 6499262941413631206456965)
                  ·
                    refine ⟨1218611801515055851210681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6499262941413631206456965 1218611801515055851210681)
                    ·
                      rfl

theorem cell22_3559857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_3559857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559857 prefixEnd_3559857 := by exact prefixLift 3559857
  have htrace : WordTrace (prefixWord ++ tailWord_3559857) baseStart_3559857 baseEnd_3559857 := by
    simpa [prefixWord, tailWord_3559857, baseEnd_3559857] using wordTrace_append hprefix tailTrace_3559857
  have hstable : (prefixWord ++ tailWord_3559857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559857).length < 2 ^ (prefixWord ++ tailWord_3559857).sum := by decide
  have hdescent : baseEnd_3559857 < baseStart_3559857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559887 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 4, 3]
def baseStart_3559887 : Nat := 118140960795 + 3559887 * 2 ^ 59
def prefixEnd_3559887 : Nat := 4983230072969 + 3 ^ 40 * 3559887 * 2
def baseEnd_3559887 : Nat := 1218622071128145772960589

theorem tailTrace_3559887 : CollatzResearch.WordTrace tailWord_3559887 prefixEnd_3559887 1218622071128145772960589 := by
  unfold tailWord_3559887
  simp only [CollatzResearch.WordTrace]
  refine ⟨129839745654144854140925915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86559830436096569427283943 129839745654144854140925915)
  ·
    refine ⟨194759618481217281211388873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129839745654144854140925915 194759618481217281211388873)
    ·
      refine ⟨146069713860912960908541655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194759618481217281211388873 146069713860912960908541655)
      ·
        refine ⟨219104570791369441362812483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146069713860912960908541655 219104570791369441362812483)
        ·
          refine ⟨328656856187054162044218725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219104570791369441362812483 328656856187054162044218725)
          ·
            refine ⟨61623160535072655383291011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 328656856187054162044218725 61623160535072655383291011)
            ·
              refine ⟨92434740802608983074936517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61623160535072655383291011 92434740802608983074936517)
              ·
                refine ⟨17331513900489184326550597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92434740802608983074936517 17331513900489184326550597)
                ·
                  refine ⟨3249658856341722061228237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17331513900489184326550597 3249658856341722061228237)
                  ·
                    refine ⟨1218622071128145772960589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249658856341722061228237 1218622071128145772960589)
                    ·
                      rfl

theorem cell22_3559887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 3].length) (baseStart_3559887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559887 prefixEnd_3559887 := by exact prefixLift 3559887
  have htrace : WordTrace (prefixWord ++ tailWord_3559887) baseStart_3559887 baseEnd_3559887 := by
    simpa [prefixWord, tailWord_3559887, baseEnd_3559887] using wordTrace_append hprefix tailTrace_3559887
  have hstable : (prefixWord ++ tailWord_3559887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559887).length < 2 ^ (prefixWord ++ tailWord_3559887).sum := by decide
  have hdescent : baseEnd_3559887 < baseStart_3559887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559921 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 2, 3]
def baseStart_3559921 : Nat := 118140960795 + 3559921 * 2 ^ 59
def prefixEnd_3559921 : Nat := 4983230072969 + 3 ^ 40 * 3559921 * 2
def baseEnd_3559921 : Nat := 1218633710022981017610485

theorem tailTrace_3559921 : CollatzResearch.WordTrace tailWord_3559921 prefixEnd_3559921 1218633710022981017610485 := by
  unfold tailWord_3559921
  simp only [CollatzResearch.WordTrace]
  refine ⟨129840985736021677947663617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86560657157347785298442411 129840985736021677947663617)
  ·
    refine ⟨97380739302016258460747713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129840985736021677947663617 97380739302016258460747713)
    ·
      refine ⟨73035554476512193845560785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97380739302016258460747713 73035554476512193845560785)
      ·
        refine ⟨54776665857384145384170589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73035554476512193845560785 54776665857384145384170589)
        ·
          refine ⟨20541249696519054519063971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54776665857384145384170589 20541249696519054519063971)
          ·
            refine ⟨30811874544778581778595957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20541249696519054519063971 30811874544778581778595957)
            ·
              refine ⟨2888613238572992041743371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30811874544778581778595957 2888613238572992041743371)
              ·
                refine ⟨4332919857859488062615057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888613238572992041743371 4332919857859488062615057)
                ·
                  refine ⟨3249689893394616046961293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4332919857859488062615057 3249689893394616046961293)
                  ·
                    refine ⟨1218633710022981017610485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249689893394616046961293 1218633710022981017610485)
                    ·
                      rfl

theorem cell22_3559921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_3559921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559921 prefixEnd_3559921 := by exact prefixLift 3559921
  have htrace : WordTrace (prefixWord ++ tailWord_3559921) baseStart_3559921 baseEnd_3559921 := by
    simpa [prefixWord, tailWord_3559921, baseEnd_3559921] using wordTrace_append hprefix tailTrace_3559921
  have hstable : (prefixWord ++ tailWord_3559921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559921).length < 2 ^ (prefixWord ++ tailWord_3559921).sum := by decide
  have hdescent : baseEnd_3559921 < baseStart_3559921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559962 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_3559962 : Nat := 118140960795 + 3559962 * 2 ^ 59
def prefixEnd_3559962 : Nat := 4983230072969 + 3 ^ 40 * 3559962 * 2
def baseEnd_3559962 : Nat := 406215915053623525778453

theorem tailTrace_3559962 : CollatzResearch.WordTrace tailWord_3559962 prefixEnd_3559962 406215915053623525778453 := by
  unfold tailWord_3559962
  simp only [CollatzResearch.WordTrace]
  refine ⟨32460620282218285487476535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86561654085915427966604093 32460620282218285487476535)
  ·
    refine ⟨48690930423327428231214803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32460620282218285487476535 48690930423327428231214803)
    ·
      refine ⟨73036395634991142346822205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48690930423327428231214803 73036395634991142346822205)
      ·
        refine ⟨27388648363121678380058327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73036395634991142346822205 27388648363121678380058327)
        ·
          refine ⟨41082972544682517570087491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27388648363121678380058327 41082972544682517570087491)
          ·
            refine ⟨61624458817023776355131237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41082972544682517570087491 61624458817023776355131237)
            ·
              refine ⟨11554586028191958066587107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61624458817023776355131237 11554586028191958066587107)
              ·
                refine ⟨17331879042287937099880661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11554586028191958066587107 17331879042287937099880661)
                ·
                  refine ⟨406215915053623525778453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17331879042287937099880661 406215915053623525778453)
                  ·
                    rfl

theorem cell22_3559962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_3559962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559962 prefixEnd_3559962 := by exact prefixLift 3559962
  have htrace : WordTrace (prefixWord ++ tailWord_3559962) baseStart_3559962 baseEnd_3559962 := by
    simpa [prefixWord, tailWord_3559962, baseEnd_3559962] using wordTrace_append hprefix tailTrace_3559962
  have hstable : (prefixWord ++ tailWord_3559962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559962).length < 2 ^ (prefixWord ++ tailWord_3559962).sum := by decide
  have hdescent : baseEnd_3559962 < baseStart_3559962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559972 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_3559972 : Nat := 118140960795 + 3559972 * 2 ^ 59
def prefixEnd_3559972 : Nat := 4983230072969 + 3 ^ 40 * 3559972 * 2
def baseEnd_3559972 : Nat := 1218651168365233884585329

theorem tailTrace_3559972 : CollatzResearch.WordTrace tailWord_3559972 prefixEnd_3559972 1218651168365233884585329 := by
  unfold tailWord_3559972
  simp only [CollatzResearch.WordTrace]
  refine ⟨64921422929418456828885085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86561897239224609105180113 64921422929418456828885085)
  ·
    refine ⟨24345533598531921310831907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64921422929418456828885085 24345533598531921310831907)
    ·
      refine ⟨36518300397797881966247861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24345533598531921310831907 36518300397797881966247861)
      ·
        refine ⟨3423590662293551434335737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36518300397797881966247861 3423590662293551434335737)
        ·
          refine ⟨2567692996720163575751803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3423590662293551434335737 2567692996720163575751803)
          ·
            refine ⟨3851539495080245363627705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567692996720163575751803 3851539495080245363627705)
            ·
              refine ⟨2888654621310184022720779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3851539495080245363627705 2888654621310184022720779)
              ·
                refine ⟨4332981931965276034081169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888654621310184022720779 4332981931965276034081169)
                ·
                  refine ⟨3249736448973957025560877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4332981931965276034081169 3249736448973957025560877)
                  ·
                    refine ⟨1218651168365233884585329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249736448973957025560877 1218651168365233884585329)
                    ·
                      rfl

theorem cell22_3559972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_3559972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3559972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3559972 prefixEnd_3559972 := by exact prefixLift 3559972
  have htrace : WordTrace (prefixWord ++ tailWord_3559972) baseStart_3559972 baseEnd_3559972 := by
    simpa [prefixWord, tailWord_3559972, baseEnd_3559972] using wordTrace_append hprefix tailTrace_3559972
  have hstable : (prefixWord ++ tailWord_3559972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559972).length < 2 ^ (prefixWord ++ tailWord_3559972).sum := by decide
  have hdescent : baseEnd_3559972 < baseStart_3559972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560039 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 6, 3]
def baseStart_3560039 : Nat := 118140960795 + 3560039 * 2 ^ 59
def prefixEnd_3560039 : Nat := 4983230072969 + 3 ^ 40 * 3560039 * 2
def baseEnd_3560039 : Nat := 1218674103834468043160123

theorem tailTrace_3560039 : CollatzResearch.WordTrace tailWord_3560039 prefixEnd_3560039 1218674103834468043160123 := by
  unfold tailWord_3560039
  simp only [CollatzResearch.WordTrace]
  refine ⟨129845289549594184100459171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86563526366396122733639447 129845289549594184100459171)
  ·
    refine ⟨194767934324391276150688757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129845289549594184100459171 194767934324391276150688757)
    ·
      refine ⟨18259493842911682139127071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194767934324391276150688757 18259493842911682139127071)
      ·
        refine ⟨27389240764367523208690607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18259493842911682139127071 27389240764367523208690607)
        ·
          refine ⟨41083861146551284813035911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27389240764367523208690607 41083861146551284813035911)
          ·
            refine ⟨61625791719826927219553867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41083861146551284813035911 61625791719826927219553867)
            ·
              refine ⟨92438687579740390829330801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61625791719826927219553867 92438687579740390829330801)
              ·
                refine ⟨69329015684805293121998101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92438687579740390829330801 69329015684805293121998101)
                ·
                  refine ⟨3249797610225248115093661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69329015684805293121998101 3249797610225248115093661)
                  ·
                    refine ⟨1218674103834468043160123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249797610225248115093661 1218674103834468043160123)
                    ·
                      rfl

theorem cell22_3560039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_3560039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560039 prefixEnd_3560039 := by exact prefixLift 3560039
  have htrace : WordTrace (prefixWord ++ tailWord_3560039) baseStart_3560039 baseEnd_3560039 := by
    simpa [prefixWord, tailWord_3560039, baseEnd_3560039] using wordTrace_append hprefix tailTrace_3560039
  have hstable : (prefixWord ++ tailWord_3560039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560039).length < 2 ^ (prefixWord ++ tailWord_3560039).sum := by decide
  have hdescent : baseEnd_3560039 < baseStart_3560039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560090 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 1, 5]
def baseStart_3560090 : Nat := 118140960795 + 3560090 * 2 ^ 59
def prefixEnd_3560090 : Nat := 4983230072969 + 3 ^ 40 * 3560090 * 2
def baseEnd_3560090 : Nat := 1218691562176720910134967

theorem tailTrace_3560090 : CollatzResearch.WordTrace tailWord_3560090 prefixEnd_3560090 1218691562176720910134967 := by
  unfold tailWord_3560090
  simp only [CollatzResearch.WordTrace]
  refine ⟨32461787418102354952641431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86564766448272946540377149 32461787418102354952641431)
  ·
    refine ⟨48692681127153532428962147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32461787418102354952641431 48692681127153532428962147)
    ·
      refine ⟨73039021690730298643443221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48692681127153532428962147 73039021690730298643443221)
      ·
        refine ⟨3423704141752982748911401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73039021690730298643443221 3423704141752982748911401)
        ·
          refine ⟨2567778106314737061683551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3423704141752982748911401 2567778106314737061683551)
          ·
            refine ⟨3851667159472105592525327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567778106314737061683551 3851667159472105592525327)
            ·
              refine ⟨5777500739208158388787991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851667159472105592525327 5777500739208158388787991)
              ·
                refine ⟨8666251108812237583181987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5777500739208158388787991 8666251108812237583181987)
                ·
                  refine ⟨12999376663218356374772981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8666251108812237583181987 12999376663218356374772981)
                  ·
                    refine ⟨1218691562176720910134967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12999376663218356374772981 1218691562176720910134967)
                    ·
                      rfl

theorem cell22_3560090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_3560090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560090 prefixEnd_3560090 := by exact prefixLift 3560090
  have htrace : WordTrace (prefixWord ++ tailWord_3560090) baseStart_3560090 baseEnd_3560090 := by
    simpa [prefixWord, tailWord_3560090, baseEnd_3560090] using wordTrace_append hprefix tailTrace_3560090
  have hstable : (prefixWord ++ tailWord_3560090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560090).length < 2 ^ (prefixWord ++ tailWord_3560090).sum := by decide
  have hdescent : baseEnd_3560090 < baseStart_3560090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560148 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 5]
def baseStart_3560148 : Nat := 118140960795 + 3560148 * 2 ^ 59
def prefixEnd_3560148 : Nat := 4983230072969 + 3 ^ 40 * 3560148 * 2
def baseEnd_3560148 : Nat := 406237138920676030728263

theorem tailTrace_3560148 : CollatzResearch.WordTrace tailWord_3560148 prefixEnd_3560148 406237138920676030728263 := by
  unfold tailWord_3560148
  simp only [CollatzResearch.WordTrace]
  refine ⟨64924632553099647858088549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86566176737466197144118065 64924632553099647858088549)
  ·
    refine ⟨12173368603706183973391603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64924632553099647858088549 12173368603706183973391603)
    ·
      refine ⟨18260052905559275960087405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12173368603706183973391603 18260052905559275960087405)
      ·
        refine ⟨6847519839584728485032777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18260052905559275960087405 6847519839584728485032777)
        ·
          refine ⟨5135639879688546363774583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6847519839584728485032777 5135639879688546363774583)
          ·
            refine ⟨7703459819532819545661875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135639879688546363774583 7703459819532819545661875)
            ·
              refine ⟨11555189729299229318492813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7703459819532819545661875 11555189729299229318492813)
              ·
                refine ⟨4333196148487210994434805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11555189729299229318492813 4333196148487210994434805)
                ·
                  refine ⟨406237138920676030728263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4333196148487210994434805 406237138920676030728263)
                  ·
                    rfl

theorem cell22_3560148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_3560148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560148 prefixEnd_3560148 := by exact prefixLift 3560148
  have htrace : WordTrace (prefixWord ++ tailWord_3560148) baseStart_3560148 baseEnd_3560148 := by
    simpa [prefixWord, tailWord_3560148, baseEnd_3560148] using wordTrace_append hprefix tailTrace_3560148
  have hstable : (prefixWord ++ tailWord_3560148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560148).length < 2 ^ (prefixWord ++ tailWord_3560148).sum := by decide
  have hdescent : baseEnd_3560148 < baseStart_3560148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560161 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 3, 4]
def baseStart_3560161 : Nat := 118140960795 + 3560161 * 2 ^ 59
def prefixEnd_3560161 : Nat := 4983230072969 + 3 ^ 40 * 3560161 * 2
def baseEnd_3560161 : Nat := 1218715866927700391609749

theorem tailTrace_3560161 : CollatzResearch.WordTrace tailWord_3560161 prefixEnd_3560161 1218715866927700391609749 := by
  unfold tailWord_3560161
  simp only [CollatzResearch.WordTrace]
  refine ⟨129849739255152198936400337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86566492836768132624266891 129849739255152198936400337)
  ·
    refine ⟨97387304441364149202300253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129849739255152198936400337 97387304441364149202300253)
    ·
      refine ⟨36520239165511555950862595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97387304441364149202300253 36520239165511555950862595)
      ·
        refine ⟨54780358748267333926293893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36520239165511555950862595 54780358748267333926293893)
        ·
          refine ⟨10271317265300125111180105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54780358748267333926293893 10271317265300125111180105)
          ·
            refine ⟨7703487948975093833385079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10271317265300125111180105 7703487948975093833385079)
            ·
              refine ⟨11555231923462640750077619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7703487948975093833385079 11555231923462640750077619)
              ·
                refine ⟨17332847885193961125116429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11555231923462640750077619 17332847885193961125116429)
                ·
                  refine ⟨6499817956947735421918661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17332847885193961125116429 6499817956947735421918661)
                  ·
                    refine ⟨1218715866927700391609749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6499817956947735421918661 1218715866927700391609749)
                    ·
                      rfl

theorem cell22_3560161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_3560161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560161 prefixEnd_3560161 := by exact prefixLift 3560161
  have htrace : WordTrace (prefixWord ++ tailWord_3560161) baseStart_3560161 baseEnd_3560161 := by
    simpa [prefixWord, tailWord_3560161, baseEnd_3560161] using wordTrace_append hprefix tailTrace_3560161
  have hstable : (prefixWord ++ tailWord_3560161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560161).length < 2 ^ (prefixWord ++ tailWord_3560161).sum := by decide
  have hdescent : baseEnd_3560161 < baseStart_3560161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560176 : List Nat := [2, 1, 1, 1, 3, 1, 4, 5, 4]
def baseStart_3560176 : Nat := 118140960795 + 3560176 * 2 ^ 59
def prefixEnd_3560176 : Nat := 4983230072969 + 3 ^ 40 * 3560176 * 2
def baseEnd_3560176 : Nat := 406240333911415117494901

theorem tailTrace_3560176 : CollatzResearch.WordTrace tailWord_3560176 prefixEnd_3560176 406240333911415117494901 := by
  unfold tailWord_3560176
  simp only [CollatzResearch.WordTrace]
  refine ⟨64925143175048928249098191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86566857566731904332130921 64925143175048928249098191)
  ·
    refine ⟨97387714762573392373647287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64925143175048928249098191 97387714762573392373647287)
    ·
      refine ⟨146081572143860088560470931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97387714762573392373647287 146081572143860088560470931)
      ·
        refine ⟨219122358215790132840706397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146081572143860088560470931 219122358215790132840706397)
        ·
          refine ⟨82170884330921299815264899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219122358215790132840706397 82170884330921299815264899)
          ·
            refine ⟨123256326496381949722897349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82170884330921299815264899 123256326496381949722897349)
            ·
              refine ⟨23110561218071615573043253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123256326496381949722897349 23110561218071615573043253)
              ·
                refine ⟨2166615114194213959972805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23110561218071615573043253 2166615114194213959972805)
                ·
                  refine ⟨406240333911415117494901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2166615114194213959972805 406240333911415117494901)
                  ·
                    rfl

theorem cell22_3560176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 4].length) (baseStart_3560176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560176 prefixEnd_3560176 := by exact prefixLift 3560176
  have htrace : WordTrace (prefixWord ++ tailWord_3560176) baseStart_3560176 baseEnd_3560176 := by
    simpa [prefixWord, tailWord_3560176, baseEnd_3560176] using wordTrace_append hprefix tailTrace_3560176
  have hstable : (prefixWord ++ tailWord_3560176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560176).length < 2 ^ (prefixWord ++ tailWord_3560176).sum := by decide
  have hdescent : baseEnd_3560176 < baseStart_3560176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560223 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 2, 4]
def baseStart_3560223 : Nat := 118140960795 + 3560223 * 2 ^ 59
def prefixEnd_3560223 : Nat := 4983230072969 + 3 ^ 40 * 3560223 * 2
def baseEnd_3560223 : Nat := 1218737090794752896559559

theorem tailTrace_3560223 : CollatzResearch.WordTrace tailWord_3560223 prefixEnd_3560223 1218737090794752896559559 := by
  unfold tailWord_3560223
  simp only [CollatzResearch.WordTrace]
  refine ⟨129852000580927583525157323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86568000387285055683438215 129852000580927583525157323)
  ·
    refine ⟨194778000871391375287735985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129852000580927583525157323 194778000871391375287735985)
    ·
      refine ⟨146083500653543531465801989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194778000871391375287735985 146083500653543531465801989)
      ·
        refine ⟨27390656372539412149837873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146083500653543531465801989 27390656372539412149837873)
        ·
          refine ⟨20542992279404559112378405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27390656372539412149837873 20542992279404559112378405)
          ·
            refine ⟨3851811052388354833570951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20542992279404559112378405 3851811052388354833570951)
            ·
              refine ⟨5777716578582532250356427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851811052388354833570951 5777716578582532250356427)
              ·
                refine ⟨8666574867873798375534641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5777716578582532250356427 8666574867873798375534641)
                ·
                  refine ⟨6499931150905348781650981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8666574867873798375534641 6499931150905348781650981)
                  ·
                    refine ⟨1218737090794752896559559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6499931150905348781650981 1218737090794752896559559)
                    ·
                      rfl

theorem cell22_3560223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 4].length) (baseStart_3560223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560223 prefixEnd_3560223 := by exact prefixLift 3560223
  have htrace : WordTrace (prefixWord ++ tailWord_3560223) baseStart_3560223 baseEnd_3560223 := by
    simpa [prefixWord, tailWord_3560223, baseEnd_3560223] using wordTrace_append hprefix tailTrace_3560223
  have hstable : (prefixWord ++ tailWord_3560223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560223).length < 2 ^ (prefixWord ++ tailWord_3560223).sum := by decide
  have hdescent : baseEnd_3560223 < baseStart_3560223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560236 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 5, 3]
def baseStart_3560236 : Nat := 118140960795 + 3560236 * 2 ^ 59
def prefixEnd_3560236 : Nat := 4983230072969 + 3 ^ 40 * 3560236 * 2
def baseEnd_3560236 : Nat := 1218741540960425195984519

theorem tailTrace_3560236 : CollatzResearch.WordTrace tailWord_3560236 prefixEnd_3560236 1218741540960425195984519 := by
  unfold tailWord_3560236
  simp only [CollatzResearch.WordTrace]
  refine ⟨64926237364940243372690281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86568316486586991163587041 64926237364940243372690281)
  ·
    refine ⟨48694678023705182529517711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64926237364940243372690281 48694678023705182529517711)
    ·
      refine ⟨73042017035557773794276567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48694678023705182529517711 73042017035557773794276567)
      ·
        refine ⟨109563025553336660691414851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73042017035557773794276567 109563025553336660691414851)
        ·
          refine ⟨164344538330004991037122277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109563025553336660691414851 164344538330004991037122277)
          ·
            refine ⟨30814600936875935819460427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164344538330004991037122277 30814600936875935819460427)
            ·
              refine ⟨46221901405313903729190641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30814600936875935819460427 46221901405313903729190641)
              ·
                refine ⟨34666426053985427796892981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46221901405313903729190641 34666426053985427796892981)
                ·
                  refine ⟨3249977442561133855958717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34666426053985427796892981 3249977442561133855958717)
                  ·
                    refine ⟨1218741540960425195984519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249977442561133855958717 1218741540960425195984519)
                    ·
                      rfl

theorem cell22_3560236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_3560236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560236 prefixEnd_3560236 := by exact prefixLift 3560236
  have htrace : WordTrace (prefixWord ++ tailWord_3560236) baseStart_3560236 baseEnd_3560236 := by
    simpa [prefixWord, tailWord_3560236, baseEnd_3560236] using wordTrace_append hprefix tailTrace_3560236
  have hstable : (prefixWord ++ tailWord_3560236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560236).length < 2 ^ (prefixWord ++ tailWord_3560236).sum := by decide
  have hdescent : baseEnd_3560236 < baseStart_3560236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560330 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_3560330 : Nat := 118140960795 + 3560330 * 2 ^ 59
def prefixEnd_3560330 : Nat := 4983230072969 + 3 ^ 40 * 3560330 * 2
def baseEnd_3560330 : Nat := 1218773719081440284134231

theorem tailTrace_3560330 : CollatzResearch.WordTrace tailWord_3560330 prefixEnd_3560330 1218773719081440284134231 := by
  unfold tailWord_3560330
  simp only [CollatzResearch.WordTrace]
  refine ⟨32463975797884985199825611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86570602127693293866201629 32463975797884985199825611)
  ·
    refine ⟨48695963696827477799738417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32463975797884985199825611 48695963696827477799738417)
    ·
      refine ⟨36521972772620608349803813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48695963696827477799738417 36521972772620608349803813)
      ·
        refine ⟨6847869894866364065588215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36521972772620608349803813 6847869894866364065588215)
        ·
          refine ⟨10271804842299546098382323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6847869894866364065588215 10271804842299546098382323)
          ·
            refine ⟨15407707263449319147573485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10271804842299546098382323 15407707263449319147573485)
            ·
              refine ⟨5777890223793494680340057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15407707263449319147573485 5777890223793494680340057)
              ·
                refine ⟨4333417667845121010255043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5777890223793494680340057 4333417667845121010255043)
                ·
                  refine ⟨6500126501767681515382565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4333417667845121010255043 6500126501767681515382565)
                  ·
                    refine ⟨1218773719081440284134231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6500126501767681515382565 1218773719081440284134231)
                    ·
                      rfl

theorem cell22_3560330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_3560330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560330 prefixEnd_3560330 := by exact prefixLift 3560330
  have htrace : WordTrace (prefixWord ++ tailWord_3560330) baseStart_3560330 baseEnd_3560330 := by
    simpa [prefixWord, tailWord_3560330, baseEnd_3560330] using wordTrace_append hprefix tailTrace_3560330
  have hstable : (prefixWord ++ tailWord_3560330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560330).length < 2 ^ (prefixWord ++ tailWord_3560330).sum := by decide
  have hdescent : baseEnd_3560330 < baseStart_3560330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560392 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 2, 4]
def baseStart_3560392 : Nat := 118140960795 + 3560392 * 2 ^ 59
def prefixEnd_3560392 : Nat := 4983230072969 + 3 ^ 40 * 3560392 * 2
def baseEnd_3560392 : Nat := 1218794942948492789084041

theorem tailTrace_3560392 : CollatzResearch.WordTrace tailWord_3560392 prefixEnd_3560392 1218794942948492789084041 := by
  unfold tailWord_3560392
  simp only [CollatzResearch.WordTrace]
  refine ⟨64929082258657662694029715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86572109678210216925372953 64929082258657662694029715)
  ·
    refine ⟨97393623387986494041044573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64929082258657662694029715 97393623387986494041044573)
    ·
      refine ⟨36522608770494935265391715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97393623387986494041044573 36522608770494935265391715)
      ·
        refine ⟨54783913155742402898087573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36522608770494935265391715 54783913155742402898087573)
        ·
          refine ⟨2567995929175425135847855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54783913155742402898087573 2567995929175425135847855)
          ·
            refine ⟨3851993893763137703771783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567995929175425135847855 3851993893763137703771783)
            ·
              refine ⟨5777990840644706555657675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851993893763137703771783 5777990840644706555657675)
              ·
                refine ⟨8666986260967059833486513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5777990840644706555657675 8666986260967059833486513)
                ·
                  refine ⟨6500239695725294875114885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8666986260967059833486513 6500239695725294875114885)
                  ·
                    refine ⟨1218794942948492789084041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6500239695725294875114885 1218794942948492789084041)
                    ·
                      rfl

theorem cell22_3560392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_3560392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560392 prefixEnd_3560392 := by exact prefixLift 3560392
  have htrace : WordTrace (prefixWord ++ tailWord_3560392) baseStart_3560392 baseEnd_3560392 := by
    simpa [prefixWord, tailWord_3560392, baseEnd_3560392] using wordTrace_append hprefix tailTrace_3560392
  have hstable : (prefixWord ++ tailWord_3560392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560392).length < 2 ^ (prefixWord ++ tailWord_3560392).sum := by decide
  have hdescent : baseEnd_3560392 < baseStart_3560392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560401 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 7]
def baseStart_3560401 : Nat := 118140960795 + 3560401 * 2 ^ 59
def prefixEnd_3560401 : Nat := 4983230072969 + 3 ^ 40 * 3560401 * 2
def baseEnd_3560401 : Nat := 406266007944139921869671

theorem tailTrace_3560401 : CollatzResearch.WordTrace tailWord_3560401 prefixEnd_3560401 406266007944139921869671 := by
  unfold tailWord_3560401
  simp only [CollatzResearch.WordTrace]
  refine ⟨129858492774282719925137057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86572328516188479950091371 129858492774282719925137057)
  ·
    refine ⟨97393869580712039943852793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129858492774282719925137057 97393869580712039943852793)
    ·
      refine ⟨73045402185534029957889595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97393869580712039943852793 73045402185534029957889595)
      ·
        refine ⟨109568103278301044936834393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73045402185534029957889595 109568103278301044936834393)
        ·
          refine ⟨82176077458725783702625795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109568103278301044936834393 82176077458725783702625795)
          ·
            refine ⟨123264116188088675553938693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82176077458725783702625795 123264116188088675553938693)
            ·
              refine ⟨23112021785266626666363505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123264116188088675553938693 23112021785266626666363505)
              ·
                refine ⟨17334016338949969999772629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23112021785266626666363505 17334016338949969999772629)
                ·
                  refine ⟨406266007944139921869671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17334016338949969999772629 406266007944139921869671)
                  ·
                    rfl

theorem cell22_3560401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_3560401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560401 prefixEnd_3560401 := by exact prefixLift 3560401
  have htrace : WordTrace (prefixWord ++ tailWord_3560401) baseStart_3560401 baseEnd_3560401 := by
    simpa [prefixWord, tailWord_3560401, baseEnd_3560401] using wordTrace_append hprefix tailTrace_3560401
  have hstable : (prefixWord ++ tailWord_3560401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560401).length < 2 ^ (prefixWord ++ tailWord_3560401).sum := by decide
  have hdescent : baseEnd_3560401 < baseStart_3560401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560433 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 2, 5]
def baseStart_3560433 : Nat := 118140960795 + 3560433 * 2 ^ 59
def prefixEnd_3560433 : Nat := 4983230072969 + 3 ^ 40 * 3560433 * 2
def baseEnd_3560433 : Nat := 1218808978086382348808915

theorem tailTrace_3560433 : CollatzResearch.WordTrace tailWord_3560433 prefixEnd_3560433 1218808978086382348808915 := by
  unfold tailWord_3560433
  simp only [CollatzResearch.WordTrace]
  refine ⟨129859659910166789390301953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86573106606777859593534635 129859659910166789390301953)
  ·
    refine ⟨97394744932625092042726465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129859659910166789390301953 97394744932625092042726465)
    ·
      refine ⟨73046058699468819032044849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97394744932625092042726465 73046058699468819032044849)
      ·
        refine ⟨54784544024601614274033637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73046058699468819032044849 54784544024601614274033637)
        ·
          refine ⟨10272102004612802676381307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54784544024601614274033637 10272102004612802676381307)
          ·
            refine ⟨15408153006919204014571961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10272102004612802676381307 15408153006919204014571961)
            ·
              refine ⟨11556114755189403010928971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15408153006919204014571961 11556114755189403010928971)
              ·
                refine ⟨17334172132784104516393457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11556114755189403010928971 17334172132784104516393457)
                ·
                  refine ⟨13000629099588078387295093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17334172132784104516393457 13000629099588078387295093)
                  ·
                    refine ⟨1218808978086382348808915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13000629099588078387295093 1218808978086382348808915)
                    ·
                      rfl

theorem cell22_3560433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_3560433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560433 prefixEnd_3560433 := by exact prefixLift 3560433
  have htrace : WordTrace (prefixWord ++ tailWord_3560433) baseStart_3560433 baseEnd_3560433 := by
    simpa [prefixWord, tailWord_3560433, baseEnd_3560433] using wordTrace_append hprefix tailTrace_3560433
  have hstable : (prefixWord ++ tailWord_3560433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560433).length < 2 ^ (prefixWord ++ tailWord_3560433).sum := by decide
  have hdescent : baseEnd_3560433 < baseStart_3560433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560508 : List Nat := [2, 2, 2, 2, 2, 2, 2, 8]
def baseStart_3560508 : Nat := 118140960795 + 3560508 * 2 ^ 59
def prefixEnd_3560508 : Nat := 4983230072969 + 3 ^ 40 * 3560508 * 2
def baseEnd_3560508 : Nat := 135426072457678572575965

theorem tailTrace_3560508 : CollatzResearch.WordTrace tailWord_3560508 prefixEnd_3560508 135426072457678572575965 := by
  unfold tailWord_3560508
  simp only [CollatzResearch.WordTrace]
  refine ⟨64931197692447538599641089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86574930256596718132854785 64931197692447538599641089)
  ·
    refine ⟨48698398269335653949730817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64931197692447538599641089 48698398269335653949730817)
    ·
      refine ⟨36523798702001740462298113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48698398269335653949730817 36523798702001740462298113)
      ·
        refine ⟨27392849026501305346723585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36523798702001740462298113 27392849026501305346723585)
        ·
          refine ⟨20544636769875979010042689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27392849026501305346723585 20544636769875979010042689)
          ·
            refine ⟨15408477577406984257532017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20544636769875979010042689 15408477577406984257532017)
            ·
              refine ⟨11556358183055238193149013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15408477577406984257532017 11556358183055238193149013)
              ·
                refine ⟨135426072457678572575965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11556358183055238193149013 135426072457678572575965)
                ·
                  rfl

theorem cell22_3560508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 8].length) (baseStart_3560508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560508 prefixEnd_3560508 := by exact prefixLift 3560508
  have htrace : WordTrace (prefixWord ++ tailWord_3560508) baseStart_3560508 baseEnd_3560508 := by
    simpa [prefixWord, tailWord_3560508, baseEnd_3560508] using wordTrace_append hprefix tailTrace_3560508
  have hstable : (prefixWord ++ tailWord_3560508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560508).length < 2 ^ (prefixWord ++ tailWord_3560508).sum := by decide
  have hdescent : baseEnd_3560508 < baseStart_3560508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560557 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_3560557 : Nat := 118140960795 + 3560557 * 2 ^ 59
def prefixEnd_3560557 : Nat := 4983230072969 + 3 ^ 40 * 3560557 * 2
def baseEnd_3560557 : Nat := 1218851425820487358708535

theorem tailTrace_3560557 : CollatzResearch.WordTrace tailWord_3560557 prefixEnd_3560557 1218851425820487358708535 := by
  unfold tailWord_3560557
  simp only [CollatzResearch.WordTrace]
  refine ⟨129864182561717558567815925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86576121707811705711877283 129864182561717558567815925)
  ·
    refine ⟨12174767115161021115732743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129864182561717558567815925 12174767115161021115732743)
    ·
      refine ⟨18262150672741531673599115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12174767115161021115732743 18262150672741531673599115)
      ·
        refine ⟨27393226009112297510398673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18262150672741531673599115 27393226009112297510398673)
        ·
          refine ⟨20544919506834223132799005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27393226009112297510398673 20544919506834223132799005)
          ·
            refine ⟨7704344815062833674799627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20544919506834223132799005 7704344815062833674799627)
            ·
              refine ⟨11556517222594250512199441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7704344815062833674799627 11556517222594250512199441)
              ·
                refine ⟨8667387916945687884149581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11556517222594250512199441 8667387916945687884149581)
                ·
                  refine ⟨3250270468854632956556093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8667387916945687884149581 3250270468854632956556093)
                  ·
                    refine ⟨1218851425820487358708535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3250270468854632956556093 1218851425820487358708535)
                    ·
                      rfl

theorem cell22_3560557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_3560557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560557 prefixEnd_3560557 := by exact prefixLift 3560557
  have htrace : WordTrace (prefixWord ++ tailWord_3560557) baseStart_3560557 baseEnd_3560557 := by
    simpa [prefixWord, tailWord_3560557, baseEnd_3560557] using wordTrace_append hprefix tailTrace_3560557
  have hstable : (prefixWord ++ tailWord_3560557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560557).length < 2 ^ (prefixWord ++ tailWord_3560557).sum := by decide
  have hdescent : baseEnd_3560557 < baseStart_3560557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560664 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 2, 3]
def baseStart_3560664 : Nat := 118140960795 + 3560664 * 2 ^ 59
def prefixEnd_3560664 : Nat := 4983230072969 + 3 ^ 40 * 3560664 * 2
def baseEnd_3560664 : Nat := 1218888054107174746283207

theorem tailTrace_3560664 : CollatzResearch.WordTrace tailWord_3560664 prefixEnd_3560664 1218888054107174746283207 := by
  unfold tailWord_3560664
  simp only [CollatzResearch.WordTrace]
  refine ⟨64934042586164957920980523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86578723448219943894640697 64934042586164957920980523)
  ·
    refine ⟨97401063879247436881470785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64934042586164957920980523 97401063879247436881470785)
    ·
      refine ⟨73050797909435577661103089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97401063879247436881470785 73050797909435577661103089)
      ·
        refine ⟨54788098432076683245827317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73050797909435577661103089 54788098432076683245827317)
        ·
          refine ⟨5136384228007189054296311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54788098432076683245827317 5136384228007189054296311)
          ·
            refine ⟨7704576342010783581444467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5136384228007189054296311 7704576342010783581444467)
            ·
              refine ⟨11556864513016175372166701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7704576342010783581444467 11556864513016175372166701)
              ·
                refine ⟨4333824192381065764562513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11556864513016175372166701 4333824192381065764562513)
                ·
                  refine ⟨3250368144285799323421885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4333824192381065764562513 3250368144285799323421885)
                  ·
                    refine ⟨1218888054107174746283207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3250368144285799323421885 1218888054107174746283207)
                    ·
                      rfl

theorem cell22_3560664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_3560664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560664 prefixEnd_3560664 := by exact prefixLift 3560664
  have htrace : WordTrace (prefixWord ++ tailWord_3560664) baseStart_3560664 baseEnd_3560664 := by
    simpa [prefixWord, tailWord_3560664, baseEnd_3560664] using wordTrace_append hprefix tailTrace_3560664
  have hstable : (prefixWord ++ tailWord_3560664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560664).length < 2 ^ (prefixWord ++ tailWord_3560664).sum := by decide
  have hdescent : baseEnd_3560664 < baseStart_3560664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560679 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 2, 4]
def baseStart_3560679 : Nat := 118140960795 + 3560679 * 2 ^ 59
def prefixEnd_3560679 : Nat := 4983230072969 + 3 ^ 40 * 3560679 * 2
def baseEnd_3560679 : Nat := 1218893188913719707158161

theorem tailTrace_3560679 : CollatzResearch.WordTrace tailWord_3560679 prefixEnd_3560679 1218893188913719707158161 := by
  unfold tailWord_3560679
  simp only [CollatzResearch.WordTrace]
  refine ⟨129868632267275573403757091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86579088178183715602504727 129868632267275573403757091)
  ·
    refine ⟨194802948400913360105635637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129868632267275573403757091 194802948400913360105635637)
    ·
      refine ⟨18262776412585627509903341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194802948400913360105635637 18262776412585627509903341)
      ·
        refine ⟨6848541154719610316213753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18262776412585627509903341 6848541154719610316213753)
        ·
          refine ⟨5136405866039707737160315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6848541154719610316213753 5136405866039707737160315)
          ·
            refine ⟨7704608799059561605740473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5136405866039707737160315 7704608799059561605740473)
            ·
              refine ⟨5778456599294671204305355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7704608799059561605740473 5778456599294671204305355)
              ·
                refine ⟨8667684898942006806458033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5778456599294671204305355 8667684898942006806458033)
                ·
                  refine ⟨6500763674206505104843525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8667684898942006806458033 6500763674206505104843525)
                  ·
                    refine ⟨1218893188913719707158161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6500763674206505104843525 1218893188913719707158161)
                    ·
                      rfl

theorem cell22_3560679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_3560679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560679 prefixEnd_3560679 := by exact prefixLift 3560679
  have htrace : WordTrace (prefixWord ++ tailWord_3560679) baseStart_3560679 baseEnd_3560679 := by
    simpa [prefixWord, tailWord_3560679, baseEnd_3560679] using wordTrace_append hprefix tailTrace_3560679
  have hstable : (prefixWord ++ tailWord_3560679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560679).length < 2 ^ (prefixWord ++ tailWord_3560679).sum := by decide
  have hdescent : baseEnd_3560679 < baseStart_3560679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560709 : List Nat := [1, 3, 1, 1, 2, 1, 5, 4, 1, 3]
def baseStart_3560709 : Nat := 118140960795 + 3560709 * 2 ^ 59
def prefixEnd_3560709 : Nat := 4983230072969 + 3 ^ 40 * 3560709 * 2
def baseEnd_3560709 : Nat := 1218903458526809628908069

theorem tailTrace_3560709 : CollatzResearch.WordTrace tailWord_3560709 prefixEnd_3560709 1218903458526809628908069 := by
  unfold tailWord_3560709
  simp only [CollatzResearch.WordTrace]
  refine ⟨129869726457166888527349181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86579817638111259018232787 129869726457166888527349181)
  ·
    refine ⟨48701147421437583197755943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129869726457166888527349181 48701147421437583197755943)
    ·
      refine ⟨73051721132156374796633915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48701147421437583197755943 73051721132156374796633915)
      ·
        refine ⟨109577581698234562194950873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73051721132156374796633915 109577581698234562194950873)
        ·
          refine ⟨82183186273675921646213155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109577581698234562194950873 82183186273675921646213155)
          ·
            refine ⟨123274779410513882469319733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82183186273675921646213155 123274779410513882469319733)
            ·
              refine ⟨11557010569735676481498725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123274779410513882469319733 11557010569735676481498725)
              ·
                refine ⟨2166939481825439340281011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11557010569735676481498725 2166939481825439340281011)
                ·
                  refine ⟨3250409222738159010421517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166939481825439340281011 3250409222738159010421517)
                  ·
                    refine ⟨1218903458526809628908069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3250409222738159010421517 1218903458526809628908069)
                    ·
                      rfl

theorem cell22_3560709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_3560709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560709 prefixEnd_3560709 := by exact prefixLift 3560709
  have htrace : WordTrace (prefixWord ++ tailWord_3560709) baseStart_3560709 baseEnd_3560709 := by
    simpa [prefixWord, tailWord_3560709, baseEnd_3560709] using wordTrace_append hprefix tailTrace_3560709
  have hstable : (prefixWord ++ tailWord_3560709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560709).length < 2 ^ (prefixWord ++ tailWord_3560709).sum := by decide
  have hdescent : baseEnd_3560709 < baseStart_3560709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560752 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 1, 4]
def baseStart_3560752 : Nat := 118140960795 + 3560752 * 2 ^ 59
def prefixEnd_3560752 : Nat := 4983230072969 + 3 ^ 40 * 3560752 * 2
def baseEnd_3560752 : Nat := 1218918178305571850082937

theorem tailTrace_3560752 : CollatzResearch.WordTrace tailWord_3560752 prefixEnd_3560752 1218918178305571850082937 := by
  unfold tailWord_3560752
  simp only [CollatzResearch.WordTrace]
  refine ⟨64935647398005553435582255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86580863197340737914109673 64935647398005553435582255)
  ·
    refine ⟨97403471097008330153373383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64935647398005553435582255 97403471097008330153373383)
    ·
      refine ⟨146105206645512495230060075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97403471097008330153373383 146105206645512495230060075)
      ·
        refine ⟨219157809968268742845090113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146105206645512495230060075 219157809968268742845090113)
        ·
          refine ⟨164368357476201557133817585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219157809968268742845090113 164368357476201557133817585)
          ·
            refine ⟨123276268107151167850363189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164368357476201557133817585 123276268107151167850363189)
            ·
              refine ⟨11557150135045421985971549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123276268107151167850363189 11557150135045421985971549)
              ·
                refine ⟨4333931300642033244739331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11557150135045421985971549 4333931300642033244739331)
                ·
                  refine ⟨6500896950963049867108997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4333931300642033244739331 6500896950963049867108997)
                  ·
                    refine ⟨1218918178305571850082937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6500896950963049867108997 1218918178305571850082937)
                    ·
                      rfl

theorem cell22_3560752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_3560752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560752 prefixEnd_3560752 := by exact prefixLift 3560752
  have htrace : WordTrace (prefixWord ++ tailWord_3560752) baseStart_3560752 baseEnd_3560752 := by
    simpa [prefixWord, tailWord_3560752, baseEnd_3560752] using wordTrace_append hprefix tailTrace_3560752
  have hstable : (prefixWord ++ tailWord_3560752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560752).length < 2 ^ (prefixWord ++ tailWord_3560752).sum := by decide
  have hdescent : baseEnd_3560752 < baseStart_3560752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560767 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 6]
def baseStart_3560767 : Nat := 118140960795 + 3560767 * 2 ^ 59
def prefixEnd_3560767 : Nat := 4983230072969 + 3 ^ 40 * 3560767 * 2
def baseEnd_3560767 : Nat := 406307771037372270319297

theorem tailTrace_3560767 : CollatzResearch.WordTrace tailWord_3560767 prefixEnd_3560767 406307771037372270319297 := by
  unfold tailWord_3560767
  simp only [CollatzResearch.WordTrace]
  refine ⟨129871841890956764432960555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86581227927304509621973703 129871841890956764432960555)
  ·
    refine ⟨194807762836435146649440833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129871841890956764432960555 194807762836435146649440833)
    ·
      refine ⟨146105822127326359987080625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194807762836435146649440833 146105822127326359987080625)
      ·
        refine ⟨109579366595494769990310469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146105822127326359987080625 109579366595494769990310469)
        ·
          refine ⟨20546131236655269373183213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109579366595494769990310469 20546131236655269373183213)
          ·
            refine ⟨7704799213745726014943705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20546131236655269373183213 7704799213745726014943705)
            ·
              refine ⟨5778599410309294511207779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7704799213745726014943705 5778599410309294511207779)
              ·
                refine ⟨8667899115463941766811669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5778599410309294511207779 8667899115463941766811669)
                ·
                  refine ⟨406307771037372270319297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8667899115463941766811669 406307771037372270319297)
                  ·
                    rfl

theorem cell22_3560767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 6].length) (baseStart_3560767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560767 prefixEnd_3560767 := by exact prefixLift 3560767
  have htrace : WordTrace (prefixWord ++ tailWord_3560767) baseStart_3560767 baseEnd_3560767 := by
    simpa [prefixWord, tailWord_3560767, baseEnd_3560767] using wordTrace_append hprefix tailTrace_3560767
  have hstable : (prefixWord ++ tailWord_3560767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560767).length < 2 ^ (prefixWord ++ tailWord_3560767).sum := by decide
  have hdescent : baseEnd_3560767 < baseStart_3560767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560812 : List Nat := [2, 2, 1, 1, 5, 3, 8]
def baseStart_3560812 : Nat := 118140960795 + 3560812 * 2 ^ 59
def prefixEnd_3560812 : Nat := 4983230072969 + 3 ^ 40 * 3560812 * 2
def baseEnd_3560812 : Nat := 45145878427101914577139

theorem tailTrace_3560812 : CollatzResearch.WordTrace tailWord_3560812 prefixEnd_3560812 45145878427101914577139 := by
  unfold tailWord_3560812
  simp only [CollatzResearch.WordTrace]
  refine ⟨64936741587896868559174345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86582322117195824745565793 64936741587896868559174345)
  ·
    refine ⟨48702556190922651419380759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64936741587896868559174345 48702556190922651419380759)
    ·
      refine ⟨73053834286383977129071139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48702556190922651419380759 73053834286383977129071139)
      ·
        refine ⟨109580751429575965693606709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73053834286383977129071139 109580751429575965693606709)
        ·
          refine ⟨10273195446522746783775629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109580751429575965693606709 10273195446522746783775629)
          ·
            refine ⟨3852448292446030043915861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10273195446522746783775629 3852448292446030043915861)
            ·
              refine ⟨45145878427101914577139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3852448292446030043915861 45145878427101914577139)
              ·
                rfl

theorem cell22_3560812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 8].length) (baseStart_3560812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560812 prefixEnd_3560812 := by exact prefixLift 3560812
  have htrace : WordTrace (prefixWord ++ tailWord_3560812) baseStart_3560812 baseEnd_3560812 := by
    simpa [prefixWord, tailWord_3560812, baseEnd_3560812] using wordTrace_append hprefix tailTrace_3560812
  have hstable : (prefixWord ++ tailWord_3560812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560812).length < 2 ^ (prefixWord ++ tailWord_3560812).sum := by decide
  have hdescent : baseEnd_3560812 < baseStart_3560812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560887 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 5, 4]
def baseStart_3560887 : Nat := 118140960795 + 3560887 * 2 ^ 59
def prefixEnd_3560887 : Nat := 4983230072969 + 3 ^ 40 * 3560887 * 2
def baseEnd_3560887 : Nat := 1218964391564476497957523

theorem tailTrace_3560887 : CollatzResearch.WordTrace tailWord_3560887 prefixEnd_3560887 1218964391564476497957523 := by
  unfold tailWord_3560887
  simp only [CollatzResearch.WordTrace]
  refine ⟨129876218650522024927328915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86584145767014683284885943 129876218650522024927328915)
  ·
    refine ⟨194814327975783037390993373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129876218650522024927328915 194814327975783037390993373)
    ·
      refine ⟨73055372990918639021622515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194814327975783037390993373 73055372990918639021622515)
      ·
        refine ⟨109583059486377958532433773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73055372990918639021622515 109583059486377958532433773)
        ·
          refine ⟨41093647307391734449662665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109583059486377958532433773 41093647307391734449662665)
          ·
            refine ⟨30820235480543800837246999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41093647307391734449662665 30820235480543800837246999)
            ·
              refine ⟨46230353220815701255870499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30820235480543800837246999 46230353220815701255870499)
              ·
                refine ⟨69345529831223551883805749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46230353220815701255870499 69345529831223551883805749)
                ·
                  refine ⟨6501143421677207989106789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69345529831223551883805749 6501143421677207989106789)
                  ·
                    refine ⟨1218964391564476497957523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6501143421677207989106789 1218964391564476497957523)
                    ·
                      rfl

theorem cell22_3560887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_3560887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560887 prefixEnd_3560887 := by exact prefixLift 3560887
  have htrace : WordTrace (prefixWord ++ tailWord_3560887) baseStart_3560887 baseEnd_3560887 := by
    simpa [prefixWord, tailWord_3560887, baseEnd_3560887] using wordTrace_append hprefix tailTrace_3560887
  have hstable : (prefixWord ++ tailWord_3560887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560887).length < 2 ^ (prefixWord ++ tailWord_3560887).sum := by decide
  have hdescent : baseEnd_3560887 < baseStart_3560887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560889 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 2, 5]
def baseStart_3560889 : Nat := 118140960795 + 3560889 * 2 ^ 59
def prefixEnd_3560889 : Nat := 4983230072969 + 3 ^ 40 * 3560889 * 2
def baseEnd_3560889 : Nat := 1218965076205349159407517

theorem tailTrace_3560889 : CollatzResearch.WordTrace tailWord_3560889 prefixEnd_3560889 1218965076205349159407517 := by
  unfold tailWord_3560889
  simp only [CollatzResearch.WordTrace]
  refine ⟨129876291596514779268901721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86584194397676519512601147 129876291596514779268901721)
  ·
    refine ⟨97407218697386084451676291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129876291596514779268901721 97407218697386084451676291)
    ·
      refine ⟨146110828046079126677514437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97407218697386084451676291 146110828046079126677514437)
      ·
        refine ⟨27395780258639836252033957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146110828046079126677514437 27395780258639836252033957)
        ·
          refine ⟨5136708798494969297256367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27395780258639836252033957 5136708798494969297256367)
          ·
            refine ⟨7705063197742453945884551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5136708798494969297256367 7705063197742453945884551)
            ·
              refine ⟨11557594796613680918826827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7705063197742453945884551 11557594796613680918826827)
              ·
                refine ⟨17336392194920521378240241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11557594796613680918826827 17336392194920521378240241)
                ·
                  refine ⟨13002294146190391033680181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17336392194920521378240241 13002294146190391033680181)
                  ·
                    refine ⟨1218965076205349159407517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13002294146190391033680181 1218965076205349159407517)
                    ·
                      rfl

theorem cell22_3560889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_3560889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560889 prefixEnd_3560889 := by exact prefixLift 3560889
  have htrace : WordTrace (prefixWord ++ tailWord_3560889) baseStart_3560889 baseEnd_3560889 := by
    simpa [prefixWord, tailWord_3560889, baseEnd_3560889] using wordTrace_append hprefix tailTrace_3560889
  have hstable : (prefixWord ++ tailWord_3560889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560889).length < 2 ^ (prefixWord ++ tailWord_3560889).sum := by decide
  have hdescent : baseEnd_3560889 < baseStart_3560889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560904 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 1, 4]
def baseStart_3560904 : Nat := 118140960795 + 3560904 * 2 ^ 59
def prefixEnd_3560904 : Nat := 4983230072969 + 3 ^ 40 * 3560904 * 2
def baseEnd_3560904 : Nat := 1218970211011894120282471

theorem tailTrace_3560904 : CollatzResearch.WordTrace tailWord_3560904 prefixEnd_3560904 1218970211011894120282471 := by
  unfold tailWord_3560904
  simp only [CollatzResearch.WordTrace]
  refine ⟨64938419345730218415348883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86584559127640291220465177 64938419345730218415348883)
  ·
    refine ⟨97407629018595327623023325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64938419345730218415348883 97407629018595327623023325)
    ·
      refine ⟨36527860881973247858633747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97407629018595327623023325 36527860881973247858633747)
      ·
        refine ⟨54791791322959871787950621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36527860881973247858633747 54791791322959871787950621)
        ·
          refine ⟨20546921746109951920481483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54791791322959871787950621 20546921746109951920481483)
          ·
            refine ⟨30820382619164927880722225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20546921746109951920481483 30820382619164927880722225)
            ·
              refine ⟨23115286964373695910541669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30820382619164927880722225 23115286964373695910541669)
              ·
                refine ⟨4334116305820067983226563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23115286964373695910541669 4334116305820067983226563)
                ·
                  refine ⟨6501174458730101974839845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334116305820067983226563 6501174458730101974839845)
                  ·
                    refine ⟨1218970211011894120282471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6501174458730101974839845 1218970211011894120282471)
                    ·
                      rfl

theorem cell22_3560904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_3560904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560904 prefixEnd_3560904 := by exact prefixLift 3560904
  have htrace : WordTrace (prefixWord ++ tailWord_3560904) baseStart_3560904 baseEnd_3560904 := by
    simpa [prefixWord, tailWord_3560904, baseEnd_3560904] using wordTrace_append hprefix tailTrace_3560904
  have hstable : (prefixWord ++ tailWord_3560904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560904).length < 2 ^ (prefixWord ++ tailWord_3560904).sum := by decide
  have hdescent : baseEnd_3560904 < baseStart_3560904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560921 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 1, 4]
def baseStart_3560921 : Nat := 118140960795 + 3560921 * 2 ^ 59
def prefixEnd_3560921 : Nat := 4983230072969 + 3 ^ 40 * 3560921 * 2
def baseEnd_3560921 : Nat := 1218976030459311742607419

theorem tailTrace_3560921 : CollatzResearch.WordTrace tailWord_3560921 prefixEnd_3560921 1218976030459311742607419 := by
  unfold tailWord_3560921
  simp only [CollatzResearch.WordTrace]
  refine ⟨129877458732398848734066617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86584972488265899156044411 129877458732398848734066617)
  ·
    refine ⟨97408094049299136550549963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129877458732398848734066617 97408094049299136550549963)
    ·
      refine ⟨146112141073948704825824945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97408094049299136550549963 146112141073948704825824945)
      ·
        refine ⟨109584105805461528619368709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146112141073948704825824945 109584105805461528619368709)
        ·
          refine ⟨20547019838524036616131633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109584105805461528619368709 20547019838524036616131633)
          ·
            refine ⟨15410264878893027462098725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20547019838524036616131633 15410264878893027462098725)
            ·
              refine ⟨2889424664792442649143511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15410264878893027462098725 2889424664792442649143511)
              ·
                refine ⟨4334136997188663973715267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2889424664792442649143511 4334136997188663973715267)
                ·
                  refine ⟨6501205495782995960572901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334136997188663973715267 6501205495782995960572901)
                  ·
                    refine ⟨1218976030459311742607419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6501205495782995960572901 1218976030459311742607419)
                    ·
                      rfl

theorem cell22_3560921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 4].length) (baseStart_3560921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3560921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3560921 prefixEnd_3560921 := by exact prefixLift 3560921
  have htrace : WordTrace (prefixWord ++ tailWord_3560921) baseStart_3560921 baseEnd_3560921 := by
    simpa [prefixWord, tailWord_3560921, baseEnd_3560921] using wordTrace_append hprefix tailTrace_3560921
  have hstable : (prefixWord ++ tailWord_3560921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560921).length < 2 ^ (prefixWord ++ tailWord_3560921).sum := by decide
  have hdescent : baseEnd_3560921 < baseStart_3560921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561120 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 2, 3]
def baseStart_3561120 : Nat := 118140960795 + 3561120 * 2 ^ 59
def prefixEnd_3561120 : Nat := 4983230072969 + 3 ^ 40 * 3561120 * 2
def baseEnd_3561120 : Nat := 1219044152226141556881809

theorem tailTrace_3561120 : CollatzResearch.WordTrace tailWord_3561120 prefixEnd_3561120 1219044152226141556881809 := by
  unfold tailWord_3561120
  simp only [CollatzResearch.WordTrace]
  refine ⟨64942358429338952860280407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86589811239118603813707209 64942358429338952860280407)
  ·
    refine ⟨97413537644008429290420611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64942358429338952860280407 97413537644008429290420611)
    ·
      refine ⟨146120306466012643935630917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97413537644008429290420611 146120306466012643935630917)
      ·
        refine ⟨27397557462377370737930797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146120306466012643935630917 27397557462377370737930797)
        ·
          refine ⟨10274084048391514026724049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27397557462377370737930797 10274084048391514026724049)
          ·
            refine ⟨7705563036293635520043037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10274084048391514026724049 7705563036293635520043037)
            ·
              refine ⟨2889586138610113320016139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7705563036293635520043037 2889586138610113320016139)
              ·
                refine ⟨4334379207915169980024209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2889586138610113320016139 4334379207915169980024209)
                ·
                  refine ⟨3250784405936377485018157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4334379207915169980024209 3250784405936377485018157)
                  ·
                    refine ⟨1219044152226141556881809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3250784405936377485018157 1219044152226141556881809)
                    ·
                      rfl

theorem cell22_3561120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 2, 3].length) (baseStart_3561120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561120 prefixEnd_3561120 := by exact prefixLift 3561120
  have htrace : WordTrace (prefixWord ++ tailWord_3561120) baseStart_3561120 baseEnd_3561120 := by
    simpa [prefixWord, tailWord_3561120, baseEnd_3561120] using wordTrace_append hprefix tailTrace_3561120
  have hstable : (prefixWord ++ tailWord_3561120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561120).length < 2 ^ (prefixWord ++ tailWord_3561120).sum := by decide
  have hdescent : baseEnd_3561120 < baseStart_3561120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561178 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 5]
def baseStart_3561178 : Nat := 118140960795 + 3561178 * 2 ^ 59
def prefixEnd_3561178 : Nat := 4983230072969 + 3 ^ 40 * 3561178 * 2
def baseEnd_3561178 : Nat := 406354668937149579643877

theorem tailTrace_3561178 : CollatzResearch.WordTrace tailWord_3561178 prefixEnd_3561178 406354668937149579643877 := by
  unfold tailWord_3561178
  simp only [CollatzResearch.WordTrace]
  refine ⟨32471708073116945406543047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86591221528311854417448125 32471708073116945406543047)
  ·
    refine ⟨48707562109675418109814571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32471708073116945406543047 48707562109675418109814571)
    ·
      refine ⟨73061343164513127164721857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48707562109675418109814571 73061343164513127164721857)
      ·
        refine ⟨54796007373384845373541393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73061343164513127164721857 54796007373384845373541393)
        ·
          refine ⟨41097005530038634030156045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54796007373384845373541393 41097005530038634030156045)
          ·
            refine ⟨15411377073764487761308517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41097005530038634030156045 15411377073764487761308517)
            ·
              refine ⟨2889633201330841455245347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15411377073764487761308517 2889633201330841455245347)
              ·
                refine ⟨4334449801996262182868021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2889633201330841455245347 4334449801996262182868021)
                ·
                  refine ⟨406354668937149579643877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4334449801996262182868021 406354668937149579643877)
                  ·
                    rfl

theorem cell22_3561178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_3561178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561178 prefixEnd_3561178 := by exact prefixLift 3561178
  have htrace : WordTrace (prefixWord ++ tailWord_3561178) baseStart_3561178 baseEnd_3561178 := by
    simpa [prefixWord, tailWord_3561178, baseEnd_3561178] using wordTrace_append hprefix tailTrace_3561178
  have hstable : (prefixWord ++ tailWord_3561178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561178).length < 2 ^ (prefixWord ++ tailWord_3561178).sum := by decide
  have hdescent : baseEnd_3561178 < baseStart_3561178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561253 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_3561253 : Nat := 118140960795 + 3561253 * 2 ^ 59
def prefixEnd_3561253 : Nat := 4983230072969 + 3 ^ 40 * 3561253 * 2
def baseEnd_3561253 : Nat := 1219089680844173543306401

theorem tailTrace_3561253 : CollatzResearch.WordTrace tailWord_3561253 prefixEnd_3561253 1219089680844173543306401 := by
  unfold tailWord_3561253
  simp only [CollatzResearch.WordTrace]
  refine ⟨129889567767196069435152413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86593045178130712956768275 129889567767196069435152413)
  ·
    refine ⟨48708587912698526038182155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129889567767196069435152413 48708587912698526038182155)
    ·
      refine ⟨73062881869047789057273233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48708587912698526038182155 73062881869047789057273233)
      ·
        refine ⟨54797161401785841792954925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73062881869047789057273233 54797161401785841792954925)
        ·
          refine ⟨20548935525669690672358097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54797161401785841792954925 20548935525669690672358097)
          ·
            refine ⟨15411701644252268004268573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20548935525669690672358097 15411701644252268004268573)
            ·
              refine ⟨5779388116594600501600715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15411701644252268004268573 5779388116594600501600715)
              ·
                refine ⟨8669082174891900752401073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5779388116594600501600715 8669082174891900752401073)
                ·
                  refine ⟨6501811631168925564300805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8669082174891900752401073 6501811631168925564300805)
                  ·
                    refine ⟨1219089680844173543306401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6501811631168925564300805 1219089680844173543306401)
                    ·
                      rfl

theorem cell22_3561253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_3561253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561253 prefixEnd_3561253 := by exact prefixLift 3561253
  have htrace : WordTrace (prefixWord ++ tailWord_3561253) baseStart_3561253 baseEnd_3561253 := by
    simpa [prefixWord, tailWord_3561253, baseEnd_3561253] using wordTrace_append hprefix tailTrace_3561253
  have hstable : (prefixWord ++ tailWord_3561253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561253).length < 2 ^ (prefixWord ++ tailWord_3561253).sum := by decide
  have hdescent : baseEnd_3561253 < baseStart_3561253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561268 : List Nat := [2, 5, 1, 1, 2, 2, 9]
def baseStart_3561268 : Nat := 118140960795 + 3561268 * 2 ^ 59
def prefixEnd_3561268 : Nat := 4983230072969 + 3 ^ 40 * 3561268 * 2
def baseEnd_3561268 : Nat := 45151659838915500154865

theorem tailTrace_3561268 : CollatzResearch.WordTrace tailWord_3561268 prefixEnd_3561268 45151659838915500154865 := by
  unfold tailWord_3561268
  simp only [CollatzResearch.WordTrace]
  refine ⟨64945057431070863498474229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86593409908094484664632305 64945057431070863498474229)
  ·
    refine ⟨6088599134162893452981959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64945057431070863498474229 6088599134162893452981959)
    ·
      refine ⟨9132898701244340179472939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6088599134162893452981959 9132898701244340179472939)
      ·
        refine ⟨13699348051866510269209409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9132898701244340179472939 13699348051866510269209409)
        ·
          refine ⟨10274511038899882701907057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13699348051866510269209409 10274511038899882701907057)
          ·
            refine ⟨7705883279174912026430293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10274511038899882701907057 7705883279174912026430293)
            ·
              refine ⟨45151659838915500154865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7705883279174912026430293 45151659838915500154865)
              ·
                rfl

theorem cell22_3561268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 9].length) (baseStart_3561268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561268 prefixEnd_3561268 := by exact prefixLift 3561268
  have htrace : WordTrace (prefixWord ++ tailWord_3561268) baseStart_3561268 baseEnd_3561268 := by
    simpa [prefixWord, tailWord_3561268, baseEnd_3561268] using wordTrace_append hprefix tailTrace_3561268
  have hstable : (prefixWord ++ tailWord_3561268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561268).length < 2 ^ (prefixWord ++ tailWord_3561268).sum := by decide
  have hdescent : baseEnd_3561268 < baseStart_3561268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561283 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 3, 3]
def baseStart_3561283 : Nat := 118140960795 + 3561283 * 2 ^ 59
def prefixEnd_3561283 : Nat := 4983230072969 + 3 ^ 40 * 3561283 * 2
def baseEnd_3561283 : Nat := 1219099950457263465056309

theorem tailTrace_3561283 : CollatzResearch.WordTrace tailWord_3561283 prefixEnd_3561283 1219099950457263465056309 := by
  unfold tailWord_3561283
  simp only [CollatzResearch.WordTrace]
  refine ⟨129890661957087384558744503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86593774638058256372496335 129890661957087384558744503)
  ·
    refine ⟨194835992935631076838116755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129890661957087384558744503 194835992935631076838116755)
    ·
      refine ⟨292253989403446615257175133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194835992935631076838116755 292253989403446615257175133)
      ·
        refine ⟨109595246026292480721440675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292253989403446615257175133 109595246026292480721440675)
        ·
          refine ⟨164392869039438721082161013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109595246026292480721440675 164392869039438721082161013)
          ·
            refine ⟨15411831472447380101452595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164392869039438721082161013 15411831472447380101452595)
            ·
              refine ⟨23117747208671070152178893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15411831472447380101452595 23117747208671070152178893)
              ·
                refine ⟨8669155203251651307067085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23117747208671070152178893 8669155203251651307067085)
                ·
                  refine ⟨3250933201219369240150157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8669155203251651307067085 3250933201219369240150157)
                  ·
                    refine ⟨1219099950457263465056309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3250933201219369240150157 1219099950457263465056309)
                    ·
                      rfl

theorem cell22_3561283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 3].length) (baseStart_3561283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561283 prefixEnd_3561283 := by exact prefixLift 3561283
  have htrace : WordTrace (prefixWord ++ tailWord_3561283) baseStart_3561283 baseEnd_3561283 := by
    simpa [prefixWord, tailWord_3561283, baseEnd_3561283] using wordTrace_append hprefix tailTrace_3561283
  have hstable : (prefixWord ++ tailWord_3561283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561283).length < 2 ^ (prefixWord ++ tailWord_3561283).sum := by decide
  have hdescent : baseEnd_3561283 < baseStart_3561283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561300 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_3561300 : Nat := 118140960795 + 3561300 * 2 ^ 59
def prefixEnd_3561300 : Nat := 4983230072969 + 3 ^ 40 * 3561300 * 2
def baseEnd_3561300 : Nat := 1219105769904681087381257

theorem tailTrace_3561300 : CollatzResearch.WordTrace tailWord_3561300 prefixEnd_3561300 1219105769904681087381257 := by
  unfold tailWord_3561300
  simp only [CollatzResearch.WordTrace]
  refine ⟨64945640999012898231056677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86594187998683864308075569 64945640999012898231056677)
  ·
    refine ⟨12177307687314918418323127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64945640999012898231056677 12177307687314918418323127)
    ·
      refine ⟨18265961530972377627484691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12177307687314918418323127 18265961530972377627484691)
      ·
        refine ⟨27398942296458566441227037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18265961530972377627484691 27398942296458566441227037)
        ·
          refine ⟨10274603361171962415460139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27398942296458566441227037 10274603361171962415460139)
          ·
            refine ⟨15411905041757943623190209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10274603361171962415460139 15411905041757943623190209)
            ·
              refine ⟨11558928781318457717392657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15411905041757943623190209 11558928781318457717392657)
              ·
                refine ⟨8669196585988843288044493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11558928781318457717392657 8669196585988843288044493)
                ·
                  refine ⟨3250948719745816233016685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8669196585988843288044493 3250948719745816233016685)
                  ·
                    refine ⟨1219105769904681087381257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3250948719745816233016685 1219105769904681087381257)
                    ·
                      rfl

theorem cell22_3561300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_3561300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561300 prefixEnd_3561300 := by exact prefixLift 3561300
  have htrace : WordTrace (prefixWord ++ tailWord_3561300) baseStart_3561300 baseEnd_3561300 := by
    simpa [prefixWord, tailWord_3561300, baseEnd_3561300] using wordTrace_append hprefix tailTrace_3561300
  have hstable : (prefixWord ++ tailWord_3561300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561300).length < 2 ^ (prefixWord ++ tailWord_3561300).sum := by decide
  have hdescent : baseEnd_3561300 < baseStart_3561300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561334 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_3561334 : Nat := 118140960795 + 3561334 * 2 ^ 59
def prefixEnd_3561334 : Nat := 4983230072969 + 3 ^ 40 * 3561334 * 2
def baseEnd_3561334 : Nat := 1219117408799516332031153

theorem tailTrace_3561334 : CollatzResearch.WordTrace tailWord_3561334 prefixEnd_3561334 1219117408799516332031153 := by
  unfold tailWord_3561334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8118282629993913766803191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86595014719935080179234037 8118282629993913766803191)
  ·
    refine ⟨12177423944990870650204787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8118282629993913766803191 12177423944990870650204787)
    ·
      refine ⟨18266135917486305975307181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12177423944990870650204787 18266135917486305975307181)
      ·
        refine ⟨6849800969057364740740193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18266135917486305975307181 6849800969057364740740193)
        ·
          refine ⟨5137350726793023555555145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6849800969057364740740193 5137350726793023555555145)
          ·
            refine ⟨3853013045094767666666359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5137350726793023555555145 3853013045094767666666359)
            ·
              refine ⟨5779519567642151499999539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853013045094767666666359 5779519567642151499999539)
              ·
                refine ⟨8669279351463227249999309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5779519567642151499999539 8669279351463227249999309)
                ·
                  refine ⟨3250979756798710218749741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8669279351463227249999309 3250979756798710218749741)
                  ·
                    refine ⟨1219117408799516332031153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3250979756798710218749741 1219117408799516332031153)
                    ·
                      rfl

theorem cell22_3561334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_3561334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561334 prefixEnd_3561334 := by exact prefixLift 3561334
  have htrace : WordTrace (prefixWord ++ tailWord_3561334) baseStart_3561334 baseEnd_3561334 := by
    simpa [prefixWord, tailWord_3561334, baseEnd_3561334] using wordTrace_append hprefix tailTrace_3561334
  have hstable : (prefixWord ++ tailWord_3561334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561334).length < 2 ^ (prefixWord ++ tailWord_3561334).sum := by decide
  have hdescent : baseEnd_3561334 < baseStart_3561334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561373 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_3561373 : Nat := 118140960795 + 3561373 * 2 ^ 59
def prefixEnd_3561373 : Nat := 4983230072969 + 3 ^ 40 * 3561373 * 2
def baseEnd_3561373 : Nat := 1219130759296533230306033

theorem tailTrace_3561373 : CollatzResearch.WordTrace tailWord_3561373 prefixEnd_3561373 1219130759296533230306033 := by
  unfold tailWord_3561373
  simp only [CollatzResearch.WordTrace]
  refine ⟨129893944526761329929520773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86595963017840886619680515 129893944526761329929520773)
  ·
    refine ⟨24355114598767749361785145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129893944526761329929520773 24355114598767749361785145)
    ·
      refine ⟨18266335949075812021338859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24355114598767749361785145 18266335949075812021338859)
      ·
        refine ⟨27399503923613718032008289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18266335949075812021338859 27399503923613718032008289)
        ·
          refine ⟨20549627942710288524006217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27399503923613718032008289 20549627942710288524006217)
          ·
            refine ⟨15412220957032716393004663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20549627942710288524006217 15412220957032716393004663)
            ·
              refine ⟨23118331435549074589506995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15412220957032716393004663 23118331435549074589506995)
              ·
                refine ⟨34677497153323611884260493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23118331435549074589506995 34677497153323611884260493)
                ·
                  refine ⟨13004061432496354456597685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34677497153323611884260493 13004061432496354456597685)
                  ·
                    refine ⟨1219130759296533230306033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13004061432496354456597685 1219130759296533230306033)
                    ·
                      rfl

theorem cell22_3561373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_3561373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561373 prefixEnd_3561373 := by exact prefixLift 3561373
  have htrace : WordTrace (prefixWord ++ tailWord_3561373) baseStart_3561373 baseEnd_3561373 := by
    simpa [prefixWord, tailWord_3561373, baseEnd_3561373] using wordTrace_append hprefix tailTrace_3561373
  have hstable : (prefixWord ++ tailWord_3561373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561373).length < 2 ^ (prefixWord ++ tailWord_3561373).sum := by decide
  have hdescent : baseEnd_3561373 < baseStart_3561373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561386 : List Nat := [3, 1, 18]
def baseStart_3561386 : Nat := 118140960795 + 3561386 * 2 ^ 59
def prefixEnd_3561386 : Nat := 4983230072969 + 3 ^ 40 * 3561386 * 2
def baseEnd_3561386 : Nat := 557446369209970521139

theorem tailTrace_3561386 : CollatzResearch.WordTrace tailWord_3561386 prefixEnd_3561386 557446369209970521139 := by
  unfold tailWord_3561386
  simp only [CollatzResearch.WordTrace]
  refine ⟨32473604668928558287436003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86596279117142822099829341 32473604668928558287436003)
  ·
    refine ⟨48710407003392837431154005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32473604668928558287436003 48710407003392837431154005)
    ·
      refine ⟨557446369209970521139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 18 48710407003392837431154005 557446369209970521139)
      ·
        rfl

theorem cell22_3561386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 18].length) (baseStart_3561386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561386 prefixEnd_3561386 := by exact prefixLift 3561386
  have htrace : WordTrace (prefixWord ++ tailWord_3561386) baseStart_3561386 baseEnd_3561386 := by
    simpa [prefixWord, tailWord_3561386, baseEnd_3561386] using wordTrace_append hprefix tailTrace_3561386
  have hstable : (prefixWord ++ tailWord_3561386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561386).length < 2 ^ (prefixWord ++ tailWord_3561386).sum := by decide
  have hdescent : baseEnd_3561386 < baseStart_3561386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561420 : List Nat := [2, 2, 1, 4, 1, 3, 3, 6]
def baseStart_3561420 : Nat := 118140960795 + 3561420 * 2 ^ 59
def prefixEnd_3561420 : Nat := 4983230072969 + 3 ^ 40 * 3561420 * 2
def baseEnd_3561420 : Nat := 135460760928560086042321

theorem tailTrace_3561420 : CollatzResearch.WordTrace tailWord_3561420 prefixEnd_3561420 135460760928560086042321 := by
  unfold tailWord_3561420
  simp only [CollatzResearch.WordTrace]
  refine ⟨64947829378795528478240857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86597105838394037970987809 64947829378795528478240857)
  ·
    refine ⟨48710872034096646358680643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64947829378795528478240857 48710872034096646358680643)
    ·
      refine ⟨73066308051144969538020965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48710872034096646358680643 73066308051144969538020965)
      ·
        refine ⟨13699932759589681788378931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73066308051144969538020965 13699932759589681788378931)
        ·
          refine ⟨20549899139384522682568397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13699932759589681788378931 20549899139384522682568397)
          ·
            refine ⟨7706212177269196005963149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20549899139384522682568397 7706212177269196005963149)
            ·
              refine ⟨2889829566475948502236181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7706212177269196005963149 2889829566475948502236181)
              ·
                refine ⟨135460760928560086042321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2889829566475948502236181 135460760928560086042321)
                ·
                  rfl

theorem cell22_3561420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 6].length) (baseStart_3561420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561420 prefixEnd_3561420 := by exact prefixLift 3561420
  have htrace : WordTrace (prefixWord ++ tailWord_3561420) baseStart_3561420 baseEnd_3561420 := by
    simpa [prefixWord, tailWord_3561420, baseEnd_3561420] using wordTrace_append hprefix tailTrace_3561420
  have hstable : (prefixWord ++ tailWord_3561420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561420).length < 2 ^ (prefixWord ++ tailWord_3561420).sum := by decide
  have hdescent : baseEnd_3561420 < baseStart_3561420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561523 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 3, 6]
def baseStart_3561523 : Nat := 118140960795 + 3561523 * 2 ^ 59
def prefixEnd_3561523 : Nat := 4983230072969 + 3 ^ 40 * 3561523 * 2
def baseEnd_3561523 : Nat := 1219182107361982839055573

theorem tailTrace_3561523 : CollatzResearch.WordTrace tailWord_3561523 prefixEnd_3561523 1219182107361982839055573 := by
  unfold tailWord_3561523
  simp only [CollatzResearch.WordTrace]
  refine ⟨129899415476217905547481223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86599610317478603698320815 129899415476217905547481223)
  ·
    refine ⟨194849123214326858321221835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129899415476217905547481223 194849123214326858321221835)
    ·
      refine ⟨292273684821490287481832753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194849123214326858321221835 292273684821490287481832753)
      ·
        refine ⟨219205263616117715611374565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292273684821490287481832753 219205263616117715611374565)
        ·
          refine ⟨41100986928022071677132731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219205263616117715611374565 41100986928022071677132731)
          ·
            refine ⟨61651480392033107515699097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41100986928022071677132731 61651480392033107515699097)
            ·
              refine ⟨46238610294024830636774323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61651480392033107515699097 46238610294024830636774323)
              ·
                refine ⟨69357915441037245955161485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46238610294024830636774323 69357915441037245955161485)
                ·
                  refine ⟨26009218290388967233185557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69357915441037245955161485 26009218290388967233185557)
                  ·
                    refine ⟨1219182107361982839055573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26009218290388967233185557 1219182107361982839055573)
                    ·
                      rfl

theorem cell22_3561523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_3561523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561523 prefixEnd_3561523 := by exact prefixLift 3561523
  have htrace : WordTrace (prefixWord ++ tailWord_3561523) baseStart_3561523 baseEnd_3561523 := by
    simpa [prefixWord, tailWord_3561523, baseEnd_3561523] using wordTrace_append hprefix tailTrace_3561523
  have hstable : (prefixWord ++ tailWord_3561523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561523).length < 2 ^ (prefixWord ++ tailWord_3561523).sum := by decide
  have hdescent : baseEnd_3561523 < baseStart_3561523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561529 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 1, 4]
def baseStart_3561529 : Nat := 118140960795 + 3561529 * 2 ^ 59
def prefixEnd_3561529 : Nat := 4983230072969 + 3 ^ 40 * 3561529 * 2
def baseEnd_3561529 : Nat := 1219184161284600823405555

theorem tailTrace_3561529 : CollatzResearch.WordTrace tailWord_3561529 prefixEnd_3561529 1219184161284600823405555 := by
  unfold tailWord_3561529
  simp only [CollatzResearch.WordTrace]
  refine ⟨129899634314196168572199641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86599756209464112381466427 129899634314196168572199641)
  ·
    refine ⟨97424725735647126429149731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129899634314196168572199641 97424725735647126429149731)
    ·
      refine ⟨146137088603470689643724597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97424725735647126429149731 146137088603470689643724597)
      ·
        refine ⟨13700352056575377154099181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146137088603470689643724597 13700352056575377154099181)
        ·
          refine ⟨5137632021215766432787193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13700352056575377154099181 5137632021215766432787193)
          ·
            refine ⟨3853224015911824824590395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5137632021215766432787193 3853224015911824824590395)
            ·
              refine ⟨5779836023867737236885593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853224015911824824590395 5779836023867737236885593)
              ·
                refine ⟨4334877017900802927664195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5779836023867737236885593 4334877017900802927664195)
                ·
                  refine ⟨6502315526851204391496293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334877017900802927664195 6502315526851204391496293)
                  ·
                    refine ⟨1219184161284600823405555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6502315526851204391496293 1219184161284600823405555)
                    ·
                      rfl

theorem cell22_3561529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 4].length) (baseStart_3561529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561529 prefixEnd_3561529 := by exact prefixLift 3561529
  have htrace : WordTrace (prefixWord ++ tailWord_3561529) baseStart_3561529 baseEnd_3561529 := by
    simpa [prefixWord, tailWord_3561529, baseEnd_3561529] using wordTrace_append hprefix tailTrace_3561529
  have hstable : (prefixWord ++ tailWord_3561529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561529).length < 2 ^ (prefixWord ++ tailWord_3561529).sum := by decide
  have hdescent : baseEnd_3561529 < baseStart_3561529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561679 : List Nat := [1, 1, 2, 1, 1, 3, 7, 2, 4]
def baseStart_3561679 : Nat := 118140960795 + 3561679 * 2 ^ 59
def prefixEnd_3561679 : Nat := 4983230072969 + 3 ^ 40 * 3561679 * 2
def baseEnd_3561679 : Nat := 406411836450016810718365

theorem tailTrace_3561679 : CollatzResearch.WordTrace tailWord_3561679 prefixEnd_3561679 406411836450016810718365 := by
  unfold tailWord_3561679
  simp only [CollatzResearch.WordTrace]
  refine ⟨129905105263652744190160091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86603403509101829460106727 129905105263652744190160091)
  ·
    refine ⟨194857657895479116285240137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129905105263652744190160091 194857657895479116285240137)
    ·
      refine ⟨146143243421609337213930103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194857657895479116285240137 146143243421609337213930103)
      ·
        refine ⟨219214865132414005820895155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146143243421609337213930103 219214865132414005820895155)
        ·
          refine ⟨328822297698621008731342733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219214865132414005820895155 328822297698621008731342733)
          ·
            refine ⟨123308361636982878274253525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328822297698621008731342733 123308361636982878274253525)
            ·
              refine ⟨2890039725866786209552817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 123308361636982878274253525 2890039725866786209552817)
              ·
                refine ⟨2167529794400089657164613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890039725866786209552817 2167529794400089657164613)
                ·
                  refine ⟨406411836450016810718365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2167529794400089657164613 406411836450016810718365)
                  ·
                    rfl

theorem cell22_3561679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 4].length) (baseStart_3561679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561679 prefixEnd_3561679 := by exact prefixLift 3561679
  have htrace : WordTrace (prefixWord ++ tailWord_3561679) baseStart_3561679 baseEnd_3561679 := by
    simpa [prefixWord, tailWord_3561679, baseEnd_3561679] using wordTrace_append hprefix tailTrace_3561679
  have hstable : (prefixWord ++ tailWord_3561679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561679).length < 2 ^ (prefixWord ++ tailWord_3561679).sum := by decide
  have hdescent : baseEnd_3561679 < baseStart_3561679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561690 : List Nat := [3, 1, 1, 2, 2, 1, 3, 9]
def baseStart_3561690 : Nat := 118140960795 + 3561690 * 2 ^ 59
def prefixEnd_3561690 : Nat := 4983230072969 + 3 ^ 40 * 3561690 * 2
def baseEnd_3561690 : Nat := 135471030541650007792229

theorem tailTrace_3561690 : CollatzResearch.WordTrace tailWord_3561690 prefixEnd_3561690 135471030541650007792229 := by
  unfold tailWord_3561690
  simp only [CollatzResearch.WordTrace]
  refine ⟨32476376616653223267202631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86603670977741928712540349 32476376616653223267202631)
  ·
    refine ⟨48714564924979834900803947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32476376616653223267202631 48714564924979834900803947)
    ·
      refine ⟨73071847387469752351205921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48714564924979834900803947 73071847387469752351205921)
      ·
        refine ⟨54803885540602314263404441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73071847387469752351205921 54803885540602314263404441)
        ·
          refine ⟨41102914155451735697553331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54803885540602314263404441 41102914155451735697553331)
          ·
            refine ⟨61654371233177603546329997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41102914155451735697553331 61654371233177603546329997)
            ·
              refine ⟨23120389212441601329873749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61654371233177603546329997 23120389212441601329873749)
              ·
                refine ⟨135471030541650007792229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23120389212441601329873749 135471030541650007792229)
                ·
                  rfl

theorem cell22_3561690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_3561690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561690 prefixEnd_3561690 := by exact prefixLift 3561690
  have htrace : WordTrace (prefixWord ++ tailWord_3561690) baseStart_3561690 baseEnd_3561690 := by
    simpa [prefixWord, tailWord_3561690, baseEnd_3561690] using wordTrace_append hprefix tailTrace_3561690
  have hstable : (prefixWord ++ tailWord_3561690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561690).length < 2 ^ (prefixWord ++ tailWord_3561690).sum := by decide
  have hdescent : baseEnd_3561690 < baseStart_3561690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561698 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3561698 : Nat := 118140960795 + 3561698 * 2 ^ 59
def prefixEnd_3561698 : Nat := 4983230072969 + 3 ^ 40 * 3561698 * 2
def baseEnd_3561698 : Nat := 1219242013438340715930037

theorem tailTrace_3561698 : CollatzResearch.WordTrace tailWord_3561698 prefixEnd_3561698 1219242013438340715930037 := by
  unfold tailWord_3561698
  simp only [CollatzResearch.WordTrace]
  refine ⟨32476449562645977608775437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86603865500389273623401165 32476449562645977608775437)
  ·
    refine ⟨12178668585992241603290789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32476449562645977608775437 12178668585992241603290789)
    ·
      refine ⟨2283500359873545300617023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12178668585992241603290789 2283500359873545300617023)
      ·
        refine ⟨3425250539810317950925535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2283500359873545300617023 3425250539810317950925535)
        ·
          refine ⟨5137875809715476926388303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3425250539810317950925535 5137875809715476926388303)
          ·
            refine ⟨7706813714573215389582455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5137875809715476926388303 7706813714573215389582455)
            ·
              refine ⟨11560220571859823084373683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7706813714573215389582455 11560220571859823084373683)
              ·
                refine ⟨17340330857789734626560525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11560220571859823084373683 17340330857789734626560525)
                ·
                  refine ⟨6502624071671150484960197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17340330857789734626560525 6502624071671150484960197)
                  ·
                    refine ⟨1219242013438340715930037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6502624071671150484960197 1219242013438340715930037)
                    ·
                      rfl

theorem cell22_3561698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3561698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561698 prefixEnd_3561698 := by exact prefixLift 3561698
  have htrace : WordTrace (prefixWord ++ tailWord_3561698) baseStart_3561698 baseEnd_3561698 := by
    simpa [prefixWord, tailWord_3561698, baseEnd_3561698] using wordTrace_append hprefix tailTrace_3561698
  have hstable : (prefixWord ++ tailWord_3561698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561698).length < 2 ^ (prefixWord ++ tailWord_3561698).sum := by decide
  have hdescent : baseEnd_3561698 < baseStart_3561698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561720 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_3561720 : Nat := 118140960795 + 3561720 * 2 ^ 59
def prefixEnd_3561720 : Nat := 4983230072969 + 3 ^ 40 * 3561720 * 2
def baseEnd_3561720 : Nat := 1219249544487939991879969

theorem tailTrace_3561720 : CollatzResearch.WordTrace tailWord_3561720 prefixEnd_3561720 1219249544487939991879969 := by
  unfold tailWord_3561720
  simp only [CollatzResearch.WordTrace]
  refine ⟨64953300328252104096201307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86604400437669472128268409 64953300328252104096201307)
  ·
    refine ⟨97429950492378156144301961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64953300328252104096201307 97429950492378156144301961)
    ·
      refine ⟨73072462869283617108226471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97429950492378156144301961 73072462869283617108226471)
      ·
        refine ⟨109608694303925425662339707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73072462869283617108226471 109608694303925425662339707)
        ·
          refine ⟨164413041455888138493509561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109608694303925425662339707 164413041455888138493509561)
          ·
            refine ⟨123309781091916103870132171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164413041455888138493509561 123309781091916103870132171)
            ·
              refine ⟨184964671637874155805198257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123309781091916103870132171 184964671637874155805198257)
              ·
                refine ⟨138723503728405616853898693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184964671637874155805198257 138723503728405616853898693)
                ·
                  refine ⟨26010656949076053160106005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138723503728405616853898693 26010656949076053160106005)
                  ·
                    refine ⟨1219249544487939991879969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26010656949076053160106005 1219249544487939991879969)
                    ·
                      rfl

theorem cell22_3561720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_3561720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561720 prefixEnd_3561720 := by exact prefixLift 3561720
  have htrace : WordTrace (prefixWord ++ tailWord_3561720) baseStart_3561720 baseEnd_3561720 := by
    simpa [prefixWord, tailWord_3561720, baseEnd_3561720] using wordTrace_append hprefix tailTrace_3561720
  have hstable : (prefixWord ++ tailWord_3561720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561720).length < 2 ^ (prefixWord ++ tailWord_3561720).sum := by decide
  have hdescent : baseEnd_3561720 < baseStart_3561720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561752 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 5]
def baseStart_3561752 : Nat := 118140960795 + 3561752 * 2 ^ 59
def prefixEnd_3561752 : Nat := 4983230072969 + 3 ^ 40 * 3561752 * 2
def baseEnd_3561752 : Nat := 406420166247300858359957

theorem tailTrace_3561752 : CollatzResearch.WordTrace tailWord_3561752 prefixEnd_3561752 406420166247300858359957 := by
  unfold tailWord_3561752
  simp only [CollatzResearch.WordTrace]
  refine ⟨64953883896194138828783755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86605178528258851771711673 64953883896194138828783755)
  ·
    refine ⟨97430825844291208243175633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64953883896194138828783755 97430825844291208243175633)
    ·
      refine ⟨73073119383218406182381725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97430825844291208243175633 73073119383218406182381725)
      ·
        refine ⟨27402419768706902318393147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73073119383218406182381725 27402419768706902318393147)
        ·
          refine ⟨41103629653060353477589721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27402419768706902318393147 41103629653060353477589721)
          ·
            refine ⟨30827722239795265108192291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41103629653060353477589721 30827722239795265108192291)
            ·
              refine ⟨46241583359692897662288437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30827722239795265108192291 46241583359692897662288437)
              ·
                refine ⟨4335148439971209155839541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46241583359692897662288437 4335148439971209155839541)
                ·
                  refine ⟨406420166247300858359957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4335148439971209155839541 406420166247300858359957)
                  ·
                    rfl

theorem cell22_3561752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_3561752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561752 prefixEnd_3561752 := by exact prefixLift 3561752
  have htrace : WordTrace (prefixWord ++ tailWord_3561752) baseStart_3561752 baseEnd_3561752 := by
    simpa [prefixWord, tailWord_3561752, baseEnd_3561752] using wordTrace_append hprefix tailTrace_3561752
  have hstable : (prefixWord ++ tailWord_3561752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561752).length < 2 ^ (prefixWord ++ tailWord_3561752).sum := by decide
  have hdescent : baseEnd_3561752 < baseStart_3561752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561827 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 1, 6]
def baseStart_3561827 : Nat := 118140960795 + 3561827 * 2 ^ 59
def prefixEnd_3561827 : Nat := 4983230072969 + 3 ^ 40 * 3561827 * 2
def baseEnd_3561827 : Nat := 1219286172774627379454641

theorem tailTrace_3561827 : CollatzResearch.WordTrace tailWord_3561827 prefixEnd_3561827 1219286172774627379454641 := by
  unfold tailWord_3561827
  simp only [CollatzResearch.WordTrace]
  refine ⟨129910503267116565466547735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86607002178077710311031823 129910503267116565466547735)
  ·
    refine ⟨194865754900674848199821603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129910503267116565466547735 194865754900674848199821603)
    ·
      refine ⟨292298632351012272299732405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194865754900674848199821603 292298632351012272299732405)
      ·
        refine ⟨27402996782907400528099913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292298632351012272299732405 27402996782907400528099913)
        ·
          refine ⟨20552247587180550396074935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27402996782907400528099913 20552247587180550396074935)
          ·
            refine ⟨30828371380770825594112403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20552247587180550396074935 30828371380770825594112403)
            ·
              refine ⟨46242557071156238391168605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30828371380770825594112403 46242557071156238391168605)
              ·
                refine ⟨17340958901683589396688227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46242557071156238391168605 17340958901683589396688227)
                ·
                  refine ⟨26011438352525384095032341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17340958901683589396688227 26011438352525384095032341)
                  ·
                    refine ⟨1219286172774627379454641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26011438352525384095032341 1219286172774627379454641)
                    ·
                      rfl

theorem cell22_3561827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_3561827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561827 prefixEnd_3561827 := by exact prefixLift 3561827
  have htrace : WordTrace (prefixWord ++ tailWord_3561827) baseStart_3561827 baseEnd_3561827 := by
    simpa [prefixWord, tailWord_3561827, baseEnd_3561827] using wordTrace_append hprefix tailTrace_3561827
  have hstable : (prefixWord ++ tailWord_3561827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561827).length < 2 ^ (prefixWord ++ tailWord_3561827).sum := by decide
  have hdescent : baseEnd_3561827 < baseStart_3561827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561829 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 4, 3]
def baseStart_3561829 : Nat := 118140960795 + 3561829 * 2 ^ 59
def prefixEnd_3561829 : Nat := 4983230072969 + 3 ^ 40 * 3561829 * 2
def baseEnd_3561829 : Nat := 1219286857415500040904635

theorem tailTrace_3561829 : CollatzResearch.WordTrace tailWord_3561829 prefixEnd_3561829 1219286857415500040904635 := by
  unfold tailWord_3561829
  simp only [CollatzResearch.WordTrace]
  refine ⟨129910576213109319808120541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86607050808739546538747027 129910576213109319808120541)
  ·
    refine ⟨48716466079915994928045203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129910576213109319808120541 48716466079915994928045203)
    ·
      refine ⟨73074699119873992392067805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48716466079915994928045203 73074699119873992392067805)
      ·
        refine ⟨27403012169952747147025427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73074699119873992392067805 27403012169952747147025427)
        ·
          refine ⟨41104518254929120720538141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27403012169952747147025427 41104518254929120720538141)
          ·
            refine ⟨15414194345598420270201803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41104518254929120720538141 15414194345598420270201803)
            ·
              refine ⟨23121291518397630405302705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15414194345598420270201803 23121291518397630405302705)
              ·
                refine ⟨17340968638798222803977029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23121291518397630405302705 17340968638798222803977029)
                ·
                  refine ⟨3251431619774666775745693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17340968638798222803977029 3251431619774666775745693)
                  ·
                    refine ⟨1219286857415500040904635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3251431619774666775745693 1219286857415500040904635)
                    ·
                      rfl

theorem cell22_3561829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_3561829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561829 prefixEnd_3561829 := by exact prefixLift 3561829
  have htrace : WordTrace (prefixWord ++ tailWord_3561829) baseStart_3561829 baseEnd_3561829 := by
    simpa [prefixWord, tailWord_3561829, baseEnd_3561829] using wordTrace_append hprefix tailTrace_3561829
  have hstable : (prefixWord ++ tailWord_3561829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561829).length < 2 ^ (prefixWord ++ tailWord_3561829).sum := by decide
  have hdescent : baseEnd_3561829 < baseStart_3561829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561831 : List Nat := [1, 1, 5, 1, 3, 1, 3, 3, 4]
def baseStart_3561831 : Nat := 118140960795 + 3561831 * 2 ^ 59
def prefixEnd_3561831 : Nat := 4983230072969 + 3 ^ 40 * 3561831 * 2
def baseEnd_3561831 : Nat := 406429180685457567451543

theorem tailTrace_3561831 : CollatzResearch.WordTrace tailWord_3561831 prefixEnd_3561831 406429180685457567451543 := by
  unfold tailWord_3561831
  simp only [CollatzResearch.WordTrace]
  refine ⟨129910649159102074149693347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86607099439401382766462231 129910649159102074149693347)
  ·
    refine ⟨194865973738653111224540021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129910649159102074149693347 194865973738653111224540021)
    ·
      refine ⟨18268685037998729177300627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194865973738653111224540021 18268685037998729177300627)
      ·
        refine ⟨27403027556998093765950941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18268685037998729177300627 27403027556998093765950941)
        ·
          refine ⟨10276135333874285162231603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27403027556998093765950941 10276135333874285162231603)
          ·
            refine ⟨15414203000811427743347405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10276135333874285162231603 15414203000811427743347405)
            ·
              refine ⟨5780326125304285403755277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15414203000811427743347405 5780326125304285403755277)
              ·
                refine ⟨2167622296989107026408229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5780326125304285403755277 2167622296989107026408229)
                ·
                  refine ⟨406429180685457567451543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2167622296989107026408229 406429180685457567451543)
                  ·
                    rfl

theorem cell22_3561831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 4].length) (baseStart_3561831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561831 prefixEnd_3561831 := by exact prefixLift 3561831
  have htrace : WordTrace (prefixWord ++ tailWord_3561831) baseStart_3561831 baseEnd_3561831 := by
    simpa [prefixWord, tailWord_3561831, baseEnd_3561831] using wordTrace_append hprefix tailTrace_3561831
  have hstable : (prefixWord ++ tailWord_3561831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561831).length < 2 ^ (prefixWord ++ tailWord_3561831).sum := by decide
  have hdescent : baseEnd_3561831 < baseStart_3561831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561842 : List Nat := [3, 2, 1, 2, 1, 3, 10]
def baseStart_3561842 : Nat := 118140960795 + 3561842 * 2 ^ 59
def prefixEnd_3561842 : Nat := 4983230072969 + 3 ^ 40 * 3561842 * 2
def baseEnd_3561842 : Nat := 45158937317821197789985

theorem tailTrace_3561842 : CollatzResearch.WordTrace tailWord_3561842 prefixEnd_3561842 45158937317821197789985 := by
  unfold tailWord_3561842
  simp only [CollatzResearch.WordTrace]
  refine ⟨32477762590515555757085945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86607366908041482018895853 32477762590515555757085945)
  ·
    refine ⟨24358321942886666817814459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32477762590515555757085945 24358321942886666817814459)
    ·
      refine ⟨36537482914330000226721689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24358321942886666817814459 36537482914330000226721689)
      ·
        refine ⟨27403112185747500170041267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36537482914330000226721689 27403112185747500170041267)
        ·
          refine ⟨41104668278621250255061901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27403112185747500170041267 41104668278621250255061901)
          ·
            refine ⟨15414250604482968845648213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41104668278621250255061901 15414250604482968845648213)
            ·
              refine ⟨45158937317821197789985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15414250604482968845648213 45158937317821197789985)
              ·
                rfl

theorem cell22_3561842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 10].length) (baseStart_3561842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561842 prefixEnd_3561842 := by exact prefixLift 3561842
  have htrace : WordTrace (prefixWord ++ tailWord_3561842) baseStart_3561842 baseEnd_3561842 := by
    simpa [prefixWord, tailWord_3561842, baseEnd_3561842] using wordTrace_append hprefix tailTrace_3561842
  have hstable : (prefixWord ++ tailWord_3561842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561842).length < 2 ^ (prefixWord ++ tailWord_3561842).sum := by decide
  have hdescent : baseEnd_3561842 < baseStart_3561842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561859 : List Nat := [1, 1, 1, 3, 6, 1, 2, 7]
def baseStart_3561859 : Nat := 118140960795 + 3561859 * 2 ^ 59
def prefixEnd_3561859 : Nat := 4983230072969 + 3 ^ 40 * 3561859 * 2
def baseEnd_3561859 : Nat := 135477458558732218072727

theorem tailTrace_3561859 : CollatzResearch.WordTrace tailWord_3561859 prefixEnd_3561859 135477458558732218072727 := by
  unfold tailWord_3561859
  simp only [CollatzResearch.WordTrace]
  refine ⟨129911670403000634931712631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86607780268667089954475087 129911670403000634931712631)
  ·
    refine ⟨194867505604500952397568947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129911670403000634931712631 194867505604500952397568947)
    ·
      refine ⟨292301258406751428596353421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194867505604500952397568947 292301258406751428596353421)
      ·
        refine ⟨109612971902531785723632533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292301258406751428596353421 109612971902531785723632533)
        ·
          refine ⟨5138108057931177455795275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109612971902531785723632533 5138108057931177455795275)
          ·
            refine ⟨7707162086896766183692913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138108057931177455795275 7707162086896766183692913)
            ·
              refine ⟨5780371565172574637769685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7707162086896766183692913 5780371565172574637769685)
              ·
                refine ⟨135477458558732218072727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5780371565172574637769685 135477458558732218072727)
                ·
                  rfl

theorem cell22_3561859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 7].length) (baseStart_3561859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561859 prefixEnd_3561859 := by exact prefixLift 3561859
  have htrace : WordTrace (prefixWord ++ tailWord_3561859) baseStart_3561859 baseEnd_3561859 := by
    simpa [prefixWord, tailWord_3561859, baseEnd_3561859] using wordTrace_append hprefix tailTrace_3561859
  have hstable : (prefixWord ++ tailWord_3561859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561859).length < 2 ^ (prefixWord ++ tailWord_3561859).sum := by decide
  have hdescent : baseEnd_3561859 < baseStart_3561859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561949 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 8]
def baseStart_3561949 : Nat := 118140960795 + 3561949 * 2 ^ 59
def prefixEnd_3561949 : Nat := 4983230072969 + 3 ^ 40 * 3561949 * 2
def baseEnd_3561949 : Nat := 406442645289286575968089

theorem tailTrace_3561949 : CollatzResearch.WordTrace tailWord_3561949 prefixEnd_3561949 406442645289286575968089 := by
  unfold tailWord_3561949
  simp only [CollatzResearch.WordTrace]
  refine ⟨129914952972674580302488901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86609968648449720201659267 129914952972674580302488901)
  ·
    refine ⟨24359053682376483806716669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129914952972674580302488901 24359053682376483806716669)
    ·
      refine ⟨9134645130891181427518751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24359053682376483806716669 9134645130891181427518751)
      ·
        refine ⟨13701967696336772141278127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9134645130891181427518751 13701967696336772141278127)
        ·
          refine ⟨20552951544505158211917191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13701967696336772141278127 20552951544505158211917191)
          ·
            refine ⟨30829427316757737317875787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20552951544505158211917191 30829427316757737317875787)
            ·
              refine ⟨46244140975136605976813681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30829427316757737317875787 46244140975136605976813681)
              ·
                refine ⟨34683105731352454482610261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46244140975136605976813681 34683105731352454482610261)
                ·
                  refine ⟨406442645289286575968089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34683105731352454482610261 406442645289286575968089)
                  ·
                    rfl

theorem cell22_3561949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_3561949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561949 prefixEnd_3561949 := by exact prefixLift 3561949
  have htrace : WordTrace (prefixWord ++ tailWord_3561949) baseStart_3561949 baseEnd_3561949 := by
    simpa [prefixWord, tailWord_3561949, baseEnd_3561949] using wordTrace_append hprefix tailTrace_3561949
  have hstable : (prefixWord ++ tailWord_3561949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561949).length < 2 ^ (prefixWord ++ tailWord_3561949).sum := by decide
  have hdescent : baseEnd_3561949 < baseStart_3561949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561951 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 1, 4]
def baseStart_3561951 : Nat := 118140960795 + 3561951 * 2 ^ 59
def prefixEnd_3561951 : Nat := 4983230072969 + 3 ^ 40 * 3561951 * 2
def baseEnd_3561951 : Nat := 1219328620508732389354261

theorem tailTrace_3561951 : CollatzResearch.WordTrace tailWord_3561951 prefixEnd_3561951 1219328620508732389354261 := by
  unfold tailWord_3561951
  simp only [CollatzResearch.WordTrace]
  refine ⟨129915025918667334644061707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86610017279111556429374471 129915025918667334644061707)
  ·
    refine ⟨194872538878001001966092561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129915025918667334644061707 194872538878001001966092561)
    ·
      refine ⟨146154404158500751474569421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194872538878001001966092561 146154404158500751474569421)
      ·
        refine ⟨54807901559437781802963533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146154404158500751474569421 54807901559437781802963533)
        ·
          refine ⟨20552963084789168176111325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54807901559437781802963533 20552963084789168176111325)
          ·
            refine ⟨7707361156795938066041747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20552963084789168176111325 7707361156795938066041747)
            ·
              refine ⟨11561041735193907099062621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707361156795938066041747 11561041735193907099062621)
              ·
                refine ⟨4335390650697715162148483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11561041735193907099062621 4335390650697715162148483)
                ·
                  refine ⟨6503085976046572743222725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335390650697715162148483 6503085976046572743222725)
                  ·
                    refine ⟨1219328620508732389354261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6503085976046572743222725 1219328620508732389354261)
                    ·
                      rfl

theorem cell22_3561951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_3561951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561951 prefixEnd_3561951 := by exact prefixLift 3561951
  have htrace : WordTrace (prefixWord ++ tailWord_3561951) baseStart_3561951 baseEnd_3561951 := by
    simpa [prefixWord, tailWord_3561951, baseEnd_3561951] using wordTrace_append hprefix tailTrace_3561951
  have hstable : (prefixWord ++ tailWord_3561951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561951).length < 2 ^ (prefixWord ++ tailWord_3561951).sum := by decide
  have hdescent : baseEnd_3561951 < baseStart_3561951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561966 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_3561966 : Nat := 118140960795 + 3561966 * 2 ^ 59
def prefixEnd_3561966 : Nat := 4983230072969 + 3 ^ 40 * 3561966 * 2
def baseEnd_3561966 : Nat := 406444585105092450076405

theorem tailTrace_3561966 : CollatzResearch.WordTrace tailWord_3561966 prefixEnd_3561966 406444585105092450076405 := by
  unfold tailWord_3561966
  simp only [CollatzResearch.WordTrace]
  refine ⟨16239446626701624025732219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86610382009075328137238501 16239446626701624025732219)
  ·
    refine ⟨24359169940052436038598329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16239446626701624025732219 24359169940052436038598329)
    ·
      refine ⟨18269377455039327028948747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24359169940052436038598329 18269377455039327028948747)
      ·
        refine ⟨27404066182558990543423121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18269377455039327028948747 27404066182558990543423121)
        ·
          refine ⟨20553049636919242907567341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27404066182558990543423121 20553049636919242907567341)
          ·
            refine ⟨7707393613844716090337753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20553049636919242907567341 7707393613844716090337753)
            ·
              refine ⟨5780545210383537067753315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7707393613844716090337753 5780545210383537067753315)
              ·
                refine ⟨8670817815575305601629973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5780545210383537067753315 8670817815575305601629973)
                ·
                  refine ⟨406444585105092450076405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8670817815575305601629973 406444585105092450076405)
                  ·
                    rfl

theorem cell22_3561966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_3561966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561966 prefixEnd_3561966 := by exact prefixLift 3561966
  have htrace : WordTrace (prefixWord ++ tailWord_3561966) baseStart_3561966 baseEnd_3561966 := by
    simpa [prefixWord, tailWord_3561966, baseEnd_3561966] using wordTrace_append hprefix tailTrace_3561966
  have hstable : (prefixWord ++ tailWord_3561966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561966).length < 2 ^ (prefixWord ++ tailWord_3561966).sum := by decide
  have hdescent : baseEnd_3561966 < baseStart_3561966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561994 : List Nat := [3, 1, 2, 2, 2, 1, 3, 8]
def baseStart_3561994 : Nat := 118140960795 + 3561994 * 2 ^ 59
def prefixEnd_3561994 : Nat := 4983230072969 + 3 ^ 40 * 3561994 * 2
def baseEnd_3561994 : Nat := 135482593365277178947681

theorem tailTrace_3561994 : CollatzResearch.WordTrace tailWord_3561994 prefixEnd_3561994 135482593365277178947681 := by
  unfold tailWord_3561994
  simp only [CollatzResearch.WordTrace]
  refine ⟨32479148564377888246969259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86611062838341035325251357 32479148564377888246969259)
  ·
    refine ⟨48718722846566832370453889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32479148564377888246969259 48718722846566832370453889)
    ·
      refine ⟨36539042134925124277840417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48718722846566832370453889 36539042134925124277840417)
      ·
        refine ⟨27404281601193843208380313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36539042134925124277840417 27404281601193843208380313)
        ·
          refine ⟨20553211200895382406285235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27404281601193843208380313 20553211200895382406285235)
          ·
            refine ⟨30829816801343073609427853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20553211200895382406285235 30829816801343073609427853)
            ·
              refine ⟨11561181300503652603535445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30829816801343073609427853 11561181300503652603535445)
              ·
                refine ⟨135482593365277178947681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11561181300503652603535445 135482593365277178947681)
                ·
                  rfl

theorem cell22_3561994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_3561994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3561994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3561994 prefixEnd_3561994 := by exact prefixLift 3561994
  have htrace : WordTrace (prefixWord ++ tailWord_3561994) baseStart_3561994 baseEnd_3561994 := by
    simpa [prefixWord, tailWord_3561994, baseEnd_3561994] using wordTrace_append hprefix tailTrace_3561994
  have hstable : (prefixWord ++ tailWord_3561994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561994).length < 2 ^ (prefixWord ++ tailWord_3561994).sum := by decide
  have hdescent : baseEnd_3561994 < baseStart_3561994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562088 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 2, 5]
def baseStart_3562088 : Nat := 118140960795 + 3562088 * 2 ^ 59
def prefixEnd_3562088 : Nat := 4983230072969 + 3 ^ 40 * 3562088 * 2
def baseEnd_3562088 : Nat := 1219375518408509698678841

theorem tailTrace_3562088 : CollatzResearch.WordTrace tailWord_3562088 prefixEnd_3562088 1219375518408509698678841 := by
  unfold tailWord_3562088
  simp only [CollatzResearch.WordTrace]
  refine ⟨64960011359585503520899459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86613348479447338027865945 64960011359585503520899459)
  ·
    refine ⟨97440017039378255281349189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64960011359585503520899459 97440017039378255281349189)
    ·
      refine ⟨18270003194883422865252973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97440017039378255281349189 18270003194883422865252973)
      ·
        refine ⟨6851251198081283574469865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18270003194883422865252973 6851251198081283574469865)
        ·
          refine ⟨5138438398560962680852399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6851251198081283574469865 5138438398560962680852399)
          ·
            refine ⟨7707657597841444021278599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138438398560962680852399 7707657597841444021278599)
            ·
              refine ⟨11561486396762166031917899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707657597841444021278599 11561486396762166031917899)
              ·
                refine ⟨17342229595143249047876849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11561486396762166031917899 17342229595143249047876849)
                ·
                  refine ⟨13006672196357436785907637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17342229595143249047876849 13006672196357436785907637)
                  ·
                    refine ⟨1219375518408509698678841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13006672196357436785907637 1219375518408509698678841)
                    ·
                      rfl

theorem cell22_3562088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_3562088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562088 prefixEnd_3562088 := by exact prefixLift 3562088
  have htrace : WordTrace (prefixWord ++ tailWord_3562088) baseStart_3562088 baseEnd_3562088 := by
    simpa [prefixWord, tailWord_3562088, baseEnd_3562088] using wordTrace_append hprefix tailTrace_3562088
  have hstable : (prefixWord ++ tailWord_3562088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562088).length < 2 ^ (prefixWord ++ tailWord_3562088).sum := by decide
  have hdescent : baseEnd_3562088 < baseStart_3562088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562163 : List Nat := [1, 1, 1, 2, 3, 6, 2, 6]
def baseStart_3562163 : Nat := 118140960795 + 3562163 * 2 ^ 59
def prefixEnd_3562163 : Nat := 4983230072969 + 3 ^ 40 * 3562163 * 2
def baseEnd_3562163 : Nat := 135489021382359389228179

theorem tailTrace_3562163 : CollatzResearch.WordTrace tailWord_3562163 prefixEnd_3562163 135489021382359389228179 := by
  unfold tailWord_3562163
  simp only [CollatzResearch.WordTrace]
  refine ⟨129922758193899294850779143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86615172129266196567186095 129922758193899294850779143)
  ·
    refine ⟨194884137290848942276168715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129922758193899294850779143 194884137290848942276168715)
    ·
      refine ⟨292326205936273413414253073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194884137290848942276168715 292326205936273413414253073)
      ·
        refine ⟨219244654452205060060689805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292326205936273413414253073 219244654452205060060689805)
        ·
          refine ⟨82216745419576897522758677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219244654452205060060689805 82216745419576897522758677)
          ·
            refine ⟨3853909941542667071379313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82216745419576897522758677 3853909941542667071379313)
            ·
              refine ⟨2890432456157000303534485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3853909941542667071379313 2890432456157000303534485)
              ·
                refine ⟨135489021382359389228179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2890432456157000303534485 135489021382359389228179)
                ·
                  rfl

theorem cell22_3562163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 6].length) (baseStart_3562163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562163 prefixEnd_3562163 := by exact prefixLift 3562163
  have htrace : WordTrace (prefixWord ++ tailWord_3562163) baseStart_3562163 baseEnd_3562163 := by
    simpa [prefixWord, tailWord_3562163, baseEnd_3562163] using wordTrace_append hprefix tailTrace_3562163
  have hstable : (prefixWord ++ tailWord_3562163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562163).length < 2 ^ (prefixWord ++ tailWord_3562163).sum := by decide
  have hdescent : baseEnd_3562163 < baseStart_3562163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562251 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 5, 5]
def baseStart_3562251 : Nat := 118140960795 + 3562251 * 2 ^ 59
def prefixEnd_3562251 : Nat := 4983230072969 + 3 ^ 40 * 3562251 * 2
def baseEnd_3562251 : Nat := 1219431316639631606853341

theorem tailTrace_3562251 : CollatzResearch.WordTrace tailWord_3562251 prefixEnd_3562251 1219431316639631606853341 := by
  unfold tailWord_3562251
  simp only [CollatzResearch.WordTrace]
  refine ⟨129925967817580485879982607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86617311878386990586655071 129925967817580485879982607)
  ·
    refine ⟨194888951726370728819973911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129925967817580485879982607 194888951726370728819973911)
    ·
      refine ⟨292333427589556093229960867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194888951726370728819973911 292333427589556093229960867)
      ·
        refine ⟨438500141384334139844941301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292333427589556093229960867 438500141384334139844941301)
        ·
          refine ⟨41109388254781325610463247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 438500141384334139844941301 41109388254781325610463247)
          ·
            refine ⟨61664082382171988415694871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41109388254781325610463247 61664082382171988415694871)
            ·
              refine ⟨92496123573257982623542307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61664082382171988415694871 92496123573257982623542307)
              ·
                refine ⟨138744185359886973935313461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92496123573257982623542307 138744185359886973935313461)
                ·
                  refine ⟨13007267377489403806435637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138744185359886973935313461 13007267377489403806435637)
                  ·
                    refine ⟨1219431316639631606853341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13007267377489403806435637 1219431316639631606853341)
                    ·
                      rfl

theorem cell22_3562251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_3562251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562251 prefixEnd_3562251 := by exact prefixLift 3562251
  have htrace : WordTrace (prefixWord ++ tailWord_3562251) baseStart_3562251 baseEnd_3562251 := by
    simpa [prefixWord, tailWord_3562251, baseEnd_3562251] using wordTrace_append hprefix tailTrace_3562251
  have hstable : (prefixWord ++ tailWord_3562251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562251).length < 2 ^ (prefixWord ++ tailWord_3562251).sum := by decide
  have hdescent : baseEnd_3562251 < baseStart_3562251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562268 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_3562268 : Nat := 118140960795 + 3562268 * 2 ^ 59
def prefixEnd_3562268 : Nat := 4983230072969 + 3 ^ 40 * 3562268 * 2
def baseEnd_3562268 : Nat := 1219437136087049229178289

theorem tailTrace_3562268 : CollatzResearch.WordTrace tailWord_3562268 prefixEnd_3562268 1219437136087049229178289 := by
  unfold tailWord_3562268
  simp only [CollatzResearch.WordTrace]
  refine ⟨64963293929259448891675729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86617725239012598522234305 64963293929259448891675729)
  ·
    refine ⟨48722470446944586668756797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64963293929259448891675729 48722470446944586668756797)
    ·
      refine ⟨18270926417604220000783799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48722470446944586668756797 18270926417604220000783799)
      ·
        refine ⟨27406389626406330001175699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18270926417604220000783799 27406389626406330001175699)
        ·
          refine ⟨41109584439609495001763549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27406389626406330001175699 41109584439609495001763549)
          ·
            refine ⟨15416094164853560625661331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41109584439609495001763549 15416094164853560625661331)
            ·
              refine ⟨23124141247280340938491997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15416094164853560625661331 23124141247280340938491997)
              ·
                refine ⟨8671552967730127851934499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23124141247280340938491997 8671552967730127851934499)
                ·
                  refine ⟨13007329451595191777901749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8671552967730127851934499 13007329451595191777901749)
                  ·
                    refine ⟨1219437136087049229178289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13007329451595191777901749 1219437136087049229178289)
                    ·
                      rfl

theorem cell22_3562268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_3562268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562268 prefixEnd_3562268 := by exact prefixLift 3562268
  have htrace : WordTrace (prefixWord ++ tailWord_3562268) baseStart_3562268 baseEnd_3562268 := by
    simpa [prefixWord, tailWord_3562268, baseEnd_3562268] using wordTrace_append hprefix tailTrace_3562268
  have hstable : (prefixWord ++ tailWord_3562268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562268).length < 2 ^ (prefixWord ++ tailWord_3562268).sum := by decide
  have hdescent : baseEnd_3562268 < baseStart_3562268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562298 : List Nat := [3, 1, 1, 1, 6, 1, 9]
def baseStart_3562298 : Nat := 118140960795 + 3562298 * 2 ^ 59
def prefixEnd_3562298 : Nat := 4983230072969 + 3 ^ 40 * 3562298 * 2
def baseEnd_3562298 : Nat := 45164718729634783367711

theorem tailTrace_3562298 : CollatzResearch.WordTrace tailWord_3562298 prefixEnd_3562298 45164718729634783367711 := by
  unfold tailWord_3562298
  simp only [CollatzResearch.WordTrace]
  refine ⟨32481920512102553226735887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86618454698940141937962365 32481920512102553226735887)
  ·
    refine ⟨48722880768153829840103831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32481920512102553226735887 48722880768153829840103831)
    ·
      refine ⟨73084321152230744760155747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48722880768153829840103831 73084321152230744760155747)
      ·
        refine ⟨109626481728346117140233621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73084321152230744760155747 109626481728346117140233621)
        ·
          refine ⟨5138741331016224240948451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109626481728346117140233621 5138741331016224240948451)
          ·
            refine ⟨7708111996524336361422677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138741331016224240948451 7708111996524336361422677)
            ·
              refine ⟨45164718729634783367711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7708111996524336361422677 45164718729634783367711)
              ·
                rfl

theorem cell22_3562298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 9].length) (baseStart_3562298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562298 prefixEnd_3562298 := by exact prefixLift 3562298
  have htrace : WordTrace (prefixWord ++ tailWord_3562298) baseStart_3562298 baseEnd_3562298 := by
    simpa [prefixWord, tailWord_3562298, baseEnd_3562298] using wordTrace_append hprefix tailTrace_3562298
  have hstable : (prefixWord ++ tailWord_3562298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562298).length < 2 ^ (prefixWord ++ tailWord_3562298).sum := by decide
  have hdescent : baseEnd_3562298 < baseStart_3562298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562302 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_3562302 : Nat := 118140960795 + 3562302 * 2 ^ 59
def prefixEnd_3562302 : Nat := 4983230072969 + 3 ^ 40 * 3562302 * 2
def baseEnd_3562302 : Nat := 1219448774981884473828185

theorem tailTrace_3562302 : CollatzResearch.WordTrace tailWord_3562302 prefixEnd_3562302 1219448774981884473828185 := by
  unfold tailWord_3562302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16240978492549465198761145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86618551960263814393392773 16240978492549465198761145)
  ·
    refine ⟨12180733869412098899070859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16240978492549465198761145 12180733869412098899070859)
    ·
      refine ⟨18271100804118148348606289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12180733869412098899070859 18271100804118148348606289)
      ·
        refine ⟨13703325603088611261454717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18271100804118148348606289 13703325603088611261454717)
        ·
          refine ⟨5138747101158229223045519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13703325603088611261454717 5138747101158229223045519)
          ·
            refine ⟨7708120651737343834568279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138747101158229223045519 7708120651737343834568279)
            ·
              refine ⟨11562180977606015751852419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7708120651737343834568279 11562180977606015751852419)
              ·
                refine ⟨17343271466409023627778629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11562180977606015751852419 17343271466409023627778629)
                ·
                  refine ⟨3251863399951691930208493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17343271466409023627778629 3251863399951691930208493)
                  ·
                    refine ⟨1219448774981884473828185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3251863399951691930208493 1219448774981884473828185)
                    ·
                      rfl

theorem cell22_3562302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_3562302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562302 prefixEnd_3562302 := by exact prefixLift 3562302
  have htrace : WordTrace (prefixWord ++ tailWord_3562302) baseStart_3562302 baseEnd_3562302 := by
    simpa [prefixWord, tailWord_3562302, baseEnd_3562302] using wordTrace_append hprefix tailTrace_3562302
  have hstable : (prefixWord ++ tailWord_3562302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562302).length < 2 ^ (prefixWord ++ tailWord_3562302).sum := by decide
  have hdescent : baseEnd_3562302 < baseStart_3562302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562330 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 3, 3]
def baseStart_3562330 : Nat := 118140960795 + 3562330 * 2 ^ 59
def prefixEnd_3562330 : Nat := 4983230072969 + 3 ^ 40 * 3562330 * 2
def baseEnd_3562330 : Nat := 1219458359954101734128099

theorem tailTrace_3562330 : CollatzResearch.WordTrace tailWord_3562330 prefixEnd_3562330 1219458359954101734128099 := by
  unfold tailWord_3562330
  simp only [CollatzResearch.WordTrace]
  refine ⟨32482212296073570593027111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86619232789529521581405629 32482212296073570593027111)
  ·
    refine ⟨48723318444110355889540667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32482212296073570593027111 48723318444110355889540667)
    ·
      refine ⟨73084977666165533834311001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48723318444110355889540667 73084977666165533834311001)
      ·
        refine ⟨54813733249624150375733251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73084977666165533834311001 54813733249624150375733251)
        ·
          refine ⟨82220599874436225563599877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54813733249624150375733251 82220599874436225563599877)
          ·
            refine ⟨15416362476456792293174977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82220599874436225563599877 15416362476456792293174977)
            ·
              refine ⟨11562271857342594219881233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15416362476456792293174977 11562271857342594219881233)
              ·
                refine ⟨8671703893006945664910925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11562271857342594219881233 8671703893006945664910925)
                ·
                  refine ⟨3251888959877604624341597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8671703893006945664910925 3251888959877604624341597)
                  ·
                    refine ⟨1219458359954101734128099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3251888959877604624341597 1219458359954101734128099)
                    ·
                      rfl

theorem cell22_3562330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_3562330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562330 prefixEnd_3562330 := by exact prefixLift 3562330
  have htrace : WordTrace (prefixWord ++ tailWord_3562330) baseStart_3562330 baseEnd_3562330 := by
    simpa [prefixWord, tailWord_3562330, baseEnd_3562330] using wordTrace_append hprefix tailTrace_3562330
  have hstable : (prefixWord ++ tailWord_3562330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562330).length < 2 ^ (prefixWord ++ tailWord_3562330).sum := by decide
  have hdescent : baseEnd_3562330 < baseStart_3562330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562332 : List Nat := [2, 2, 4, 2, 1, 3, 2, 6]
def baseStart_3562332 : Nat := 118140960795 + 3562332 * 2 ^ 59
def prefixEnd_3562332 : Nat := 4983230072969 + 3 ^ 40 * 3562332 * 2
def baseEnd_3562332 : Nat := 135495449399441599508677

theorem tailTrace_3562332 : CollatzResearch.WordTrace tailWord_3562332 prefixEnd_3562332 135495449399441599508677 := by
  unfold tailWord_3562332
  simp only [CollatzResearch.WordTrace]
  refine ⟨64964461065143518356840625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86619281420191357809120833 64964461065143518356840625)
  ·
    refine ⟨48723345798857638767630469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64964461065143518356840625 48723345798857638767630469)
    ·
      refine ⟨9135627337285807268930713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48723345798857638767630469 9135627337285807268930713)
      ·
        refine ⟨6851720502964355451698035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9135627337285807268930713 6851720502964355451698035)
        ·
          refine ⟨10277580754446533177547053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6851720502964355451698035 10277580754446533177547053)
          ·
            refine ⟨3854092782917449941580145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10277580754446533177547053 3854092782917449941580145)
            ·
              refine ⟨2890569587188087456185109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3854092782917449941580145 2890569587188087456185109)
              ·
                refine ⟨135495449399441599508677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2890569587188087456185109 135495449399441599508677)
                ·
                  rfl

theorem cell22_3562332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 6].length) (baseStart_3562332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562332 prefixEnd_3562332 := by exact prefixLift 3562332
  have htrace : WordTrace (prefixWord ++ tailWord_3562332) baseStart_3562332 baseEnd_3562332 := by
    simpa [prefixWord, tailWord_3562332, baseEnd_3562332] using wordTrace_append hprefix tailTrace_3562332
  have hstable : (prefixWord ++ tailWord_3562332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562332).length < 2 ^ (prefixWord ++ tailWord_3562332).sum := by decide
  have hdescent : baseEnd_3562332 < baseStart_3562332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562343 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 7]
def baseStart_3562343 : Nat := 118140960795 + 3562343 * 2 ^ 59
def prefixEnd_3562343 : Nat := 4983230072969 + 3 ^ 40 * 3562343 * 2
def baseEnd_3562343 : Nat := 406487603373258011184353

theorem tailTrace_3562343 : CollatzResearch.WordTrace tailWord_3562343 prefixEnd_3562343 406487603373258011184353 := by
  unfold tailWord_3562343
  simp only [CollatzResearch.WordTrace]
  refine ⟨129929323333247185592331683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86619548888831457061554455 129929323333247185592331683)
  ·
    refine ⟨194893984999870778388497525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129929323333247185592331683 194893984999870778388497525)
    ·
      refine ⟨18271311093737885473921643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194893984999870778388497525 18271311093737885473921643)
      ·
        refine ⟨27406966640606828210882465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18271311093737885473921643 27406966640606828210882465)
        ·
          refine ⟨20555224980455121158161849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27406966640606828210882465 20555224980455121158161849)
          ·
            refine ⟨15416418735341340868621387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20555224980455121158161849 15416418735341340868621387)
            ·
              refine ⟨23124628103012011302932081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15416418735341340868621387 23124628103012011302932081)
              ·
                refine ⟨17343471077259008477199061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23124628103012011302932081 17343471077259008477199061)
                ·
                  refine ⟨406487603373258011184353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17343471077259008477199061 406487603373258011184353)
                  ·
                    rfl

theorem cell22_3562343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 7].length) (baseStart_3562343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562343 prefixEnd_3562343 := by exact prefixLift 3562343
  have htrace : WordTrace (prefixWord ++ tailWord_3562343) baseStart_3562343 baseEnd_3562343 := by
    simpa [prefixWord, tailWord_3562343, baseEnd_3562343] using wordTrace_append hprefix tailTrace_3562343
  have hstable : (prefixWord ++ tailWord_3562343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562343).length < 2 ^ (prefixWord ++ tailWord_3562343).sum := by decide
  have hdescent : baseEnd_3562343 < baseStart_3562343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562347 : List Nat := [1, 1, 1, 1, 2, 2, 7, 3, 1, 3]
def baseStart_3562347 : Nat := 118140960795 + 3562347 * 2 ^ 59
def prefixEnd_3562347 : Nat := 4983230072969 + 3 ^ 40 * 3562347 * 2
def baseEnd_3562347 : Nat := 1219464179401519356453047

theorem tailTrace_3562347 : CollatzResearch.WordTrace tailWord_3562347 prefixEnd_3562347 1219464179401519356453047 := by
  unfold tailWord_3562347
  simp only [CollatzResearch.WordTrace]
  refine ⟨129929469225232694275477295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86619646150155129516984863 129929469225232694275477295)
  ·
    refine ⟨194894203837849041413215943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129929469225232694275477295 194894203837849041413215943)
    ·
      refine ⟨292341305756773562119823915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194894203837849041413215943 292341305756773562119823915)
      ·
        refine ⟨438511958635160343179735873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292341305756773562119823915 438511958635160343179735873)
        ·
          refine ⟨328883968976370257384801905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438511958635160343179735873 328883968976370257384801905)
          ·
            refine ⟨246662976732277693038601429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328883968976370257384801905 246662976732277693038601429)
            ·
              refine ⟨5781163517162758430592221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 246662976732277693038601429 5781163517162758430592221)
              ·
                refine ⟨2167936318936034411472083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5781163517162758430592221 2167936318936034411472083)
                ·
                  refine ⟨3251904478404051617208125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167936318936034411472083 3251904478404051617208125)
                  ·
                    refine ⟨1219464179401519356453047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3251904478404051617208125 1219464179401519356453047)
                    ·
                      rfl

theorem cell22_3562347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 1, 3].length) (baseStart_3562347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562347 prefixEnd_3562347 := by exact prefixLift 3562347
  have htrace : WordTrace (prefixWord ++ tailWord_3562347) baseStart_3562347 baseEnd_3562347 := by
    simpa [prefixWord, tailWord_3562347, baseEnd_3562347] using wordTrace_append hprefix tailTrace_3562347
  have hstable : (prefixWord ++ tailWord_3562347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562347).length < 2 ^ (prefixWord ++ tailWord_3562347).sum := by decide
  have hdescent : baseEnd_3562347 < baseStart_3562347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562370 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3562370 : Nat := 118140960795 + 3562370 * 2 ^ 59
def prefixEnd_3562370 : Nat := 4983230072969 + 3 ^ 40 * 3562370 * 2
def baseEnd_3562370 : Nat := 1219472052771554963127977

theorem tailTrace_3562370 : CollatzResearch.WordTrace tailWord_3562370 prefixEnd_3562370 1219472052771554963127977 := by
  unfold tailWord_3562370
  simp only [CollatzResearch.WordTrace]
  refine ⟨32482577026037342300891141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86620205402766246135709709 32482577026037342300891141)
  ·
    refine ⟨6090483192382001681417089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32482577026037342300891141 6090483192382001681417089)
    ·
      refine ⟨4567862394286501261062817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6090483192382001681417089 4567862394286501261062817)
      ·
        refine ⟨3425896795714875945797113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4567862394286501261062817 3425896795714875945797113)
        ·
          refine ⟨2569422596786156959347835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3425896795714875945797113 2569422596786156959347835)
          ·
            refine ⟨3854133895179235439021753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569422596786156959347835 3854133895179235439021753)
            ·
              refine ⟨2890600421384426579266315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3854133895179235439021753 2890600421384426579266315)
              ·
                refine ⟨4335900632076639868899473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2890600421384426579266315 4335900632076639868899473)
                ·
                  refine ⟨3251925474057479901674605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4335900632076639868899473 3251925474057479901674605)
                  ·
                    refine ⟨1219472052771554963127977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3251925474057479901674605 1219472052771554963127977)
                    ·
                      rfl

theorem cell22_3562370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3562370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562370 prefixEnd_3562370 := by exact prefixLift 3562370
  have htrace : WordTrace (prefixWord ++ tailWord_3562370) baseStart_3562370 baseEnd_3562370 := by
    simpa [prefixWord, tailWord_3562370, baseEnd_3562370] using wordTrace_append hprefix tailTrace_3562370
  have hstable : (prefixWord ++ tailWord_3562370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562370).length < 2 ^ (prefixWord ++ tailWord_3562370).sum := by decide
  have hdescent : baseEnd_3562370 < baseStart_3562370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562377 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 5]
def baseStart_3562377 : Nat := 118140960795 + 3562377 * 2 ^ 59
def prefixEnd_3562377 : Nat := 4983230072969 + 3 ^ 40 * 3562377 * 2
def baseEnd_3562377 : Nat := 406491483004869759400985

theorem tailTrace_3562377 : CollatzResearch.WordTrace tailWord_3562377 prefixEnd_3562377 406491483004869759400985 := by
  unfold tailWord_3562377
  simp only [CollatzResearch.WordTrace]
  refine ⟨129930563415124009399069385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86620375610082672932712923 129930563415124009399069385)
  ·
    refine ⟨97447922561343007049302039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129930563415124009399069385 97447922561343007049302039)
    ·
      refine ⟨146171883842014510573953059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97447922561343007049302039 146171883842014510573953059)
      ·
        refine ⟨219257825763021765860929589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146171883842014510573953059 219257825763021765860929589)
        ·
          refine ⟨20555421165283290549462149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219257825763021765860929589 20555421165283290549462149)
          ·
            refine ⟨3854141468490616978024153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20555421165283290549462149 3854141468490616978024153)
            ·
              refine ⟨2890606101367962733518115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3854141468490616978024153 2890606101367962733518115)
              ·
                refine ⟨4335909152051944100277173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2890606101367962733518115 4335909152051944100277173)
                ·
                  refine ⟨406491483004869759400985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4335909152051944100277173 406491483004869759400985)
                  ·
                    rfl

theorem cell22_3562377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 5].length) (baseStart_3562377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562377 prefixEnd_3562377 := by exact prefixLift 3562377
  have htrace : WordTrace (prefixWord ++ tailWord_3562377) baseStart_3562377 baseEnd_3562377 := by
    simpa [prefixWord, tailWord_3562377, baseEnd_3562377] using wordTrace_append hprefix tailTrace_3562377
  have hstable : (prefixWord ++ tailWord_3562377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562377).length < 2 ^ (prefixWord ++ tailWord_3562377).sum := by decide
  have hdescent : baseEnd_3562377 < baseStart_3562377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562403 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 3, 5]
def baseStart_3562403 : Nat := 118140960795 + 3562403 * 2 ^ 59
def prefixEnd_3562403 : Nat := 4983230072969 + 3 ^ 40 * 3562403 * 2
def baseEnd_3562403 : Nat := 1219483349345953877052875

theorem tailTrace_3562403 : CollatzResearch.WordTrace tailWord_3562403 prefixEnd_3562403 1219483349345953877052875 := by
  unfold tailWord_3562403
  simp only [CollatzResearch.WordTrace]
  refine ⟨129931511713029815839515863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86621007808686543893010575 129931511713029815839515863)
  ·
    refine ⟨194897267569544723759273795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129931511713029815839515863 194897267569544723759273795)
    ·
      refine ⟨292345901354317085638910693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194897267569544723759273795 292345901354317085638910693)
      ·
        refine ⟨54814856503934453557295755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292345901354317085638910693 54814856503934453557295755)
        ·
          refine ⟨82222284755901680335943633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54814856503934453557295755 82222284755901680335943633)
          ·
            refine ⟨61666713566926260251957725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82222284755901680335943633 61666713566926260251957725)
            ·
              refine ⟨23125017587597347594484147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61666713566926260251957725 23125017587597347594484147)
              ·
                refine ⟨34687526381396021391726221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23125017587597347594484147 34687526381396021391726221)
                ·
                  refine ⟨13007822393023508021897333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34687526381396021391726221 13007822393023508021897333)
                  ·
                    refine ⟨1219483349345953877052875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13007822393023508021897333 1219483349345953877052875)
                    ·
                      rfl

theorem cell22_3562403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_3562403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562403 prefixEnd_3562403 := by exact prefixLift 3562403
  have htrace : WordTrace (prefixWord ++ tailWord_3562403) baseStart_3562403 baseEnd_3562403 := by
    simpa [prefixWord, tailWord_3562403, baseEnd_3562403] using wordTrace_append hprefix tailTrace_3562403
  have hstable : (prefixWord ++ tailWord_3562403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562403).length < 2 ^ (prefixWord ++ tailWord_3562403).sum := by decide
  have hdescent : baseEnd_3562403 < baseStart_3562403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562418 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_3562418 : Nat := 118140960795 + 3562418 * 2 ^ 59
def prefixEnd_3562418 : Nat := 4983230072969 + 3 ^ 40 * 3562418 * 2
def baseEnd_3562418 : Nat := 1219488484152498837927829

theorem tailTrace_3562418 : CollatzResearch.WordTrace tailWord_3562418 prefixEnd_3562418 1219488484152498837927829 := by
  unfold tailWord_3562418
  simp only [CollatzResearch.WordTrace]
  refine ⟨32483014701993868350327977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86621372538650315600874605 32483014701993868350327977)
  ·
    refine ⟨24362261026495401262745983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32483014701993868350327977 24362261026495401262745983)
    ·
      refine ⟨36543391539743101894118975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24362261026495401262745983 36543391539743101894118975)
      ·
        refine ⟨54815087309614652841178463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36543391539743101894118975 54815087309614652841178463)
        ·
          refine ⟨82222630964421979261767695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54815087309614652841178463 82222630964421979261767695)
          ·
            refine ⟨123333946446632968892651543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82222630964421979261767695 123333946446632968892651543)
            ·
              refine ⟨185000919669949453338977315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123333946446632968892651543 185000919669949453338977315)
              ·
                refine ⟨277501379504924180008465973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185000919669949453338977315 277501379504924180008465973)
                ·
                  refine ⟨26015754328586641875793685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 277501379504924180008465973 26015754328586641875793685)
                  ·
                    refine ⟨1219488484152498837927829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26015754328586641875793685 1219488484152498837927829)
                    ·
                      rfl

theorem cell22_3562418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_3562418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562418 prefixEnd_3562418 := by exact prefixLift 3562418
  have htrace : WordTrace (prefixWord ++ tailWord_3562418) baseStart_3562418 baseEnd_3562418 := by
    simpa [prefixWord, tailWord_3562418, baseEnd_3562418] using wordTrace_append hprefix tailTrace_3562418
  have hstable : (prefixWord ++ tailWord_3562418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562418).length < 2 ^ (prefixWord ++ tailWord_3562418).sum := by decide
  have hdescent : baseEnd_3562418 < baseStart_3562418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562452 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_3562452 : Nat := 118140960795 + 3562452 * 2 ^ 59
def prefixEnd_3562452 : Nat := 4983230072969 + 3 ^ 40 * 3562452 * 2
def baseEnd_3562452 : Nat := 1219500123047334082577725

theorem tailTrace_3562452 : CollatzResearch.WordTrace tailWord_3562452 prefixEnd_3562452 1219500123047334082577725 := by
  unfold tailWord_3562452
  simp only [CollatzResearch.WordTrace]
  refine ⟨64966649444926148604024805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86622199259901531472033073 64966649444926148604024805)
  ·
    refine ⟨12181246770923652863254651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64966649444926148604024805 12181246770923652863254651)
    ·
      refine ⟨18271870156385479294881977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12181246770923652863254651 18271870156385479294881977)
      ·
        refine ⟨13703902617289109471161483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18271870156385479294881977 13703902617289109471161483)
        ·
          refine ⟨20555853925933664206742225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13703902617289109471161483 20555853925933664206742225)
          ·
            refine ⟨15416890444450248155056669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20555853925933664206742225 15416890444450248155056669)
            ·
              refine ⟨5781333916668843058146251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15416890444450248155056669 5781333916668843058146251)
              ·
                refine ⟨8672000875003264587219377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781333916668843058146251 8672000875003264587219377)
                ·
                  refine ⟨6504000656252448440414533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8672000875003264587219377 6504000656252448440414533)
                  ·
                    refine ⟨1219500123047334082577725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6504000656252448440414533 1219500123047334082577725)
                    ·
                      rfl

theorem cell22_3562452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_3562452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562452 prefixEnd_3562452 := by exact prefixLift 3562452
  have htrace : WordTrace (prefixWord ++ tailWord_3562452) baseStart_3562452 baseEnd_3562452 := by
    simpa [prefixWord, tailWord_3562452, baseEnd_3562452] using wordTrace_append hprefix tailTrace_3562452
  have hstable : (prefixWord ++ tailWord_3562452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562452).length < 2 ^ (prefixWord ++ tailWord_3562452).sum := by decide
  have hdescent : baseEnd_3562452 < baseStart_3562452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562465 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 7, 3]
def baseStart_3562465 : Nat := 118140960795 + 3562465 * 2 ^ 59
def prefixEnd_3562465 : Nat := 4983230072969 + 3 ^ 40 * 3562465 * 2
def baseEnd_3562465 : Nat := 1219504573213006382002685

theorem tailTrace_3562465 : CollatzResearch.WordTrace tailWord_3562465 prefixEnd_3562465 1219504573213006382002685 := by
  unfold tailWord_3562465
  simp only [CollatzResearch.WordTrace]
  refine ⟨129933773038805200428272849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86622515359203466952181899 129933773038805200428272849)
  ·
    refine ⟨97450329779103900321204637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129933773038805200428272849 97450329779103900321204637)
    ·
      refine ⟨36543873667163962620451739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97450329779103900321204637 36543873667163962620451739)
      ·
        refine ⟨54815810500745943930677609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36543873667163962620451739 54815810500745943930677609)
        ·
          refine ⟨41111857875559457948008207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54815810500745943930677609 41111857875559457948008207)
          ·
            refine ⟨61667786813339186922012311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41111857875559457948008207 61667786813339186922012311)
            ·
              refine ⟨92501680220008780383018467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61667786813339186922012311 92501680220008780383018467)
              ·
                refine ⟨138752520330013170574527701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92501680220008780383018467 138752520330013170574527701)
                ·
                  refine ⟨3252012195234683685340493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 138752520330013170574527701 3252012195234683685340493)
                  ·
                    refine ⟨1219504573213006382002685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252012195234683685340493 1219504573213006382002685)
                    ·
                      rfl

theorem cell22_3562465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_3562465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562465 prefixEnd_3562465 := by exact prefixLift 3562465
  have htrace : WordTrace (prefixWord ++ tailWord_3562465) baseStart_3562465 baseEnd_3562465 := by
    simpa [prefixWord, tailWord_3562465, baseEnd_3562465] using wordTrace_append hprefix tailTrace_3562465
  have hstable : (prefixWord ++ tailWord_3562465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562465).length < 2 ^ (prefixWord ++ tailWord_3562465).sum := by decide
  have hdescent : baseEnd_3562465 < baseStart_3562465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562542 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3562542 : Nat := 118140960795 + 3562542 * 2 ^ 59
def prefixEnd_3562542 : Nat := 4983230072969 + 3 ^ 40 * 3562542 * 2
def baseEnd_3562542 : Nat := 1219530931886603847827449

theorem tailTrace_3562542 : CollatzResearch.WordTrace tailWord_3562542 prefixEnd_3562542 1219530931886603847827449 := by
  unfold tailWord_3562542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16242072682440780322353235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86624387639684161719217253 16242072682440780322353235)
  ·
    refine ⟨24363109023661170483529853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16242072682440780322353235 24363109023661170483529853)
    ·
      refine ⟨9136165883872938931323695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24363109023661170483529853 9136165883872938931323695)
      ·
        refine ⟨13704248825809408396985543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9136165883872938931323695 13704248825809408396985543)
        ·
          refine ⟨20556373238714112595478315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13704248825809408396985543 20556373238714112595478315)
          ·
            refine ⟨30834559858071168893217473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20556373238714112595478315 30834559858071168893217473)
            ·
              refine ⟨23125919893553376669913105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30834559858071168893217473 23125919893553376669913105)
              ·
                refine ⟨17344439920165032502434829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23125919893553376669913105 17344439920165032502434829)
                ·
                  refine ⟨6504164970061887188413061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17344439920165032502434829 6504164970061887188413061)
                  ·
                    refine ⟨1219530931886603847827449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6504164970061887188413061 1219530931886603847827449)
                    ·
                      rfl

theorem cell22_3562542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3562542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562542 prefixEnd_3562542 := by exact prefixLift 3562542
  have htrace : WordTrace (prefixWord ++ tailWord_3562542) baseStart_3562542 baseEnd_3562542 := by
    simpa [prefixWord, tailWord_3562542, baseEnd_3562542] using wordTrace_append hprefix tailTrace_3562542
  have hstable : (prefixWord ++ tailWord_3562542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562542).length < 2 ^ (prefixWord ++ tailWord_3562542).sum := by decide
  have hdescent : baseEnd_3562542 < baseStart_3562542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562570 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_3562570 : Nat := 118140960795 + 3562570 * 2 ^ 59
def prefixEnd_3562570 : Nat := 4983230072969 + 3 ^ 40 * 3562570 * 2
def baseEnd_3562570 : Nat := 1219540516858821108127363

theorem tailTrace_3562570 : CollatzResearch.WordTrace tailWord_3562570 prefixEnd_3562570 1219540516858821108127363 := by
  unfold tailWord_3562570
  simp only [CollatzResearch.WordTrace]
  refine ⟨32484400675856200840211291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86625068468949868907230109 32484400675856200840211291)
  ·
    refine ⟨48726601013784301260316937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32484400675856200840211291 48726601013784301260316937)
    ·
      refine ⟨36544950760338225945237703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48726601013784301260316937 36544950760338225945237703)
      ·
        refine ⟨54817426140507338917856555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36544950760338225945237703 54817426140507338917856555)
        ·
          refine ⟨82226139210761008376784833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54817426140507338917856555 82226139210761008376784833)
          ·
            refine ⟨61669604408070756282588625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82226139210761008376784833 61669604408070756282588625)
            ·
              refine ⟨46252203306053067211941469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61669604408070756282588625 46252203306053067211941469)
              ·
                refine ⟨17344576239769900204478051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46252203306053067211941469 17344576239769900204478051)
                ·
                  refine ⟨26016864359654850306717077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17344576239769900204478051 26016864359654850306717077)
                  ·
                    refine ⟨1219540516858821108127363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26016864359654850306717077 1219540516858821108127363)
                    ·
                      rfl

theorem cell22_3562570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_3562570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562570 prefixEnd_3562570 := by exact prefixLift 3562570
  have htrace : WordTrace (prefixWord ++ tailWord_3562570) baseStart_3562570 baseEnd_3562570 := by
    simpa [prefixWord, tailWord_3562570, baseEnd_3562570] using wordTrace_append hprefix tailTrace_3562570
  have hstable : (prefixWord ++ tailWord_3562570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562570).length < 2 ^ (prefixWord ++ tailWord_3562570).sum := by decide
  have hdescent : baseEnd_3562570 < baseStart_3562570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562602 : List Nat := [3, 1, 3, 2, 2, 1, 3, 7]
def baseStart_3562602 : Nat := 118140960795 + 3562602 * 2 ^ 59
def prefixEnd_3562602 : Nat := 4983230072969 + 3 ^ 40 * 3562602 * 2
def baseEnd_3562602 : Nat := 135505719012531521258585

theorem tailTrace_3562602 : CollatzResearch.WordTrace tailWord_3562602 prefixEnd_3562602 135505719012531521258585 := by
  unfold tailWord_3562602
  simp only [CollatzResearch.WordTrace]
  refine ⟨32484692459827218206502515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86625846559539248550673373 32484692459827218206502515)
  ·
    refine ⟨48727038689740827309753773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32484692459827218206502515 48727038689740827309753773)
    ·
      refine ⟨18272639508652810241157665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48727038689740827309753773 18272639508652810241157665)
      ·
        refine ⟨13704479631489607680868249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18272639508652810241157665 13704479631489607680868249)
        ·
          refine ⟨10278359723617205760651187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13704479631489607680868249 10278359723617205760651187)
          ·
            refine ⟨15417539585425808640976781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10278359723617205760651187 15417539585425808640976781)
            ·
              refine ⟨5781577344534678240366293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15417539585425808640976781 5781577344534678240366293)
              ·
                refine ⟨135505719012531521258585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5781577344534678240366293 135505719012531521258585)
                ·
                  rfl

theorem cell22_3562602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_3562602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562602 prefixEnd_3562602 := by exact prefixLift 3562602
  have htrace : WordTrace (prefixWord ++ tailWord_3562602) baseStart_3562602 baseEnd_3562602 := by
    simpa [prefixWord, tailWord_3562602, baseEnd_3562602] using wordTrace_append hprefix tailTrace_3562602
  have hstable : (prefixWord ++ tailWord_3562602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562602).length < 2 ^ (prefixWord ++ tailWord_3562602).sum := by decide
  have hdescent : baseEnd_3562602 < baseStart_3562602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562615 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 2, 6]
def baseStart_3562615 : Nat := 118140960795 + 3562615 * 2 ^ 59
def prefixEnd_3562615 : Nat := 4983230072969 + 3 ^ 40 * 3562615 * 2
def baseEnd_3562615 : Nat := 1219555921278455990752225

theorem tailTrace_3562615 : CollatzResearch.WordTrace tailWord_3562615 prefixEnd_3562615 1219555921278455990752225 := by
  unfold tailWord_3562615
  simp only [CollatzResearch.WordTrace]
  refine ⟨129939243988261776046233299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86626162658841184030822199 129939243988261776046233299)
  ·
    refine ⟨194908865982392664069349949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129939243988261776046233299 194908865982392664069349949)
    ·
      refine ⟨73090824743397249026006231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194908865982392664069349949 73090824743397249026006231)
      ·
        refine ⟨109636237115095873539009347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73090824743397249026006231 109636237115095873539009347)
        ·
          refine ⟨164454355672643810308514021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109636237115095873539009347 164454355672643810308514021)
          ·
            refine ⟨30835191688620714432846379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164454355672643810308514021 30835191688620714432846379)
            ·
              refine ⟨46252787532931071649269569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30835191688620714432846379 46252787532931071649269569)
              ·
                refine ⟨34689590649698303736952177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46252787532931071649269569 34689590649698303736952177)
                ·
                  refine ⟨26017192987273727802714133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34689590649698303736952177 26017192987273727802714133)
                  ·
                    refine ⟨1219555921278455990752225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26017192987273727802714133 1219555921278455990752225)
                    ·
                      rfl

theorem cell22_3562615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_3562615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562615 prefixEnd_3562615 := by exact prefixLift 3562615
  have htrace : WordTrace (prefixWord ++ tailWord_3562615) baseStart_3562615 baseEnd_3562615 := by
    simpa [prefixWord, tailWord_3562615, baseEnd_3562615] using wordTrace_append hprefix tailTrace_3562615
  have hstable : (prefixWord ++ tailWord_3562615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562615).length < 2 ^ (prefixWord ++ tailWord_3562615).sum := by decide
  have hdescent : baseEnd_3562615 < baseStart_3562615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562647 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 7]
def baseStart_3562647 : Nat := 118140960795 + 3562647 * 2 ^ 59
def prefixEnd_3562647 : Nat := 4983230072969 + 3 ^ 40 * 3562647 * 2
def baseEnd_3562647 : Nat := 406522291844139524650709

theorem tailTrace_3562647 : CollatzResearch.WordTrace tailWord_3562647 prefixEnd_3562647 406522291844139524650709 := by
  unfold tailWord_3562647
  simp only [CollatzResearch.WordTrace]
  refine ⟨129940411124145845511398195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86626940749430563674265463 129940411124145845511398195)
  ·
    refine ⟨194910616686218768267097293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129940411124145845511398195 194910616686218768267097293)
    ·
      refine ⟨73091481257332038100161485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194910616686218768267097293 73091481257332038100161485)
      ·
        refine ⟨27409305471499514287560557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73091481257332038100161485 27409305471499514287560557)
        ·
          refine ⟨10278489551812317857835209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27409305471499514287560557 10278489551812317857835209)
          ·
            refine ⟨7708867163859238393376407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10278489551812317857835209 7708867163859238393376407)
            ·
              refine ⟨11563300745788857590064611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7708867163859238393376407 11563300745788857590064611)
              ·
                refine ⟨17344951118683286385096917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11563300745788857590064611 17344951118683286385096917)
                ·
                  refine ⟨406522291844139524650709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17344951118683286385096917 406522291844139524650709)
                  ·
                    rfl

theorem cell22_3562647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 7].length) (baseStart_3562647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562647 prefixEnd_3562647 := by exact prefixLift 3562647
  have htrace : WordTrace (prefixWord ++ tailWord_3562647) baseStart_3562647 baseEnd_3562647 := by
    simpa [prefixWord, tailWord_3562647, baseEnd_3562647] using wordTrace_append hprefix tailTrace_3562647
  have hstable : (prefixWord ++ tailWord_3562647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562647).length < 2 ^ (prefixWord ++ tailWord_3562647).sum := by decide
  have hdescent : baseEnd_3562647 < baseStart_3562647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562709 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 6]
def baseStart_3562709 : Nat := 118140960795 + 3562709 * 2 ^ 59
def prefixEnd_3562709 : Nat := 4983230072969 + 3 ^ 40 * 3562709 * 2
def baseEnd_3562709 : Nat := 406529366466490359633979

theorem tailTrace_3562709 : CollatzResearch.WordTrace tailWord_3562709 prefixEnd_3562709 406529366466490359633979 := by
  unfold tailWord_3562709
  simp only [CollatzResearch.WordTrace]
  refine ⟨129942672449921230100155181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86628448299947486733436787 129942672449921230100155181)
  ·
    refine ⟨48728502168720461287558193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129942672449921230100155181 48728502168720461287558193)
    ·
      refine ⟨36546376626540345965668645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48728502168720461287558193 36546376626540345965668645)
      ·
        refine ⟨6852445617476314868562871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36546376626540345965668645 6852445617476314868562871)
        ·
          refine ⟨10278668426214472302844307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852445617476314868562871 10278668426214472302844307)
          ·
            refine ⟨15418002639321708454266461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10278668426214472302844307 15418002639321708454266461)
            ·
              refine ⟨5781750989745640670349923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15418002639321708454266461 5781750989745640670349923)
              ·
                refine ⟨8672626484618461005524885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781750989745640670349923 8672626484618461005524885)
                ·
                  refine ⟨406529366466490359633979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8672626484618461005524885 406529366466490359633979)
                  ·
                    rfl

theorem cell22_3562709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_3562709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562709 prefixEnd_3562709 := by exact prefixLift 3562709
  have htrace : WordTrace (prefixWord ++ tailWord_3562709) baseStart_3562709 baseEnd_3562709 := by
    simpa [prefixWord, tailWord_3562709, baseEnd_3562709] using wordTrace_append hprefix tailTrace_3562709
  have hstable : (prefixWord ++ tailWord_3562709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562709).length < 2 ^ (prefixWord ++ tailWord_3562709).sum := by decide
  have hdescent : baseEnd_3562709 < baseStart_3562709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562739 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 2, 4]
def baseStart_3562739 : Nat := 118140960795 + 3562739 * 2 ^ 59
def prefixEnd_3562739 : Nat := 4983230072969 + 3 ^ 40 * 3562739 * 2
def baseEnd_3562739 : Nat := 1219598369012561000651845

theorem tailTrace_3562739 : CollatzResearch.WordTrace tailWord_3562739 prefixEnd_3562739 1219598369012561000651845 := by
  unfold tailWord_3562739
  simp only [CollatzResearch.WordTrace]
  refine ⟨129943766639812545223747271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86629177759875030149164847 129943766639812545223747271)
  ·
    refine ⟨194915649959718817835620907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129943766639812545223747271 194915649959718817835620907)
    ·
      refine ⟨292373474939578226753431361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194915649959718817835620907 292373474939578226753431361)
      ·
        refine ⟨219280106204683670065073521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292373474939578226753431361 219280106204683670065073521)
        ·
          refine ⟨164460079653512752548805141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219280106204683670065073521 164460079653512752548805141)
          ·
            refine ⟨7709066233758410275725241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164460079653512752548805141 7709066233758410275725241)
            ·
              refine ⟨5781799675318807706793931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7709066233758410275725241 5781799675318807706793931)
              ·
                refine ⟨8672699512978211560190897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781799675318807706793931 8672699512978211560190897)
                ·
                  refine ⟨6504524634733658670143173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8672699512978211560190897 6504524634733658670143173)
                  ·
                    refine ⟨1219598369012561000651845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6504524634733658670143173 1219598369012561000651845)
                    ·
                      rfl

theorem cell22_3562739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 4].length) (baseStart_3562739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562739 prefixEnd_3562739 := by exact prefixLift 3562739
  have htrace : WordTrace (prefixWord ++ tailWord_3562739) baseStart_3562739 baseEnd_3562739 := by
    simpa [prefixWord, tailWord_3562739, baseEnd_3562739] using wordTrace_append hprefix tailTrace_3562739
  have hstable : (prefixWord ++ tailWord_3562739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562739).length < 2 ^ (prefixWord ++ tailWord_3562739).sum := by decide
  have hdescent : baseEnd_3562739 < baseStart_3562739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562754 : List Nat := [3, 4, 1, 1, 3, 10]
def baseStart_3562754 : Nat := 118140960795 + 3562754 * 2 ^ 59
def prefixEnd_3562754 : Nat := 4983230072969 + 3 ^ 40 * 3562754 * 2
def baseEnd_3562754 : Nat := 15056833380482789648479

theorem tailTrace_3562754 : CollatzResearch.WordTrace tailWord_3562754 prefixEnd_3562754 15056833380482789648479 := by
  unfold tailWord_3562754
  simp only [CollatzResearch.WordTrace]
  refine ⟨32486078433689550696385829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86629542489838801857028877 32486078433689550696385829)
  ·
    refine ⟨6091139706316790755572343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32486078433689550696385829 6091139706316790755572343)
    ·
      refine ⟨9136709559475186133358515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6091139706316790755572343 9136709559475186133358515)
      ·
        refine ⟨13705064339212779200037773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9136709559475186133358515 13705064339212779200037773)
        ·
          refine ⟨5139399127204792200014165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13705064339212779200037773 5139399127204792200014165)
          ·
            refine ⟨15056833380482789648479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5139399127204792200014165 15056833380482789648479)
            ·
              rfl

theorem cell22_3562754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 10].length) (baseStart_3562754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562754 prefixEnd_3562754 := by exact prefixLift 3562754
  have htrace : WordTrace (prefixWord ++ tailWord_3562754) baseStart_3562754 baseEnd_3562754 := by
    simpa [prefixWord, tailWord_3562754, baseEnd_3562754] using wordTrace_append hprefix tailTrace_3562754
  have hstable : (prefixWord ++ tailWord_3562754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562754).length < 2 ^ (prefixWord ++ tailWord_3562754).sum := by decide
  have hdescent : baseEnd_3562754 < baseStart_3562754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562760 : List Nat := [2, 1, 3, 2, 5, 1, 2, 2, 4]
def baseStart_3562760 : Nat := 118140960795 + 3562760 * 2 ^ 59
def prefixEnd_3562760 : Nat := 4983230072969 + 3 ^ 40 * 3562760 * 2
def baseEnd_3562760 : Nat := 406535185913907981958927

theorem tailTrace_3562760 : CollatzResearch.WordTrace tailWord_3562760 prefixEnd_3562760 406535185913907981958927 := by
  unfold tailWord_3562760
  simp only [CollatzResearch.WordTrace]
  refine ⟨64972266286368232905130867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86629688381824310540174489 64972266286368232905130867)
  ·
    refine ⟨97458399429552349357696301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64972266286368232905130867 97458399429552349357696301)
    ·
      refine ⟨36546899786082131009136113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97458399429552349357696301 36546899786082131009136113)
      ·
        refine ⟨27410174839561598256852085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36546899786082131009136113 27410174839561598256852085)
        ·
          refine ⟨2569703891208899836579883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27410174839561598256852085 2569703891208899836579883)
          ·
            refine ⟨3854555836813349754869825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569703891208899836579883 3854555836813349754869825)
            ·
              refine ⟨2890916877610012316152369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3854555836813349754869825 2890916877610012316152369)
              ·
                refine ⟨2168187658207509237114277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890916877610012316152369 2168187658207509237114277)
                ·
                  refine ⟨406535185913907981958927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2168187658207509237114277 406535185913907981958927)
                  ·
                    rfl

theorem cell22_3562760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 4].length) (baseStart_3562760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562760 prefixEnd_3562760 := by exact prefixLift 3562760
  have htrace : WordTrace (prefixWord ++ tailWord_3562760) baseStart_3562760 baseEnd_3562760 := by
    simpa [prefixWord, tailWord_3562760, baseEnd_3562760] using wordTrace_append hprefix tailTrace_3562760
  have hstable : (prefixWord ++ tailWord_3562760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562760).length < 2 ^ (prefixWord ++ tailWord_3562760).sum := by decide
  have hdescent : baseEnd_3562760 < baseStart_3562760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562769 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 3, 3]
def baseStart_3562769 : Nat := 118140960795 + 3562769 * 2 ^ 59
def prefixEnd_3562769 : Nat := 4983230072969 + 3 ^ 40 * 3562769 * 2
def baseEnd_3562769 : Nat := 1219608638625650922401753

theorem tailTrace_3562769 : CollatzResearch.WordTrace tailWord_3562769 prefixEnd_3562769 1219608638625650922401753 := by
  unfold tailWord_3562769
  simp only [CollatzResearch.WordTrace]
  refine ⟨129944860829703860347339361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86629907219802573564892907 129944860829703860347339361)
  ·
    refine ⟨97458645622277895260504521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129944860829703860347339361 97458645622277895260504521)
    ·
      refine ⟨73093984216708421445378391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97458645622277895260504521 73093984216708421445378391)
      ·
        refine ⟨109640976325062632168067587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73093984216708421445378391 109640976325062632168067587)
        ·
          refine ⟨164461464487593948252101381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109640976325062632168067587 164461464487593948252101381)
          ·
            refine ⟨30836524591423865297269009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164461464487593948252101381 30836524591423865297269009)
            ·
              refine ⟨23127393443567898972951757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30836524591423865297269009 23127393443567898972951757)
              ·
                refine ⟨8672772541337962114856909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23127393443567898972951757 8672772541337962114856909)
                ·
                  refine ⟨3252289703001735793071341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8672772541337962114856909 3252289703001735793071341)
                  ·
                    refine ⟨1219608638625650922401753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252289703001735793071341 1219608638625650922401753)
                    ·
                      rfl

theorem cell22_3562769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_3562769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562769 prefixEnd_3562769 := by exact prefixLift 3562769
  have htrace : WordTrace (prefixWord ++ tailWord_3562769) baseStart_3562769 baseEnd_3562769 := by
    simpa [prefixWord, tailWord_3562769, baseEnd_3562769] using wordTrace_append hprefix tailTrace_3562769
  have hstable : (prefixWord ++ tailWord_3562769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562769).length < 2 ^ (prefixWord ++ tailWord_3562769).sum := by decide
  have hdescent : baseEnd_3562769 < baseStart_3562769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562803 : List Nat := [1, 1, 1, 2, 5, 3, 2, 3, 1, 3]
def baseStart_3562803 : Nat := 118140960795 + 3562803 * 2 ^ 59
def prefixEnd_3562803 : Nat := 4983230072969 + 3 ^ 40 * 3562803 * 2
def baseEnd_3562803 : Nat := 1219620277520486167051649

theorem tailTrace_3562803 : CollatzResearch.WordTrace tailWord_3562803 prefixEnd_3562803 1219620277520486167051649 := by
  unfold tailWord_3562803
  simp only [CollatzResearch.WordTrace]
  refine ⟨129946100911580684154077063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86630733941053789436051375 129946100911580684154077063)
  ·
    refine ⟨194919151367371026231115595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129946100911580684154077063 194919151367371026231115595)
    ·
      refine ⟨292378727051056539346673393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194919151367371026231115595 292378727051056539346673393)
      ·
        refine ⟨219284045288292404510005045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292378727051056539346673393 219284045288292404510005045)
        ·
          refine ⟨20557879245777412922812973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219284045288292404510005045 20557879245777412922812973)
          ·
            refine ⟨7709204717166529846054865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20557879245777412922812973 7709204717166529846054865)
            ·
              refine ⟨5781903537874897384541149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7709204717166529846054865 5781903537874897384541149)
              ·
                refine ⟨2168213826703086519202931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5781903537874897384541149 2168213826703086519202931)
                ·
                  refine ⟨3252320740054629778804397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168213826703086519202931 3252320740054629778804397)
                  ·
                    refine ⟨1219620277520486167051649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252320740054629778804397 1219620277520486167051649)
                    ·
                      rfl

theorem cell22_3562803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 1, 3].length) (baseStart_3562803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562803 prefixEnd_3562803 := by exact prefixLift 3562803
  have htrace : WordTrace (prefixWord ++ tailWord_3562803) baseStart_3562803 baseEnd_3562803 := by
    simpa [prefixWord, tailWord_3562803, baseEnd_3562803] using wordTrace_append hprefix tailTrace_3562803
  have hstable : (prefixWord ++ tailWord_3562803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562803).length < 2 ^ (prefixWord ++ tailWord_3562803).sum := by decide
  have hdescent : baseEnd_3562803 < baseStart_3562803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562814 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3562814 : Nat := 118140960795 + 3562814 * 2 ^ 59
def prefixEnd_3562814 : Nat := 4983230072969 + 3 ^ 40 * 3562814 * 2
def baseEnd_3562814 : Nat := 1219624043045285805026615

theorem tailTrace_3562814 : CollatzResearch.WordTrace tailWord_3562814 prefixEnd_3562814 1219624043045285805026615 := by
  unfold tailWord_3562814
  simp only [CollatzResearch.WordTrace]
  refine ⟨16243312764317604129090937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86631001409693888688484997 16243312764317604129090937)
  ·
    refine ⟨12182484573238203096818203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16243312764317604129090937 12182484573238203096818203)
    ·
      refine ⟨18273726859857304645227305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12182484573238203096818203 18273726859857304645227305)
      ·
        refine ⟨13705295144892978483920479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18273726859857304645227305 13705295144892978483920479)
        ·
          refine ⟨20557942717339467725880719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13705295144892978483920479 20557942717339467725880719)
          ·
            refine ⟨30836914076009201588821079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20557942717339467725880719 30836914076009201588821079)
            ·
              refine ⟨46255371114013802383231619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30836914076009201588821079 46255371114013802383231619)
              ·
                refine ⟨69383056671020703574847429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46255371114013802383231619 69383056671020703574847429)
                ·
                  refine ⟨13009323125816381920283893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69383056671020703574847429 13009323125816381920283893)
                  ·
                    refine ⟨1219624043045285805026615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13009323125816381920283893 1219624043045285805026615)
                    ·
                      rfl

theorem cell22_3562814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3562814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562814 prefixEnd_3562814 := by exact prefixLift 3562814
  have htrace : WordTrace (prefixWord ++ tailWord_3562814) baseStart_3562814 baseEnd_3562814 := by
    simpa [prefixWord, tailWord_3562814, baseEnd_3562814] using wordTrace_append hprefix tailTrace_3562814
  have hstable : (prefixWord ++ tailWord_3562814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562814).length < 2 ^ (prefixWord ++ tailWord_3562814).sum := by decide
  have hdescent : baseEnd_3562814 < baseStart_3562814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562820 : List Nat := [2, 3, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3562820 : Nat := 118140960795 + 3562820 * 2 ^ 59
def prefixEnd_3562820 : Nat := 4983230072969 + 3 ^ 40 * 3562820 * 2
def baseEnd_3562820 : Nat := 1219626096967903789376597

theorem tailTrace_3562820 : CollatzResearch.WordTrace tailWord_3562820 prefixEnd_3562820 1219626096967903789376597 := by
  unfold tailWord_3562820
  simp only [CollatzResearch.WordTrace]
  refine ⟨64973360476259548028722957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86631147301679397371630609 64973360476259548028722957)
  ·
    refine ⟨24365010178597330510771109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64973360476259548028722957 24365010178597330510771109)
    ·
      refine ⟨4568439408486999470769583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24365010178597330510771109 4568439408486999470769583)
      ·
        refine ⟨6852659112730499206154375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4568439408486999470769583 6852659112730499206154375)
        ·
          refine ⟨10278988669095748809231563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852659112730499206154375 10278988669095748809231563)
          ·
            refine ⟨15418483003643623213847345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10278988669095748809231563 15418483003643623213847345)
            ·
              refine ⟨11563862252732717410385509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15418483003643623213847345 11563862252732717410385509)
              ·
                refine ⟨2168224172387384514447283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11563862252732717410385509 2168224172387384514447283)
                ·
                  refine ⟨3252336258581076771670925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168224172387384514447283 3252336258581076771670925)
                  ·
                    refine ⟨1219626096967903789376597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252336258581076771670925 1219626096967903789376597)
                    ·
                      rfl

theorem cell22_3562820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3562820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562820 prefixEnd_3562820 := by exact prefixLift 3562820
  have htrace : WordTrace (prefixWord ++ tailWord_3562820) baseStart_3562820 baseEnd_3562820 := by
    simpa [prefixWord, tailWord_3562820, baseEnd_3562820] using wordTrace_append hprefix tailTrace_3562820
  have hstable : (prefixWord ++ tailWord_3562820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562820).length < 2 ^ (prefixWord ++ tailWord_3562820).sum := by decide
  have hdescent : baseEnd_3562820 < baseStart_3562820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562874 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_3562874 : Nat := 118140960795 + 3562874 * 2 ^ 59
def prefixEnd_3562874 : Nat := 4983230072969 + 3 ^ 40 * 3562874 * 2
def baseEnd_3562874 : Nat := 1219644582271465648526431

theorem tailTrace_3562874 : CollatzResearch.WordTrace tailWord_3562874 prefixEnd_3562874 1219644582271465648526431 := by
  unfold tailWord_3562874
  simp only [CollatzResearch.WordTrace]
  refine ⟨32487172623580865819977919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86632460329548975519941117 32487172623580865819977919)
  ·
    refine ⟨48730758935371298729966879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32487172623580865819977919 48730758935371298729966879)
    ·
      refine ⟨73096138403056948094950319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48730758935371298729966879 73096138403056948094950319)
      ·
        refine ⟨109644207604585422142425479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73096138403056948094950319 109644207604585422142425479)
        ·
          refine ⟨164466311406878133213638219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109644207604585422142425479 164466311406878133213638219)
          ·
            refine ⟨246699467110317199820457329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164466311406878133213638219 246699467110317199820457329)
            ·
              refine ⟨185024600332737899865342997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246699467110317199820457329 185024600332737899865342997)
              ·
                refine ⟨8673028140597089056187953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185024600332737899865342997 8673028140597089056187953)
                ·
                  refine ⟨6504771105447816792140965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8673028140597089056187953 6504771105447816792140965)
                  ·
                    refine ⟨1219644582271465648526431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6504771105447816792140965 1219644582271465648526431)
                    ·
                      rfl

theorem cell22_3562874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_3562874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562874 prefixEnd_3562874 := by exact prefixLift 3562874
  have htrace : WordTrace (prefixWord ++ tailWord_3562874) baseStart_3562874 baseEnd_3562874 := by
    simpa [prefixWord, tailWord_3562874, baseEnd_3562874] using wordTrace_append hprefix tailTrace_3562874
  have hstable : (prefixWord ++ tailWord_3562874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562874).length < 2 ^ (prefixWord ++ tailWord_3562874).sum := by decide
  have hdescent : baseEnd_3562874 < baseStart_3562874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562876 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 2, 3]
def baseStart_3562876 : Nat := 118140960795 + 3562876 * 2 ^ 59
def prefixEnd_3562876 : Nat := 4983230072969 + 3 ^ 40 * 3562876 * 2
def baseEnd_3562876 : Nat := 1219645266912338309976425

theorem tailTrace_3562876 : CollatzResearch.WordTrace tailWord_3562876 prefixEnd_3562876 1219645266912338309976425 := by
  unfold tailWord_3562876
  simp only [CollatzResearch.WordTrace]
  refine ⟨64974381720158108810742241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86632508960210811747656321 64974381720158108810742241)
  ·
    refine ⟨48730786290118581608056681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64974381720158108810742241 48730786290118581608056681)
    ·
      refine ⟨36548089717588936206042511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48730786290118581608056681 36548089717588936206042511)
      ·
        refine ⟨54822134576383404309063767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36548089717588936206042511 54822134576383404309063767)
        ·
          refine ⟨82233201864575106463595651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54822134576383404309063767 82233201864575106463595651)
          ·
            refine ⟨123349802796862659695393477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82233201864575106463595651 123349802796862659695393477)
            ·
              refine ⟨23128088024411748692886277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123349802796862659695393477 23128088024411748692886277)
              ·
                refine ⟨4336516504577202879916177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23128088024411748692886277 4336516504577202879916177)
                ·
                  refine ⟨3252387378432902159937133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4336516504577202879916177 3252387378432902159937133)
                  ·
                    refine ⟨1219645266912338309976425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252387378432902159937133 1219645266912338309976425)
                    ·
                      rfl

theorem cell22_3562876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_3562876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3562876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3562876 prefixEnd_3562876 := by exact prefixLift 3562876
  have htrace : WordTrace (prefixWord ++ tailWord_3562876) baseStart_3562876 baseEnd_3562876 := by
    simpa [prefixWord, tailWord_3562876, baseEnd_3562876] using wordTrace_append hprefix tailTrace_3562876
  have hstable : (prefixWord ++ tailWord_3562876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562876).length < 2 ^ (prefixWord ++ tailWord_3562876).sum := by decide
  have hdescent : baseEnd_3562876 < baseStart_3562876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563041 : List Nat := [1, 2, 3, 2, 2, 4, 8]
def baseStart_3563041 : Nat := 118140960795 + 3563041 * 2 ^ 59
def prefixEnd_3563041 : Nat := 4983230072969 + 3 ^ 40 * 3563041 * 2
def baseEnd_3563041 : Nat := 45174138880901217762997

theorem tailTrace_3563041 : CollatzResearch.WordTrace tailWord_3563041 prefixEnd_3563041 45174138880901217762997 := by
  unfold tailWord_3563041
  simp only [CollatzResearch.WordTrace]
  refine ⟨129954781484718450801240977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86636520989812300534160651 129954781484718450801240977)
  ·
    refine ⟨97466086113538838100930733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129954781484718450801240977 97466086113538838100930733)
    ·
      refine ⟨36549782292577064287849025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97466086113538838100930733 36549782292577064287849025)
      ·
        refine ⟨27412336719432798215886769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36549782292577064287849025 27412336719432798215886769)
        ·
          refine ⟨20559252539574598661915077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27412336719432798215886769 20559252539574598661915077)
          ·
            refine ⟨3854859851170237249109077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20559252539574598661915077 3854859851170237249109077)
            ·
              refine ⟨45174138880901217762997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3854859851170237249109077 45174138880901217762997)
              ·
                rfl

theorem cell22_3563041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 8].length) (baseStart_3563041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563041 prefixEnd_3563041 := by exact prefixLift 3563041
  have htrace : WordTrace (prefixWord ++ tailWord_3563041) baseStart_3563041 baseEnd_3563041 := by
    simpa [prefixWord, tailWord_3563041, baseEnd_3563041] using wordTrace_append hprefix tailTrace_3563041
  have hstable : (prefixWord ++ tailWord_3563041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563041).length < 2 ^ (prefixWord ++ tailWord_3563041).sum := by decide
  have hdescent : baseEnd_3563041 < baseStart_3563041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563043 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 2, 4]
def baseStart_3563043 : Nat := 118140960795 + 3563043 * 2 ^ 59
def prefixEnd_3563043 : Nat := 4983230072969 + 3 ^ 40 * 3563043 * 2
def baseEnd_3563043 : Nat := 1219702434425205541050913

theorem tailTrace_3563043 : CollatzResearch.WordTrace tailWord_3563043 prefixEnd_3563043 1219702434425205541050913 := by
  unfold tailWord_3563043
  simp only [CollatzResearch.WordTrace]
  refine ⟨129954854430711205142813783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86636569620474136761875855 129954854430711205142813783)
  ·
    refine ⟨194932281646066807714220675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129954854430711205142813783 194932281646066807714220675)
    ·
      refine ⟨292398422469100211571331013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194932281646066807714220675 292398422469100211571331013)
      ·
        refine ⟨54824704212956289669624565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292398422469100211571331013 54824704212956289669624565)
        ·
          refine ⟨5139816019964652156527303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54824704212956289669624565 5139816019964652156527303)
          ·
            refine ⟨7709724029946978234790955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5139816019964652156527303 7709724029946978234790955)
            ·
              refine ⟨11564586044920467352186433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7709724029946978234790955 11564586044920467352186433)
              ·
                refine ⟨8673439533690350514139825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11564586044920467352186433 8673439533690350514139825)
                ·
                  refine ⟨6505079650267762885604869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8673439533690350514139825 6505079650267762885604869)
                  ·
                    refine ⟨1219702434425205541050913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6505079650267762885604869 1219702434425205541050913)
                    ·
                      rfl

theorem cell22_3563043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 4].length) (baseStart_3563043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563043 prefixEnd_3563043 := by exact prefixLift 3563043
  have htrace : WordTrace (prefixWord ++ tailWord_3563043) baseStart_3563043 baseEnd_3563043 := by
    simpa [prefixWord, tailWord_3563043, baseEnd_3563043] using wordTrace_append hprefix tailTrace_3563043
  have hstable : (prefixWord ++ tailWord_3563043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563043).length < 2 ^ (prefixWord ++ tailWord_3563043).sum := by decide
  have hdescent : baseEnd_3563043 < baseStart_3563043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563062 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_3563062 : Nat := 118140960795 + 3563062 * 2 ^ 59
def prefixEnd_3563062 : Nat := 4983230072969 + 3 ^ 40 * 3563062 * 2
def baseEnd_3563062 : Nat := 1219708938513495824825855

theorem tailTrace_3563062 : CollatzResearch.WordTrace tailWord_3563062 prefixEnd_3563062 1219708938513495824825855 := by
  unfold tailWord_3563062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8122221713602648211734715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86637031611761580925170293 8122221713602648211734715)
  ·
    refine ⟨12183332570403972317602073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8122221713602648211734715 12183332570403972317602073)
    ·
      refine ⟨9137499427802979238201555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12183332570403972317602073 9137499427802979238201555)
      ·
        refine ⟨13706249141704468857302333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9137499427802979238201555 13706249141704468857302333)
        ·
          refine ⟨5139843428139175821488375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13706249141704468857302333 5139843428139175821488375)
          ·
            refine ⟨7709765142208763732232563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5139843428139175821488375 7709765142208763732232563)
            ·
              refine ⟨11564647713313145598348845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7709765142208763732232563 11564647713313145598348845)
              ·
                refine ⟨4336742892492429599380817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11564647713313145598348845 4336742892492429599380817)
                ·
                  refine ⟨3252557169369322199535613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4336742892492429599380817 3252557169369322199535613)
                  ·
                    refine ⟨1219708938513495824825855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252557169369322199535613 1219708938513495824825855)
                    ·
                      rfl

theorem cell22_3563062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_3563062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563062 prefixEnd_3563062 := by exact prefixLift 3563062
  have htrace : WordTrace (prefixWord ++ tailWord_3563062) baseStart_3563062 baseEnd_3563062 := by
    simpa [prefixWord, tailWord_3563062, baseEnd_3563062] using wordTrace_append hprefix tailTrace_3563062
  have hstable : (prefixWord ++ tailWord_3563062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563062).length < 2 ^ (prefixWord ++ tailWord_3563062).sum := by decide
  have hdescent : baseEnd_3563062 < baseStart_3563062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563073 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3563073 : Nat := 118140960795 + 3563073 * 2 ^ 59
def prefixEnd_3563073 : Nat := 4983230072969 + 3 ^ 40 * 3563073 * 2
def baseEnd_3563073 : Nat := 1219712704038295462800821

theorem tailTrace_3563073 : CollatzResearch.WordTrace tailWord_3563073 prefixEnd_3563073 1219712704038295462800821 := by
  unfold tailWord_3563073
  simp only [CollatzResearch.WordTrace]
  refine ⟨129955948620602520266405873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86637299080401680177603915 129955948620602520266405873)
  ·
    refine ⟨97466961465451890199804405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129955948620602520266405873 97466961465451890199804405)
    ·
      refine ⟨9137527637386114706231663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97466961465451890199804405 9137527637386114706231663)
      ·
        refine ⟨13706291456079172059347495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9137527637386114706231663 13706291456079172059347495)
        ·
          refine ⟨20559437184118758089021243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13706291456079172059347495 20559437184118758089021243)
          ·
            refine ⟨30839155776178137133531865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20559437184118758089021243 30839155776178137133531865)
            ·
              refine ⟨23129366832133602850148899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30839155776178137133531865 23129366832133602850148899)
              ·
                refine ⟨34694050248200404275223349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23129366832133602850148899 34694050248200404275223349)
                ·
                  refine ⟨3252567210768787900802189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34694050248200404275223349 3252567210768787900802189)
                  ·
                    refine ⟨1219712704038295462800821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252567210768787900802189 1219712704038295462800821)
                    ·
                      rfl

theorem cell22_3563073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3563073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563073 prefixEnd_3563073 := by exact prefixLift 3563073
  have htrace : WordTrace (prefixWord ++ tailWord_3563073) baseStart_3563073 baseEnd_3563073 := by
    simpa [prefixWord, tailWord_3563073, baseEnd_3563073] using wordTrace_append hprefix tailTrace_3563073
  have hstable : (prefixWord ++ tailWord_3563073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563073).length < 2 ^ (prefixWord ++ tailWord_3563073).sum := by decide
  have hdescent : baseEnd_3563073 < baseStart_3563073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563107 : List Nat := [1, 1, 1, 5, 1, 3, 4, 2, 1, 3]
def baseStart_3563107 : Nat := 118140960795 + 3563107 * 2 ^ 59
def prefixEnd_3563107 : Nat := 4983230072969 + 3 ^ 40 * 3563107 * 2
def baseEnd_3563107 : Nat := 1219724342933130707450717

theorem tailTrace_3563107 : CollatzResearch.WordTrace tailWord_3563107 prefixEnd_3563107 1219724342933130707450717 := by
  unfold tailWord_3563107
  simp only [CollatzResearch.WordTrace]
  refine ⟨129957188702479344073143575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86638125801652896048762383 129957188702479344073143575)
  ·
    refine ⟨194935783053719016109715363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129957188702479344073143575 194935783053719016109715363)
    ·
      refine ⟨292403674580578524164573045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194935783053719016109715363 292403674580578524164573045)
      ·
        refine ⟨27412844491929236640428723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292403674580578524164573045 27412844491929236640428723)
        ·
          refine ⟨41119266737893854960643085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27412844491929236640428723 41119266737893854960643085)
          ·
            refine ⟨15419725026710195610241157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41119266737893854960643085 15419725026710195610241157)
            ·
              refine ⟨2891198442508161676920217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15419725026710195610241157 2891198442508161676920217)
              ·
                refine ⟨2168398831881121257690163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2891198442508161676920217 2168398831881121257690163)
                ·
                  refine ⟨3252598247821681886535245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168398831881121257690163 3252598247821681886535245)
                  ·
                    refine ⟨1219724342933130707450717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252598247821681886535245 1219724342933130707450717)
                    ·
                      rfl

theorem cell22_3563107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 1, 3].length) (baseStart_3563107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563107 prefixEnd_3563107 := by exact prefixLift 3563107
  have htrace : WordTrace (prefixWord ++ tailWord_3563107) baseStart_3563107 baseEnd_3563107 := by
    simpa [prefixWord, tailWord_3563107, baseEnd_3563107] using wordTrace_append hprefix tailTrace_3563107
  have hstable : (prefixWord ++ tailWord_3563107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563107).length < 2 ^ (prefixWord ++ tailWord_3563107).sum := by decide
  have hdescent : baseEnd_3563107 < baseStart_3563107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563131 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 6]
def baseStart_3563131 : Nat := 118140960795 + 3563131 * 2 ^ 59
def prefixEnd_3563131 : Nat := 4983230072969 + 3 ^ 40 * 3563131 * 2
def baseEnd_3563131 : Nat := 406577519541200881616881

theorem tailTrace_3563131 : CollatzResearch.WordTrace tailWord_3563131 prefixEnd_3563131 406577519541200881616881 := by
  unfold tailWord_3563131
  simp only [CollatzResearch.WordTrace]
  refine ⟨129958064054392396172017247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86638709369594930781344831 129958064054392396172017247)
  ·
    refine ⟨194937096081588594258025871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129958064054392396172017247 194937096081588594258025871)
    ·
      refine ⟨292405644122382891387038807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194937096081588594258025871 292405644122382891387038807)
      ·
        refine ⟨438608466183574337080558211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292405644122382891387038807 438608466183574337080558211)
        ·
          refine ⟨657912699275361505620837317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438608466183574337080558211 657912699275361505620837317)
          ·
            refine ⟨123358631114130282303906997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 657912699275361505620837317 123358631114130282303906997)
            ·
              refine ⟨11564871666949713965991281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123358631114130282303906997 11564871666949713965991281)
              ·
                refine ⟨8673653750212285474493461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11564871666949713965991281 8673653750212285474493461)
                ·
                  refine ⟨406577519541200881616881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8673653750212285474493461 406577519541200881616881)
                  ·
                    rfl

theorem cell22_3563131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 6].length) (baseStart_3563131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563131 prefixEnd_3563131 := by exact prefixLift 3563131
  have htrace : WordTrace (prefixWord ++ tailWord_3563131) baseStart_3563131 baseEnd_3563131 := by
    simpa [prefixWord, tailWord_3563131, baseEnd_3563131] using wordTrace_append hprefix tailTrace_3563131
  have hstable : (prefixWord ++ tailWord_3563131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563131).length < 2 ^ (prefixWord ++ tailWord_3563131).sum := by decide
  have hdescent : baseEnd_3563131 < baseStart_3563131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563133 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_3563133 : Nat := 118140960795 + 3563133 * 2 ^ 59
def prefixEnd_3563133 : Nat := 4983230072969 + 3 ^ 40 * 3563133 * 2
def baseEnd_3563133 : Nat := 1219733243264475306300637

theorem tailTrace_3563133 : CollatzResearch.WordTrace tailWord_3563133 prefixEnd_3563133 1219733243264475306300637 := by
  unfold tailWord_3563133
  simp only [CollatzResearch.WordTrace]
  refine ⟨129958137000385150513590053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86638758000256767009060035 129958137000385150513590053)
  ·
    refine ⟨24367150687572215721298135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129958137000385150513590053 24367150687572215721298135)
    ·
      refine ⟨36550726031358323581947203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24367150687572215721298135 36550726031358323581947203)
      ·
        refine ⟨54826089047037485372920805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36550726031358323581947203 54826089047037485372920805)
        ·
          refine ⟨10279891696319528507422651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54826089047037485372920805 10279891696319528507422651)
          ·
            refine ⟨15419837544479292761133977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10279891696319528507422651 15419837544479292761133977)
            ·
              refine ⟨11564878158359469570850483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15419837544479292761133977 11564878158359469570850483)
              ·
                refine ⟨17347317237539204356275725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11564878158359469570850483 17347317237539204356275725)
                ·
                  refine ⟨6505243964077201633603397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17347317237539204356275725 6505243964077201633603397)
                  ·
                    refine ⟨1219733243264475306300637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6505243964077201633603397 1219733243264475306300637)
                    ·
                      rfl

theorem cell22_3563133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_3563133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563133 prefixEnd_3563133 := by exact prefixLift 3563133
  have htrace : WordTrace (prefixWord ++ tailWord_3563133) baseStart_3563133 baseEnd_3563133 := by
    simpa [prefixWord, tailWord_3563133, baseEnd_3563133] using wordTrace_append hprefix tailTrace_3563133
  have hstable : (prefixWord ++ tailWord_3563133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563133).length < 2 ^ (prefixWord ++ tailWord_3563133).sum := by decide
  have hdescent : baseEnd_3563133 < baseStart_3563133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563150 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_3563150 : Nat := 118140960795 + 3563150 * 2 ^ 59
def prefixEnd_3563150 : Nat := 4983230072969 + 3 ^ 40 * 3563150 * 2
def baseEnd_3563150 : Nat := 1219739062711892928625585

theorem tailTrace_3563150 : CollatzResearch.WordTrace tailWord_3563150 prefixEnd_3563150 1219739062711892928625585 := by
  unfold tailWord_3563150
  simp only [CollatzResearch.WordTrace]
  refine ⟨16244844630165445302119863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86639171360882374944639269 16244844630165445302119863)
  ·
    refine ⟨24367266945248167953179795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16244844630165445302119863 24367266945248167953179795)
    ·
      refine ⟨36550900417872251929769693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24367266945248167953179795 36550900417872251929769693)
      ·
        refine ⟨13706587656702094473663635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36550900417872251929769693 13706587656702094473663635)
        ·
          refine ⟨20559881485053141710495453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13706587656702094473663635 20559881485053141710495453)
          ·
            refine ⟨7709955556894928141435795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20559881485053141710495453 7709955556894928141435795)
            ·
              refine ⟨11564933335342392212153693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7709955556894928141435795 11564933335342392212153693)
              ·
                refine ⟨4336850000753397079557635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11564933335342392212153693 4336850000753397079557635)
                ·
                  refine ⟨6505275001130095619336453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336850000753397079557635 6505275001130095619336453)
                  ·
                    refine ⟨1219739062711892928625585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6505275001130095619336453 1219739062711892928625585)
                    ·
                      rfl

theorem cell22_3563150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_3563150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563150 prefixEnd_3563150 := by exact prefixLift 3563150
  have htrace : WordTrace (prefixWord ++ tailWord_3563150) baseStart_3563150 baseEnd_3563150 := by
    simpa [prefixWord, tailWord_3563150, baseEnd_3563150] using wordTrace_append hprefix tailTrace_3563150
  have hstable : (prefixWord ++ tailWord_3563150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563150).length < 2 ^ (prefixWord ++ tailWord_3563150).sum := by decide
  have hdescent : baseEnd_3563150 < baseStart_3563150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563193 : List Nat := [1, 2, 1, 4, 1, 1, 6, 6]
def baseStart_3563193 : Nat := 118140960795 + 3563193 * 2 ^ 59
def prefixEnd_3563193 : Nat := 4983230072969 + 3 ^ 40 * 3563193 * 2
def baseEnd_3563193 : Nat := 135528198054517238866717

theorem tailTrace_3563193 : CollatzResearch.WordTrace tailWord_3563193 prefixEnd_3563193 135528198054517238866717 := by
  unfold tailWord_3563193
  simp only [CollatzResearch.WordTrace]
  refine ⟨129960325380167780760774233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86640216920111853840516155 129960325380167780760774233)
  ·
    refine ⟨97470244035125835570580675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129960325380167780760774233 97470244035125835570580675)
    ·
      refine ⟨146205366052688753355871013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97470244035125835570580675 146205366052688753355871013)
      ·
        refine ⟨27413506134879141254225815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146205366052688753355871013 27413506134879141254225815)
        ·
          refine ⟨41120259202318711881338723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27413506134879141254225815 41120259202318711881338723)
          ·
            refine ⟨61680388803478067822008085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41120259202318711881338723 61680388803478067822008085)
            ·
              refine ⟨2891268225163034429156629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61680388803478067822008085 2891268225163034429156629)
              ·
                refine ⟨135528198054517238866717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2891268225163034429156629 135528198054517238866717)
                ·
                  rfl

theorem cell22_3563193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 6].length) (baseStart_3563193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563193 prefixEnd_3563193 := by exact prefixLift 3563193
  have htrace : WordTrace (prefixWord ++ tailWord_3563193) baseStart_3563193 baseEnd_3563193 := by
    simpa [prefixWord, tailWord_3563193, baseEnd_3563193] using wordTrace_append hprefix tailTrace_3563193
  have hstable : (prefixWord ++ tailWord_3563193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563193).length < 2 ^ (prefixWord ++ tailWord_3563193).sum := by decide
  have hdescent : baseEnd_3563193 < baseStart_3563193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563210 : List Nat := [3, 1, 2, 1, 6, 1, 8]
def baseStart_3563210 : Nat := 118140960795 + 3563210 * 2 ^ 59
def prefixEnd_3563210 : Nat := 4983230072969 + 3 ^ 40 * 3563210 * 2
def baseEnd_3563210 : Nat := 45176281553261954523163

theorem tailTrace_3563210 : CollatzResearch.WordTrace tailWord_3563210 prefixEnd_3563210 45176281553261954523163 := by
  unfold tailWord_3563210
  simp only [CollatzResearch.WordTrace]
  refine ⟨32490236355276548166035771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86640630280737461776095389 32490236355276548166035771)
  ·
    refine ⟨48735354532914822249053657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32490236355276548166035771 48735354532914822249053657)
    ·
      refine ⟨36551515899686116686790243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48735354532914822249053657 36551515899686116686790243)
      ·
        refine ⟨54827273849529175030185365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36551515899686116686790243 54827273849529175030185365)
        ·
          refine ⟨2570028461696680079539939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54827273849529175030185365 2570028461696680079539939)
          ·
            refine ⟨3855042692545020119309909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570028461696680079539939 3855042692545020119309909)
            ·
              refine ⟨45176281553261954523163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3855042692545020119309909 45176281553261954523163)
              ·
                rfl

theorem cell22_3563210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 8].length) (baseStart_3563210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563210 prefixEnd_3563210 := by exact prefixLift 3563210
  have htrace : WordTrace (prefixWord ++ tailWord_3563210) baseStart_3563210 baseEnd_3563210 := by
    simpa [prefixWord, tailWord_3563210, baseEnd_3563210] using wordTrace_append hprefix tailTrace_3563210
  have hstable : (prefixWord ++ tailWord_3563210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563210).length < 2 ^ (prefixWord ++ tailWord_3563210).sum := by decide
  have hdescent : baseEnd_3563210 < baseStart_3563210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563225 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 3, 3]
def baseStart_3563225 : Nat := 118140960795 + 3563225 * 2 ^ 59
def prefixEnd_3563225 : Nat := 4983230072969 + 3 ^ 40 * 3563225 * 2
def baseEnd_3563225 : Nat := 1219764736744617733000355

theorem tailTrace_3563225 : CollatzResearch.WordTrace tailWord_3563225 prefixEnd_3563225 1219764736744617733000355 := by
  unfold tailWord_3563225
  simp only [CollatzResearch.WordTrace]
  refine ⟨129961492516051850225939129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86640995010701233483959419 129961492516051850225939129)
  ·
    refine ⟨97471119387038887669454347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129961492516051850225939129 97471119387038887669454347)
    ·
      refine ⟨146206679080558331504181521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97471119387038887669454347 146206679080558331504181521)
      ·
        refine ⟨109655009310418748628136141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146206679080558331504181521 109655009310418748628136141)
        ·
          refine ⟨41120628491407030735551053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109655009310418748628136141 41120628491407030735551053)
          ·
            refine ⟨15420235684277636525831645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41120628491407030735551053 15420235684277636525831645)
            ·
              refine ⟨5782588381604113697186867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15420235684277636525831645 5782588381604113697186867)
              ·
                refine ⟨8673882572406170545780301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5782588381604113697186867 8673882572406170545780301)
                ·
                  refine ⟨3252705964652313954667613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8673882572406170545780301 3252705964652313954667613)
                  ·
                    refine ⟨1219764736744617733000355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252705964652313954667613 1219764736744617733000355)
                    ·
                      rfl

theorem cell22_3563225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 3].length) (baseStart_3563225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563225 prefixEnd_3563225 := by exact prefixLift 3563225
  have htrace : WordTrace (prefixWord ++ tailWord_3563225) baseStart_3563225 baseEnd_3563225 := by
    simpa [prefixWord, tailWord_3563225, baseEnd_3563225] using wordTrace_append hprefix tailTrace_3563225
  have hstable : (prefixWord ++ tailWord_3563225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563225).length < 2 ^ (prefixWord ++ tailWord_3563225).sum := by decide
  have hdescent : baseEnd_3563225 < baseStart_3563225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563300 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 6]
def baseStart_3563300 : Nat := 118140960795 + 3563300 * 2 ^ 59
def prefixEnd_3563300 : Nat := 4983230072969 + 3 ^ 40 * 3563300 * 2
def baseEnd_3563300 : Nat := 406596803592447512458375

theorem tailTrace_3563300 : CollatzResearch.WordTrace tailWord_3563300 prefixEnd_3563300 406596803592447512458375 := by
  unfold tailWord_3563300
  simp only [CollatzResearch.WordTrace]
  refine ⟨64982113995390069017459677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86642818660520092023279569 64982113995390069017459677)
  ·
    refine ⟨24368292748271275881547379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64982113995390069017459677 24368292748271275881547379)
    ·
      refine ⟨36552439122406913822321069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24368292748271275881547379 36552439122406913822321069)
      ·
        refine ⟨13707164670902592683370401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36552439122406913822321069 13707164670902592683370401)
        ·
          refine ⟨10280373503176944512527801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13707164670902592683370401 10280373503176944512527801)
          ·
            refine ⟨7710280127382708384395851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10280373503176944512527801 7710280127382708384395851)
            ·
              refine ⟨11565420191074062576593777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7710280127382708384395851 11565420191074062576593777)
              ·
                refine ⟨8674065143305546932445333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11565420191074062576593777 8674065143305546932445333)
                ·
                  refine ⟨406596803592447512458375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8674065143305546932445333 406596803592447512458375)
                  ·
                    rfl

theorem cell22_3563300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_3563300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563300 prefixEnd_3563300 := by exact prefixLift 3563300
  have htrace : WordTrace (prefixWord ++ tailWord_3563300) baseStart_3563300 baseEnd_3563300 := by
    simpa [prefixWord, tailWord_3563300, baseEnd_3563300] using wordTrace_append hprefix tailTrace_3563300
  have hstable : (prefixWord ++ tailWord_3563300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563300).length < 2 ^ (prefixWord ++ tailWord_3563300).sum := by decide
  have hdescent : baseEnd_3563300 < baseStart_3563300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563334 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3563334 : Nat := 118140960795 + 3563334 * 2 ^ 59
def prefixEnd_3563334 : Nat := 4983230072969 + 3 ^ 40 * 3563334 * 2
def baseEnd_3563334 : Nat := 406600683224059260675007

theorem tailTrace_3563334 : CollatzResearch.WordTrace tailWord_3563334 prefixEnd_3563334 406600683224059260675007 := by
  unfold tailWord_3563334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061420877270530057551783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86643645381771307894438037 4061420877270530057551783)
  ·
    refine ⟨6092131315905795086327675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4061420877270530057551783 6092131315905795086327675)
    ·
      refine ⟨9138196973858692629491513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6092131315905795086327675 9138196973858692629491513)
      ·
        refine ⟨6853647730394019472118635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9138196973858692629491513 6853647730394019472118635)
        ·
          refine ⟨10280471595591029208177953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6853647730394019472118635 10280471595591029208177953)
          ·
            refine ⟨7710353696693271906133465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10280471595591029208177953 7710353696693271906133465)
            ·
              refine ⟨5782765272519953929600099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7710353696693271906133465 5782765272519953929600099)
              ·
                refine ⟨8674147908779930894400149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5782765272519953929600099 8674147908779930894400149)
                ·
                  refine ⟨406600683224059260675007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8674147908779930894400149 406600683224059260675007)
                  ·
                    rfl

theorem cell22_3563334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3563334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563334 prefixEnd_3563334 := by exact prefixLift 3563334
  have htrace : WordTrace (prefixWord ++ tailWord_3563334) baseStart_3563334 baseEnd_3563334 := by
    simpa [prefixWord, tailWord_3563334, baseEnd_3563334] using wordTrace_append hprefix tailTrace_3563334
  have hstable : (prefixWord ++ tailWord_3563334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563334).length < 2 ^ (prefixWord ++ tailWord_3563334).sum := by decide
  have hdescent : baseEnd_3563334 < baseStart_3563334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563349 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 2, 3]
def baseStart_3563349 : Nat := 118140960795 + 3563349 * 2 ^ 59
def prefixEnd_3563349 : Nat := 4983230072969 + 3 ^ 40 * 3563349 * 2
def baseEnd_3563349 : Nat := 1219807184478722742899975

theorem tailTrace_3563349 : CollatzResearch.WordTrace tailWord_3563349 prefixEnd_3563349 1219807184478722742899975 := by
  unfold tailWord_3563349
  simp only [CollatzResearch.WordTrace]
  refine ⟨129966015167602619403453101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86644010111735079602302067 129966015167602619403453101)
  ·
    refine ⟨48737255687850982276294913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129966015167602619403453101 48737255687850982276294913)
    ·
      refine ⟨36552941765888236707221185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48737255687850982276294913 36552941765888236707221185)
      ·
        refine ⟨27414706324416177530415889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36552941765888236707221185 27414706324416177530415889)
        ·
          refine ⟨20561029743312133147811917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27414706324416177530415889 20561029743312133147811917)
          ·
            refine ⟨7710386153742049930429469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20561029743312133147811917 7710386153742049930429469)
            ·
              refine ⟨2891394807653268723911051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7710386153742049930429469 2891394807653268723911051)
              ·
                refine ⟨4337092211479903085866577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891394807653268723911051 4337092211479903085866577)
                ·
                  refine ⟨3252819158609927314399933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4337092211479903085866577 3252819158609927314399933)
                  ·
                    refine ⟨1219807184478722742899975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252819158609927314399933 1219807184478722742899975)
                    ·
                      rfl

theorem cell22_3563349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_3563349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563349 prefixEnd_3563349 := by exact prefixLift 3563349
  have htrace : WordTrace (prefixWord ++ tailWord_3563349) baseStart_3563349 baseEnd_3563349 := by
    simpa [prefixWord, tailWord_3563349, baseEnd_3563349] using wordTrace_append hprefix tailTrace_3563349
  have hstable : (prefixWord ++ tailWord_3563349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563349).length < 2 ^ (prefixWord ++ tailWord_3563349).sum := by decide
  have hdescent : baseEnd_3563349 < baseStart_3563349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563362 : List Nat := [3, 3, 2, 1, 2, 1, 4, 6]
def baseStart_3563362 : Nat := 118140960795 + 3563362 * 2 ^ 59
def prefixEnd_3563362 : Nat := 4983230072969 + 3 ^ 40 * 3563362 * 2
def baseEnd_3563362 : Nat := 135534626071599449147215

theorem tailTrace_3563362 : CollatzResearch.WordTrace tailWord_3563362 prefixEnd_3563362 135534626071599449147215 := by
  unfold tailWord_3563362
  simp only [CollatzResearch.WordTrace]
  refine ⟨32491622329138880655919085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86644326211037015082450893 32491622329138880655919085)
  ·
    refine ⟨12184358373427080245969657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32491622329138880655919085 12184358373427080245969657)
    ·
      refine ⟨9138268780070310184477243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12184358373427080245969657 9138268780070310184477243)
      ·
        refine ⟨13707403170105465276715865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9138268780070310184477243 13707403170105465276715865)
        ·
          refine ⟨10280552377579098957536899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13707403170105465276715865 10280552377579098957536899)
          ·
            refine ⟨15420828566368648436305349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10280552377579098957536899 15420828566368648436305349)
            ·
              refine ⟨2891405356194121581807253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15420828566368648436305349 2891405356194121581807253)
              ·
                refine ⟨135534626071599449147215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2891405356194121581807253 135534626071599449147215)
                ·
                  rfl

theorem cell22_3563362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_3563362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563362 prefixEnd_3563362 := by exact prefixLift 3563362
  have htrace : WordTrace (prefixWord ++ tailWord_3563362) baseStart_3563362 baseEnd_3563362 := by
    simpa [prefixWord, tailWord_3563362, baseEnd_3563362] using wordTrace_append hprefix tailTrace_3563362
  have hstable : (prefixWord ++ tailWord_3563362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563362).length < 2 ^ (prefixWord ++ tailWord_3563362).sum := by decide
  have hdescent : baseEnd_3563362 < baseStart_3563362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563403 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 2, 8]
def baseStart_3563403 : Nat := 118140960795 + 3563403 * 2 ^ 59
def prefixEnd_3563403 : Nat := 4983230072969 + 3 ^ 40 * 3563403 * 2
def baseEnd_3563403 : Nat := 1219825669782284602049809

theorem tailTrace_3563403 : CollatzResearch.WordTrace tailWord_3563403 prefixEnd_3563403 1219825669782284602049809 := by
  unfold tailWord_3563403
  simp only [CollatzResearch.WordTrace]
  refine ⟨129967984709406986625918863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86645323139604657750612575 129967984709406986625918863)
  ·
    refine ⟨194951977064110479938878295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129967984709406986625918863 194951977064110479938878295)
    ·
      refine ⟨292427965596165719908317443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194951977064110479938878295 292427965596165719908317443)
      ·
        refine ⟨438641948394248579862476165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292427965596165719908317443 438641948394248579862476165)
        ·
          refine ⟨82245365323921608724214281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438641948394248579862476165 82245365323921608724214281)
          ·
            refine ⟨61684023992941206543160711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82245365323921608724214281 61684023992941206543160711)
            ·
              refine ⟨92526035989411809814741067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61684023992941206543160711 92526035989411809814741067)
              ·
                refine ⟨138789053984117714722111601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92526035989411809814741067 138789053984117714722111601)
                ·
                  refine ⟨104091790488088286041583701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138789053984117714722111601 104091790488088286041583701)
                  ·
                    refine ⟨1219825669782284602049809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104091790488088286041583701 1219825669782284602049809)
                    ·
                      rfl

theorem cell22_3563403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_3563403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563403 prefixEnd_3563403 := by exact prefixLift 3563403
  have htrace : WordTrace (prefixWord ++ tailWord_3563403) baseStart_3563403 baseEnd_3563403 := by
    simpa [prefixWord, tailWord_3563403, baseEnd_3563403] using wordTrace_append hprefix tailTrace_3563403
  have hstable : (prefixWord ++ tailWord_3563403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563403).length < 2 ^ (prefixWord ++ tailWord_3563403).sum := by decide
  have hdescent : baseEnd_3563403 < baseStart_3563403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563467 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 2, 3]
def baseStart_3563467 : Nat := 118140960795 + 3563467 * 2 ^ 59
def prefixEnd_3563467 : Nat := 4983230072969 + 3 ^ 40 * 3563467 * 2
def baseEnd_3563467 : Nat := 1219847578290209768449613

theorem tailTrace_3563467 : CollatzResearch.WordTrace tailWord_3563467 prefixEnd_3563467 1219847578290209768449613 := by
  unfold tailWord_3563467
  simp only [CollatzResearch.WordTrace]
  refine ⟨129970318981175125556248655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86646879320783417037499103 129970318981175125556248655)
  ·
    refine ⟨194955478471762688334372983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129970318981175125556248655 194955478471762688334372983)
    ·
      refine ⟨292433217707644032501559475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194955478471762688334372983 292433217707644032501559475)
      ·
        refine ⟨438649826561466048752339213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292433217707644032501559475 438649826561466048752339213)
        ·
          refine ⟨164493684960549768282127205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438649826561466048752339213 164493684960549768282127205)
          ·
            refine ⟨30842565930103081552898851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164493684960549768282127205 30842565930103081552898851)
            ·
              refine ⟨46263848895154622329348277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30842565930103081552898851 46263848895154622329348277)
              ·
                refine ⟨4337235833920745843376401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46263848895154622329348277 4337235833920745843376401)
                ·
                  refine ⟨3252926875440559382532301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4337235833920745843376401 3252926875440559382532301)
                  ·
                    refine ⟨1219847578290209768449613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252926875440559382532301 1219847578290209768449613)
                    ·
                      rfl

theorem cell22_3563467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 3].length) (baseStart_3563467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563467 prefixEnd_3563467 := by exact prefixLift 3563467
  have htrace : WordTrace (prefixWord ++ tailWord_3563467) baseStart_3563467 baseEnd_3563467 := by
    simpa [prefixWord, tailWord_3563467, baseEnd_3563467] using wordTrace_append hprefix tailTrace_3563467
  have hstable : (prefixWord ++ tailWord_3563467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563467).length < 2 ^ (prefixWord ++ tailWord_3563467).sum := by decide
  have hdescent : baseEnd_3563467 < baseStart_3563467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563482 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_3563482 : Nat := 118140960795 + 3563482 * 2 ^ 59
def prefixEnd_3563482 : Nat := 4983230072969 + 3 ^ 40 * 3563482 * 2
def baseEnd_3563482 : Nat := 1219852713096754729324567

theorem tailTrace_3563482 : CollatzResearch.WordTrace tailWord_3563482 prefixEnd_3563482 1219852713096754729324567 := by
  unfold tailWord_3563482
  simp only [CollatzResearch.WordTrace]
  refine ⟨32492716519030195779511175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86647244050747188745363133 32492716519030195779511175)
  ·
    refine ⟨48739074778545293669266763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32492716519030195779511175 48739074778545293669266763)
    ·
      refine ⟨73108612167817940503900145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48739074778545293669266763 73108612167817940503900145)
      ·
        refine ⟨54831459125863455377925109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73108612167817940503900145 54831459125863455377925109)
        ·
          refine ⟨5140449293049698941680479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54831459125863455377925109 5140449293049698941680479)
          ·
            refine ⟨7710673939574548412520719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140449293049698941680479 7710673939574548412520719)
            ·
              refine ⟨11566010909361822618781079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7710673939574548412520719 11566010909361822618781079)
              ·
                refine ⟨17349016364042733928171619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11566010909361822618781079 17349016364042733928171619)
                ·
                  refine ⟨26023524546064100892257429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17349016364042733928171619 26023524546064100892257429)
                  ·
                    refine ⟨1219852713096754729324567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26023524546064100892257429 1219852713096754729324567)
                    ·
                      rfl

theorem cell22_3563482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_3563482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563482 prefixEnd_3563482 := by exact prefixLift 3563482
  have htrace : WordTrace (prefixWord ++ tailWord_3563482) baseStart_3563482 baseEnd_3563482 := by
    simpa [prefixWord, tailWord_3563482, baseEnd_3563482] using wordTrace_append hprefix tailTrace_3563482
  have hstable : (prefixWord ++ tailWord_3563482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563482).length < 2 ^ (prefixWord ++ tailWord_3563482).sum := by decide
  have hdescent : baseEnd_3563482 < baseStart_3563482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563501 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_3563501 : Nat := 118140960795 + 3563501 * 2 ^ 59
def prefixEnd_3563501 : Nat := 4983230072969 + 3 ^ 40 * 3563501 * 2
def baseEnd_3563501 : Nat := 1219859217185045013099509

theorem tailTrace_3563501 : CollatzResearch.WordTrace tailWord_3563501 prefixEnd_3563501 1219859217185045013099509 := by
  unfold tailWord_3563501
  simp only [CollatzResearch.WordTrace]
  refine ⟨129971559063051949362986357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86647706042034632908657571 129971559063051949362986357)
  ·
    refine ⟨12184833662161120252779971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129971559063051949362986357 12184833662161120252779971)
    ·
      refine ⟨18277250493241680379169957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12184833662161120252779971 18277250493241680379169957)
      ·
        refine ⟨3426984467482815071094367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18277250493241680379169957 3426984467482815071094367)
        ·
          refine ⟨5140476701224222606641551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3426984467482815071094367 5140476701224222606641551)
          ·
            refine ⟨7710715051836333909962327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140476701224222606641551 7710715051836333909962327)
            ·
              refine ⟨11566072577754500864943491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7710715051836333909962327 11566072577754500864943491)
              ·
                refine ⟨17349108866631751297415237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11566072577754500864943491 17349108866631751297415237)
                ·
                  refine ⟨3252957912493453368265357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17349108866631751297415237 3252957912493453368265357)
                  ·
                    refine ⟨1219859217185045013099509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252957912493453368265357 1219859217185045013099509)
                    ·
                      rfl

theorem cell22_3563501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_3563501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563501 prefixEnd_3563501 := by exact prefixLift 3563501
  have htrace : WordTrace (prefixWord ++ tailWord_3563501) baseStart_3563501 baseEnd_3563501 := by
    simpa [prefixWord, tailWord_3563501, baseEnd_3563501] using wordTrace_append hprefix tailTrace_3563501
  have hstable : (prefixWord ++ tailWord_3563501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563501).length < 2 ^ (prefixWord ++ tailWord_3563501).sum := by decide
  have hdescent : baseEnd_3563501 < baseStart_3563501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563512 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 3, 3]
def baseStart_3563512 : Nat := 118140960795 + 3563512 * 2 ^ 59
def prefixEnd_3563512 : Nat := 4983230072969 + 3 ^ 40 * 3563512 * 2
def baseEnd_3563512 : Nat := 1219862982709844651074475

theorem tailTrace_3563512 : CollatzResearch.WordTrace tailWord_3563512 prefixEnd_3563512 1219862982709844651074475 := by
  unfold tailWord_3563512
  simp only [CollatzResearch.WordTrace]
  refine ⟨64985980133006049120818395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86647973510674732161091193 64985980133006049120818395)
  ·
    refine ⟨97478970199509073681227593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64985980133006049120818395 97478970199509073681227593)
    ·
      refine ⟨73109227649631805260920695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97478970199509073681227593 73109227649631805260920695)
      ·
        refine ⟨109663841474447707891381043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73109227649631805260920695 109663841474447707891381043)
        ·
          refine ⟨164495762211671561837071565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109663841474447707891381043 164495762211671561837071565)
          ·
            refine ⟨61685910829376835688901837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164495762211671561837071565 61685910829376835688901837)
            ·
              refine ⟨23132216561016313383338189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61685910829376835688901837 23132216561016313383338189)
              ·
                refine ⟨8674581210381117518751821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23132216561016313383338189 8674581210381117518751821)
                ·
                  refine ⟨3252967953892919069531933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8674581210381117518751821 3252967953892919069531933)
                  ·
                    refine ⟨1219862982709844651074475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252967953892919069531933 1219862982709844651074475)
                    ·
                      rfl

theorem cell22_3563512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_3563512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563512 prefixEnd_3563512 := by exact prefixLift 3563512
  have htrace : WordTrace (prefixWord ++ tailWord_3563512) baseStart_3563512 baseEnd_3563512 := by
    simpa [prefixWord, tailWord_3563512, baseEnd_3563512] using wordTrace_append hprefix tailTrace_3563512
  have hstable : (prefixWord ++ tailWord_3563512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563512).length < 2 ^ (prefixWord ++ tailWord_3563512).sum := by decide
  have hdescent : baseEnd_3563512 < baseStart_3563512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563518 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_3563518 : Nat := 118140960795 + 3563518 * 2 ^ 59
def prefixEnd_3563518 : Nat := 4983230072969 + 3 ^ 40 * 3563518 * 2
def baseEnd_3563518 : Nat := 1219865036632462635424457

theorem tailTrace_3563518 : CollatzResearch.WordTrace tailWord_3563518 prefixEnd_3563518 1219865036632462635424457 := by
  unfold tailWord_3563518
  simp only [CollatzResearch.WordTrace]
  refine ⟨16246522387998795158294401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86648119402660240844236805 16246522387998795158294401)
  ·
    refine ⟨12184891790999096368720801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16246522387998795158294401 12184891790999096368720801)
    ·
      refine ⟨9138668843249322276540601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12184891790999096368720801 9138668843249322276540601)
      ·
        refine ⟨6854001632436991707405451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9138668843249322276540601 6854001632436991707405451)
        ·
          refine ⟨10281002448655487561108177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854001632436991707405451 10281002448655487561108177)
          ·
            refine ⟨7710751836491615670831133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10281002448655487561108177 7710751836491615670831133)
            ·
              refine ⟨2891531938684355876561675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7710751836491615670831133 2891531938684355876561675)
              ·
                refine ⟨4337297908026533814842513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891531938684355876561675 4337297908026533814842513)
                ·
                  refine ⟨3252973431019900361131885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4337297908026533814842513 3252973431019900361131885)
                  ·
                    refine ⟨1219865036632462635424457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252973431019900361131885 1219865036632462635424457)
                    ·
                      rfl

theorem cell22_3563518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_3563518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563518 prefixEnd_3563518 := by exact prefixLift 3563518
  have htrace : WordTrace (prefixWord ++ tailWord_3563518) baseStart_3563518 baseEnd_3563518 := by
    simpa [prefixWord, tailWord_3563518, baseEnd_3563518] using wordTrace_append hprefix tailTrace_3563518
  have hstable : (prefixWord ++ tailWord_3563518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563518).length < 2 ^ (prefixWord ++ tailWord_3563518).sum := by decide
  have hdescent : baseEnd_3563518 < baseStart_3563518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563546 : List Nat := [3, 1, 1, 3, 1, 3, 3, 3, 1, 3]
def baseStart_3563546 : Nat := 118140960795 + 3563546 * 2 ^ 59
def prefixEnd_3563546 : Nat := 4983230072969 + 3 ^ 40 * 3563546 * 2
def baseEnd_3563546 : Nat := 1219874621604679895724371

theorem tailTrace_3563546 : CollatzResearch.WordTrace tailWord_3563546 prefixEnd_3563546 1219874621604679895724371 := by
  unfold tailWord_3563546
  simp only [CollatzResearch.WordTrace]
  refine ⟨32493300086972230512093623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86648800231925948032249661 32493300086972230512093623)
  ·
    refine ⟨48739950130458345768140435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32493300086972230512093623 48739950130458345768140435)
    ·
      refine ⟨73109925195687518652210653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48739950130458345768140435 73109925195687518652210653)
      ·
        refine ⟨27416221948382819494578995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73109925195687518652210653 27416221948382819494578995)
        ·
          refine ⟨41124332922574229241868493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27416221948382819494578995 41124332922574229241868493)
          ·
            refine ⟨15421624845965335965700685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41124332922574229241868493 15421624845965335965700685)
            ·
              refine ⟨5783109317237000987137757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15421624845965335965700685 5783109317237000987137757)
              ·
                refine ⟨2168665993963875370176659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5783109317237000987137757 2168665993963875370176659)
                ·
                  refine ⟨3252998990945813055264989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168665993963875370176659 3252998990945813055264989)
                  ·
                    refine ⟨1219874621604679895724371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252998990945813055264989 1219874621604679895724371)
                    ·
                      rfl

theorem cell22_3563546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_3563546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563546 prefixEnd_3563546 := by exact prefixLift 3563546
  have htrace : WordTrace (prefixWord ++ tailWord_3563546) baseStart_3563546 baseEnd_3563546 := by
    simpa [prefixWord, tailWord_3563546, baseEnd_3563546] using wordTrace_append hprefix tailTrace_3563546
  have hstable : (prefixWord ++ tailWord_3563546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563546).length < 2 ^ (prefixWord ++ tailWord_3563546).sum := by decide
  have hdescent : baseEnd_3563546 < baseStart_3563546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563576 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 5]
def baseStart_3563576 : Nat := 118140960795 + 3563576 * 2 ^ 59
def prefixEnd_3563576 : Nat := 4983230072969 + 3 ^ 40 * 3563576 * 2
def baseEnd_3563576 : Nat := 406628297072589939158093

theorem tailTrace_3563576 : CollatzResearch.WordTrace tailWord_3563576 prefixEnd_3563576 406628297072589939158093 := by
  unfold tailWord_3563576
  simp only [CollatzResearch.WordTrace]
  refine ⟨64987147268890118585983291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86649529691853491447977721 64987147268890118585983291)
  ·
    refine ⟨97480720903335177878974937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64987147268890118585983291 97480720903335177878974937)
    ·
      refine ⟨73110540677501383409231203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97480720903335177878974937 73110540677501383409231203)
      ·
        refine ⟨109665811016252075113846805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73110540677501383409231203 109665811016252075113846805)
        ·
          refine ⟨5140584891386816020961569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109665811016252075113846805 5140584891386816020961569)
          ·
            refine ⟨3855438668540112015721177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5140584891386816020961569 3855438668540112015721177)
            ·
              refine ⟨2891579001405084011790883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3855438668540112015721177 2891579001405084011790883)
              ·
                refine ⟨4337368502107626017686325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891579001405084011790883 4337368502107626017686325)
                ·
                  refine ⟨406628297072589939158093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4337368502107626017686325 406628297072589939158093)
                  ·
                    rfl

theorem cell22_3563576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 5].length) (baseStart_3563576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563576 prefixEnd_3563576 := by exact prefixLift 3563576
  have htrace : WordTrace (prefixWord ++ tailWord_3563576) baseStart_3563576 baseEnd_3563576 := by
    simpa [prefixWord, tailWord_3563576, baseEnd_3563576] using wordTrace_append hprefix tailTrace_3563576
  have hstable : (prefixWord ++ tailWord_3563576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563576).length < 2 ^ (prefixWord ++ tailWord_3563576).sum := by decide
  have hdescent : baseEnd_3563576 < baseStart_3563576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563604 : List Nat := [2, 4, 1, 1, 1, 1, 1, 7, 4]
def baseStart_3563604 : Nat := 118140960795 + 3563604 * 2 ^ 59
def prefixEnd_3563604 : Nat := 4983230072969 + 3 ^ 40 * 3563604 * 2
def baseEnd_3563604 : Nat := 406631492063329025924731

theorem tailTrace_3563604 : CollatzResearch.WordTrace tailWord_3563604 prefixEnd_3563604 406631492063329025924731 := by
  unfold tailWord_3563604
  simp only [CollatzResearch.WordTrace]
  refine ⟨64987657890839398976992933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86650210521119198635990577 64987657890839398976992933)
  ·
    refine ⟨12185185854532387308186175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64987657890839398976992933 12185185854532387308186175)
    ·
      refine ⟨18277778781798580962279263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12185185854532387308186175 18277778781798580962279263)
      ·
        refine ⟨27416668172697871443418895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18277778781798580962279263 27416668172697871443418895)
        ·
          refine ⟨41125002259046807165128343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27416668172697871443418895 41125002259046807165128343)
          ·
            refine ⟨61687503388570210747692515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41125002259046807165128343 61687503388570210747692515)
            ·
              refine ⟨92531255082855316121538773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61687503388570210747692515 92531255082855316121538773)
              ·
                refine ⟨2168701291004421471598565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 92531255082855316121538773 2168701291004421471598565)
                ·
                  refine ⟨406631492063329025924731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2168701291004421471598565 406631492063329025924731)
                  ·
                    rfl

theorem cell22_3563604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_3563604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563604 prefixEnd_3563604 := by exact prefixLift 3563604
  have htrace : WordTrace (prefixWord ++ tailWord_3563604) baseStart_3563604 baseEnd_3563604 := by
    simpa [prefixWord, tailWord_3563604, baseEnd_3563604] using wordTrace_append hprefix tailTrace_3563604
  have hstable : (prefixWord ++ tailWord_3563604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563604).length < 2 ^ (prefixWord ++ tailWord_3563604).sum := by decide
  have hdescent : baseEnd_3563604 < baseStart_3563604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563614 : List Nat := [4, 4, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3563614 : Nat := 118140960795 + 3563614 * 2 ^ 59
def prefixEnd_3563614 : Nat := 4983230072969 + 3 ^ 40 * 3563614 * 2
def baseEnd_3563614 : Nat := 1219897899394350385024163

theorem tailTrace_3563614 : CollatzResearch.WordTrace tailWord_3563614 prefixEnd_3563614 1219897899394350385024163 := by
  unfold tailWord_3563614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16246960063955321207731237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86650453674428379774566597 16246960063955321207731237)
  ·
    refine ⟨3046305011991622726449607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16246960063955321207731237 3046305011991622726449607)
    ·
      refine ⟨4569457517987434089674411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3046305011991622726449607 4569457517987434089674411)
      ·
        refine ⟨6854186276981151134511617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569457517987434089674411 6854186276981151134511617)
        ·
          refine ⟨5140639707735863350883713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6854186276981151134511617 5140639707735863350883713)
          ·
            refine ⟨3855479780801897513162785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5140639707735863350883713 3855479780801897513162785)
            ·
              refine ⟨2891609835601423134872089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3855479780801897513162785 2891609835601423134872089)
              ·
                refine ⟨2168707376701067351154067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2891609835601423134872089 2168707376701067351154067)
                ·
                  refine ⟨3253061065051601026731101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168707376701067351154067 3253061065051601026731101)
                  ·
                    refine ⟨1219897899394350385024163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3253061065051601026731101 1219897899394350385024163)
                    ·
                      rfl

theorem cell22_3563614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3563614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563614 prefixEnd_3563614 := by exact prefixLift 3563614
  have htrace : WordTrace (prefixWord ++ tailWord_3563614) baseStart_3563614 baseEnd_3563614 := by
    simpa [prefixWord, tailWord_3563614, baseEnd_3563614] using wordTrace_append hprefix tailTrace_3563614
  have hstable : (prefixWord ++ tailWord_3563614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563614).length < 2 ^ (prefixWord ++ tailWord_3563614).sum := by decide
  have hdescent : baseEnd_3563614 < baseStart_3563614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563619 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 2, 3]
def baseStart_3563619 : Nat := 118140960795 + 3563619 * 2 ^ 59
def prefixEnd_3563619 : Nat := 4983230072969 + 3 ^ 40 * 3563619 * 2
def baseEnd_3563619 : Nat := 1219899610996532038649147

theorem tailTrace_3563619 : CollatzResearch.WordTrace tailWord_3563619 prefixEnd_3563619 1219899610996532038649147 := by
  unfold tailWord_3563619
  simp only [CollatzResearch.WordTrace]
  refine ⟨129975862876624455515781911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86650575251082970343854607 129975862876624455515781911)
  ·
    refine ⟨194963794314936683273672867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129975862876624455515781911 194963794314936683273672867)
    ·
      refine ⟨292445691472405024910509301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194963794314936683273672867 292445691472405024910509301)
      ·
        refine ⟨27416783575537971085360247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292445691472405024910509301 27416783575537971085360247)
        ·
          refine ⟨41125175363306956628040371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27416783575537971085360247 41125175363306956628040371)
          ·
            refine ⟨61687763044960434942060557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41125175363306956628040371 61687763044960434942060557)
            ·
              refine ⟨23132911141860163103272709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61687763044960434942060557 23132911141860163103272709)
              ·
                refine ⟨4337420839098780581863633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23132911141860163103272709 4337420839098780581863633)
                ·
                  refine ⟨3253065629324085436397725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4337420839098780581863633 3253065629324085436397725)
                  ·
                    refine ⟨1219899610996532038649147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3253065629324085436397725 1219899610996532038649147)
                    ·
                      rfl

theorem cell22_3563619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 3].length) (baseStart_3563619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563619 prefixEnd_3563619 := by exact prefixLift 3563619
  have htrace : WordTrace (prefixWord ++ tailWord_3563619) baseStart_3563619 baseEnd_3563619 := by
    simpa [prefixWord, tailWord_3563619, baseEnd_3563619] using wordTrace_append hprefix tailTrace_3563619
  have hstable : (prefixWord ++ tailWord_3563619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563619).length < 2 ^ (prefixWord ++ tailWord_3563619).sum := by decide
  have hdescent : baseEnd_3563619 < baseStart_3563619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563621 : List Nat := [1, 3, 1, 3, 2, 2, 4, 2, 4]
def baseStart_3563621 : Nat := 118140960795 + 3563621 * 2 ^ 59
def prefixEnd_3563621 : Nat := 4983230072969 + 3 ^ 40 * 3563621 * 2
def baseEnd_3563621 : Nat := 406633431879134900033047

theorem tailTrace_3563621 : CollatzResearch.WordTrace tailWord_3563621 prefixEnd_3563621 406633431879134900033047 := by
  unfold tailWord_3563621
  simp only [CollatzResearch.WordTrace]
  refine ⟨129975935822617209857354717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86650623881744806571569811 129975935822617209857354717)
  ·
    refine ⟨48740975933481453696508019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129975935822617209857354717 48740975933481453696508019)
    ·
      refine ⟨73111463900222180544762029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48740975933481453696508019 73111463900222180544762029)
      ·
        refine ⟨27416798962583317704285761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73111463900222180544762029 27416798962583317704285761)
        ·
          refine ⟨20562599221937488278214321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27416798962583317704285761 20562599221937488278214321)
          ·
            refine ⟨15421949416453116208660741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20562599221937488278214321 15421949416453116208660741)
            ·
              refine ⟨2891615515584959289123889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15421949416453116208660741 2891615515584959289123889)
              ·
                refine ⟨2168711636688719466842917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2891615515584959289123889 2168711636688719466842917)
                ·
                  refine ⟨406633431879134900033047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2168711636688719466842917 406633431879134900033047)
                  ·
                    rfl

theorem cell22_3563621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_3563621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563621 prefixEnd_3563621 := by exact prefixLift 3563621
  have htrace : WordTrace (prefixWord ++ tailWord_3563621) baseStart_3563621 baseEnd_3563621 := by
    simpa [prefixWord, tailWord_3563621, baseEnd_3563621] using wordTrace_append hprefix tailTrace_3563621
  have hstable : (prefixWord ++ tailWord_3563621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563621).length < 2 ^ (prefixWord ++ tailWord_3563621).sum := by decide
  have hdescent : baseEnd_3563621 < baseStart_3563621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563632 : List Nat := [2, 1, 1, 1, 5, 2, 3, 7]
def baseStart_3563632 : Nat := 118140960795 + 3563632 * 2 ^ 59
def prefixEnd_3563632 : Nat := 4983230072969 + 3 ^ 40 * 3563632 * 2
def baseEnd_3563632 : Nat := 135544895684689370897123

theorem tailTrace_3563632 : CollatzResearch.WordTrace tailWord_3563632 prefixEnd_3563632 135544895684689370897123 := by
  unfold tailWord_3563632
  simp only [CollatzResearch.WordTrace]
  refine ⟨64988168512788679368002575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86650891350384905824003433 64988168512788679368002575)
  ·
    refine ⟨97482252769183019052003863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64988168512788679368002575 97482252769183019052003863)
    ·
      refine ⟨146223379153774528578005795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97482252769183019052003863 146223379153774528578005795)
      ·
        refine ⟨219335068730661792867008693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146223379153774528578005795 219335068730661792867008693)
        ·
          refine ⟨20562662693499543081282065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219335068730661792867008693 20562662693499543081282065)
          ·
            refine ⟨15421997020124657310961549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20562662693499543081282065 15421997020124657310961549)
            ·
              refine ⟨5783248882546746491610581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15421997020124657310961549 5783248882546746491610581)
              ·
                refine ⟨135544895684689370897123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5783248882546746491610581 135544895684689370897123)
                ·
                  rfl

theorem cell22_3563632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 7].length) (baseStart_3563632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563632 prefixEnd_3563632 := by exact prefixLift 3563632
  have htrace : WordTrace (prefixWord ++ tailWord_3563632) baseStart_3563632 baseEnd_3563632 := by
    simpa [prefixWord, tailWord_3563632, baseEnd_3563632] using wordTrace_append hprefix tailTrace_3563632
  have hstable : (prefixWord ++ tailWord_3563632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563632).length < 2 ^ (prefixWord ++ tailWord_3563632).sum := by decide
  have hdescent : baseEnd_3563632 < baseStart_3563632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563681 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 3, 3]
def baseStart_3563681 : Nat := 118140960795 + 3563681 * 2 ^ 59
def prefixEnd_3563681 : Nat := 4983230072969 + 3 ^ 40 * 3563681 * 2
def baseEnd_3563681 : Nat := 1219920834863584543598957

theorem tailTrace_3563681 : CollatzResearch.WordTrace tailWord_3563681 prefixEnd_3563681 1219920834863584543598957 := by
  unfold tailWord_3563681
  simp only [CollatzResearch.WordTrace]
  refine ⟨129978124202399840104538897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86652082801599893403025931 129978124202399840104538897)
  ·
    refine ⟨97483593151799880078404173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129978124202399840104538897 97483593151799880078404173)
    ·
      refine ⟨36556347431924955029401565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97483593151799880078404173 36556347431924955029401565)
      ·
        refine ⟨13708630286971858136025587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36556347431924955029401565 13708630286971858136025587)
        ·
          refine ⟨20562945430457787204038381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13708630286971858136025587 20562945430457787204038381)
          ·
            refine ⟨7711104536421670201514393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20562945430457787204038381 7711104536421670201514393)
            ·
              refine ⟨5783328402316252651135795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7711104536421670201514393 5783328402316252651135795)
              ·
                refine ⟨8674992603474378976703693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5783328402316252651135795 8674992603474378976703693)
                ·
                  refine ⟨3253122226302892116263885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8674992603474378976703693 3253122226302892116263885)
                  ·
                    refine ⟨1219920834863584543598957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3253122226302892116263885 1219920834863584543598957)
                    ·
                      rfl

theorem cell22_3563681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_3563681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563681 prefixEnd_3563681 := by exact prefixLift 3563681
  have htrace : WordTrace (prefixWord ++ tailWord_3563681) baseStart_3563681 baseEnd_3563681 := by
    simpa [prefixWord, tailWord_3563681, baseEnd_3563681] using wordTrace_append hprefix tailTrace_3563681
  have hstable : (prefixWord ++ tailWord_3563681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563681).length < 2 ^ (prefixWord ++ tailWord_3563681).sum := by decide
  have hdescent : baseEnd_3563681 < baseStart_3563681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563754 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_3563754 : Nat := 118140960795 + 3563754 * 2 ^ 59
def prefixEnd_3563754 : Nat := 4983230072969 + 3 ^ 40 * 3563754 * 2
def baseEnd_3563754 : Nat := 1219945824255436686523733

theorem tailTrace_3563754 : CollatzResearch.WordTrace tailWord_3563754 prefixEnd_3563754 1219945824255436686523733 := by
  unfold tailWord_3563754
  simp only [CollatzResearch.WordTrace]
  refine ⟨32495196682783843392986579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86653857820756915714630877 32495196682783843392986579)
  ·
    refine ⟨48742795024175765089479869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32495196682783843392986579 48742795024175765089479869)
    ·
      refine ⟨18278548134065911908554951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48742795024175765089479869 18278548134065911908554951)
      ·
        refine ⟨27417822201098867862832427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18278548134065911908554951 27417822201098867862832427)
        ·
          refine ⟨41126733301648301794248641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27417822201098867862832427 41126733301648301794248641)
          ·
            refine ⟨30845049976236226345686481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41126733301648301794248641 30845049976236226345686481)
            ·
              refine ⟨23133787482177169759264861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30845049976236226345686481 23133787482177169759264861)
              ·
                refine ⟨8675170305816438659724323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23133787482177169759264861 8675170305816438659724323)
                ·
                  refine ⟨13012755458724657989586485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8675170305816438659724323 13012755458724657989586485)
                  ·
                    refine ⟨1219945824255436686523733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13012755458724657989586485 1219945824255436686523733)
                    ·
                      rfl

theorem cell22_3563754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_3563754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563754 prefixEnd_3563754 := by exact prefixLift 3563754
  have htrace : WordTrace (prefixWord ++ tailWord_3563754) baseStart_3563754 baseEnd_3563754 := by
    simpa [prefixWord, tailWord_3563754, baseEnd_3563754] using wordTrace_append hprefix tailTrace_3563754
  have hstable : (prefixWord ++ tailWord_3563754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563754).length < 2 ^ (prefixWord ++ tailWord_3563754).sum := by decide
  have hdescent : baseEnd_3563754 < baseStart_3563754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563818 : List Nat := [3, 1, 4, 2, 2, 1, 3, 6]
def baseStart_3563818 : Nat := 118140960795 + 3563818 * 2 ^ 59
def prefixEnd_3563818 : Nat := 4983230072969 + 3 ^ 40 * 3563818 * 2
def baseEnd_3563818 : Nat := 135551970307040205880393

theorem tailTrace_3563818 : CollatzResearch.WordTrace tailWord_3563818 prefixEnd_3563818 135551970307040205880393 := by
  unfold tailWord_3563818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32495780250725878125569027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86655414001935675001517405 32495780250725878125569027)
  ·
    refine ⟨48743670376088817188353541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32495780250725878125569027 48743670376088817188353541)
    ·
      refine ⟨9139438195516653222816289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48743670376088817188353541 9139438195516653222816289)
      ·
        refine ⟨6854578646637489917112217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9139438195516653222816289 6854578646637489917112217)
        ·
          refine ⟨5140933984978117437834163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6854578646637489917112217 5140933984978117437834163)
          ·
            refine ⟨7711400977467176156751245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140933984978117437834163 7711400977467176156751245)
            ·
              refine ⟨2891775366550191058781717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7711400977467176156751245 2891775366550191058781717)
              ·
                refine ⟨135551970307040205880393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2891775366550191058781717 135551970307040205880393)
                ·
                  rfl

theorem cell22_3563818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_3563818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563818 prefixEnd_3563818 := by exact prefixLift 3563818
  have htrace : WordTrace (prefixWord ++ tailWord_3563818) baseStart_3563818 baseEnd_3563818 := by
    simpa [prefixWord, tailWord_3563818, baseEnd_3563818] using wordTrace_append hprefix tailTrace_3563818
  have hstable : (prefixWord ++ tailWord_3563818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563818).length < 2 ^ (prefixWord ++ tailWord_3563818).sum := by decide
  have hdescent : baseEnd_3563818 < baseStart_3563818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563829 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 7]
def baseStart_3563829 : Nat := 118140960795 + 3563829 * 2 ^ 59
def prefixEnd_3563829 : Nat := 4983230072969 + 3 ^ 40 * 3563829 * 2
def baseEnd_3563829 : Nat := 406657166096053830299501

theorem tailTrace_3563829 : CollatzResearch.WordTrace tailWord_3563829 prefixEnd_3563829 406657166096053830299501 := by
  unfold tailWord_3563829
  simp only [CollatzResearch.WordTrace]
  refine ⟨129983522205863661380926541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86655681470575774253951027 129983522205863661380926541)
  ·
    refine ⟨48743820827198873017847453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129983522205863661380926541 48743820827198873017847453)
    ·
      refine ⟨18278932810199577381692795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48743820827198873017847453 18278932810199577381692795)
      ·
        refine ⟨27418399215299366072539193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18278932810199577381692795 27418399215299366072539193)
        ·
          refine ⟨20563799411474524554404395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27418399215299366072539193 20563799411474524554404395)
          ·
            refine ⟨30845699117211786831606593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20563799411474524554404395 30845699117211786831606593)
            ·
              refine ⟨23134274337908840123704945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30845699117211786831606593 23134274337908840123704945)
              ·
                refine ⟨17350705753431630092778709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23134274337908840123704945 17350705753431630092778709)
                ·
                  refine ⟨406657166096053830299501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17350705753431630092778709 406657166096053830299501)
                  ·
                    rfl

theorem cell22_3563829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_3563829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563829 prefixEnd_3563829 := by exact prefixLift 3563829
  have htrace : WordTrace (prefixWord ++ tailWord_3563829) baseStart_3563829 baseEnd_3563829 := by
    simpa [prefixWord, tailWord_3563829, baseEnd_3563829] using wordTrace_append hprefix tailTrace_3563829
  have hstable : (prefixWord ++ tailWord_3563829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563829).length < 2 ^ (prefixWord ++ tailWord_3563829).sum := by decide
  have hdescent : baseEnd_3563829 < baseStart_3563829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563859 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 3, 4]
def baseStart_3563859 : Nat := 118140960795 + 3563859 * 2 ^ 59
def prefixEnd_3563859 : Nat := 4983230072969 + 3 ^ 40 * 3563859 * 2
def baseEnd_3563859 : Nat := 1219981767901251412648411

theorem tailTrace_3563859 : CollatzResearch.WordTrace tailWord_3563859 prefixEnd_3563859 1219981767901251412648411 := by
  unfold tailWord_3563859
  simp only [CollatzResearch.WordTrace]
  refine ⟨129984616395754976504518631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86656410930503317669679087 129984616395754976504518631)
  ·
    refine ⟨194976924593632464756777947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129984616395754976504518631 194976924593632464756777947)
    ·
      refine ⟨292465386890448697135166921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194976924593632464756777947 292465386890448697135166921)
      ·
        refine ⟨219349040167836522851375191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292465386890448697135166921 219349040167836522851375191)
        ·
          refine ⟨329023560251754784277062787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219349040167836522851375191 329023560251754784277062787)
          ·
            refine ⟨493535340377632176415594181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329023560251754784277062787 493535340377632176415594181)
            ·
              refine ⟨92537876320806033077923909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 493535340377632176415594181 92537876320806033077923909)
              ·
                refine ⟨17350851810151131202110733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92537876320806033077923909 17350851810151131202110733)
                ·
                  refine ⟨6506569428806674200791525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17350851810151131202110733 6506569428806674200791525)
                  ·
                    refine ⟨1219981767901251412648411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6506569428806674200791525 1219981767901251412648411)
                    ·
                      rfl

theorem cell22_3563859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 4].length) (baseStart_3563859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563859 prefixEnd_3563859 := by exact prefixLift 3563859
  have htrace : WordTrace (prefixWord ++ tailWord_3563859) baseStart_3563859 baseEnd_3563859 := by
    simpa [prefixWord, tailWord_3563859, baseEnd_3563859] using wordTrace_append hprefix tailTrace_3563859
  have hstable : (prefixWord ++ tailWord_3563859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563859).length < 2 ^ (prefixWord ++ tailWord_3563859).sum := by decide
  have hdescent : baseEnd_3563859 < baseStart_3563859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563889 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_3563889 : Nat := 118140960795 + 3563889 * 2 ^ 59
def prefixEnd_3563889 : Nat := 4983230072969 + 3 ^ 40 * 3563889 * 2
def baseEnd_3563889 : Nat := 1219992037514341334398319

theorem tailTrace_3563889 : CollatzResearch.WordTrace tailWord_3563889 prefixEnd_3563889 1219992037514341334398319 := by
  unfold tailWord_3563889
  simp only [CollatzResearch.WordTrace]
  refine ⟨129985710585646291628110721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86657140390430861085407147 129985710585646291628110721)
  ·
    refine ⟨97489282939234718721083041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129985710585646291628110721 97489282939234718721083041)
    ·
      refine ⟨73116962204426039040812281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97489282939234718721083041 73116962204426039040812281)
      ·
        refine ⟨54837721653319529280609211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73116962204426039040812281 54837721653319529280609211)
        ·
          refine ⟨82256582479979293920913817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54837721653319529280609211 82256582479979293920913817)
          ·
            refine ⟨61692436859984470440685363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82256582479979293920913817 61692436859984470440685363)
            ·
              refine ⟨92538655289976705661028045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61692436859984470440685363 92538655289976705661028045)
              ·
                refine ⟨34701995733741264622885517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92538655289976705661028045 34701995733741264622885517)
                ·
                  refine ⟨13013248400152974233582069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34701995733741264622885517 13013248400152974233582069)
                  ·
                    refine ⟨1219992037514341334398319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13013248400152974233582069 1219992037514341334398319)
                    ·
                      rfl

theorem cell22_3563889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_3563889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563889 prefixEnd_3563889 := by exact prefixLift 3563889
  have htrace : WordTrace (prefixWord ++ tailWord_3563889) baseStart_3563889 baseEnd_3563889 := by
    simpa [prefixWord, tailWord_3563889, baseEnd_3563889] using wordTrace_append hprefix tailTrace_3563889
  have hstable : (prefixWord ++ tailWord_3563889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563889).length < 2 ^ (prefixWord ++ tailWord_3563889).sum := by decide
  have hdescent : baseEnd_3563889 < baseStart_3563889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563893 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3563893 : Nat := 118140960795 + 3563893 * 2 ^ 59
def prefixEnd_3563893 : Nat := 4983230072969 + 3 ^ 40 * 3563893 * 2
def baseEnd_3563893 : Nat := 1219993406796086657298307

theorem tailTrace_3563893 : CollatzResearch.WordTrace tailWord_3563893 prefixEnd_3563893 1219993406796086657298307 := by
  unfold tailWord_3563893
  simp only [CollatzResearch.WordTrace]
  refine ⟨129985856477631800311256333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86657237651754533540837555 129985856477631800311256333)
  ·
    refine ⟨48744696179111925116721125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129985856477631800311256333 48744696179111925116721125)
    ·
      refine ⟨9139630533583485959385211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48744696179111925116721125 9139630533583485959385211)
      ·
        refine ⟨13709445800375228939077817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9139630533583485959385211 13709445800375228939077817)
        ·
          refine ⟨10282084350281421704308363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13709445800375228939077817 10282084350281421704308363)
          ·
            refine ⟨15423126525422132556462545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10282084350281421704308363 15423126525422132556462545)
            ·
              refine ⟨11567344894066599417346909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15423126525422132556462545 11567344894066599417346909)
              ·
                refine ⟨4337754335274974781505091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11567344894066599417346909 4337754335274974781505091)
                ·
                  refine ⟨6506631502912462172257637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4337754335274974781505091 6506631502912462172257637)
                  ·
                    refine ⟨1219993406796086657298307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6506631502912462172257637 1219993406796086657298307)
                    ·
                      rfl

theorem cell22_3563893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3563893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563893 prefixEnd_3563893 := by exact prefixLift 3563893
  have htrace : WordTrace (prefixWord ++ tailWord_3563893) baseStart_3563893 baseEnd_3563893 := by
    simpa [prefixWord, tailWord_3563893, baseEnd_3563893] using wordTrace_append hprefix tailTrace_3563893
  have hstable : (prefixWord ++ tailWord_3563893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563893).length < 2 ^ (prefixWord ++ tailWord_3563893).sum := by decide
  have hdescent : baseEnd_3563893 < baseStart_3563893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563938 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_3563938 : Nat := 118140960795 + 3563938 * 2 ^ 59
def prefixEnd_3563938 : Nat := 4983230072969 + 3 ^ 40 * 3563938 * 2
def baseEnd_3563938 : Nat := 1220008811215721539923169

theorem tailTrace_3563938 : CollatzResearch.WordTrace tailWord_3563938 prefixEnd_3563938 1220008811215721539923169 := by
  unfold tailWord_3563938
  simp only [CollatzResearch.WordTrace]
  refine ⟨32496874440617193249161117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86658331841645848664429645 32496874440617193249161117)
  ·
    refine ⟨12186327915231447468435419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32496874440617193249161117 12186327915231447468435419)
    ·
      refine ⟨18279491872847171202653129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12186327915231447468435419 18279491872847171202653129)
      ·
        refine ⟨13709618904635378401989847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18279491872847171202653129 13709618904635378401989847)
        ·
          refine ⟨20564428356953067602984771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13709618904635378401989847 20564428356953067602984771)
          ·
            refine ⟨30846642535429601404477157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20564428356953067602984771 30846642535429601404477157)
            ·
              refine ⟨5783745475393050263339467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30846642535429601404477157 5783745475393050263339467)
              ·
                refine ⟨8675618213089575395009201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5783745475393050263339467 8675618213089575395009201)
                ·
                  refine ⟨6506713659817181546256901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8675618213089575395009201 6506713659817181546256901)
                  ·
                    refine ⟨1220008811215721539923169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6506713659817181546256901 1220008811215721539923169)
                    ·
                      rfl

theorem cell22_3563938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_3563938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563938 prefixEnd_3563938 := by exact prefixLift 3563938
  have htrace : WordTrace (prefixWord ++ tailWord_3563938) baseStart_3563938 baseEnd_3563938 := by
    simpa [prefixWord, tailWord_3563938, baseEnd_3563938] using wordTrace_append hprefix tailTrace_3563938
  have hstable : (prefixWord ++ tailWord_3563938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563938).length < 2 ^ (prefixWord ++ tailWord_3563938).sum := by decide
  have hdescent : baseEnd_3563938 < baseStart_3563938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563966 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3563966 : Nat := 118140960795 + 3563966 * 2 ^ 59
def prefixEnd_3563966 : Nat := 4983230072969 + 3 ^ 40 * 3563966 * 2
def baseEnd_3563966 : Nat := 1220018396187938800223083

theorem tailTrace_3563966 : CollatzResearch.WordTrace tailWord_3563966 prefixEnd_3563966 1220018396187938800223083 := by
  unfold tailWord_3563966
  simp only [CollatzResearch.WordTrace]
  refine ⟨16248564875795916722332969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86659012670911555852442501 16248564875795916722332969)
  ·
    refine ⟨12186423656846937541749727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16248564875795916722332969 12186423656846937541749727)
    ·
      refine ⟨18279635485270406312624591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12186423656846937541749727 18279635485270406312624591)
      ·
        refine ⟨27419453227905609468936887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18279635485270406312624591 27419453227905609468936887)
        ·
          refine ⟨41129179841858414203405331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27419453227905609468936887 41129179841858414203405331)
          ·
            refine ⟨61693769762787621305107997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41129179841858414203405331 61693769762787621305107997)
            ·
              refine ⟨23135163661045357989415499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61693769762787621305107997 23135163661045357989415499)
              ·
                refine ⟨34702745491568036984123249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23135163661045357989415499 34702745491568036984123249)
                ·
                  refine ⟨26027059118676027738092437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34702745491568036984123249 26027059118676027738092437)
                  ·
                    refine ⟨1220018396187938800223083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26027059118676027738092437 1220018396187938800223083)
                    ·
                      rfl

theorem cell22_3563966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3563966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3563966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3563966 prefixEnd_3563966 := by exact prefixLift 3563966
  have htrace : WordTrace (prefixWord ++ tailWord_3563966) baseStart_3563966 baseEnd_3563966 := by
    simpa [prefixWord, tailWord_3563966, baseEnd_3563966] using wordTrace_append hprefix tailTrace_3563966
  have hstable : (prefixWord ++ tailWord_3563966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563966).length < 2 ^ (prefixWord ++ tailWord_3563966).sum := by decide
  have hdescent : baseEnd_3563966 < baseStart_3563966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564013 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3564013 : Nat := 118140960795 + 3564013 * 2 ^ 59
def prefixEnd_3564013 : Nat := 4983230072969 + 3 ^ 40 * 3564013 * 2
def baseEnd_3564013 : Nat := 1220034485248446344297939

theorem tailTrace_3564013 : CollatzResearch.WordTrace tailWord_3564013 prefixEnd_3564013 1220034485248446344297939 := by
  unfold tailWord_3564013
  simp only [CollatzResearch.WordTrace]
  refine ⟨129990233237197060805624693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86660155491464707203749795 129990233237197060805624693)
  ·
    refine ⟨12186584365987224450527315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129990233237197060805624693 12186584365987224450527315)
    ·
      refine ⟨18279876548980836675790973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12186584365987224450527315 18279876548980836675790973)
      ·
        refine ⟨6854953705867813753421615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18279876548980836675790973 6854953705867813753421615)
        ·
          refine ⟨10282430558801720630132423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854953705867813753421615 10282430558801720630132423)
          ·
            refine ⟨15423645838202580945198635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10282430558801720630132423 15423645838202580945198635)
            ·
              refine ⟨23135468757303871417797953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15423645838202580945198635 23135468757303871417797953)
              ·
                refine ⟨17351601567977903563348465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23135468757303871417797953 17351601567977903563348465)
                ·
                  refine ⟨13013701175983427672511349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17351601567977903563348465 13013701175983427672511349)
                  ·
                    refine ⟨1220034485248446344297939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13013701175983427672511349 1220034485248446344297939)
                    ·
                      rfl

theorem cell22_3564013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3564013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564013 prefixEnd_3564013 := by exact prefixLift 3564013
  have htrace : WordTrace (prefixWord ++ tailWord_3564013) baseStart_3564013 baseEnd_3564013 := by
    simpa [prefixWord, tailWord_3564013, baseEnd_3564013] using wordTrace_append hprefix tailTrace_3564013
  have hstable : (prefixWord ++ tailWord_3564013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564013).length < 2 ^ (prefixWord ++ tailWord_3564013).sum := by decide
  have hdescent : baseEnd_3564013 < baseStart_3564013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564041 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 1, 5]
def baseStart_3564041 : Nat := 118140960795 + 3564041 * 2 ^ 59
def prefixEnd_3564041 : Nat := 4983230072969 + 3 ^ 40 * 3564041 * 2
def baseEnd_3564041 : Nat := 1220044070220663604597853

theorem tailTrace_3564041 : CollatzResearch.WordTrace tailWord_3564041 prefixEnd_3564041 1220044070220663604597853 := by
  unfold tailWord_3564041
  simp only [CollatzResearch.WordTrace]
  refine ⟨129991254481095621587643977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86660836320730414391762651 129991254481095621587643977)
  ·
    refine ⟨97493440860821716190732983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129991254481095621587643977 97493440860821716190732983)
    ·
      refine ⟨146240161291232574286099475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97493440860821716190732983 146240161291232574286099475)
      ·
        refine ⟨219360241936848861429149213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146240161291232574286099475 219360241936848861429149213)
        ·
          refine ⟨82260090726318323035930955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219360241936848861429149213 82260090726318323035930955)
          ·
            refine ⟨123390136089477484553896433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82260090726318323035930955 123390136089477484553896433)
            ·
              refine ⟨92542602067108113415422325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123390136089477484553896433 92542602067108113415422325)
              ·
                refine ⟨8675868943791385632695843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92542602067108113415422325 8675868943791385632695843)
                ·
                  refine ⟨13013803415687078449043765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8675868943791385632695843 13013803415687078449043765)
                  ·
                    refine ⟨1220044070220663604597853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13013803415687078449043765 1220044070220663604597853)
                    ·
                      rfl

theorem cell22_3564041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_3564041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564041 prefixEnd_3564041 := by exact prefixLift 3564041
  have htrace : WordTrace (prefixWord ++ tailWord_3564041) baseStart_3564041 baseEnd_3564041 := by
    simpa [prefixWord, tailWord_3564041, baseEnd_3564041] using wordTrace_append hprefix tailTrace_3564041
  have hstable : (prefixWord ++ tailWord_3564041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564041).length < 2 ^ (prefixWord ++ tailWord_3564041).sum := by decide
  have hdescent : baseEnd_3564041 < baseStart_3564041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564058 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 4, 3]
def baseStart_3564058 : Nat := 118140960795 + 3564058 * 2 ^ 59
def prefixEnd_3564058 : Nat := 4983230072969 + 3 ^ 40 * 3564058 * 2
def baseEnd_3564058 : Nat := 1220049889668081226922801

theorem tailTrace_3564058 : CollatzResearch.WordTrace tailWord_3564058 prefixEnd_3564058 1220049889668081226922801 := by
  unfold tailWord_3564058
  simp only [CollatzResearch.WordTrace]
  refine ⟨32497968630508508372753207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86661249681356022327341885 32497968630508508372753207)
  ·
    refine ⟨48746952945762762559129811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32497968630508508372753207 48746952945762762559129811)
    ·
      refine ⟨73120429418644143838694717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48746952945762762559129811 73120429418644143838694717)
      ·
        refine ⟨27420161031991553939510519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73120429418644143838694717 27420161031991553939510519)
        ·
          refine ⟨41130241547987330909265779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27420161031991553939510519 41130241547987330909265779)
          ·
            refine ⟨61695362321980996363898669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41130241547987330909265779 61695362321980996363898669)
            ·
              refine ⟨23135760870742873636462001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61695362321980996363898669 23135760870742873636462001)
              ·
                refine ⟨17351820653057155227346501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23135760870742873636462001 17351820653057155227346501)
                ·
                  refine ⟨3253466372448216605127469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17351820653057155227346501 3253466372448216605127469)
                  ·
                    refine ⟨1220049889668081226922801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3253466372448216605127469 1220049889668081226922801)
                    ·
                      rfl

theorem cell22_3564058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_3564058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564058 prefixEnd_3564058 := by exact prefixLift 3564058
  have htrace : WordTrace (prefixWord ++ tailWord_3564058) baseStart_3564058 baseEnd_3564058 := by
    simpa [prefixWord, tailWord_3564058, baseEnd_3564058] using wordTrace_append hprefix tailTrace_3564058
  have hstable : (prefixWord ++ tailWord_3564058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564058).length < 2 ^ (prefixWord ++ tailWord_3564058).sum := by decide
  have hdescent : baseEnd_3564058 < baseStart_3564058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564060 : List Nat := [2, 2, 3, 1, 2, 2, 3, 3, 4]
def baseStart_3564060 : Nat := 118140960795 + 3564060 * 2 ^ 59
def prefixEnd_3564060 : Nat := 4983230072969 + 3 ^ 40 * 3564060 * 2
def baseEnd_3564060 : Nat := 406683524769651296124265

theorem tailTrace_3564060 : CollatzResearch.WordTrace tailWord_3564060 prefixEnd_3564060 406683524769651296124265 := by
  unfold tailWord_3564060
  simp only [CollatzResearch.WordTrace]
  refine ⟨64995973734013393916292817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86661298312017858555057089 64995973734013393916292817)
  ·
    refine ⟨48746980300510045437219613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64995973734013393916292817 48746980300510045437219613)
    ·
      refine ⟨18280117612691267038957355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48746980300510045437219613 18280117612691267038957355)
      ·
        refine ⟨27420176419036900558436033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18280117612691267038957355 27420176419036900558436033)
        ·
          refine ⟨20565132314277675418827025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27420176419036900558436033 20565132314277675418827025)
          ·
            refine ⟨15423849235708256564120269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20565132314277675418827025 15423849235708256564120269)
            ·
              refine ⟨5783943463390596211545101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15423849235708256564120269 5783943463390596211545101)
              ·
                refine ⟨2168978798771473579329413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5783943463390596211545101 2168978798771473579329413)
                ·
                  refine ⟨406683524769651296124265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2168978798771473579329413 406683524769651296124265)
                  ·
                    rfl

theorem cell22_3564060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_3564060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564060 prefixEnd_3564060 := by exact prefixLift 3564060
  have htrace : WordTrace (prefixWord ++ tailWord_3564060) baseStart_3564060 baseEnd_3564060 := by
    simpa [prefixWord, tailWord_3564060, baseEnd_3564060] using wordTrace_append hprefix tailTrace_3564060
  have hstable : (prefixWord ++ tailWord_3564060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564060).length < 2 ^ (prefixWord ++ tailWord_3564060).sum := by decide
  have hdescent : baseEnd_3564060 < baseStart_3564060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564092 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 2, 3]
def baseStart_3564092 : Nat := 118140960795 + 3564092 * 2 ^ 59
def prefixEnd_3564092 : Nat := 4983230072969 + 3 ^ 40 * 3564092 * 2
def baseEnd_3564092 : Nat := 1220061528562916471572697

theorem tailTrace_3564092 : CollatzResearch.WordTrace tailWord_3564092 prefixEnd_3564092 1220061528562916471572697 := by
  unfold tailWord_3564092
  simp only [CollatzResearch.WordTrace]
  refine ⟨64996557301955428648875265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86662076402607238198500353 64996557301955428648875265)
  ·
    refine ⟨48747417976466571486656449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64996557301955428648875265 48747417976466571486656449)
    ·
      refine ⟨36560563482349928614992337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48747417976466571486656449 36560563482349928614992337)
      ·
        refine ⟨27420422611762446461244253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36560563482349928614992337 27420422611762446461244253)
        ·
          refine ⟨10282658479410917422966595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27420422611762446461244253 10282658479410917422966595)
          ·
            refine ⟨15423987719116376134449893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10282658479410917422966595 15423987719116376134449893)
            ·
              refine ⟨2891997697334320525209355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15423987719116376134449893 2891997697334320525209355)
              ·
                refine ⟨4337996546001480787814033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891997697334320525209355 4337996546001480787814033)
                ·
                  refine ⟨3253497409501110590860525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4337996546001480787814033 3253497409501110590860525)
                  ·
                    refine ⟨1220061528562916471572697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3253497409501110590860525 1220061528562916471572697)
                    ·
                      rfl

theorem cell22_3564092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_3564092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564092 prefixEnd_3564092 := by exact prefixLift 3564092
  have htrace : WordTrace (prefixWord ++ tailWord_3564092) baseStart_3564092 baseEnd_3564092 := by
    simpa [prefixWord, tailWord_3564092, baseEnd_3564092] using wordTrace_append hprefix tailTrace_3564092
  have hstable : (prefixWord ++ tailWord_3564092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564092).length < 2 ^ (prefixWord ++ tailWord_3564092).sum := by decide
  have hdescent : baseEnd_3564092 < baseStart_3564092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564163 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 3, 4]
def baseStart_3564163 : Nat := 118140960795 + 3564163 * 2 ^ 59
def prefixEnd_3564163 : Nat := 4983230072969 + 3 ^ 40 * 3564163 * 2
def baseEnd_3564163 : Nat := 1220085833313895953047479

theorem tailTrace_3564163 : CollatzResearch.WordTrace tailWord_3564163 prefixEnd_3564163 1220085833313895953047479 := by
  unfold tailWord_3564163
  simp only [CollatzResearch.WordTrace]
  refine ⟨129995704186653636423585143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86663802791102424282390095 129995704186653636423585143)
  ·
    refine ⟨194993556279980454635377715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129995704186653636423585143 194993556279980454635377715)
    ·
      refine ⟨292490334419970681953066573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194993556279980454635377715 292490334419970681953066573)
      ·
        refine ⟨109683875407489005732399965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292490334419970681953066573 109683875407489005732399965)
        ·
          refine ⟨41131453277808377149649987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109683875407489005732399965 41131453277808377149649987)
          ·
            refine ⟨61697179916712565724474981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41131453277808377149649987 61697179916712565724474981)
            ·
              refine ⟨11568221234383606073339059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61697179916712565724474981 11568221234383606073339059)
              ·
                refine ⟨17352331851575409110008589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11568221234383606073339059 17352331851575409110008589)
                ·
                  refine ⟨6507124444340778416253221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17352331851575409110008589 6507124444340778416253221)
                  ·
                    refine ⟨1220085833313895953047479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6507124444340778416253221 1220085833313895953047479)
                    ·
                      rfl

theorem cell22_3564163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 4].length) (baseStart_3564163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564163 prefixEnd_3564163 := by exact prefixLift 3564163
  have htrace : WordTrace (prefixWord ++ tailWord_3564163) baseStart_3564163 baseEnd_3564163 := by
    simpa [prefixWord, tailWord_3564163, baseEnd_3564163] using wordTrace_append hprefix tailTrace_3564163
  have hstable : (prefixWord ++ tailWord_3564163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564163).length < 2 ^ (prefixWord ++ tailWord_3564163).sum := by decide
  have hdescent : baseEnd_3564163 < baseStart_3564163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564223 : List Nat := [1, 1, 2, 2, 2, 5, 1, 8]
def baseStart_3564223 : Nat := 118140960795 + 3564223 * 2 ^ 59
def prefixEnd_3564223 : Nat := 4983230072969 + 3 ^ 40 * 3564223 * 2
def baseEnd_3564223 : Nat := 135567374726675088505255

theorem tailTrace_3564223 : CollatzResearch.WordTrace tailWord_3564223 prefixEnd_3564223 135567374726675088505255 := by
  unfold tailWord_3564223
  simp only [CollatzResearch.WordTrace]
  refine ⟨129997892566436266670769323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86665261710957511113846215 129997892566436266670769323)
  ·
    refine ⟨194996838849654400006153985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129997892566436266670769323 194996838849654400006153985)
    ·
      refine ⟨146247629137240800004615489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194996838849654400006153985 146247629137240800004615489)
      ·
        refine ⟨109685721852930600003461617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146247629137240800004615489 109685721852930600003461617)
        ·
          refine ⟨82264291389697950002596213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109685721852930600003461617 82264291389697950002596213)
          ·
            refine ⟨7712277317784182812743395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82264291389697950002596213 7712277317784182812743395)
            ·
              refine ⟨11568415976676274219115093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7712277317784182812743395 11568415976676274219115093)
              ·
                refine ⟨135567374726675088505255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11568415976676274219115093 135567374726675088505255)
                ·
                  rfl

theorem cell22_3564223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 8].length) (baseStart_3564223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564223 prefixEnd_3564223 := by exact prefixLift 3564223
  have htrace : WordTrace (prefixWord ++ tailWord_3564223) baseStart_3564223 baseEnd_3564223 := by
    simpa [prefixWord, tailWord_3564223, baseEnd_3564223] using wordTrace_append hprefix tailTrace_3564223
  have hstable : (prefixWord ++ tailWord_3564223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564223).length < 2 ^ (prefixWord ++ tailWord_3564223).sum := by decide
  have hdescent : baseEnd_3564223 < baseStart_3564223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564242 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_3564242 : Nat := 118140960795 + 3564242 * 2 ^ 59
def prefixEnd_3564242 : Nat := 4983230072969 + 3 ^ 40 * 3564242 * 2
def baseEnd_3564242 : Nat := 1220112876628366080322237

theorem tailTrace_3564242 : CollatzResearch.WordTrace tailWord_3564242 prefixEnd_3564242 1220112876628366080322237 := by
  unfold tailWord_3564242
  simp only [CollatzResearch.WordTrace]
  refine ⟨32499646388341858228927745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86665723702244955277140653 32499646388341858228927745)
  ·
    refine ⟨24374734791256393671695809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32499646388341858228927745 24374734791256393671695809)
    ·
      refine ⟨18281051093442295253771857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24374734791256393671695809 18281051093442295253771857)
      ·
        refine ⟨13710788320081721440328893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18281051093442295253771857 13710788320081721440328893)
        ·
          refine ⟨5141545620030645540123335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13710788320081721440328893 5141545620030645540123335)
          ·
            refine ⟨7712318430045968310185003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141545620030645540123335 7712318430045968310185003)
            ·
              refine ⟨11568477645068952465277505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7712318430045968310185003 11568477645068952465277505)
              ·
                refine ⟨8676358233801714348958129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11568477645068952465277505 8676358233801714348958129)
                ·
                  refine ⟨6507268675351285761718597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8676358233801714348958129 6507268675351285761718597)
                  ·
                    refine ⟨1220112876628366080322237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6507268675351285761718597 1220112876628366080322237)
                    ·
                      rfl

theorem cell22_3564242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_3564242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564242 prefixEnd_3564242 := by exact prefixLift 3564242
  have htrace : WordTrace (prefixWord ++ tailWord_3564242) baseStart_3564242 baseEnd_3564242 := by
    simpa [prefixWord, tailWord_3564242, baseEnd_3564242] using wordTrace_append hprefix tailTrace_3564242
  have hstable : (prefixWord ++ tailWord_3564242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564242).length < 2 ^ (prefixWord ++ tailWord_3564242).sum := by decide
  have hdescent : baseEnd_3564242 < baseStart_3564242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564276 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3564276 : Nat := 118140960795 + 3564276 * 2 ^ 59
def prefixEnd_3564276 : Nat := 4983230072969 + 3 ^ 40 * 3564276 * 2
def baseEnd_3564276 : Nat := 1220124515523201324972133

theorem tailTrace_3564276 : CollatzResearch.WordTrace tailWord_3564276 prefixEnd_3564276 1220124515523201324972133 := by
  unfold tailWord_3564276
  simp only [CollatzResearch.WordTrace]
  refine ⟨64999912817622128361224341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86666550423496171148299121 64999912817622128361224341)
  ·
    refine ⟨3046870913326037266932391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64999912817622128361224341 3046870913326037266932391)
    ·
      refine ⟨4570306369989055900398587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3046870913326037266932391 4570306369989055900398587)
      ·
        refine ⟨6855459554983583850597881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4570306369989055900398587 6855459554983583850597881)
        ·
          refine ⟨5141594666237687887948411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6855459554983583850597881 5141594666237687887948411)
          ·
            refine ⟨7712391999356531831922617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141594666237687887948411 7712391999356531831922617)
            ·
              refine ⟨5784293999517398873941963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7712391999356531831922617 5784293999517398873941963)
              ·
                refine ⟨8676440999276098310912945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784293999517398873941963 8676440999276098310912945)
                ·
                  refine ⟨6507330749457073733184709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8676440999276098310912945 6507330749457073733184709)
                  ·
                    refine ⟨1220124515523201324972133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6507330749457073733184709 1220124515523201324972133)
                    ·
                      rfl

theorem cell22_3564276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3564276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564276 prefixEnd_3564276 := by exact prefixLift 3564276
  have htrace : WordTrace (prefixWord ++ tailWord_3564276) baseStart_3564276 baseEnd_3564276 := by
    simpa [prefixWord, tailWord_3564276, baseEnd_3564276] using wordTrace_append hprefix tailTrace_3564276
  have hstable : (prefixWord ++ tailWord_3564276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564276).length < 2 ^ (prefixWord ++ tailWord_3564276).sum := by decide
  have hdescent : baseEnd_3564276 < baseStart_3564276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564349 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_3564349 : Nat := 118140960795 + 3564349 * 2 ^ 59
def prefixEnd_3564349 : Nat := 4983230072969 + 3 ^ 40 * 3564349 * 2
def baseEnd_3564349 : Nat := 1220149504915053467896909

theorem tailTrace_3564349 : CollatzResearch.WordTrace tailWord_3564349 prefixEnd_3564349 1220149504915053467896909 := by
  unfold tailWord_3564349
  simp only [CollatzResearch.WordTrace]
  refine ⟨130002488163979790189856101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86668325442653193459904067 130002488163979790189856101)
  ·
    refine ⟨24375466530746210660598019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130002488163979790189856101 24375466530746210660598019)
    ·
      refine ⟨36563199796119315990897029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24375466530746210660598019 36563199796119315990897029)
      ·
        refine ⟨6855599961772371748293193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36563199796119315990897029 6855599961772371748293193)
        ·
          refine ⟨5141699971329278811219895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6855599961772371748293193 5141699971329278811219895)
          ·
            refine ⟨7712549956993918216829843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141699971329278811219895 7712549956993918216829843)
            ·
              refine ⟨11568824935490877325244765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7712549956993918216829843 11568824935490877325244765)
              ·
                refine ⟨4338309350809078996966787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11568824935490877325244765 4338309350809078996966787)
                ·
                  refine ⟨6507464026213618495450181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4338309350809078996966787 6507464026213618495450181)
                  ·
                    refine ⟨1220149504915053467896909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6507464026213618495450181 1220149504915053467896909)
                    ·
                      rfl

theorem cell22_3564349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_3564349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564349 prefixEnd_3564349 := by exact prefixLift 3564349
  have htrace : WordTrace (prefixWord ++ tailWord_3564349) baseStart_3564349 baseEnd_3564349 := by
    simpa [prefixWord, tailWord_3564349, baseEnd_3564349] using wordTrace_append hprefix tailTrace_3564349
  have hstable : (prefixWord ++ tailWord_3564349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564349).length < 2 ^ (prefixWord ++ tailWord_3564349).sum := by decide
  have hdescent : baseEnd_3564349 < baseStart_3564349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564360 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 4, 4]
def baseStart_3564360 : Nat := 118140960795 + 3564360 * 2 ^ 59
def prefixEnd_3564360 : Nat := 4983230072969 + 3 ^ 40 * 3564360 * 2
def baseEnd_3564360 : Nat := 1220153270439853105871875

theorem tailTrace_3564360 : CollatzResearch.WordTrace tailWord_3564360 prefixEnd_3564360 1220153270439853105871875 := by
  unfold tailWord_3564360
  simp only [CollatzResearch.WordTrace]
  refine ⟨65001444683469969534253267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86668592911293292712337689 65001444683469969534253267)
  ·
    refine ⟨97502167025204954301379901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65001444683469969534253267 97502167025204954301379901)
    ·
      refine ⟨36563312634451857863017463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97502167025204954301379901 36563312634451857863017463)
      ·
        refine ⟨54844968951677786794526195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36563312634451857863017463 54844968951677786794526195)
        ·
          refine ⟨82267453427516680191789293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54844968951677786794526195 82267453427516680191789293)
          ·
            refine ⟨30850295035318755071920985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82267453427516680191789293 30850295035318755071920985)
            ·
              refine ⟨23137721276489066303940739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30850295035318755071920985 23137721276489066303940739)
              ·
                refine ⟨34706581914733599455911109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23137721276489066303940739 34706581914733599455911109)
                ·
                  refine ⟨6507484109012549897983333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34706581914733599455911109 6507484109012549897983333)
                  ·
                    refine ⟨1220153270439853105871875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6507484109012549897983333 1220153270439853105871875)
                    ·
                      rfl

theorem cell22_3564360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_3564360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564360 prefixEnd_3564360 := by exact prefixLift 3564360
  have htrace : WordTrace (prefixWord ++ tailWord_3564360) baseStart_3564360 baseEnd_3564360 := by
    simpa [prefixWord, tailWord_3564360, baseEnd_3564360] using wordTrace_append hprefix tailTrace_3564360
  have hstable : (prefixWord ++ tailWord_3564360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564360).length < 2 ^ (prefixWord ++ tailWord_3564360).sum := by decide
  have hdescent : baseEnd_3564360 < baseStart_3564360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564362 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 2, 3]
def baseStart_3564362 : Nat := 118140960795 + 3564362 * 2 ^ 59
def prefixEnd_3564362 : Nat := 4983230072969 + 3 ^ 40 * 3564362 * 2
def baseEnd_3564362 : Nat := 1220153955080725767321869

theorem tailTrace_3564362 : CollatzResearch.WordTrace tailWord_3564362 prefixEnd_3564362 1220153955080725767321869 := by
  unfold tailWord_3564362
  simp only [CollatzResearch.WordTrace]
  refine ⟨32500740578233173352519835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86668641541955128940052893 32500740578233173352519835)
  ·
    refine ⟨48751110867349760028779753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32500740578233173352519835 48751110867349760028779753)
    ·
      refine ⟨36563333150512320021584815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48751110867349760028779753 36563333150512320021584815)
      ·
        refine ⟨54844999725768480032377223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36563333150512320021584815 54844999725768480032377223)
        ·
          refine ⟨82267499588652720048565835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54844999725768480032377223 82267499588652720048565835)
          ·
            refine ⟨123401249382979080072848753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82267499588652720048565835 123401249382979080072848753)
            ·
              refine ⟨92550937037234310054636565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123401249382979080072848753 92550937037234310054636565)
              ·
                refine ⟨4338325173620358283811089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92550937037234310054636565 4338325173620358283811089)
                ·
                  refine ⟨3253743880215268712858317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4338325173620358283811089 3253743880215268712858317)
                  ·
                    refine ⟨1220153955080725767321869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3253743880215268712858317 1220153955080725767321869)
                    ·
                      rfl

theorem cell22_3564362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_3564362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564362 prefixEnd_3564362 := by exact prefixLift 3564362
  have htrace : WordTrace (prefixWord ++ tailWord_3564362) baseStart_3564362 baseEnd_3564362 := by
    simpa [prefixWord, tailWord_3564362, baseEnd_3564362] using wordTrace_append hprefix tailTrace_3564362
  have hstable : (prefixWord ++ tailWord_3564362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564362).length < 2 ^ (prefixWord ++ tailWord_3564362).sum := by decide
  have hdescent : baseEnd_3564362 < baseStart_3564362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564392 : List Nat := [2, 1, 4, 2, 1, 2, 4, 6]
def baseStart_3564392 : Nat := 118140960795 + 3564392 * 2 ^ 59
def prefixEnd_3564392 : Nat := 4983230072969 + 3 ^ 40 * 3564392 * 2
def baseEnd_3564392 : Nat := 135573802743757298785753

theorem tailTrace_3564392 : CollatzResearch.WordTrace tailWord_3564392 prefixEnd_3564392 135573802743757298785753 := by
  unfold tailWord_3564392
  simp only [CollatzResearch.WordTrace]
  refine ⟨65002028251412004266835715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86669371001882672355780953 65002028251412004266835715)
  ·
    refine ⟨97503042377118006400253573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65002028251412004266835715 97503042377118006400253573)
    ·
      refine ⟨18281820445709626200047545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97503042377118006400253573 18281820445709626200047545)
      ·
        refine ⟨13711365334282219650035659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18281820445709626200047545 13711365334282219650035659)
        ·
          refine ⟨20567048001423329475053489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13711365334282219650035659 20567048001423329475053489)
          ·
            refine ⟨15425286001067497106290117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20567048001423329475053489 15425286001067497106290117)
            ·
              refine ⟨2892241125200155707429397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15425286001067497106290117 2892241125200155707429397)
              ·
                refine ⟨135573802743757298785753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2892241125200155707429397 135573802743757298785753)
                ·
                  rfl

theorem cell22_3564392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 6].length) (baseStart_3564392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564392 prefixEnd_3564392 := by exact prefixLift 3564392
  have htrace : WordTrace (prefixWord ++ tailWord_3564392) baseStart_3564392 baseEnd_3564392 := by
    simpa [prefixWord, tailWord_3564392, baseEnd_3564392] using wordTrace_append hprefix tailTrace_3564392
  have hstable : (prefixWord ++ tailWord_3564392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564392).length < 2 ^ (prefixWord ++ tailWord_3564392).sum := by decide
  have hdescent : baseEnd_3564392 < baseStart_3564392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564398 : List Nat := [4, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_3564398 : Nat := 118140960795 + 3564398 * 2 ^ 59
def prefixEnd_3564398 : Nat := 4983230072969 + 3 ^ 40 * 3564398 * 2
def baseEnd_3564398 : Nat := 406722092872144557807253

theorem tailTrace_3564398 : CollatzResearch.WordTrace tailWord_3564398 prefixEnd_3564398 406722092872144557807253 := by
  unfold tailWord_3564398
  simp only [CollatzResearch.WordTrace]
  refine ⟨16250534417600283944798731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86669516893868181038926565 16250534417600283944798731)
  ·
    refine ⟨24375801626400425917198097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16250534417600283944798731 24375801626400425917198097)
    ·
      refine ⟨18281851219800319437898573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24375801626400425917198097 18281851219800319437898573)
      ·
        refine ⟨6855694207425119789211965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18281851219800319437898573 6855694207425119789211965)
        ·
          refine ⟨2570885327784419920954487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6855694207425119789211965 2570885327784419920954487)
          ·
            refine ⟨3856327991676629881431731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570885327784419920954487 3856327991676629881431731)
            ·
              refine ⟨5784491987514944822147597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856327991676629881431731 5784491987514944822147597)
              ·
                refine ⟨2169184495318104308305349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5784491987514944822147597 2169184495318104308305349)
                ·
                  refine ⟨406722092872144557807253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169184495318104308305349 406722092872144557807253)
                  ·
                    rfl

theorem cell22_3564398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_3564398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564398 prefixEnd_3564398 := by exact prefixLift 3564398
  have htrace : WordTrace (prefixWord ++ tailWord_3564398) baseStart_3564398 baseEnd_3564398 := by
    simpa [prefixWord, tailWord_3564398, baseEnd_3564398] using wordTrace_append hprefix tailTrace_3564398
  have hstable : (prefixWord ++ tailWord_3564398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564398).length < 2 ^ (prefixWord ++ tailWord_3564398).sum := by decide
  have hdescent : baseEnd_3564398 < baseStart_3564398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564424 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 3, 3]
def baseStart_3564424 : Nat := 118140960795 + 3564424 * 2 ^ 59
def prefixEnd_3564424 : Nat := 4983230072969 + 3 ^ 40 * 3564424 * 2
def baseEnd_3564424 : Nat := 1220175178947778272271679

theorem tailTrace_3564424 : CollatzResearch.WordTrace tailWord_3564424 prefixEnd_3564424 1220175178947778272271679 := by
  unfold tailWord_3564424
  simp only [CollatzResearch.WordTrace]
  refine ⟨65002611819354038999418163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86670149092472051999224217 65002611819354038999418163)
  ·
    refine ⟨97503917729031058499127245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65002611819354038999418163 97503917729031058499127245)
    ·
      refine ⟨36563969148386646937172717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97503917729031058499127245 36563969148386646937172717)
      ·
        refine ⟨13711488430644992601439769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36563969148386646937172717 13711488430644992601439769)
        ·
          refine ⟨10283616322983744451079827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13711488430644992601439769 10283616322983744451079827)
          ·
            refine ⟨15425424484475616676619741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10283616322983744451079827 15425424484475616676619741)
            ·
              refine ⟨5784534181678356253732403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15425424484475616676619741 5784534181678356253732403)
              ·
                refine ⟨8676801272517534380598605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784534181678356253732403 8676801272517534380598605)
                ·
                  refine ⟨3253800477194075392724477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8676801272517534380598605 3253800477194075392724477)
                  ·
                    refine ⟨1220175178947778272271679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3253800477194075392724477 1220175178947778272271679)
                    ·
                      rfl

theorem cell22_3564424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_3564424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564424 prefixEnd_3564424 := by exact prefixLift 3564424
  have htrace : WordTrace (prefixWord ++ tailWord_3564424) baseStart_3564424 baseEnd_3564424 := by
    simpa [prefixWord, tailWord_3564424, baseEnd_3564424] using wordTrace_append hprefix tailTrace_3564424
  have hstable : (prefixWord ++ tailWord_3564424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564424).length < 2 ^ (prefixWord ++ tailWord_3564424).sum := by decide
  have hdescent : baseEnd_3564424 < baseStart_3564424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564437 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 5]
def baseStart_3564437 : Nat := 118140960795 + 3564437 * 2 ^ 59
def prefixEnd_3564437 : Nat := 4983230072969 + 3 ^ 40 * 3564437 * 2
def baseEnd_3564437 : Nat := 406726543037816857232213

theorem tailTrace_3564437 : CollatzResearch.WordTrace tailWord_3564437 prefixEnd_3564437 406726543037816857232213 := by
  unfold tailWord_3564437
  simp only [CollatzResearch.WordTrace]
  refine ⟨130005697787660981219059565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86670465191773987479373043 130005697787660981219059565)
  ·
    refine ⟨48752136670372867957147337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130005697787660981219059565 48752136670372867957147337)
    ·
      refine ⟨36564102502779650967860503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48752136670372867957147337 36564102502779650967860503)
      ·
        refine ⟨54846153754169476451790755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36564102502779650967860503 54846153754169476451790755)
        ·
          refine ⟨82269230631254214677686133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54846153754169476451790755 82269230631254214677686133)
          ·
            refine ⟨7712740371680082626033075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82269230631254214677686133 7712740371680082626033075)
            ·
              refine ⟨11569110557520123939049613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7712740371680082626033075 11569110557520123939049613)
              ·
                refine ⟨4338416459070046477143605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11569110557520123939049613 4338416459070046477143605)
                ·
                  refine ⟨406726543037816857232213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4338416459070046477143605 406726543037816857232213)
                  ·
                    rfl

theorem cell22_3564437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_3564437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564437 prefixEnd_3564437 := by exact prefixLift 3564437
  have htrace : WordTrace (prefixWord ++ tailWord_3564437) baseStart_3564437 baseEnd_3564437 := by
    simpa [prefixWord, tailWord_3564437, baseEnd_3564437] using wordTrace_append hprefix tailTrace_3564437
  have hstable : (prefixWord ++ tailWord_3564437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564437).length < 2 ^ (prefixWord ++ tailWord_3564437).sum := by decide
  have hdescent : baseEnd_3564437 < baseStart_3564437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564497 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 1, 5]
def baseStart_3564497 : Nat := 118140960795 + 3564497 * 2 ^ 59
def prefixEnd_3564497 : Nat := 4983230072969 + 3 ^ 40 * 3564497 * 2
def baseEnd_3564497 : Nat := 1220200168339630415196455

theorem tailTrace_3564497 : CollatzResearch.WordTrace tailWord_3564497 prefixEnd_3564497 1220200168339630415196455 := by
  unfold tailWord_3564497
  simp only [CollatzResearch.WordTrace]
  refine ⟨130007886167443611466243745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86671924111629074310829163 130007886167443611466243745)
  ·
    refine ⟨97505914625582708599682809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130007886167443611466243745 97505914625582708599682809)
    ·
      refine ⟨73129435969187031449762107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97505914625582708599682809 73129435969187031449762107)
      ·
        refine ⟨109694153953780547174643161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73129435969187031449762107 109694153953780547174643161)
        ·
          refine ⟨82270615465335410380982371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109694153953780547174643161 82270615465335410380982371)
          ·
            refine ⟨123405923198003115571473557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82270615465335410380982371 123405923198003115571473557)
            ·
              refine ⟨5784652649906396042412823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123405923198003115571473557 5784652649906396042412823)
              ·
                refine ⟨8676978974859594063619235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784652649906396042412823 8676978974859594063619235)
                ·
                  refine ⟨13015468462289391095428853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8676978974859594063619235 13015468462289391095428853)
                  ·
                    refine ⟨1220200168339630415196455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13015468462289391095428853 1220200168339630415196455)
                    ·
                      rfl

theorem cell22_3564497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_3564497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564497 prefixEnd_3564497 := by exact prefixLift 3564497
  have htrace : WordTrace (prefixWord ++ tailWord_3564497) baseStart_3564497 baseEnd_3564497 := by
    simpa [prefixWord, tailWord_3564497, baseEnd_3564497] using wordTrace_append hprefix tailTrace_3564497
  have hstable : (prefixWord ++ tailWord_3564497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564497).length < 2 ^ (prefixWord ++ tailWord_3564497).sum := by decide
  have hdescent : baseEnd_3564497 < baseStart_3564497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564593 : List Nat := [1, 2, 2, 3, 1, 2, 5, 2, 1, 3]
def baseStart_3564593 : Nat := 118140960795 + 3564593 * 2 ^ 59
def prefixEnd_3564593 : Nat := 4983230072969 + 3 ^ 40 * 3564593 * 2
def baseEnd_3564593 : Nat := 1220233031101518164796161

theorem tailTrace_3564593 : CollatzResearch.WordTrace tailWord_3564593 prefixEnd_3564593 1220233031101518164796161 := by
  unfold tailWord_3564593
  simp only [CollatzResearch.WordTrace]
  refine ⟨130011387575095819861738433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86674258383397213241158955 130011387575095819861738433)
  ·
    refine ⟨97508540681321864896303825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130011387575095819861738433 97508540681321864896303825)
    ·
      refine ⟨73131405510991398672227869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97508540681321864896303825 73131405510991398672227869)
      ·
        refine ⟨27424277066621774502085451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73131405510991398672227869 27424277066621774502085451)
        ·
          refine ⟨41136415599932661753128177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27424277066621774502085451 41136415599932661753128177)
          ·
            refine ⟨30852311699949496314846133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41136415599932661753128177 30852311699949496314846133)
            ·
              refine ⟨2892404221870265279516825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30852311699949496314846133 2892404221870265279516825)
              ·
                refine ⟨2169303166402698959637619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2892404221870265279516825 2169303166402698959637619)
                ·
                  refine ⟨3253954749604048439456429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169303166402698959637619 3253954749604048439456429)
                  ·
                    refine ⟨1220233031101518164796161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3253954749604048439456429 1220233031101518164796161)
                    ·
                      rfl

theorem cell22_3564593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_3564593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564593 prefixEnd_3564593 := by exact prefixLift 3564593
  have htrace : WordTrace (prefixWord ++ tailWord_3564593) baseStart_3564593 baseEnd_3564593 := by
    simpa [prefixWord, tailWord_3564593, baseEnd_3564593] using wordTrace_append hprefix tailTrace_3564593
  have hstable : (prefixWord ++ tailWord_3564593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564593).length < 2 ^ (prefixWord ++ tailWord_3564593).sum := by decide
  have hdescent : baseEnd_3564593 < baseStart_3564593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564606 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_3564606 : Nat := 118140960795 + 3564606 * 2 ^ 59
def prefixEnd_3564606 : Nat := 4983230072969 + 3 ^ 40 * 3564606 * 2
def baseEnd_3564606 : Nat := 406745827089063488073707

theorem tailTrace_3564606 : CollatzResearch.WordTrace tailWord_3564606 prefixEnd_3564606 406745827089063488073707 := by
  unfold tailWord_3564606
  simp only [CollatzResearch.WordTrace]
  refine ⟨16251482715506090385245209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86674574482699148721307781 16251482715506090385245209)
  ·
    refine ⟨12188612036629567788933907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16251482715506090385245209 12188612036629567788933907)
    ·
      refine ⟨18282918054944351683400861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12188612036629567788933907 18282918054944351683400861)
      ·
        refine ⟨6856094270604131881275323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18282918054944351683400861 6856094270604131881275323)
        ·
          refine ⟨10284141405906197821912985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856094270604131881275323 10284141405906197821912985)
          ·
            refine ⟨7713106054429648366434739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10284141405906197821912985 7713106054429648366434739)
            ·
              refine ⟨11569659081644472549652109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713106054429648366434739 11569659081644472549652109)
              ·
                refine ⟨4338622155616677206119541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11569659081644472549652109 4338622155616677206119541)
                ·
                  refine ⟨406745827089063488073707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4338622155616677206119541 406745827089063488073707)
                  ·
                    rfl

theorem cell22_3564606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_3564606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564606 prefixEnd_3564606 := by exact prefixLift 3564606
  have htrace : WordTrace (prefixWord ++ tailWord_3564606) baseStart_3564606 baseEnd_3564606 := by
    simpa [prefixWord, tailWord_3564606, baseEnd_3564606] using wordTrace_append hprefix tailTrace_3564606
  have hstable : (prefixWord ++ tailWord_3564606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564606).length < 2 ^ (prefixWord ++ tailWord_3564606).sum := by decide
  have hdescent : baseEnd_3564606 < baseStart_3564606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564681 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 2, 4]
def baseStart_3564681 : Nat := 118140960795 + 3564681 * 2 ^ 59
def prefixEnd_3564681 : Nat := 4983230072969 + 3 ^ 40 * 3564681 * 2
def baseEnd_3564681 : Nat := 1220263155299915268595891

theorem tailTrace_3564681 : CollatzResearch.WordTrace tailWord_3564681 prefixEnd_3564681 1220263155299915268595891 := by
  unfold tailWord_3564681
  simp only [CollatzResearch.WordTrace]
  refine ⟨130014597198777010890941897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86676398132518007260627931 130014597198777010890941897)
  ·
    refine ⟨97510947899082758168206423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130014597198777010890941897 97510947899082758168206423)
    ·
      refine ⟨146266421848624137252309635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97510947899082758168206423 146266421848624137252309635)
      ·
        refine ⟨219399632772936205878464453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146266421848624137252309635 219399632772936205878464453)
        ·
          refine ⟨41137431144925538602212085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219399632772936205878464453 41137431144925538602212085)
          ·
            refine ⟨3856634169836769243957383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41137431144925538602212085 3856634169836769243957383)
            ·
              refine ⟨5784951254755153865936075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856634169836769243957383 5784951254755153865936075)
              ·
                refine ⟨8677426882132730798904113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784951254755153865936075 8677426882132730798904113)
                ·
                  refine ⟨6508070161599548099178085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8677426882132730798904113 6508070161599548099178085)
                  ·
                    refine ⟨1220263155299915268595891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6508070161599548099178085 1220263155299915268595891)
                    ·
                      rfl

theorem cell22_3564681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 4].length) (baseStart_3564681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564681 prefixEnd_3564681 := by exact prefixLift 3564681
  have htrace : WordTrace (prefixWord ++ tailWord_3564681) baseStart_3564681 baseEnd_3564681 := by
    simpa [prefixWord, tailWord_3564681, baseEnd_3564681] using wordTrace_append hprefix tailTrace_3564681
  have hstable : (prefixWord ++ tailWord_3564681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564681).length < 2 ^ (prefixWord ++ tailWord_3564681).sum := by decide
  have hdescent : baseEnd_3564681 < baseStart_3564681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564775 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 5]
def baseStart_3564775 : Nat := 118140960795 + 3564775 * 2 ^ 59
def prefixEnd_3564775 : Nat := 4983230072969 + 3 ^ 40 * 3564775 * 2
def baseEnd_3564775 : Nat := 406765111140310118915201

theorem tailTrace_3564775 : CollatzResearch.WordTrace tailWord_3564775 prefixEnd_3564775 406765111140310118915201 := by
  unfold tailWord_3564775
  simp only [CollatzResearch.WordTrace]
  refine ⟨130018025660436464944863779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86678683773624309963242519 130018025660436464944863779)
  ·
    refine ⟨195027038490654697417295669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130018025660436464944863779 195027038490654697417295669)
    ·
      refine ⟨18283784858498877882871469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195027038490654697417295669 18283784858498877882871469)
      ·
        refine ⟨6856419321937079206076801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18283784858498877882871469 6856419321937079206076801)
        ·
          refine ⟨5142314491452809404557601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6856419321937079206076801 5142314491452809404557601)
          ·
            refine ⟨3856735868589607053418201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5142314491452809404557601 3856735868589607053418201)
            ·
              refine ⟨2892551901442205290063651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3856735868589607053418201 2892551901442205290063651)
              ·
                refine ⟨4338827852163307935095477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2892551901442205290063651 4338827852163307935095477)
                ·
                  refine ⟨406765111140310118915201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4338827852163307935095477 406765111140310118915201)
                  ·
                    rfl

theorem cell22_3564775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 5].length) (baseStart_3564775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564775 prefixEnd_3564775 := by exact prefixLift 3564775
  have htrace : WordTrace (prefixWord ++ tailWord_3564775) baseStart_3564775 baseEnd_3564775 := by
    simpa [prefixWord, tailWord_3564775, baseEnd_3564775] using wordTrace_append hprefix tailTrace_3564775
  have hstable : (prefixWord ++ tailWord_3564775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564775).length < 2 ^ (prefixWord ++ tailWord_3564775).sum := by decide
  have hdescent : baseEnd_3564775 < baseStart_3564775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564801 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3564801 : Nat := 118140960795 + 3564801 * 2 ^ 59
def prefixEnd_3564801 : Nat := 4983230072969 + 3 ^ 40 * 3564801 * 2
def baseEnd_3564801 : Nat := 1220304233752274955595523

theorem tailTrace_3564801 : CollatzResearch.WordTrace tailWord_3564801 prefixEnd_3564801 1220304233752274955595523 := by
  unfold tailWord_3564801
  simp only [CollatzResearch.WordTrace]
  refine ⟨130018973958342271385310257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86679315972228180923540171 130018973958342271385310257)
  ·
    refine ⟨97514230468756703538982693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130018973958342271385310257 97514230468756703538982693)
    ·
      refine ⟨18283918212891881913559255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97514230468756703538982693 18283918212891881913559255)
      ·
        refine ⟨27425877319337822870338883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18283918212891881913559255 27425877319337822870338883)
        ·
          refine ⟨41138815979006734305508325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27425877319337822870338883 41138815979006734305508325)
          ·
            refine ⟨7713527996063762682282811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41138815979006734305508325 7713527996063762682282811)
            ·
              refine ⟨11570291994095644023424217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713527996063762682282811 11570291994095644023424217)
              ·
                refine ⟨8677718995571733017568163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11570291994095644023424217 8677718995571733017568163)
                ·
                  refine ⟨13016578493357599526352245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8677718995571733017568163 13016578493357599526352245)
                  ·
                    refine ⟨1220304233752274955595523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13016578493357599526352245 1220304233752274955595523)
                    ·
                      rfl

theorem cell22_3564801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3564801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564801 prefixEnd_3564801 := by exact prefixLift 3564801
  have htrace : WordTrace (prefixWord ++ tailWord_3564801) baseStart_3564801 baseEnd_3564801 := by
    simpa [prefixWord, tailWord_3564801, baseEnd_3564801] using wordTrace_append hprefix tailTrace_3564801
  have hstable : (prefixWord ++ tailWord_3564801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564801).length < 2 ^ (prefixWord ++ tailWord_3564801).sum := by decide
  have hdescent : baseEnd_3564801 < baseStart_3564801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564814 : List Nat := [4, 1, 1, 2, 1, 13]
def baseStart_3564814 : Nat := 118140960795 + 3564814 * 2 ^ 59
def prefixEnd_3564814 : Nat := 4983230072969 + 3 ^ 40 * 3564814 * 2
def baseEnd_3564814 : Nat := 15065539307628978457043

theorem tailTrace_3564814 : CollatzResearch.WordTrace tailWord_3564814 prefixEnd_3564814 15065539307628978457043 := by
  unfold tailWord_3564814
  simp only [CollatzResearch.WordTrace]
  refine ⟨16252431013411896825691687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86679632071530116403688997 16252431013411896825691687)
  ·
    refine ⟨24378646520117845238537531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16252431013411896825691687 24378646520117845238537531)
    ·
      refine ⟨36567969780176767857806297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24378646520117845238537531 36567969780176767857806297)
      ·
        refine ⟨27425977335132575893354723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36567969780176767857806297 27425977335132575893354723)
        ·
          refine ⟨41138966002698863840032085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27425977335132575893354723 41138966002698863840032085)
          ·
            refine ⟨15065539307628978457043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 41138966002698863840032085 15065539307628978457043)
            ·
              rfl

theorem cell22_3564814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 13].length) (baseStart_3564814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564814 prefixEnd_3564814 := by exact prefixLift 3564814
  have htrace : WordTrace (prefixWord ++ tailWord_3564814) baseStart_3564814 baseEnd_3564814 := by
    simpa [prefixWord, tailWord_3564814, baseEnd_3564814] using wordTrace_append hprefix tailTrace_3564814
  have hstable : (prefixWord ++ tailWord_3564814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564814).length < 2 ^ (prefixWord ++ tailWord_3564814).sum := by decide
  have hdescent : baseEnd_3564814 < baseStart_3564814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564844 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_3564844 : Nat := 118140960795 + 3564844 * 2 ^ 59
def prefixEnd_3564844 : Nat := 4983230072969 + 3 ^ 40 * 3564844 * 2
def baseEnd_3564844 : Nat := 1220318953531037176770391

theorem tailTrace_3564844 : CollatzResearch.WordTrace tailWord_3564844 prefixEnd_3564844 1220318953531037176770391 := by
  unfold tailWord_3564844
  simp only [CollatzResearch.WordTrace]
  refine ⟨65010271148593244864562793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86680361531457659819417057 65010271148593244864562793)
  ·
    refine ⟨48757703361444933648422095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65010271148593244864562793 48757703361444933648422095)
    ·
      refine ⟨73136555042167400472633143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48757703361444933648422095 73136555042167400472633143)
      ·
        refine ⟨109704832563251100708949715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73136555042167400472633143 109704832563251100708949715)
        ·
          refine ⟨164557248844876651063424573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109704832563251100708949715 164557248844876651063424573)
          ·
            refine ⟨61708968316828744148784215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164557248844876651063424573 61708968316828744148784215)
            ·
              refine ⟨92563452475243116223176323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61708968316828744148784215 92563452475243116223176323)
              ·
                refine ⟨138845178712864674334764485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92563452475243116223176323 138845178712864674334764485)
                ·
                  refine ⟨26033471008662126437768341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138845178712864674334764485 26033471008662126437768341)
                  ·
                    refine ⟨1220318953531037176770391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26033471008662126437768341 1220318953531037176770391)
                    ·
                      rfl

theorem cell22_3564844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_3564844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564844 prefixEnd_3564844 := by exact prefixLift 3564844
  have htrace : WordTrace (prefixWord ++ tailWord_3564844) baseStart_3564844 baseEnd_3564844 := by
    simpa [prefixWord, tailWord_3564844, baseEnd_3564844] using wordTrace_append hprefix tailTrace_3564844
  have hstable : (prefixWord ++ tailWord_3564844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564844).length < 2 ^ (prefixWord ++ tailWord_3564844).sum := by decide
  have hdescent : baseEnd_3564844 < baseStart_3564844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564876 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 7]
def baseStart_3564876 : Nat := 118140960795 + 3564876 * 2 ^ 59
def prefixEnd_3564876 : Nat := 4983230072969 + 3 ^ 40 * 3564876 * 2
def baseEnd_3564876 : Nat := 406776635928333253323431

theorem tailTrace_3564876 : CollatzResearch.WordTrace tailWord_3564876 prefixEnd_3564876 406776635928333253323431 := by
  unfold tailWord_3564876
  simp only [CollatzResearch.WordTrace]
  refine ⟨65010854716535279597145241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86681139622047039462860321 65010854716535279597145241)
  ·
    refine ⟨48758141037401459697858931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65010854716535279597145241 48758141037401459697858931)
    ·
      refine ⟨73137211556102189546788397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48758141037401459697858931 73137211556102189546788397)
      ·
        refine ⟨27426454333538321080045649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73137211556102189546788397 27426454333538321080045649)
        ·
          refine ⟨20569840750153740810034237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27426454333538321080045649 20569840750153740810034237)
          ·
            refine ⟨7713690281307652803762839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20569840750153740810034237 7713690281307652803762839)
            ·
              refine ⟨11570535421961479205644259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713690281307652803762839 11570535421961479205644259)
              ·
                refine ⟨17355803132942218808466389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11570535421961479205644259 17355803132942218808466389)
                ·
                  refine ⟨406776635928333253323431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17355803132942218808466389 406776635928333253323431)
                  ·
                    rfl

theorem cell22_3564876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_3564876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564876 prefixEnd_3564876 := by exact prefixLift 3564876
  have htrace : WordTrace (prefixWord ++ tailWord_3564876) baseStart_3564876 baseEnd_3564876 := by
    simpa [prefixWord, tailWord_3564876, baseEnd_3564876] using wordTrace_append hprefix tailTrace_3564876
  have hstable : (prefixWord ++ tailWord_3564876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564876).length < 2 ^ (prefixWord ++ tailWord_3564876).sum := by decide
  have hdescent : baseEnd_3564876 < baseStart_3564876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564886 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3564886 : Nat := 118140960795 + 3564886 * 2 ^ 59
def prefixEnd_3564886 : Nat := 4983230072969 + 3 ^ 40 * 3564886 * 2
def baseEnd_3564886 : Nat := 1220333330989363067220263

theorem tailTrace_3564886 : CollatzResearch.WordTrace tailWord_3564886 prefixEnd_3564886 1220333330989363067220263 := by
  unfold tailWord_3564886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8126379635189645681384657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86681382775356220601436341 8126379635189645681384657)
  ·
    refine ⟨6094784726392234261038493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8126379635189645681384657 6094784726392234261038493)
    ·
      refine ⟨2285544272397087847889435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6094784726392234261038493 2285544272397087847889435)
      ·
        refine ⟨3428316408595631771834153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2285544272397087847889435 3428316408595631771834153)
        ·
          refine ⟨2571237306446723828875615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3428316408595631771834153 2571237306446723828875615)
          ·
            refine ⟨3856855959670085743313423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571237306446723828875615 3856855959670085743313423)
            ·
              refine ⟨5785283939505128614970135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856855959670085743313423 5785283939505128614970135)
              ·
                refine ⟨8677925909257692922455203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5785283939505128614970135 8677925909257692922455203)
                ·
                  refine ⟨13016888863886539383682805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8677925909257692922455203 13016888863886539383682805)
                  ·
                    refine ⟨1220333330989363067220263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13016888863886539383682805 1220333330989363067220263)
                    ·
                      rfl

theorem cell22_3564886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3564886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564886 prefixEnd_3564886 := by exact prefixLift 3564886
  have htrace : WordTrace (prefixWord ++ tailWord_3564886) baseStart_3564886 baseEnd_3564886 := by
    simpa [prefixWord, tailWord_3564886, baseEnd_3564886] using wordTrace_append hprefix tailTrace_3564886
  have hstable : (prefixWord ++ tailWord_3564886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564886).length < 2 ^ (prefixWord ++ tailWord_3564886).sum := by decide
  have hdescent : baseEnd_3564886 < baseStart_3564886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564951 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 6, 4]
def baseStart_3564951 : Nat := 118140960795 + 3564951 * 2 ^ 59
def prefixEnd_3564951 : Nat := 4983230072969 + 3 ^ 40 * 3564951 * 2
def baseEnd_3564951 : Nat := 1220355581817724564345063

theorem tailTrace_3564951 : CollatzResearch.WordTrace tailWord_3564951 prefixEnd_3564951 1220355581817724564345063 := by
  unfold tailWord_3564951
  simp only [CollatzResearch.WordTrace]
  refine ⟨130024444907798847003270707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86682963271865898002180471 130024444907798847003270707)
  ·
    refine ⟨195036667361698270504906061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130024444907798847003270707 195036667361698270504906061)
    ·
      refine ⟨73138750260636851439339773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195036667361698270504906061 73138750260636851439339773)
      ·
        refine ⟨27427031347738819289752415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73138750260636851439339773 27427031347738819289752415)
        ·
          refine ⟨41140547021608228934628623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27427031347738819289752415 41140547021608228934628623)
          ·
            refine ⟨61710820532412343401942935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41140547021608228934628623 61710820532412343401942935)
            ·
              refine ⟨92566230798618515102914403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61710820532412343401942935 92566230798618515102914403)
              ·
                refine ⟨138849346197927772654371605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92566230798618515102914403 138849346197927772654371605)
                ·
                  refine ⟨6508563103027864343173669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138849346197927772654371605 6508563103027864343173669)
                  ·
                    refine ⟨1220355581817724564345063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6508563103027864343173669 1220355581817724564345063)
                    ·
                      rfl

theorem cell22_3564951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_3564951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3564951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3564951 prefixEnd_3564951 := by exact prefixLift 3564951
  have htrace : WordTrace (prefixWord ++ tailWord_3564951) baseStart_3564951 baseEnd_3564951 := by
    simpa [prefixWord, tailWord_3564951, baseEnd_3564951] using wordTrace_append hprefix tailTrace_3564951
  have hstable : (prefixWord ++ tailWord_3564951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564951).length < 2 ^ (prefixWord ++ tailWord_3564951).sum := by decide
  have hdescent : baseEnd_3564951 < baseStart_3564951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565032 : List Nat := [2, 1, 4, 1, 1, 2, 4, 3, 1, 3]
def baseStart_3565032 : Nat := 118140960795 + 3565032 * 2 ^ 59
def prefixEnd_3565032 : Nat := 4983230072969 + 3 ^ 40 * 3565032 * 2
def baseEnd_3565032 : Nat := 1220383309773067353069815

theorem tailTrace_3565032 : CollatzResearch.WordTrace tailWord_3565032 prefixEnd_3565032 1220383309773067353069815 := by
  unfold tailWord_3565032
  simp only [CollatzResearch.WordTrace]
  refine ⟨65013699610252698918484675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86684932813670265224646233 65013699610252698918484675)
  ·
    refine ⟨97520549415379048377727013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65013699610252698918484675 97520549415379048377727013)
    ·
      refine ⟨18285103015383571570823815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97520549415379048377727013 18285103015383571570823815)
      ·
        refine ⟨27427654523075357356235723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18285103015383571570823815 27427654523075357356235723)
        ·
          refine ⟨41141481784613036034353585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27427654523075357356235723 41141481784613036034353585)
          ·
            refine ⟨30856111338459777025765189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41141481784613036034353585 30856111338459777025765189)
            ·
              refine ⟨5785520875961208192330973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30856111338459777025765189 5785520875961208192330973)
              ·
                refine ⟨2169570328485453072124115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5785520875961208192330973 2169570328485453072124115)
                ·
                  refine ⟨3254355492728179608186173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169570328485453072124115 3254355492728179608186173)
                  ·
                    refine ⟨1220383309773067353069815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3254355492728179608186173 1220383309773067353069815)
                    ·
                      rfl

theorem cell22_3565032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_3565032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565032 prefixEnd_3565032 := by exact prefixLift 3565032
  have htrace : WordTrace (prefixWord ++ tailWord_3565032) baseStart_3565032 baseEnd_3565032 := by
    simpa [prefixWord, tailWord_3565032, baseEnd_3565032] using wordTrace_append hprefix tailTrace_3565032
  have hstable : (prefixWord ++ tailWord_3565032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565032).length < 2 ^ (prefixWord ++ tailWord_3565032).sum := by decide
  have hdescent : baseEnd_3565032 < baseStart_3565032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565045 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 7]
def baseStart_3565045 : Nat := 118140960795 + 3565045 * 2 ^ 59
def prefixEnd_3565045 : Nat := 4983230072969 + 3 ^ 40 * 3565045 * 2
def baseEnd_3565045 : Nat := 406795919979579884164925

theorem tailTrace_3565045 : CollatzResearch.WordTrace tailWord_3565045 prefixEnd_3565045 406795919979579884164925 := by
  unfold tailWord_3565045
  simp only [CollatzResearch.WordTrace]
  refine ⟨130027873369458301057192589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86685248912972200704795059 130027873369458301057192589)
  ·
    refine ⟨48760452513546862896447221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130027873369458301057192589 48760452513546862896447221)
    ·
      refine ⟨4571292423145018396541927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48760452513546862896447221 4571292423145018396541927)
      ·
        refine ⟨6856938634717527594812891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4571292423145018396541927 6856938634717527594812891)
        ·
          refine ⟨10285407952076291392219337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856938634717527594812891 10285407952076291392219337)
          ·
            refine ⟨7714055964057218544164503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10285407952076291392219337 7714055964057218544164503)
            ·
              refine ⟨11571083946085827816246755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7714055964057218544164503 11571083946085827816246755)
              ·
                refine ⟨17356625919128741724370133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11571083946085827816246755 17356625919128741724370133)
                ·
                  refine ⟨406795919979579884164925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17356625919128741724370133 406795919979579884164925)
                  ·
                    rfl

theorem cell22_3565045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_3565045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565045 prefixEnd_3565045 := by exact prefixLift 3565045
  have htrace : WordTrace (prefixWord ++ tailWord_3565045) baseStart_3565045 baseEnd_3565045 := by
    simpa [prefixWord, tailWord_3565045, baseEnd_3565045] using wordTrace_append hprefix tailTrace_3565045
  have hstable : (prefixWord ++ tailWord_3565045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565045).length < 2 ^ (prefixWord ++ tailWord_3565045).sum := by decide
  have hdescent : baseEnd_3565045 < baseStart_3565045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565075 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 1, 4]
def baseStart_3565075 : Nat := 118140960795 + 3565075 * 2 ^ 59
def prefixEnd_3565075 : Nat := 4983230072969 + 3 ^ 40 * 3565075 * 2
def baseEnd_3565075 : Nat := 1220398029551829574244683

theorem tailTrace_3565075 : CollatzResearch.WordTrace tailWord_3565075 prefixEnd_3565075 1220398029551829574244683 := by
  unfold tailWord_3565075
  simp only [CollatzResearch.WordTrace]
  refine ⟨130028967559349616180784679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86685978372899744120523119 130028967559349616180784679)
  ·
    refine ⟨195043451339024424271177019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130028967559349616180784679 195043451339024424271177019)
    ·
      refine ⟨292565177008536636406765529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195043451339024424271177019 292565177008536636406765529)
      ·
        refine ⟨219423882756402477305074147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292565177008536636406765529 219423882756402477305074147)
        ·
          refine ⟨329135824134603715957611221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219423882756402477305074147 329135824134603715957611221)
          ·
            refine ⟨7714120878154774592756513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 329135824134603715957611221 7714120878154774592756513)
            ·
              refine ⟨5785590658616080944567385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7714120878154774592756513 5785590658616080944567385)
              ·
                refine ⟨4339192993962060708425539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5785590658616080944567385 4339192993962060708425539)
                ·
                  refine ⟨6508789490943091062638309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4339192993962060708425539 6508789490943091062638309)
                  ·
                    refine ⟨1220398029551829574244683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6508789490943091062638309 1220398029551829574244683)
                    ·
                      rfl

theorem cell22_3565075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 4].length) (baseStart_3565075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565075 prefixEnd_3565075 := by exact prefixLift 3565075
  have htrace : WordTrace (prefixWord ++ tailWord_3565075) baseStart_3565075 baseEnd_3565075 := by
    simpa [prefixWord, tailWord_3565075, baseEnd_3565075] using wordTrace_append hprefix tailTrace_3565075
  have hstable : (prefixWord ++ tailWord_3565075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565075).length < 2 ^ (prefixWord ++ tailWord_3565075).sum := by decide
  have hdescent : baseEnd_3565075 < baseStart_3565075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565105 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 2, 3]
def baseStart_3565105 : Nat := 118140960795 + 3565105 * 2 ^ 59
def prefixEnd_3565105 : Nat := 4983230072969 + 3 ^ 40 * 3565105 * 2
def baseEnd_3565105 : Nat := 1220408299164919495994591

theorem tailTrace_3565105 : CollatzResearch.WordTrace tailWord_3565105 prefixEnd_3565105 1220408299164919495994591 := by
  unfold tailWord_3565105
  simp only [CollatzResearch.WordTrace]
  refine ⟨130030061749240931304376769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86686707832827287536251179 130030061749240931304376769)
  ·
    refine ⟨97522546311930698478282577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130030061749240931304376769 97522546311930698478282577)
    ·
      refine ⟨73141909733948023858711933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97522546311930698478282577 73141909733948023858711933)
      ·
        refine ⟨27428216150230508947016975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73141909733948023858711933 27428216150230508947016975)
        ·
          refine ⟨41142324225345763420525463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27428216150230508947016975 41142324225345763420525463)
          ·
            refine ⟨61713486338018645130788195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41142324225345763420525463 61713486338018645130788195)
            ·
              refine ⟨92570229507027967696182293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61713486338018645130788195 92570229507027967696182293)
              ·
                refine ⟨4339229508141935985758545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92570229507027967696182293 4339229508141935985758545)
                ·
                  refine ⟨3254422131106451989318909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4339229508141935985758545 3254422131106451989318909)
                  ·
                    refine ⟨1220408299164919495994591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3254422131106451989318909 1220408299164919495994591)
                    ·
                      rfl

theorem cell22_3565105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_3565105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565105 prefixEnd_3565105 := by exact prefixLift 3565105
  have htrace : WordTrace (prefixWord ++ tailWord_3565105) baseStart_3565105 baseEnd_3565105 := by
    simpa [prefixWord, tailWord_3565105, baseEnd_3565105] using wordTrace_append hprefix tailTrace_3565105
  have hstable : (prefixWord ++ tailWord_3565105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565105).length < 2 ^ (prefixWord ++ tailWord_3565105).sum := by decide
  have hdescent : baseEnd_3565105 < baseStart_3565105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565107 : List Nat := [1, 1, 1, 2, 4, 4, 3, 2, 4]
def baseStart_3565107 : Nat := 118140960795 + 3565107 * 2 ^ 59
def prefixEnd_3565107 : Nat := 4983230072969 + 3 ^ 40 * 3565107 * 2
def baseEnd_3565107 : Nat := 406802994601930719148195

theorem tailTrace_3565107 : CollatzResearch.WordTrace tailWord_3565107 prefixEnd_3565107 406802994601930719148195 := by
  unfold tailWord_3565107
  simp only [CollatzResearch.WordTrace]
  refine ⟨130030134695233685645949575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86686756463489123763966383 130030134695233685645949575)
  ·
    refine ⟨195045202042850528468924363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130030134695233685645949575 195045202042850528468924363)
    ·
      refine ⟨292567803064275792703386545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195045202042850528468924363 292567803064275792703386545)
      ·
        refine ⟨219425852298206844527539909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292567803064275792703386545 219425852298206844527539909)
        ·
          refine ⟨41142347305913783348913733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219425852298206844527539909 41142347305913783348913733)
          ·
            refine ⟨7714190119858834377921325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41142347305913783348913733 7714190119858834377921325)
            ·
              refine ⟨2892821294947062891720497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7714190119858834377921325 2892821294947062891720497)
              ·
                refine ⟨2169615971210297168790373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2892821294947062891720497 2169615971210297168790373)
                ·
                  refine ⟨406802994601930719148195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169615971210297168790373 406802994601930719148195)
                  ·
                    rfl

theorem cell22_3565107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 4].length) (baseStart_3565107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565107 prefixEnd_3565107 := by exact prefixLift 3565107
  have htrace : WordTrace (prefixWord ++ tailWord_3565107) baseStart_3565107 baseEnd_3565107 := by
    simpa [prefixWord, tailWord_3565107, baseEnd_3565107] using wordTrace_append hprefix tailTrace_3565107
  have hstable : (prefixWord ++ tailWord_3565107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565107).length < 2 ^ (prefixWord ++ tailWord_3565107).sum := by decide
  have hdescent : baseEnd_3565107 < baseStart_3565107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565126 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3565126 : Nat := 118140960795 + 3565126 * 2 ^ 59
def prefixEnd_3565126 : Nat := 4983230072969 + 3 ^ 40 * 3565126 * 2
def baseEnd_3565126 : Nat := 1220415487894082441219527

theorem tailTrace_3565126 : CollatzResearch.WordTrace tailWord_3565126 prefixEnd_3565126 1220415487894082441219527 := by
  unfold tailWord_3565126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4063463365067651621590351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86687218454776567927260821 4063463365067651621590351)
  ·
    refine ⟨6095195047601477432385527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4063463365067651621590351 6095195047601477432385527)
    ·
      refine ⟨9142792571402216148578291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6095195047601477432385527 9142792571402216148578291)
      ·
        refine ⟨13714188857103324222867437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9142792571402216148578291 13714188857103324222867437)
        ·
          refine ⟨5142820821413746583575289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13714188857103324222867437 5142820821413746583575289)
          ·
            refine ⟨3857115616060309937681467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5142820821413746583575289 3857115616060309937681467)
            ·
              refine ⟨5785673424090464906522201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3857115616060309937681467 5785673424090464906522201)
              ·
                refine ⟨4339255068067848679891651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5785673424090464906522201 4339255068067848679891651)
                ·
                  refine ⟨6508882602101773019837477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4339255068067848679891651 6508882602101773019837477)
                  ·
                    refine ⟨1220415487894082441219527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6508882602101773019837477 1220415487894082441219527)
                    ·
                      rfl

theorem cell22_3565126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3565126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565126 prefixEnd_3565126 := by exact prefixLift 3565126
  have htrace : WordTrace (prefixWord ++ tailWord_3565126) baseStart_3565126 baseEnd_3565126 := by
    simpa [prefixWord, tailWord_3565126, baseEnd_3565126] using wordTrace_append hprefix tailTrace_3565126
  have hstable : (prefixWord ++ tailWord_3565126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565126).length < 2 ^ (prefixWord ++ tailWord_3565126).sum := by decide
  have hdescent : baseEnd_3565126 < baseStart_3565126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565214 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_3565214 : Nat := 118140960795 + 3565214 * 2 ^ 59
def prefixEnd_3565214 : Nat := 4983230072969 + 3 ^ 40 * 3565214 * 2
def baseEnd_3565214 : Nat := 406815204030826515006419

theorem tailTrace_3565214 : CollatzResearch.WordTrace tailWord_3565214 prefixEnd_3565214 406815204030826515006419 := by
  unfold tailWord_3565214
  simp only [CollatzResearch.WordTrace]
  refine ⟨16254254663230755365011837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86689358203897361946729797 16254254663230755365011837)
  ·
    refine ⟨6095345498711533261879439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16254254663230755365011837 6095345498711533261879439)
    ·
      refine ⟨9143018248067299892819159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6095345498711533261879439 9143018248067299892819159)
      ·
        refine ⟨13714527372100949839228739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9143018248067299892819159 13714527372100949839228739)
        ·
          refine ⟨20571791058151424758843109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13714527372100949839228739 20571791058151424758843109)
          ·
            refine ⟨3857210823403392142283083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20571791058151424758843109 3857210823403392142283083)
            ·
              refine ⟨5785816235105088213424625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3857210823403392142283083 5785816235105088213424625)
              ·
                refine ⟨4339362176328816160068469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5785816235105088213424625 4339362176328816160068469)
                ·
                  refine ⟨406815204030826515006419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4339362176328816160068469 406815204030826515006419)
                  ·
                    rfl

theorem cell22_3565214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_3565214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565214 prefixEnd_3565214 := by exact prefixLift 3565214
  have htrace : WordTrace (prefixWord ++ tailWord_3565214) baseStart_3565214 baseEnd_3565214 := by
    simpa [prefixWord, tailWord_3565214, baseEnd_3565214] using wordTrace_append hprefix tailTrace_3565214
  have hstable : (prefixWord ++ tailWord_3565214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565214).length < 2 ^ (prefixWord ++ tailWord_3565214).sum := by decide
  have hdescent : baseEnd_3565214 < baseStart_3565214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565253 : List Nat := [1, 3, 1, 1, 1, 1, 2, 12]
def baseStart_3565253 : Nat := 118140960795 + 3565253 * 2 ^ 59
def prefixEnd_3565253 : Nat := 4983230072969 + 3 ^ 40 * 3565253 * 2
def baseEnd_3565253 : Nat := 135606551398832938143793

theorem tailTrace_3565253 : CollatzResearch.WordTrace tailWord_3565253 prefixEnd_3565253 135606551398832938143793 := by
  unfold tailWord_3565253
  simp only [CollatzResearch.WordTrace]
  refine ⟨130035459752704752580764413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86690306501803168387176275 130035459752704752580764413)
  ·
    refine ⟨48763297407264282217786655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130035459752704752580764413 48763297407264282217786655)
    ·
      refine ⟨73144946110896423326679983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48763297407264282217786655 73144946110896423326679983)
      ·
        refine ⟨109717419166344634990019975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73144946110896423326679983 109717419166344634990019975)
        ·
          refine ⟨164576128749516952485029963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109717419166344634990019975 164576128749516952485029963)
          ·
            refine ⟨246864193124275428727544945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164576128749516952485029963 246864193124275428727544945)
            ·
              refine ⟨185148144843206571545658709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246864193124275428727544945 185148144843206571545658709)
              ·
                refine ⟨135606551398832938143793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 185148144843206571545658709 135606551398832938143793)
                ·
                  rfl

theorem cell22_3565253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 12].length) (baseStart_3565253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565253 prefixEnd_3565253 := by exact prefixLift 3565253
  have htrace : WordTrace (prefixWord ++ tailWord_3565253) baseStart_3565253 baseEnd_3565253 := by
    simpa [prefixWord, tailWord_3565253, baseEnd_3565253] using wordTrace_append hprefix tailTrace_3565253
  have hstable : (prefixWord ++ tailWord_3565253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565253).length < 2 ^ (prefixWord ++ tailWord_3565253).sum := by decide
  have hdescent : baseEnd_3565253 < baseStart_3565253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565255 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3565255 : Nat := 118140960795 + 3565255 * 2 ^ 59
def prefixEnd_3565255 : Nat := 4983230072969 + 3 ^ 40 * 3565255 * 2
def baseEnd_3565255 : Nat := 1220459647230369104744131

theorem tailTrace_3565255 : CollatzResearch.WordTrace tailWord_3565255 prefixEnd_3565255 1220459647230369104744131 := by
  unfold tailWord_3565255
  simp only [CollatzResearch.WordTrace]
  refine ⟨130035532698697506922337219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86690355132465004614891479 130035532698697506922337219)
  ·
    refine ⟨195053299048046260383505829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130035532698697506922337219 195053299048046260383505829)
    ·
      refine ⟨36572493571508673821907343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195053299048046260383505829 36572493571508673821907343)
      ·
        refine ⟨54858740357263010732861015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36572493571508673821907343 54858740357263010732861015)
        ·
          refine ⟨82288110535894516099291523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54858740357263010732861015 82288110535894516099291523)
          ·
            refine ⟨123432165803841774148937285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82288110535894516099291523 123432165803841774148937285)
            ·
              refine ⟨23143531088220332652925741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123432165803841774148937285 23143531088220332652925741)
              ·
                refine ⟨8678824158082624744847153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23143531088220332652925741 8678824158082624744847153)
                ·
                  refine ⟨6509118118561968558635365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8678824158082624744847153 6509118118561968558635365)
                  ·
                    refine ⟨1220459647230369104744131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6509118118561968558635365 1220459647230369104744131)
                    ·
                      rfl

theorem cell22_3565255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3565255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565255 prefixEnd_3565255 := by exact prefixLift 3565255
  have htrace : WordTrace (prefixWord ++ tailWord_3565255) baseStart_3565255 baseEnd_3565255 := by
    simpa [prefixWord, tailWord_3565255, baseEnd_3565255] using wordTrace_append hprefix tailTrace_3565255
  have hstable : (prefixWord ++ tailWord_3565255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565255).length < 2 ^ (prefixWord ++ tailWord_3565255).sum := by decide
  have hdescent : baseEnd_3565255 < baseStart_3565255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565276 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 6]
def baseStart_3565276 : Nat := 118140960795 + 3565276 * 2 ^ 59
def prefixEnd_3565276 : Nat := 4983230072969 + 3 ^ 40 * 3565276 * 2
def baseEnd_3565276 : Nat := 406822278653177349989689

theorem tailTrace_3565276 : CollatzResearch.WordTrace tailWord_3565276 prefixEnd_3565276 406822278653177349989689 := by
  unfold tailWord_3565276
  simp only [CollatzResearch.WordTrace]
  refine ⟨65018149315810713754425841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86690865754414285005901121 65018149315810713754425841)
  ·
    refine ⟨48763611986858035315819381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65018149315810713754425841 48763611986858035315819381)
    ·
      refine ⟨4571588623767940810858067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48763611986858035315819381 4571588623767940810858067)
      ·
        refine ⟨6857382935651911216287101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4571588623767940810858067 6857382935651911216287101)
        ·
          refine ⟨2571518600869466706107663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6857382935651911216287101 2571518600869466706107663)
          ·
            refine ⟨3857277901304200059161495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571518600869466706107663 3857277901304200059161495)
            ·
              refine ⟨5785916851956300088742243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3857277901304200059161495 5785916851956300088742243)
              ·
                refine ⟨8678875277934450133113365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5785916851956300088742243 8678875277934450133113365)
                ·
                  refine ⟨406822278653177349989689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8678875277934450133113365 406822278653177349989689)
                  ·
                    rfl

theorem cell22_3565276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_3565276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565276 prefixEnd_3565276 := by exact prefixLift 3565276
  have htrace : WordTrace (prefixWord ++ tailWord_3565276) baseStart_3565276 baseEnd_3565276 := by
    simpa [prefixWord, tailWord_3565276, baseEnd_3565276] using wordTrace_append hprefix tailTrace_3565276
  have hstable : (prefixWord ++ tailWord_3565276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565276).length < 2 ^ (prefixWord ++ tailWord_3565276).sum := by decide
  have hdescent : baseEnd_3565276 < baseStart_3565276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565336 : List Nat := [2, 1, 2, 3, 1, 1, 6, 2, 1, 3]
def baseStart_3565336 : Nat := 118140960795 + 3565336 * 2 ^ 59
def prefixEnd_3565336 : Nat := 4983230072969 + 3 ^ 40 * 3565336 * 2
def baseEnd_3565336 : Nat := 1220487375185711893468883

theorem tailTrace_3565336 : CollatzResearch.WordTrace tailWord_3565336 prefixEnd_3565336 1220487375185711893468883 := by
  unfold tailWord_3565336
  simp only [CollatzResearch.WordTrace]
  refine ⟨65019243505702028878017931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86692324674269371837357241 65019243505702028878017931)
  ·
    refine ⟨97528865258553043317026897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65019243505702028878017931 97528865258553043317026897)
    ·
      refine ⟨73146648943914782487770173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97528865258553043317026897 73146648943914782487770173)
      ·
        refine ⟨27429993353968043432913815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73146648943914782487770173 27429993353968043432913815)
        ·
          refine ⟨41144990030952065149370723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27429993353968043432913815 41144990030952065149370723)
          ·
            refine ⟨61717485046428097724056085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41144990030952065149370723 61717485046428097724056085)
            ·
              refine ⟨2893007111551317080815129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61717485046428097724056085 2893007111551317080815129)
              ·
                refine ⟨2169755333663487810611347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2893007111551317080815129 2169755333663487810611347)
                ·
                  refine ⟨3254633000495231715917021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169755333663487810611347 3254633000495231715917021)
                  ·
                    refine ⟨1220487375185711893468883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3254633000495231715917021 1220487375185711893468883)
                    ·
                      rfl

theorem cell22_3565336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_3565336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565336 prefixEnd_3565336 := by exact prefixLift 3565336
  have htrace : WordTrace (prefixWord ++ tailWord_3565336) baseStart_3565336 baseEnd_3565336 := by
    simpa [prefixWord, tailWord_3565336, baseEnd_3565336] using wordTrace_append hprefix tailTrace_3565336
  have hstable : (prefixWord ++ tailWord_3565336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565336).length < 2 ^ (prefixWord ++ tailWord_3565336).sum := by decide
  have hdescent : baseEnd_3565336 < baseStart_3565336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565362 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_3565362 : Nat := 118140960795 + 3565362 * 2 ^ 59
def prefixEnd_3565362 : Nat := 4983230072969 + 3 ^ 40 * 3565362 * 2
def baseEnd_3565362 : Nat := 1220496275517056492318803

theorem tailTrace_3565362 : CollatzResearch.WordTrace tailWord_3565362 prefixEnd_3565362 1220496275517056492318803 := by
  unfold tailWord_3565362
  simp only [CollatzResearch.WordTrace]
  refine ⟨32509858827327466049120585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86692956872873242797654893 32509858827327466049120585)
  ·
    refine ⟨24382394120495599536840439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32509858827327466049120585 24382394120495599536840439)
    ·
      refine ⟨36573591180743399305260659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24382394120495599536840439 36573591180743399305260659)
      ·
        refine ⟨54860386771115098957890989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36573591180743399305260659 54860386771115098957890989)
        ·
          refine ⟨20572645039168162109209121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54860386771115098957890989 20572645039168162109209121)
          ·
            refine ⟨15429483779376121581906841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20572645039168162109209121 15429483779376121581906841)
            ·
              refine ⟨11572112834532091186430131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15429483779376121581906841 11572112834532091186430131)
              ·
                refine ⟨17358169251798136779645197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11572112834532091186430131 17358169251798136779645197)
                ·
                  refine ⟨6509313469424301292366949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17358169251798136779645197 6509313469424301292366949)
                  ·
                    refine ⟨1220496275517056492318803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6509313469424301292366949 1220496275517056492318803)
                    ·
                      rfl

theorem cell22_3565362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_3565362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565362 prefixEnd_3565362 := by exact prefixLift 3565362
  have htrace : WordTrace (prefixWord ++ tailWord_3565362) baseStart_3565362 baseEnd_3565362 := by
    simpa [prefixWord, tailWord_3565362, baseEnd_3565362] using wordTrace_append hprefix tailTrace_3565362
  have hstable : (prefixWord ++ tailWord_3565362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565362).length < 2 ^ (prefixWord ++ tailWord_3565362).sum := by decide
  have hdescent : baseEnd_3565362 < baseStart_3565362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565379 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 1, 4]
def baseStart_3565379 : Nat := 118140960795 + 3565379 * 2 ^ 59
def prefixEnd_3565379 : Nat := 4983230072969 + 3 ^ 40 * 3565379 * 2
def baseEnd_3565379 : Nat := 1220502094964474114643751

theorem tailTrace_3565379 : CollatzResearch.WordTrace tailWord_3565379 prefixEnd_3565379 1220502094964474114643751 := by
  unfold tailWord_3565379
  simp only [CollatzResearch.WordTrace]
  refine ⟨130040055350248276099851191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86693370233498850733234127 130040055350248276099851191)
  ·
    refine ⟨195060083025372414149776787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130040055350248276099851191 195060083025372414149776787)
    ·
      refine ⟨292590124538058621224665181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195060083025372414149776787 292590124538058621224665181)
      ·
        refine ⟨109721296701771982959249443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292590124538058621224665181 109721296701771982959249443)
        ·
          refine ⟨164581945052657974438874165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109721296701771982959249443 164581945052657974438874165)
          ·
            refine ⟨15429557348686685103644453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164581945052657974438874165 15429557348686685103644453)
            ·
              refine ⟨2893042002878753456933335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15429557348686685103644453 2893042002878753456933335)
              ·
                refine ⟨4339563004318130185400003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893042002878753456933335 4339563004318130185400003)
                ·
                  refine ⟨6509344506477195278100005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4339563004318130185400003 6509344506477195278100005)
                  ·
                    refine ⟨1220502094964474114643751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6509344506477195278100005 1220502094964474114643751)
                    ·
                      rfl

theorem cell22_3565379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 4].length) (baseStart_3565379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565379 prefixEnd_3565379 := by exact prefixLift 3565379
  have htrace : WordTrace (prefixWord ++ tailWord_3565379) baseStart_3565379 baseEnd_3565379 := by
    simpa [prefixWord, tailWord_3565379, baseEnd_3565379] using wordTrace_append hprefix tailTrace_3565379
  have hstable : (prefixWord ++ tailWord_3565379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565379).length < 2 ^ (prefixWord ++ tailWord_3565379).sum := by decide
  have hdescent : baseEnd_3565379 < baseStart_3565379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565394 : List Nat := [3, 2, 2, 1, 1, 3, 2, 4, 4]
def baseStart_3565394 : Nat := 118140960795 + 3565394 * 2 ^ 59
def prefixEnd_3565394 : Nat := 4983230072969 + 3 ^ 40 * 3565394 * 2
def baseEnd_3565394 : Nat := 406835743257006358506235

theorem tailTrace_3565394 : CollatzResearch.WordTrace tailWord_3565394 prefixEnd_3565394 406835743257006358506235 := by
  unfold tailWord_3565394
  simp only [CollatzResearch.WordTrace]
  refine ⟨32510150611298483415411809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86693734963462622441098157 32510150611298483415411809)
  ·
    refine ⟨24382612958473862561558857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32510150611298483415411809 24382612958473862561558857)
    ·
      refine ⟨18286959718855396921169143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24382612958473862561558857 18286959718855396921169143)
      ·
        refine ⟨27430439578283095381753715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18286959718855396921169143 27430439578283095381753715)
        ·
          refine ⟨41145659367424643072630573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27430439578283095381753715 41145659367424643072630573)
          ·
            refine ⟨15429622262784241152236465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41145659367424643072630573 15429622262784241152236465)
            ·
              refine ⟨11572216697088180864177349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15429622262784241152236465 11572216697088180864177349)
              ·
                refine ⟨2169790630704033912033253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11572216697088180864177349 2169790630704033912033253)
                ·
                  refine ⟨406835743257006358506235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169790630704033912033253 406835743257006358506235)
                  ·
                    rfl

theorem cell22_3565394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_3565394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565394 prefixEnd_3565394 := by exact prefixLift 3565394
  have htrace : WordTrace (prefixWord ++ tailWord_3565394) baseStart_3565394 baseEnd_3565394 := by
    simpa [prefixWord, tailWord_3565394, baseEnd_3565394] using wordTrace_append hprefix tailTrace_3565394
  have hstable : (prefixWord ++ tailWord_3565394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565394).length < 2 ^ (prefixWord ++ tailWord_3565394).sum := by decide
  have hdescent : baseEnd_3565394 < baseStart_3565394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565435 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 1, 8]
def baseStart_3565435 : Nat := 118140960795 + 3565435 * 2 ^ 59
def prefixEnd_3565435 : Nat := 4983230072969 + 3 ^ 40 * 3565435 * 2
def baseEnd_3565435 : Nat := 1220521264908908635243579

theorem tailTrace_3565435 : CollatzResearch.WordTrace tailWord_3565435 prefixEnd_3565435 1220521264908908635243579 := by
  unfold tailWord_3565435
  simp only [CollatzResearch.WordTrace]
  refine ⟨130042097838045397663889759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86694731892030265109259839 130042097838045397663889759)
  ·
    refine ⟨195063146757068096495834639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130042097838045397663889759 195063146757068096495834639)
    ·
      refine ⟨292594720135602144743751959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195063146757068096495834639 292594720135602144743751959)
      ·
        refine ⟨438892080203403217115627939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292594720135602144743751959 438892080203403217115627939)
        ·
          refine ⟨658338120305104825673441909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438892080203403217115627939 658338120305104825673441909)
          ·
            refine ⟨61719198778603577406885179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 658338120305104825673441909 61719198778603577406885179)
            ·
              refine ⟨92578798167905366110327769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61719198778603577406885179 92578798167905366110327769)
              ·
                refine ⟨69434098625929024582745827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92578798167905366110327769 69434098625929024582745827)
                ·
                  refine ⟨104151147938893536874118741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69434098625929024582745827 104151147938893536874118741)
                  ·
                    refine ⟨1220521264908908635243579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104151147938893536874118741 1220521264908908635243579)
                    ·
                      rfl

theorem cell22_3565435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_3565435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565435 prefixEnd_3565435 := by exact prefixLift 3565435
  have htrace : WordTrace (prefixWord ++ tailWord_3565435) baseStart_3565435 baseEnd_3565435 := by
    simpa [prefixWord, tailWord_3565435, baseEnd_3565435] using wordTrace_append hprefix tailTrace_3565435
  have hstable : (prefixWord ++ tailWord_3565435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565435).length < 2 ^ (prefixWord ++ tailWord_3565435).sum := by decide
  have hdescent : baseEnd_3565435 < baseStart_3565435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565441 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 2, 4]
def baseStart_3565441 : Nat := 118140960795 + 3565441 * 2 ^ 59
def prefixEnd_3565441 : Nat := 4983230072969 + 3 ^ 40 * 3565441 * 2
def baseEnd_3565441 : Nat := 1220523318831526619593561

theorem tailTrace_3565441 : CollatzResearch.WordTrace tailWord_3565441 prefixEnd_3565441 1220523318831526619593561 := by
  unfold tailWord_3565441
  simp only [CollatzResearch.WordTrace]
  refine ⟨130042316676023660688608177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86694877784015773792405451 130042316676023660688608177)
  ·
    refine ⟨97531737507017745516456133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130042316676023660688608177 97531737507017745516456133)
    ·
      refine ⟨18287200782565827284335525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97531737507017745516456133 18287200782565827284335525)
      ·
        refine ⟨3428850146731092615812911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18287200782565827284335525 3428850146731092615812911)
        ·
          refine ⟨5143275220096638923719367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3428850146731092615812911 5143275220096638923719367)
          ·
            refine ⟨7714912830144958385579051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143275220096638923719367 7714912830144958385579051)
            ·
              refine ⟨11572369245217437578368577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7714912830144958385579051 11572369245217437578368577)
              ·
                refine ⟨8679276933913078183776433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11572369245217437578368577 8679276933913078183776433)
                ·
                  refine ⟨6509457700434808637832325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8679276933913078183776433 6509457700434808637832325)
                  ·
                    refine ⟨1220523318831526619593561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6509457700434808637832325 1220523318831526619593561)
                    ·
                      rfl

theorem cell22_3565441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_3565441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565441 prefixEnd_3565441 := by exact prefixLift 3565441
  have htrace : WordTrace (prefixWord ++ tailWord_3565441) baseStart_3565441 baseEnd_3565441 := by
    simpa [prefixWord, tailWord_3565441, baseEnd_3565441] using wordTrace_append hprefix tailTrace_3565441
  have hstable : (prefixWord ++ tailWord_3565441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565441).length < 2 ^ (prefixWord ++ tailWord_3565441).sum := by decide
  have hdescent : baseEnd_3565441 < baseStart_3565441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565529 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 6]
def baseStart_3565529 : Nat := 118140960795 + 3565529 * 2 ^ 59
def prefixEnd_3565529 : Nat := 4983230072969 + 3 ^ 40 * 3565529 * 2
def baseEnd_3565529 : Nat := 406851147676641241131097

theorem tailTrace_3565529 : CollatzResearch.WordTrace tailWord_3565529 prefixEnd_3565529 406851147676641241131097 := by
  unfold tailWord_3565529
  simp only [CollatzResearch.WordTrace]
  refine ⟨130045526299704851717811641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86697017533136567811874427 130045526299704851717811641)
  ·
    refine ⟨97534144724778638788358731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130045526299704851717811641 97534144724778638788358731)
    ·
      refine ⟨146301217087167958182538097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97534144724778638788358731 146301217087167958182538097)
      ·
        refine ⟨109725912815375968636903573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146301217087167958182538097 109725912815375968636903573)
        ·
          refine ⟨5143402163220748529854855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109725912815375968636903573 5143402163220748529854855)
          ·
            refine ⟨7715103244831122794782283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143402163220748529854855 7715103244831122794782283)
            ·
              refine ⟨11572654867246684192173425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7715103244831122794782283 11572654867246684192173425)
              ·
                refine ⟨8679491150435013144130069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11572654867246684192173425 8679491150435013144130069)
                ·
                  refine ⟨406851147676641241131097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8679491150435013144130069 406851147676641241131097)
                  ·
                    rfl

theorem cell22_3565529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_3565529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565529 prefixEnd_3565529 := by exact prefixLift 3565529
  have htrace : WordTrace (prefixWord ++ tailWord_3565529) baseStart_3565529 baseEnd_3565529 := by
    simpa [prefixWord, tailWord_3565529, baseEnd_3565529] using wordTrace_append hprefix tailTrace_3565529
  have hstable : (prefixWord ++ tailWord_3565529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565529).length < 2 ^ (prefixWord ++ tailWord_3565529).sum := by decide
  have hdescent : baseEnd_3565529 < baseStart_3565529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565544 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 4, 3]
def baseStart_3565544 : Nat := 118140960795 + 3565544 * 2 ^ 59
def prefixEnd_3565544 : Nat := 4983230072969 + 3 ^ 40 * 3565544 * 2
def baseEnd_3565544 : Nat := 1220558577836468684268245

theorem tailTrace_3565544 : CollatzResearch.WordTrace tailWord_3565544 prefixEnd_3565544 1220558577836468684268245 := by
  unfold tailWord_3565544
  simp only [CollatzResearch.WordTrace]
  refine ⟨65023036697325254639803843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86697382263100339519738457 65023036697325254639803843)
  ·
    refine ⟨97534555045987881959705765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65023036697325254639803843 97534555045987881959705765)
    ·
      refine ⟨18287729071122727867444831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97534555045987881959705765 18287729071122727867444831)
      ·
        refine ⟨27431593606684091801167247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18287729071122727867444831 27431593606684091801167247)
        ·
          refine ⟨41147390410026137701750871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27431593606684091801167247 41147390410026137701750871)
          ·
            refine ⟨61721085615039206552626307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41147390410026137701750871 61721085615039206552626307)
            ·
              refine ⟨92581628422558809828939461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61721085615039206552626307 92581628422558809828939461)
              ·
                refine ⟨17359055329229776842926149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92581628422558809828939461 17359055329229776842926149)
                ·
                  refine ⟨3254822874230583158048653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17359055329229776842926149 3254822874230583158048653)
                  ·
                    refine ⟨1220558577836468684268245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3254822874230583158048653 1220558577836468684268245)
                    ·
                      rfl

theorem cell22_3565544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_3565544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565544 prefixEnd_3565544 := by exact prefixLift 3565544
  have htrace : WordTrace (prefixWord ++ tailWord_3565544) baseStart_3565544 baseEnd_3565544 := by
    simpa [prefixWord, tailWord_3565544, baseEnd_3565544] using wordTrace_append hprefix tailTrace_3565544
  have hstable : (prefixWord ++ tailWord_3565544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565544).length < 2 ^ (prefixWord ++ tailWord_3565544).sum := by decide
  have hdescent : baseEnd_3565544 < baseStart_3565544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565546 : List Nat := [3, 1, 3, 1, 2, 1, 4, 3, 4]
def baseStart_3565546 : Nat := 118140960795 + 3565546 * 2 ^ 59
def prefixEnd_3565546 : Nat := 4983230072969 + 3 ^ 40 * 3565546 * 2
def baseEnd_3565546 : Nat := 406853087492447115239413

theorem tailTrace_3565546 : CollatzResearch.WordTrace tailWord_3565546 prefixEnd_3565546 406853087492447115239413 := by
  unfold tailWord_3565546
  simp only [CollatzResearch.WordTrace]
  refine ⟨32511536585160815905295123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86697430893762175747453661 32511536585160815905295123)
  ·
    refine ⟨48767304877741223857942685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32511536585160815905295123 48767304877741223857942685)
    ·
      refine ⟨18287739329152958946728507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48767304877741223857942685 18287739329152958946728507)
      ·
        refine ⟨27431608993729438420092761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18287739329152958946728507 27431608993729438420092761)
        ·
          refine ⟨20573706745297078815069571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27431608993729438420092761 20573706745297078815069571)
          ·
            refine ⟨30860560117945618222604357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20573706745297078815069571 30860560117945618222604357)
            ·
              refine ⟨5786355022114803416738317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30860560117945618222604357 5786355022114803416738317)
              ·
                refine ⟨2169883133293051281276869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5786355022114803416738317 2169883133293051281276869)
                ·
                  refine ⟨406853087492447115239413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169883133293051281276869 406853087492447115239413)
                  ·
                    rfl

theorem cell22_3565546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_3565546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565546 prefixEnd_3565546 := by exact prefixLift 3565546
  have htrace : WordTrace (prefixWord ++ tailWord_3565546) baseStart_3565546 baseEnd_3565546 := by
    simpa [prefixWord, tailWord_3565546, baseEnd_3565546] using wordTrace_append hprefix tailTrace_3565546
  have hstable : (prefixWord ++ tailWord_3565546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565546).length < 2 ^ (prefixWord ++ tailWord_3565546).sum := by decide
  have hdescent : baseEnd_3565546 < baseStart_3565546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565561 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 2, 3]
def baseStart_3565561 : Nat := 118140960795 + 3565561 * 2 ^ 59
def prefixEnd_3565561 : Nat := 4983230072969 + 3 ^ 40 * 3565561 * 2
def baseEnd_3565561 : Nat := 1220564397283886306593193

theorem tailTrace_3565561 : CollatzResearch.WordTrace tailWord_3565561 prefixEnd_3565561 1220564397283886306593193 := by
  unfold tailWord_3565561
  simp only [CollatzResearch.WordTrace]
  refine ⟨130046693435588921182976537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86697795623725947455317691 130046693435588921182976537)
  ·
    refine ⟨97535020076691690887232403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130046693435588921182976537 97535020076691690887232403)
    ·
      refine ⟨146302530115037536330848605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97535020076691690887232403 146302530115037536330848605)
      ·
        refine ⟨54863448793139076124068227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146302530115037536330848605 54863448793139076124068227)
        ·
          refine ⟨82295173189708614186102341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54863448793139076124068227 82295173189708614186102341)
          ·
            refine ⟨15430344973070365159894189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82295173189708614186102341 15430344973070365159894189)
            ·
              refine ⟨5786379364901386934960321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15430344973070365159894189 5786379364901386934960321)
              ·
                refine ⟨4339784523676040201220241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5786379364901386934960321 4339784523676040201220241)
                ·
                  refine ⟨3254838392757030150915181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4339784523676040201220241 3254838392757030150915181)
                  ·
                    refine ⟨1220564397283886306593193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3254838392757030150915181 1220564397283886306593193)
                    ·
                      rfl

theorem cell22_3565561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 3].length) (baseStart_3565561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565561 prefixEnd_3565561 := by exact prefixLift 3565561
  have htrace : WordTrace (prefixWord ++ tailWord_3565561) baseStart_3565561 baseEnd_3565561 := by
    simpa [prefixWord, tailWord_3565561, baseEnd_3565561] using wordTrace_append hprefix tailTrace_3565561
  have hstable : (prefixWord ++ tailWord_3565561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565561).length < 2 ^ (prefixWord ++ tailWord_3565561).sum := by decide
  have hdescent : baseEnd_3565561 < baseStart_3565561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565578 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 1, 5]
def baseStart_3565578 : Nat := 118140960795 + 3565578 * 2 ^ 59
def prefixEnd_3565578 : Nat := 4983230072969 + 3 ^ 40 * 3565578 * 2
def baseEnd_3565578 : Nat := 1220570216731303928918141

theorem tailTrace_3565578 : CollatzResearch.WordTrace tailWord_3565578 prefixEnd_3565578 1220570216731303928918141 := by
  unfold tailWord_3565578
  simp only [CollatzResearch.WordTrace]
  refine ⟨32511828369131833271586347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86698208984351555390896925 32511828369131833271586347)
  ·
    refine ⟨48767742553697749907379521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32511828369131833271586347 48767742553697749907379521)
    ·
      refine ⟨36575806915273312430534641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48767742553697749907379521 36575806915273312430534641)
      ·
        refine ⟨27431855186454984322900981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36575806915273312430534641 27431855186454984322900981)
        ·
          refine ⟨2571736423730154780271967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27431855186454984322900981 2571736423730154780271967)
          ·
            refine ⟨3857604635595232170407951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571736423730154780271967 3857604635595232170407951)
            ·
              refine ⟨5786406953392848255611927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3857604635595232170407951 5786406953392848255611927)
              ·
                refine ⟨8679610430089272383417891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5786406953392848255611927 8679610430089272383417891)
                ·
                  refine ⟨13019415645133908575126837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8679610430089272383417891 13019415645133908575126837)
                  ·
                    refine ⟨1220570216731303928918141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13019415645133908575126837 1220570216731303928918141)
                    ·
                      rfl

theorem cell22_3565578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_3565578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565578 prefixEnd_3565578 := by exact prefixLift 3565578
  have htrace : WordTrace (prefixWord ++ tailWord_3565578) baseStart_3565578 baseEnd_3565578 := by
    simpa [prefixWord, tailWord_3565578, baseEnd_3565578] using wordTrace_append hprefix tailTrace_3565578
  have hstable : (prefixWord ++ tailWord_3565578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565578).length < 2 ^ (prefixWord ++ tailWord_3565578).sum := by decide
  have hdescent : baseEnd_3565578 < baseStart_3565578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565587 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 2, 6]
def baseStart_3565587 : Nat := 118140960795 + 3565587 * 2 ^ 59
def prefixEnd_3565587 : Nat := 4983230072969 + 3 ^ 40 * 3565587 * 2
def baseEnd_3565587 : Nat := 1220573297615230905443113

theorem tailTrace_3565587 : CollatzResearch.WordTrace tailWord_3565587 prefixEnd_3565587 1220573297615230905443113 := by
  unfold tailWord_3565587
  simp only [CollatzResearch.WordTrace]
  refine ⟨130047641733494727623423015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86698427822329818415615343 130047641733494727623423015)
  ·
    refine ⟨195071462600242091435134523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130047641733494727623423015 195071462600242091435134523)
    ·
      refine ⟨292607193900363137152701785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195071462600242091435134523 292607193900363137152701785)
      ·
        refine ⟨219455395425272352864526339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292607193900363137152701785 219455395425272352864526339)
        ·
          refine ⟨329183093137908529296789509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219455395425272352864526339 329183093137908529296789509)
          ·
            refine ⟨61721829963357849243148033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329183093137908529296789509 61721829963357849243148033)
            ·
              refine ⟨46291372472518386932361025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61721829963357849243148033 46291372472518386932361025)
              ·
                refine ⟨34718529354388790199270769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46291372472518386932361025 34718529354388790199270769)
                ·
                  refine ⟨26038897015791592649453077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34718529354388790199270769 26038897015791592649453077)
                  ·
                    refine ⟨1220573297615230905443113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26038897015791592649453077 1220573297615230905443113)
                    ·
                      rfl

theorem cell22_3565587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_3565587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565587 prefixEnd_3565587 := by exact prefixLift 3565587
  have htrace : WordTrace (prefixWord ++ tailWord_3565587) baseStart_3565587 baseEnd_3565587 := by
    simpa [prefixWord, tailWord_3565587, baseEnd_3565587] using wordTrace_append hprefix tailTrace_3565587
  have hstable : (prefixWord ++ tailWord_3565587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565587).length < 2 ^ (prefixWord ++ tailWord_3565587).sum := by decide
  have hdescent : baseEnd_3565587 < baseStart_3565587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565608 : List Nat := [2, 1, 5, 3, 2, 1, 8]
def baseStart_3565608 : Nat := 118140960795 + 3565608 * 2 ^ 59
def prefixEnd_3565608 : Nat := 4983230072969 + 3 ^ 40 * 3565608 * 2
def baseEnd_3565608 : Nat := 45206684679421994469187

theorem tailTrace_3565608 : CollatzResearch.WordTrace tailWord_3565608 prefixEnd_3565608 45206684679421994469187 := by
  unfold tailWord_3565608
  simp only [CollatzResearch.WordTrace]
  refine ⟨65024203833209324104968739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86698938444279098806624985 65024203833209324104968739)
  ·
    refine ⟨97536305749813986157453109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65024203833209324104968739 97536305749813986157453109)
    ·
      refine ⟨9144028664045061202261229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97536305749813986157453109 9144028664045061202261229)
      ·
        refine ⟨3429010749016897950847961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9144028664045061202261229 3429010749016897950847961)
        ·
          refine ⟨2571758061762673463135971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3429010749016897950847961 2571758061762673463135971)
          ·
            refine ⟨3857637092644010194703957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571758061762673463135971 3857637092644010194703957)
            ·
              refine ⟨45206684679421994469187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3857637092644010194703957 45206684679421994469187)
              ·
                rfl

theorem cell22_3565608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 8].length) (baseStart_3565608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565608 prefixEnd_3565608 := by exact prefixLift 3565608
  have htrace : WordTrace (prefixWord ++ tailWord_3565608) baseStart_3565608 baseEnd_3565608 := by
    simpa [prefixWord, tailWord_3565608, baseEnd_3565608] using wordTrace_append hprefix tailTrace_3565608
  have hstable : (prefixWord ++ tailWord_3565608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565608).length < 2 ^ (prefixWord ++ tailWord_3565608).sum := by decide
  have hdescent : baseEnd_3565608 < baseStart_3565608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565674 : List Nat := [3, 1, 3, 2, 4, 1, 2, 2, 1, 3]
def baseStart_3565674 : Nat := 118140960795 + 3565674 * 2 ^ 59
def prefixEnd_3565674 : Nat := 4983230072969 + 3 ^ 40 * 3565674 * 2
def baseEnd_3565674 : Nat := 1220603079493191678517847

theorem tailTrace_3565674 : CollatzResearch.WordTrace tailWord_3565674 prefixEnd_3565674 1220603079493191678517847 := by
  unfold tailWord_3565674
  simp only [CollatzResearch.WordTrace]
  refine ⟨32512703721044885370460019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86700543256119694321226717 32512703721044885370460019)
  ·
    refine ⟨48769055581567328055690029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32512703721044885370460019 48769055581567328055690029)
    ·
      refine ⟨18288395843087748020883761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48769055581567328055690029 18288395843087748020883761)
      ·
        refine ⟨13716296882315811015662821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18288395843087748020883761 13716296882315811015662821)
        ·
          refine ⟨2571805665434214565436779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13716296882315811015662821 2571805665434214565436779)
          ·
            refine ⟨3857708498151321848155169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571805665434214565436779 3857708498151321848155169)
            ·
              refine ⟨2893281373613491386116377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3857708498151321848155169 2893281373613491386116377)
              ·
                refine ⟨2169961030210118539587283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2893281373613491386116377 2169961030210118539587283)
                ·
                  refine ⟨3254941545315177809380925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169961030210118539587283 3254941545315177809380925)
                  ·
                    refine ⟨1220603079493191678517847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3254941545315177809380925 1220603079493191678517847)
                    ·
                      rfl

theorem cell22_3565674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_3565674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565674 prefixEnd_3565674 := by exact prefixLift 3565674
  have htrace : WordTrace (prefixWord ++ tailWord_3565674) baseStart_3565674 baseEnd_3565674 := by
    simpa [prefixWord, tailWord_3565674, baseEnd_3565674] using wordTrace_append hprefix tailTrace_3565674
  have hstable : (prefixWord ++ tailWord_3565674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565674).length < 2 ^ (prefixWord ++ tailWord_3565674).sum := by decide
  have hdescent : baseEnd_3565674 < baseStart_3565674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565681 : List Nat := [1, 2, 2, 2, 1, 1, 5, 4, 4]
def baseStart_3565681 : Nat := 118140960795 + 3565681 * 2 ^ 59
def prefixEnd_3565681 : Nat := 4983230072969 + 3 ^ 40 * 3565681 * 2
def baseEnd_3565681 : Nat := 406868491912081997864275

theorem tailTrace_3565681 : CollatzResearch.WordTrace tailWord_3565681 prefixEnd_3565681 406868491912081997864275 := by
  unfold tailWord_3565681
  simp only [CollatzResearch.WordTrace]
  refine ⟨130051070195154181677344897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86700713463436121118229931 130051070195154181677344897)
  ·
    refine ⟨97538302646365636258008673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130051070195154181677344897 97538302646365636258008673)
    ·
      refine ⟨73153726984774227193506505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97538302646365636258008673 73153726984774227193506505)
      ·
        refine ⟨54865295238580670395129879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73153726984774227193506505 54865295238580670395129879)
        ·
          refine ⟨82297942857871005592694819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54865295238580670395129879 82297942857871005592694819)
          ·
            refine ⟨123446914286806508389042229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82297942857871005592694819 123446914286806508389042229)
            ·
              refine ⟨11573148214388110161472709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123446914286806508389042229 11573148214388110161472709)
              ·
                refine ⟨2169965290197770655276133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11573148214388110161472709 2169965290197770655276133)
                ·
                  refine ⟨406868491912081997864275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2169965290197770655276133 406868491912081997864275)
                  ·
                    rfl

theorem cell22_3565681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 4].length) (baseStart_3565681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565681 prefixEnd_3565681 := by exact prefixLift 3565681
  have htrace : WordTrace (prefixWord ++ tailWord_3565681) baseStart_3565681 baseEnd_3565681 := by
    simpa [prefixWord, tailWord_3565681, baseEnd_3565681] using wordTrace_append hprefix tailTrace_3565681
  have hstable : (prefixWord ++ tailWord_3565681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565681).length < 2 ^ (prefixWord ++ tailWord_3565681).sum := by decide
  have hdescent : baseEnd_3565681 < baseStart_3565681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565730 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3565730 : Nat := 118140960795 + 3565730 * 2 ^ 59
def prefixEnd_3565730 : Nat := 4983230072969 + 3 ^ 40 * 3565730 * 2
def baseEnd_3565730 : Nat := 1220622249437626199117675

theorem tailTrace_3565730 : CollatzResearch.WordTrace tailWord_3565730 prefixEnd_3565730 1220622249437626199117675 := by
  unfold tailWord_3565730
  simp only [CollatzResearch.WordTrace]
  refine ⟨32513214342994165761469661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86701904914651108697252429 32513214342994165761469661)
  ·
    refine ⟨12192455378622812160551123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32513214342994165761469661 12192455378622812160551123)
    ·
      refine ⟨18288683067934218240826685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12192455378622812160551123 18288683067934218240826685)
      ·
        refine ⟨6858256150475331840310007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18288683067934218240826685 6858256150475331840310007)
        ·
          refine ⟨10287384225712997760465011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6858256150475331840310007 10287384225712997760465011)
          ·
            refine ⟨15431076338569496640697517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10287384225712997760465011 15431076338569496640697517)
            ·
              refine ⟨5786653626963561240261569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15431076338569496640697517 5786653626963561240261569)
              ·
                refine ⟨4339990220222670930196177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5786653626963561240261569 4339990220222670930196177)
                ·
                  refine ⟨3254992665167003197647133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4339990220222670930196177 3254992665167003197647133)
                  ·
                    refine ⟨1220622249437626199117675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3254992665167003197647133 1220622249437626199117675)
                    ·
                      rfl

theorem cell22_3565730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3565730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565730 prefixEnd_3565730 := by exact prefixLift 3565730
  have htrace : WordTrace (prefixWord ++ tailWord_3565730) baseStart_3565730 baseEnd_3565730 := by
    simpa [prefixWord, tailWord_3565730, baseEnd_3565730] using wordTrace_append hprefix tailTrace_3565730
  have hstable : (prefixWord ++ tailWord_3565730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565730).length < 2 ^ (prefixWord ++ tailWord_3565730).sum := by decide
  have hdescent : baseEnd_3565730 < baseStart_3565730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565769 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_3565769 : Nat := 118140960795 + 3565769 * 2 ^ 59
def prefixEnd_3565769 : Nat := 4983230072969 + 3 ^ 40 * 3565769 * 2
def baseEnd_3565769 : Nat := 1220635599934643097392555

theorem tailTrace_3565769 : CollatzResearch.WordTrace tailWord_3565769 prefixEnd_3565769 1220635599934643097392555 := by
  unfold tailWord_3565769
  simp only [CollatzResearch.WordTrace]
  refine ⟨130054279818835372706548361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86702853212556915137698907 130054279818835372706548361)
  ·
    refine ⟨97540709864126529529911271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130054279818835372706548361 97540709864126529529911271)
    ·
      refine ⟨146311064796189794294866907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97540709864126529529911271 146311064796189794294866907)
      ·
        refine ⟨219466597194284691442300361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146311064796189794294866907 219466597194284691442300361)
        ·
          refine ⟨164599947895713518581725271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219466597194284691442300361 164599947895713518581725271)
          ·
            refine ⟨246899921843570277872587907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164599947895713518581725271 246899921843570277872587907)
            ·
              refine ⟨370349882765355416808881861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246899921843570277872587907 370349882765355416808881861)
              ·
                refine ⟨69440603018504140651665349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370349882765355416808881861 69440603018504140651665349)
                ·
                  refine ⟨13020113065969526372187253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69440603018504140651665349 13020113065969526372187253)
                  ·
                    refine ⟨1220635599934643097392555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13020113065969526372187253 1220635599934643097392555)
                    ·
                      rfl

theorem cell22_3565769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_3565769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565769 prefixEnd_3565769 := by exact prefixLift 3565769
  have htrace : WordTrace (prefixWord ++ tailWord_3565769) baseStart_3565769 baseEnd_3565769 := by
    simpa [prefixWord, tailWord_3565769, baseEnd_3565769] using wordTrace_append hprefix tailTrace_3565769
  have hstable : (prefixWord ++ tailWord_3565769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565769).length < 2 ^ (prefixWord ++ tailWord_3565769).sum := by decide
  have hdescent : baseEnd_3565769 < baseStart_3565769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565818 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_3565818 : Nat := 118140960795 + 3565818 * 2 ^ 59
def prefixEnd_3565818 : Nat := 4983230072969 + 3 ^ 40 * 3565818 * 2
def baseEnd_3565818 : Nat := 1220652373636023302917405

theorem tailTrace_3565818 : CollatzResearch.WordTrace tailWord_3565818 prefixEnd_3565818 1220652373636023302917405 := by
  unfold tailWord_3565818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32514016748914463518770527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86704044663771902716721405 32514016748914463518770527)
  ·
    refine ⟨48771025123371695278155791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32514016748914463518770527 48771025123371695278155791)
    ·
      refine ⟨73156537685057542917233687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48771025123371695278155791 73156537685057542917233687)
      ·
        refine ⟨109734806527586314375850531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73156537685057542917233687 109734806527586314375850531)
        ·
          refine ⟨164602209791379471563775797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109734806527586314375850531 164602209791379471563775797)
          ·
            refine ⟨15431457167941825459103981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164602209791379471563775797 15431457167941825459103981)
            ·
              refine ⟨5786796437978184547163993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15431457167941825459103981 5786796437978184547163993)
              ·
                refine ⟨4340097328483638410372995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5786796437978184547163993 4340097328483638410372995)
                ·
                  refine ⟨6510145992725457615559493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340097328483638410372995 6510145992725457615559493)
                  ·
                    refine ⟨1220652373636023302917405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6510145992725457615559493 1220652373636023302917405)
                    ·
                      rfl

theorem cell22_3565818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_3565818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565818 prefixEnd_3565818 := by exact prefixLift 3565818
  have htrace : WordTrace (prefixWord ++ tailWord_3565818) baseStart_3565818 baseEnd_3565818 := by
    simpa [prefixWord, tailWord_3565818, baseEnd_3565818] using wordTrace_append hprefix tailTrace_3565818
  have hstable : (prefixWord ++ tailWord_3565818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565818).length < 2 ^ (prefixWord ++ tailWord_3565818).sum := by decide
  have hdescent : baseEnd_3565818 < baseStart_3565818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565850 : List Nat := [3, 1, 1, 3, 4, 1, 1, 4, 4]
def baseStart_3565850 : Nat := 118140960795 + 3565850 * 2 ^ 59
def prefixEnd_3565850 : Nat := 4983230072969 + 3 ^ 40 * 3565850 * 2
def baseEnd_3565850 : Nat := 406887775963328628705769

theorem tailTrace_3565850 : CollatzResearch.WordTrace tailWord_3565850 prefixEnd_3565850 406887775963328628705769 := by
  unfold tailWord_3565850
  simp only [CollatzResearch.WordTrace]
  refine ⟨32514308532885480885061751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86704822754361282360164669 32514308532885480885061751)
  ·
    refine ⟨48771462799328221327592627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32514308532885480885061751 48771462799328221327592627)
    ·
      refine ⟨73157194198992331991388941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48771462799328221327592627 73157194198992331991388941)
      ·
        refine ⟨27433947824622124496770853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73157194198992331991388941 27433947824622124496770853)
        ·
          refine ⟨5143865217116648343144535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27433947824622124496770853 5143865217116648343144535)
          ·
            refine ⟨7715797825674972514716803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143865217116648343144535 7715797825674972514716803)
            ·
              refine ⟨11573696738512458772075205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7715797825674972514716803 11573696738512458772075205)
              ·
                refine ⟨2170068138471086019764101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11573696738512458772075205 2170068138471086019764101)
                ·
                  refine ⟨406887775963328628705769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2170068138471086019764101 406887775963328628705769)
                  ·
                    rfl

theorem cell22_3565850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_3565850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565850 prefixEnd_3565850 := by exact prefixLift 3565850
  have htrace : WordTrace (prefixWord ++ tailWord_3565850) baseStart_3565850 baseEnd_3565850 := by
    simpa [prefixWord, tailWord_3565850, baseEnd_3565850] using wordTrace_append hprefix tailTrace_3565850
  have hstable : (prefixWord ++ tailWord_3565850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565850).length < 2 ^ (prefixWord ++ tailWord_3565850).sum := by decide
  have hdescent : baseEnd_3565850 < baseStart_3565850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565983 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 1, 5]
def baseStart_3565983 : Nat := 118140960795 + 3565983 * 2 ^ 59
def prefixEnd_3565983 : Nat := 4983230072969 + 3 ^ 40 * 3565983 * 2
def baseEnd_3565983 : Nat := 1220708856508017872541899

theorem tailTrace_3565983 : CollatzResearch.WordTrace tailWord_3565983 prefixEnd_3565983 1220708856508017872541899 := by
  unfold tailWord_3565983
  simp only [CollatzResearch.WordTrace]
  refine ⟨130062085040060087254838603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86708056693373391503225735 130062085040060087254838603)
  ·
    refine ⟨195093127560090130882257905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130062085040060087254838603 195093127560090130882257905)
    ·
      refine ⟨146319845670067598161693429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195093127560090130882257905 146319845670067598161693429)
      ·
        refine ⟨13717485531568837327658759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146319845670067598161693429 13717485531568837327658759)
        ·
          refine ⟨20576228297353255991488139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13717485531568837327658759 20576228297353255991488139)
          ·
            refine ⟨30864342446029883987232209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20576228297353255991488139 30864342446029883987232209)
            ·
              refine ⟨23148256834522412990424157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30864342446029883987232209 23148256834522412990424157)
              ·
                refine ⟨8680596312945904871409059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23148256834522412990424157 8680596312945904871409059)
                ·
                  refine ⟨13020894469418857307113589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8680596312945904871409059 13020894469418857307113589)
                  ·
                    refine ⟨1220708856508017872541899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13020894469418857307113589 1220708856508017872541899)
                    ·
                      rfl

theorem cell22_3565983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_3565983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3565983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3565983 prefixEnd_3565983 := by exact prefixLift 3565983
  have htrace : WordTrace (prefixWord ++ tailWord_3565983) baseStart_3565983 baseEnd_3565983 := by
    simpa [prefixWord, tailWord_3565983, baseEnd_3565983] using wordTrace_append hprefix tailTrace_3565983
  have hstable : (prefixWord ++ tailWord_3565983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565983).length < 2 ^ (prefixWord ++ tailWord_3565983).sum := by decide
  have hdescent : baseEnd_3565983 < baseStart_3565983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566011 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 3, 9]
def baseStart_3566011 : Nat := 118140960795 + 3566011 * 2 ^ 59
def prefixEnd_3566011 : Nat := 4983230072969 + 3 ^ 40 * 3566011 * 2
def baseEnd_3566011 : Nat := 1220718441480235132841813

theorem tailTrace_3566011 : CollatzResearch.WordTrace tailWord_3566011 prefixEnd_3566011 1220718441480235132841813 := by
  unfold tailWord_3566011
  simp only [CollatzResearch.WordTrace]
  refine ⟨130063106283958648036857887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86708737522639098691238591 130063106283958648036857887)
  ·
    refine ⟨195094659425937972055286831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130063106283958648036857887 195094659425937972055286831)
    ·
      refine ⟨292641989138906958082930247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195094659425937972055286831 292641989138906958082930247)
      ·
        refine ⟨438962983708360437124395371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292641989138906958082930247 438962983708360437124395371)
        ·
          refine ⟨658444475562540655686593057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438962983708360437124395371 658444475562540655686593057)
          ·
            refine ⟨493833356671905491764944793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658444475562540655686593057 493833356671905491764944793)
            ·
              refine ⟨370375017503929118823708595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493833356671905491764944793 370375017503929118823708595)
              ·
                refine ⟨555562526255893678235562893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370375017503929118823708595 555562526255893678235562893)
                ·
                  refine ⟨208335947345960129338336085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555562526255893678235562893 208335947345960129338336085)
                  ·
                    refine ⟨1220718441480235132841813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 208335947345960129338336085 1220718441480235132841813)
                    ·
                      rfl

theorem cell22_3566011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_3566011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566011 prefixEnd_3566011 := by exact prefixLift 3566011
  have htrace : WordTrace (prefixWord ++ tailWord_3566011) baseStart_3566011 baseEnd_3566011 := by
    simpa [prefixWord, tailWord_3566011, baseEnd_3566011] using wordTrace_append hprefix tailTrace_3566011
  have hstable : (prefixWord ++ tailWord_3566011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566011).length < 2 ^ (prefixWord ++ tailWord_3566011).sum := by decide
  have hdescent : baseEnd_3566011 < baseStart_3566011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566073 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_3566073 : Nat := 118140960795 + 3566073 * 2 ^ 59
def prefixEnd_3566073 : Nat := 4983230072969 + 3 ^ 40 * 3566073 * 2
def baseEnd_3566073 : Nat := 1220739665347287637791623

theorem tailTrace_3566073 : CollatzResearch.WordTrace tailWord_3566073 prefixEnd_3566073 1220739665347287637791623 := by
  unfold tailWord_3566073
  simp only [CollatzResearch.WordTrace]
  refine ⟨130065367609734032625614873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86710245073156021750409915 130065367609734032625614873)
  ·
    refine ⟨97549025707300524469211155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130065367609734032625614873 97549025707300524469211155)
    ·
      refine ⟨146323538560950786703816733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97549025707300524469211155 146323538560950786703816733)
      ·
        refine ⟨54871326960356545013931275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146323538560950786703816733 54871326960356545013931275)
        ·
          refine ⟨82306990440534817520896913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54871326960356545013931275 82306990440534817520896913)
          ·
            refine ⟨61730242830401113140672685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82306990440534817520896913 61730242830401113140672685)
            ·
              refine ⟨23148841061400417427752257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61730242830401113140672685 23148841061400417427752257)
              ·
                refine ⟨17361630796050313070814193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23148841061400417427752257 17361630796050313070814193)
                ·
                  refine ⟨13021223097037734803110645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17361630796050313070814193 13021223097037734803110645)
                  ·
                    refine ⟨1220739665347287637791623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13021223097037734803110645 1220739665347287637791623)
                    ·
                      rfl

theorem cell22_3566073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_3566073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566073 prefixEnd_3566073 := by exact prefixLift 3566073
  have htrace : WordTrace (prefixWord ++ tailWord_3566073) baseStart_3566073 baseEnd_3566073 := by
    simpa [prefixWord, tailWord_3566073, baseEnd_3566073] using wordTrace_append hprefix tailTrace_3566073
  have hstable : (prefixWord ++ tailWord_3566073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566073).length < 2 ^ (prefixWord ++ tailWord_3566073).sum := by decide
  have hdescent : baseEnd_3566073 < baseStart_3566073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566092 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 5]
def baseStart_3566092 : Nat := 118140960795 + 3566092 * 2 ^ 59
def prefixEnd_3566092 : Nat := 4983230072969 + 3 ^ 40 * 3566092 * 2
def baseEnd_3566092 : Nat := 406915389811859307188855

theorem tailTrace_3566092 : CollatzResearch.WordTrace tailWord_3566092 prefixEnd_3566092 406915389811859307188855 := by
  unfold tailWord_3566092
  simp only [CollatzResearch.WordTrace]
  refine ⟨65033030298332599435278265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86710707064443465913704353 65033030298332599435278265)
  ·
    refine ⟨48774772723749449576458699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65033030298332599435278265 48774772723749449576458699)
    ·
      refine ⟨73162159085624174364688049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48774772723749449576458699 73162159085624174364688049)
      ·
        refine ⟨54871619314218130773516037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73162159085624174364688049 54871619314218130773516037)
        ·
          refine ⟨10288428621415899520034257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54871619314218130773516037 10288428621415899520034257)
          ·
            refine ⟨7716321466061924640025693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10288428621415899520034257 7716321466061924640025693)
            ·
              refine ⟨2893620549773221740009635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7716321466061924640025693 2893620549773221740009635)
              ·
                refine ⟨4340430824659832610014453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893620549773221740009635 4340430824659832610014453)
                ·
                  refine ⟨406915389811859307188855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4340430824659832610014453 406915389811859307188855)
                  ·
                    rfl

theorem cell22_3566092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_3566092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566092 prefixEnd_3566092 := by exact prefixLift 3566092
  have htrace : WordTrace (prefixWord ++ tailWord_3566092) baseStart_3566092 baseEnd_3566092 := by
    simpa [prefixWord, tailWord_3566092, baseEnd_3566092] using wordTrace_append hprefix tailTrace_3566092
  have hstable : (prefixWord ++ tailWord_3566092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566092).length < 2 ^ (prefixWord ++ tailWord_3566092).sum := by decide
  have hdescent : baseEnd_3566092 < baseStart_3566092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566122 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_3566122 : Nat := 118140960795 + 3566122 * 2 ^ 59
def prefixEnd_3566122 : Nat := 4983230072969 + 3 ^ 40 * 3566122 * 2
def baseEnd_3566122 : Nat := 1220756439048667843316473

theorem tailTrace_3566122 : CollatzResearch.WordTrace tailWord_3566122 prefixEnd_3566122 1220756439048667843316473 := by
  unfold tailWord_3566122
  simp only [CollatzResearch.WordTrace]
  refine ⟨32516788696639128498537155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86711436524371009329432413 32516788696639128498537155)
  ·
    refine ⟨48775183044958692747805733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32516788696639128498537155 48775183044958692747805733)
    ·
      refine ⟨9145346820929754890213575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48775183044958692747805733 9145346820929754890213575)
      ·
        refine ⟨13718020231394632335320363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9145346820929754890213575 13718020231394632335320363)
        ·
          refine ⟨20577030347091948502980545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13718020231394632335320363 20577030347091948502980545)
          ·
            refine ⟨15432772760318961377235409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20577030347091948502980545 15432772760318961377235409)
            ·
              refine ⟨11574579570239221032926557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15432772760318961377235409 11574579570239221032926557)
              ·
                refine ⟨4340467338839707887347459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11574579570239221032926557 4340467338839707887347459)
                ·
                  refine ⟨6510701008259561831021189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340467338839707887347459 6510701008259561831021189)
                  ·
                    refine ⟨1220756439048667843316473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6510701008259561831021189 1220756439048667843316473)
                    ·
                      rfl

theorem cell22_3566122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_3566122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566122 prefixEnd_3566122 := by exact prefixLift 3566122
  have htrace : WordTrace (prefixWord ++ tailWord_3566122) baseStart_3566122 baseEnd_3566122 := by
    simpa [prefixWord, tailWord_3566122, baseEnd_3566122] using wordTrace_append hprefix tailTrace_3566122
  have hstable : (prefixWord ++ tailWord_3566122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566122).length < 2 ^ (prefixWord ++ tailWord_3566122).sum := by decide
  have hdescent : baseEnd_3566122 < baseStart_3566122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566135 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 4, 3]
def baseStart_3566135 : Nat := 118140960795 + 3566135 * 2 ^ 59
def prefixEnd_3566135 : Nat := 4983230072969 + 3 ^ 40 * 3566135 * 2
def baseEnd_3566135 : Nat := 1220760889214340142741433

theorem tailTrace_3566135 : CollatzResearch.WordTrace tailWord_3566135 prefixEnd_3566135 1220760889214340142741433 := by
  unfold tailWord_3566135
  simp only [CollatzResearch.WordTrace]
  refine ⟨130067628935509417214371859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86711752623672944809581239 130067628935509417214371859)
  ·
    refine ⟨195101443403264125821557789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130067628935509417214371859 195101443403264125821557789)
    ·
      refine ⟨73163041276224047183084171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195101443403264125821557789 73163041276224047183084171)
      ·
        refine ⟨109744561914336070774626257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73163041276224047183084171 109744561914336070774626257)
        ·
          refine ⟨82308421435752053080969693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109744561914336070774626257 82308421435752053080969693)
          ·
            refine ⟨30865658038407019905363635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82308421435752053080969693 30865658038407019905363635)
            ·
              refine ⟨46298487057610529858045453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30865658038407019905363635 46298487057610529858045453)
              ·
                refine ⟨17361932646603948696767045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46298487057610529858045453 17361932646603948696767045)
                ·
                  refine ⟨3255362371238240380643821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17361932646603948696767045 3255362371238240380643821)
                  ·
                    refine ⟨1220760889214340142741433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3255362371238240380643821 1220760889214340142741433)
                    ·
                      rfl

theorem cell22_3566135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_3566135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566135 prefixEnd_3566135 := by exact prefixLift 3566135
  have htrace : WordTrace (prefixWord ++ tailWord_3566135) baseStart_3566135 baseEnd_3566135 := by
    simpa [prefixWord, tailWord_3566135, baseEnd_3566135] using wordTrace_append hprefix tailTrace_3566135
  have hstable : (prefixWord ++ tailWord_3566135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566135).length < 2 ^ (prefixWord ++ tailWord_3566135).sum := by decide
  have hdescent : baseEnd_3566135 < baseStart_3566135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566255 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 6]
def baseStart_3566255 : Nat := 118140960795 + 3566255 * 2 ^ 59
def prefixEnd_3566255 : Nat := 4983230072969 + 3 ^ 40 * 3566255 * 2
def baseEnd_3566255 : Nat := 406933989222233276580355

theorem tailTrace_3566255 : CollatzResearch.WordTrace tailWord_3566255 prefixEnd_3566255 406933989222233276580355 := by
  unfold tailWord_3566255
  simp only [CollatzResearch.WordTrace]
  refine ⟨130072005695074677708740219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86714670463383118472493479 130072005695074677708740219)
  ·
    refine ⟨195108008542612016563110329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130072005695074677708740219 195108008542612016563110329)
    ·
      refine ⟨146331006406959012422332747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195108008542612016563110329 146331006406959012422332747)
      ·
        refine ⟨219496509610438518633499121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146331006406959012422332747 219496509610438518633499121)
        ·
          refine ⟨164622382207828888975124341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219496509610438518633499121 164622382207828888975124341)
          ·
            refine ⟨15433348331983958341417907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164622382207828888975124341 15433348331983958341417907)
            ·
              refine ⟨23150022497975937512126861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15433348331983958341417907 23150022497975937512126861)
              ·
                refine ⟨8681258436740976567047573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23150022497975937512126861 8681258436740976567047573)
                ·
                  refine ⟨406933989222233276580355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8681258436740976567047573 406933989222233276580355)
                  ·
                    rfl

theorem cell22_3566255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 6].length) (baseStart_3566255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566255 prefixEnd_3566255 := by exact prefixLift 3566255
  have htrace : WordTrace (prefixWord ++ tailWord_3566255) baseStart_3566255 baseEnd_3566255 := by
    simpa [prefixWord, tailWord_3566255, baseEnd_3566255] using wordTrace_append hprefix tailTrace_3566255
  have hstable : (prefixWord ++ tailWord_3566255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566255).length < 2 ^ (prefixWord ++ tailWord_3566255).sum := by decide
  have hdescent : baseEnd_3566255 < baseStart_3566255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566317 : List Nat := [1, 5, 1, 2, 1, 1, 4, 7]
def baseStart_3566317 : Nat := 118140960795 + 3566317 * 2 ^ 59
def prefixEnd_3566317 : Nat := 4983230072969 + 3 ^ 40 * 3566317 * 2
def baseEnd_3566317 : Nat := 135647021281528037187875

theorem tailTrace_3566317 : CollatzResearch.WordTrace tailWord_3566317 prefixEnd_3566317 135647021281528037187875 := by
  unfold tailWord_3566317
  simp only [CollatzResearch.WordTrace]
  refine ⟨130074267020850062297497205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86716178013900041531664803 130074267020850062297497205)
  ·
    refine ⟨12194462533204693340390363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130074267020850062297497205 12194462533204693340390363)
    ·
      refine ⟨18291693799807040010585545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12194462533204693340390363 18291693799807040010585545)
      ·
        refine ⟨13718770349855280007939159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18291693799807040010585545 13718770349855280007939159)
        ·
          refine ⟨20578155524782920011908739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13718770349855280007939159 20578155524782920011908739)
          ·
            refine ⟨30867233287174380017863109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20578155524782920011908739 30867233287174380017863109)
            ·
              refine ⟨5787606241345196253349333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30867233287174380017863109 5787606241345196253349333)
              ·
                refine ⟨135647021281528037187875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5787606241345196253349333 135647021281528037187875)
                ·
                  rfl

theorem cell22_3566317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 7].length) (baseStart_3566317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566317 prefixEnd_3566317 := by exact prefixLift 3566317
  have htrace : WordTrace (prefixWord ++ tailWord_3566317) baseStart_3566317 baseEnd_3566317 := by
    simpa [prefixWord, tailWord_3566317, baseEnd_3566317] using wordTrace_append hprefix tailTrace_3566317
  have hstable : (prefixWord ++ tailWord_3566317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566317).length < 2 ^ (prefixWord ++ tailWord_3566317).sum := by decide
  have hdescent : baseEnd_3566317 < baseStart_3566317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566325 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3566325 : Nat := 118140960795 + 3566325 * 2 ^ 59
def prefixEnd_3566325 : Nat := 4983230072969 + 3 ^ 40 * 3566325 * 2
def baseEnd_3566325 : Nat := 1220825930097242980490851

theorem tailTrace_3566325 : CollatzResearch.WordTrace tailWord_3566325 prefixEnd_3566325 1220825930097242980490851 := by
  unfold tailWord_3566325
  simp only [CollatzResearch.WordTrace]
  refine ⟨130074558804821079663788429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86716372536547386442525619 130074558804821079663788429)
  ·
    refine ⟨48777959551807904873920661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130074558804821079663788429 48777959551807904873920661)
    ·
      refine ⟨2286466853990995540965031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48777959551807904873920661 2286466853990995540965031)
      ·
        refine ⟨3429700280986493311447547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286466853990995540965031 3429700280986493311447547)
        ·
          refine ⟨5144550421479739967171321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429700280986493311447547 5144550421479739967171321)
          ·
            refine ⟨3858412816109804975378491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5144550421479739967171321 3858412816109804975378491)
            ·
              refine ⟨5787619224164707463067737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3858412816109804975378491 5787619224164707463067737)
              ·
                refine ⟨4340714418123530597300803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787619224164707463067737 4340714418123530597300803)
                ·
                  refine ⟨6511071627185295895951205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340714418123530597300803 6511071627185295895951205)
                  ·
                    refine ⟨1220825930097242980490851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6511071627185295895951205 1220825930097242980490851)
                    ·
                      rfl

theorem cell22_3566325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3566325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566325 prefixEnd_3566325 := by exact prefixLift 3566325
  have htrace : WordTrace (prefixWord ++ tailWord_3566325) baseStart_3566325 baseEnd_3566325 := by
    simpa [prefixWord, tailWord_3566325, baseEnd_3566325] using wordTrace_append hprefix tailTrace_3566325
  have hstable : (prefixWord ++ tailWord_3566325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566325).length < 2 ^ (prefixWord ++ tailWord_3566325).sum := by decide
  have hdescent : baseEnd_3566325 < baseStart_3566325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566345 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 9]
def baseStart_3566345 : Nat := 118140960795 + 3566345 * 2 ^ 59
def prefixEnd_3566345 : Nat := 4983230072969 + 3 ^ 40 * 3566345 * 2
def baseEnd_3566345 : Nat := 406944258835323198330263

theorem tailTrace_3566345 : CollatzResearch.WordTrace tailWord_3566345 prefixEnd_3566345 406944258835323198330263 := by
  unfold tailWord_3566345
  simp only [CollatzResearch.WordTrace]
  refine ⟨130075288264748623079516489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86716858843165748719677659 130075288264748623079516489)
  ·
    refine ⟨97556466198561467309637367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130075288264748623079516489 97556466198561467309637367)
    ·
      refine ⟨146334699297842200964456051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97556466198561467309637367 146334699297842200964456051)
      ·
        refine ⟨219502048946763301446684077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146334699297842200964456051 219502048946763301446684077)
        ·
          refine ⟨82313268355036238042506529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219502048946763301446684077 82313268355036238042506529)
          ·
            refine ⟨61734951266277178531879897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82313268355036238042506529 61734951266277178531879897)
            ·
              refine ⟨46301213449707883898909923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61734951266277178531879897 46301213449707883898909923)
              ·
                refine ⟨69451820174561825848364885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46301213449707883898909923 69451820174561825848364885)
                ·
                  refine ⟨406944258835323198330263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69451820174561825848364885 406944258835323198330263)
                  ·
                    rfl

theorem cell22_3566345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_3566345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566345 prefixEnd_3566345 := by exact prefixLift 3566345
  have htrace : WordTrace (prefixWord ++ tailWord_3566345) baseStart_3566345 baseEnd_3566345 := by
    simpa [prefixWord, tailWord_3566345, baseEnd_3566345] using wordTrace_append hprefix tailTrace_3566345
  have hstable : (prefixWord ++ tailWord_3566345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566345).length < 2 ^ (prefixWord ++ tailWord_3566345).sum := by decide
  have hdescent : baseEnd_3566345 < baseStart_3566345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566392 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 3, 4]
def baseStart_3566392 : Nat := 118140960795 + 3566392 * 2 ^ 59
def prefixEnd_3566392 : Nat := 4983230072969 + 3 ^ 40 * 3566392 * 2
def baseEnd_3566392 : Nat := 1220848865566477139065645

theorem tailTrace_3566392 : CollatzResearch.WordTrace tailWord_3566392 prefixEnd_3566392 1220848865566477139065645 := by
  unfold tailWord_3566392
  simp only [CollatzResearch.WordTrace]
  refine ⟨65038501247789175053238715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86718001663718900070984953 65038501247789175053238715)
  ·
    refine ⟨97557751871683762579858073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65038501247789175053238715 97557751871683762579858073)
    ·
      refine ⟨73168313903762821934893555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97557751871683762579858073 73168313903762821934893555)
      ·
        refine ⟨109752470855644232902340333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73168313903762821934893555 109752470855644232902340333)
        ·
          refine ⟨41157176570866587338377625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109752470855644232902340333 41157176570866587338377625)
          ·
            refine ⟨30867882428149940503783219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41157176570866587338377625 30867882428149940503783219)
            ·
              refine ⟨46301823642224910755674829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30867882428149940503783219 46301823642224910755674829)
              ·
                refine ⟨17363183865834341533378061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46301823642224910755674829 17363183865834341533378061)
                ·
                  refine ⟨6511193949687878075016773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17363183865834341533378061 6511193949687878075016773)
                  ·
                    refine ⟨1220848865566477139065645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6511193949687878075016773 1220848865566477139065645)
                    ·
                      rfl

theorem cell22_3566392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_3566392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566392 prefixEnd_3566392 := by exact prefixLift 3566392
  have htrace : WordTrace (prefixWord ++ tailWord_3566392) baseStart_3566392 baseEnd_3566392 := by
    simpa [prefixWord, tailWord_3566392, baseEnd_3566392] using wordTrace_append hprefix tailTrace_3566392
  have hstable : (prefixWord ++ tailWord_3566392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566392).length < 2 ^ (prefixWord ++ tailWord_3566392).sum := by decide
  have hdescent : baseEnd_3566392 < baseStart_3566392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566409 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 1, 4]
def baseStart_3566409 : Nat := 118140960795 + 3566409 * 2 ^ 59
def prefixEnd_3566409 : Nat := 4983230072969 + 3 ^ 40 * 3566409 * 2
def baseEnd_3566409 : Nat := 1220854685013894761390593

theorem tailTrace_3566409 : CollatzResearch.WordTrace tailWord_3566409 prefixEnd_3566409 1220854685013894761390593 := by
  unfold tailWord_3566409
  simp only [CollatzResearch.WordTrace]
  refine ⟨130077622536516762009846281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86718415024344508006564187 130077622536516762009846281)
  ·
    refine ⟨97558216902387571507384711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130077622536516762009846281 97558216902387571507384711)
    ·
      refine ⟨146337325353581357261077067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97558216902387571507384711 146337325353581357261077067)
      ·
        refine ⟨219505988030372035891615601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146337325353581357261077067 219505988030372035891615601)
        ·
          refine ⟨164629491022779026918711701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219505988030372035891615601 164629491022779026918711701)
          ·
            refine ⟨7717007391692766886814611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164629491022779026918711701 7717007391692766886814611)
            ·
              refine ⟨11575511087539150330221917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717007391692766886814611 11575511087539150330221917)
              ·
                refine ⟨4340816657827181373833219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11575511087539150330221917 4340816657827181373833219)
                ·
                  refine ⟨6511224986740772060749829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340816657827181373833219 6511224986740772060749829)
                  ·
                    refine ⟨1220854685013894761390593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6511224986740772060749829 1220854685013894761390593)
                    ·
                      rfl

theorem cell22_3566409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_3566409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566409 prefixEnd_3566409 := by exact prefixLift 3566409
  have htrace : WordTrace (prefixWord ++ tailWord_3566409) baseStart_3566409 baseEnd_3566409 := by
    simpa [prefixWord, tailWord_3566409, baseEnd_3566409] using wordTrace_append hprefix tailTrace_3566409
  have hstable : (prefixWord ++ tailWord_3566409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566409).length < 2 ^ (prefixWord ++ tailWord_3566409).sum := by decide
  have hdescent : baseEnd_3566409 < baseStart_3566409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566413 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 5]
def baseStart_3566413 : Nat := 118140960795 + 3566413 * 2 ^ 59
def prefixEnd_3566413 : Nat := 4983230072969 + 3 ^ 40 * 3566413 * 2
def baseEnd_3566413 : Nat := 406952018098546694763527

theorem tailTrace_3566413 : CollatzResearch.WordTrace tailWord_3566413 prefixEnd_3566413 406952018098546694763527 := by
  unfold tailWord_3566413
  simp only [CollatzResearch.WordTrace]
  refine ⟨130077768428502270692991893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86718512285668180461994595 130077768428502270692991893)
  ·
    refine ⟨6097395395086043938733995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130077768428502270692991893 6097395395086043938733995)
    ·
      refine ⟨9146093092629065908100993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6097395395086043938733995 9146093092629065908100993)
      ·
        refine ⟨6859569819471799431075745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9146093092629065908100993 6859569819471799431075745)
        ·
          refine ⟨5144677364603849573306809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6859569819471799431075745 5144677364603849573306809)
          ·
            refine ⟨3858508023452887179980107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5144677364603849573306809 3858508023452887179980107)
            ·
              refine ⟨5787762035179330769970161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3858508023452887179980107 5787762035179330769970161)
              ·
                refine ⟨4340821526384498077477621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787762035179330769970161 4340821526384498077477621)
                ·
                  refine ⟨406952018098546694763527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4340821526384498077477621 406952018098546694763527)
                  ·
                    rfl

theorem cell22_3566413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_3566413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566413 prefixEnd_3566413 := by exact prefixLift 3566413
  have htrace : WordTrace (prefixWord ++ tailWord_3566413) baseStart_3566413 baseEnd_3566413 := by
    simpa [prefixWord, tailWord_3566413, baseEnd_3566413] using wordTrace_append hprefix tailTrace_3566413
  have hstable : (prefixWord ++ tailWord_3566413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566413).length < 2 ^ (prefixWord ++ tailWord_3566413).sum := by decide
  have hdescent : baseEnd_3566413 < baseStart_3566413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566437 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_3566437 : Nat := 118140960795 + 3566437 * 2 ^ 59
def prefixEnd_3566437 : Nat := 4983230072969 + 3 ^ 40 * 3566437 * 2
def baseEnd_3566437 : Nat := 1220864269986112021690507

theorem tailTrace_3566437 : CollatzResearch.WordTrace tailWord_3566437 prefixEnd_3566437 1220864269986112021690507 := by
  unfold tailWord_3566437
  simp only [CollatzResearch.WordTrace]
  refine ⟨130078643780415322791865565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86719095853610215194577043 130078643780415322791865565)
  ·
    refine ⟨48779491417655746046949587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130078643780415322791865565 48779491417655746046949587)
    ·
      refine ⟨73169237126483619070424381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48779491417655746046949587 73169237126483619070424381)
      ·
        refine ⟨27438463922431357151409143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73169237126483619070424381 27438463922431357151409143)
        ·
          refine ⟨41157695883647035727113715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27438463922431357151409143 41157695883647035727113715)
          ·
            refine ⟨61736543825470553590670573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41157695883647035727113715 61736543825470553590670573)
            ·
              refine ⟨23151203934551457596501465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61736543825470553590670573 23151203934551457596501465)
              ·
                refine ⟨17363402950913593197376099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23151203934551457596501465 17363402950913593197376099)
                ·
                  refine ⟨26045104426370389796064149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17363402950913593197376099 26045104426370389796064149)
                  ·
                    refine ⟨1220864269986112021690507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26045104426370389796064149 1220864269986112021690507)
                    ·
                      rfl

theorem cell22_3566437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_3566437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566437 prefixEnd_3566437 := by exact prefixLift 3566437
  have htrace : WordTrace (prefixWord ++ tailWord_3566437) baseStart_3566437 baseEnd_3566437 := by
    simpa [prefixWord, tailWord_3566437, baseEnd_3566437] using wordTrace_append hprefix tailTrace_3566437
  have hstable : (prefixWord ++ tailWord_3566437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566437).length < 2 ^ (prefixWord ++ tailWord_3566437).sum := by decide
  have hdescent : baseEnd_3566437 < baseStart_3566437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566439 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 1, 5]
def baseStart_3566439 : Nat := 118140960795 + 3566439 * 2 ^ 59
def prefixEnd_3566439 : Nat := 4983230072969 + 3 ^ 40 * 3566439 * 2
def baseEnd_3566439 : Nat := 1220864954626984683140501

theorem tailTrace_3566439 : CollatzResearch.WordTrace tailWord_3566439 prefixEnd_3566439 1220864954626984683140501 := by
  unfold tailWord_3566439
  simp only [CollatzResearch.WordTrace]
  refine ⟨130078716726408077133438371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86719144484272051422292247 130078716726408077133438371)
  ·
    refine ⟨195118075089612115700157557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130078716726408077133438371 195118075089612115700157557)
    ·
      refine ⟨18292319539651135846889771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195118075089612115700157557 18292319539651135846889771)
      ·
        refine ⟨27438479309476703770334657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18292319539651135846889771 27438479309476703770334657)
        ·
          refine ⟨20578859482107527827750993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27438479309476703770334657 20578859482107527827750993)
          ·
            refine ⟨15434144611580645870813245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20578859482107527827750993 15434144611580645870813245)
            ·
              refine ⟨5787804229342742201554967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15434144611580645870813245 5787804229342742201554967)
              ·
                refine ⟨8681706344014113302332451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5787804229342742201554967 8681706344014113302332451)
                ·
                  refine ⟨13022559516021169953498677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8681706344014113302332451 13022559516021169953498677)
                  ·
                    refine ⟨1220864954626984683140501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13022559516021169953498677 1220864954626984683140501)
                    ·
                      rfl

theorem cell22_3566439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_3566439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566439 prefixEnd_3566439 := by exact prefixLift 3566439
  have htrace : WordTrace (prefixWord ++ tailWord_3566439) baseStart_3566439 baseEnd_3566439 := by
    simpa [prefixWord, tailWord_3566439, baseEnd_3566439] using wordTrace_append hprefix tailTrace_3566439
  have hstable : (prefixWord ++ tailWord_3566439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566439).length < 2 ^ (prefixWord ++ tailWord_3566439).sum := by decide
  have hdescent : baseEnd_3566439 < baseStart_3566439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566490 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 2, 3]
def baseStart_3566490 : Nat := 118140960795 + 3566490 * 2 ^ 59
def prefixEnd_3566490 : Nat := 4983230072969 + 3 ^ 40 * 3566490 * 2
def baseEnd_3566490 : Nat := 1220882412969237550115345

theorem tailTrace_3566490 : CollatzResearch.WordTrace tailWord_3566490 prefixEnd_3566490 1220882412969237550115345 := by
  unfold tailWord_3566490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32520144212305828210886231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86720384566148875229029949 32520144212305828210886231)
  ·
    refine ⟨48780216318458742316329347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32520144212305828210886231 48780216318458742316329347)
    ·
      refine ⟨73170324477688113474494021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48780216318458742316329347 73170324477688113474494021)
      ·
        refine ⟨13719435839566521276467629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73170324477688113474494021 13719435839566521276467629)
        ·
          refine ⟨5144788439837445478675361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13719435839566521276467629 5144788439837445478675361)
          ·
            refine ⟨3858591329878084109006521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5144788439837445478675361 3858591329878084109006521)
            ·
              refine ⟨2893943497408563081754891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3858591329878084109006521 2893943497408563081754891)
              ·
                refine ⟨4340915246112844622632337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893943497408563081754891 4340915246112844622632337)
                ·
                  refine ⟨3255686434584633466974253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4340915246112844622632337 3255686434584633466974253)
                  ·
                    refine ⟨1220882412969237550115345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3255686434584633466974253 1220882412969237550115345)
                    ·
                      rfl

theorem cell22_3566490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_3566490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566490 prefixEnd_3566490 := by exact prefixLift 3566490
  have htrace : WordTrace (prefixWord ++ tailWord_3566490) baseStart_3566490 baseEnd_3566490 := by
    simpa [prefixWord, tailWord_3566490, baseEnd_3566490] using wordTrace_append hprefix tailTrace_3566490
  have hstable : (prefixWord ++ tailWord_3566490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566490).length < 2 ^ (prefixWord ++ tailWord_3566490).sum := by decide
  have hdescent : baseEnd_3566490 < baseStart_3566490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566546 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_3566546 : Nat := 118140960795 + 3566546 * 2 ^ 59
def prefixEnd_3566546 : Nat := 4983230072969 + 3 ^ 40 * 3566546 * 2
def baseEnd_3566546 : Nat := 1220901582913672070715173

theorem tailTrace_3566546 : CollatzResearch.WordTrace tailWord_3566546 prefixEnd_3566546 1220901582913672070715173 := by
  unfold tailWord_3566546
  simp only [CollatzResearch.WordTrace]
  refine ⟨32520654834255108601895873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86721746224680289605055661 32520654834255108601895873)
  ·
    refine ⟨24390491125691331451421905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32520654834255108601895873 24390491125691331451421905)
    ·
      refine ⟨18292868344268498588566429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24390491125691331451421905 18292868344268498588566429)
      ·
        refine ⟨6859825629100686970712411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18292868344268498588566429 6859825629100686970712411)
        ·
          refine ⟨10289738443651030456068617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6859825629100686970712411 10289738443651030456068617)
          ·
            refine ⟨7717303832738272842051463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10289738443651030456068617 7717303832738272842051463)
            ·
              refine ⟨11575955749107409263077195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717303832738272842051463 11575955749107409263077195)
              ·
                refine ⟨17363933623661113894615793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11575955749107409263077195 17363933623661113894615793)
                ·
                  refine ⟨13022950217745835420961845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17363933623661113894615793 13022950217745835420961845)
                  ·
                    refine ⟨1220901582913672070715173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13022950217745835420961845 1220901582913672070715173)
                    ·
                      rfl

theorem cell22_3566546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_3566546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566546 prefixEnd_3566546 := by exact prefixLift 3566546
  have htrace : WordTrace (prefixWord ++ tailWord_3566546) baseStart_3566546 baseEnd_3566546 := by
    simpa [prefixWord, tailWord_3566546, baseEnd_3566546] using wordTrace_append hprefix tailTrace_3566546
  have hstable : (prefixWord ++ tailWord_3566546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566546).length < 2 ^ (prefixWord ++ tailWord_3566546).sum := by decide
  have hdescent : baseEnd_3566546 < baseStart_3566546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566589 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_3566589 : Nat := 118140960795 + 3566589 * 2 ^ 59
def prefixEnd_3566589 : Nat := 4983230072969 + 3 ^ 40 * 3566589 * 2
def baseEnd_3566589 : Nat := 1220916302692434291890041

theorem tailTrace_3566589 : CollatzResearch.WordTrace tailWord_3566589 prefixEnd_3566589 1220916302692434291890041 := by
  unfold tailWord_3566589
  simp only [CollatzResearch.WordTrace]
  refine ⟨130084187675864652751398821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86722791783909768500932547 130084187675864652751398821)
  ·
    refine ⟨24390785189224622390887279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130084187675864652751398821 24390785189224622390887279)
    ·
      refine ⟨36586177783836933586330919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24390785189224622390887279 36586177783836933586330919)
      ·
        refine ⟨54879266675755400379496379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36586177783836933586330919 54879266675755400379496379)
        ·
          refine ⟨82318900013633100569244569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54879266675755400379496379 82318900013633100569244569)
          ·
            refine ⟨61739175010224825426933427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82318900013633100569244569 61739175010224825426933427)
            ·
              refine ⟨92608762515337238140400141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61739175010224825426933427 92608762515337238140400141)
              ·
                refine ⟨34728285943251464302650053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92608762515337238140400141 34728285943251464302650053)
                ·
                  refine ⟨6511553614359649556746885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34728285943251464302650053 6511553614359649556746885)
                  ·
                    refine ⟨1220916302692434291890041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6511553614359649556746885 1220916302692434291890041)
                    ·
                      rfl

theorem cell22_3566589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_3566589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566589 prefixEnd_3566589 := by exact prefixLift 3566589
  have htrace : WordTrace (prefixWord ++ tailWord_3566589) baseStart_3566589 baseEnd_3566589 := by
    simpa [prefixWord, tailWord_3566589, baseEnd_3566589] using wordTrace_append hprefix tailTrace_3566589
  have hstable : (prefixWord ++ tailWord_3566589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566589).length < 2 ^ (prefixWord ++ tailWord_3566589).sum := by decide
  have hdescent : baseEnd_3566589 < baseStart_3566589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566621 : List Nat := [1, 4, 2, 2, 3, 1, 1, 8]
def baseStart_3566621 : Nat := 118140960795 + 3566621 * 2 ^ 59
def prefixEnd_3566621 : Nat := 4983230072969 + 3 ^ 40 * 3566621 * 2
def baseEnd_3566621 : Nat := 135658584105155208343327

theorem tailTrace_3566621 : CollatzResearch.WordTrace tailWord_3566621 prefixEnd_3566621 135658584105155208343327 := by
  unfold tailWord_3566621
  simp only [CollatzResearch.WordTrace]
  refine ⟨130085354811748722216563717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86723569874499148144375811 130085354811748722216563717)
  ·
    refine ⟨24391004027202885415605697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130085354811748722216563717 24391004027202885415605697)
    ·
      refine ⟨18293253020402164061704273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24391004027202885415605697 18293253020402164061704273)
      ·
        refine ⟨13719939765301623046278205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18293253020402164061704273 13719939765301623046278205)
        ·
          refine ⟨5144977411988108642354327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13719939765301623046278205 5144977411988108642354327)
          ·
            refine ⟨7717466117982162963531491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5144977411988108642354327 7717466117982162963531491)
            ·
              refine ⟨11576199176973244445297237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717466117982162963531491 11576199176973244445297237)
              ·
                refine ⟨135658584105155208343327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11576199176973244445297237 135658584105155208343327)
                ·
                  rfl

theorem cell22_3566621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 8].length) (baseStart_3566621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566621 prefixEnd_3566621 := by exact prefixLift 3566621
  have htrace : WordTrace (prefixWord ++ tailWord_3566621) baseStart_3566621 baseEnd_3566621 := by
    simpa [prefixWord, tailWord_3566621, baseEnd_3566621] using wordTrace_append hprefix tailTrace_3566621
  have hstable : (prefixWord ++ tailWord_3566621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566621).length < 2 ^ (prefixWord ++ tailWord_3566621).sum := by decide
  have hdescent : baseEnd_3566621 < baseStart_3566621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566653 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_3566653 : Nat := 118140960795 + 3566653 * 2 ^ 59
def prefixEnd_3566653 : Nat := 4983230072969 + 3 ^ 40 * 3566653 * 2
def baseEnd_3566653 : Nat := 1220938211200359458289845

theorem tailTrace_3566653 : CollatzResearch.WordTrace tailWord_3566653 prefixEnd_3566653 1220938211200359458289845 := by
  unfold tailWord_3566653
  simp only [CollatzResearch.WordTrace]
  refine ⟨130086521947632791681728613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86724347965088527787819075 130086521947632791681728613)
  ·
    refine ⟨24391222865181148440324115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130086521947632791681728613 24391222865181148440324115)
    ·
      refine ⟨36586834297771722660486173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24391222865181148440324115 36586834297771722660486173)
      ·
        refine ⟨13720062861664395997682315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36586834297771722660486173 13720062861664395997682315)
        ·
          refine ⟨20580094292496593996523473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13720062861664395997682315 20580094292496593996523473)
          ·
            refine ⟨15435070719372445497392605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20580094292496593996523473 15435070719372445497392605)
            ·
              refine ⟨5788151519764667061522227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15435070719372445497392605 5788151519764667061522227)
              ·
                refine ⟨8682227279647000592283341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788151519764667061522227 8682227279647000592283341)
                ·
                  refine ⟨3255835229867625222106253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8682227279647000592283341 3255835229867625222106253)
                  ·
                    refine ⟨1220938211200359458289845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3255835229867625222106253 1220938211200359458289845)
                    ·
                      rfl

theorem cell22_3566653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_3566653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566653 prefixEnd_3566653 := by exact prefixLift 3566653
  have htrace : WordTrace (prefixWord ++ tailWord_3566653) baseStart_3566653 baseEnd_3566653 := by
    simpa [prefixWord, tailWord_3566653, baseEnd_3566653] using wordTrace_append hprefix tailTrace_3566653
  have hstable : (prefixWord ++ tailWord_3566653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566653).length < 2 ^ (prefixWord ++ tailWord_3566653).sum := by decide
  have hdescent : baseEnd_3566653 < baseStart_3566653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566664 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_3566664 : Nat := 118140960795 + 3566664 * 2 ^ 59
def prefixEnd_3566664 : Nat := 4983230072969 + 3 ^ 40 * 3566664 * 2
def baseEnd_3566664 : Nat := 1220941976725159096264811

theorem tailTrace_3566664 : CollatzResearch.WordTrace tailWord_3566664 prefixEnd_3566664 1220941976725159096264811 := by
  unfold tailWord_3566664
  simp only [CollatzResearch.WordTrace]
  refine ⟨65043461575296470280189523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86724615433728627040252697 65043461575296470280189523)
  ·
    refine ⟨97565192362944705420284285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65043461575296470280189523 97565192362944705420284285)
    ·
      refine ⟨36586947136104264532606607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97565192362944705420284285 36586947136104264532606607)
      ·
        refine ⟨54880420704156396798909911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36586947136104264532606607 54880420704156396798909911)
        ·
          refine ⟨82320631056234595198364867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54880420704156396798909911 82320631056234595198364867)
          ·
            refine ⟨123480946584351892797547301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82320631056234595198364867 123480946584351892797547301)
            ·
              refine ⟨23152677484565979899540119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123480946584351892797547301 23152677484565979899540119)
              ·
                refine ⟨34729016226848969849310179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23152677484565979899540119 34729016226848969849310179)
                ·
                  refine ⟨52093524340273454773965269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34729016226848969849310179 52093524340273454773965269)
                  ·
                    refine ⟨1220941976725159096264811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52093524340273454773965269 1220941976725159096264811)
                    ·
                      rfl

theorem cell22_3566664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_3566664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566664 prefixEnd_3566664 := by exact prefixLift 3566664
  have htrace : WordTrace (prefixWord ++ tailWord_3566664) baseStart_3566664 baseEnd_3566664 := by
    simpa [prefixWord, tailWord_3566664, baseEnd_3566664] using wordTrace_append hprefix tailTrace_3566664
  have hstable : (prefixWord ++ tailWord_3566664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566664).length < 2 ^ (prefixWord ++ tailWord_3566664).sum := by decide
  have hdescent : baseEnd_3566664 < baseStart_3566664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566728 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 6]
def baseStart_3566728 : Nat := 118140960795 + 3566728 * 2 ^ 59
def prefixEnd_3566728 : Nat := 4983230072969 + 3 ^ 40 * 3566728 * 2
def baseEnd_3566728 : Nat := 406987961744361420888205

theorem tailTrace_3566728 : CollatzResearch.WordTrace tailWord_3566728 prefixEnd_3566728 406987961744361420888205 := by
  unfold tailWord_3566728
  simp only [CollatzResearch.WordTrace]
  refine ⟨65044628711180539745354419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86726171614907386327139225 65044628711180539745354419)
  ·
    refine ⟨97566943066770809618031629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65044628711180539745354419 97566943066770809618031629)
    ·
      refine ⟨36587603650039053606761861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97566943066770809618031629 36587603650039053606761861)
      ·
        refine ⟨6860175684382322551267849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36587603650039053606761861 6860175684382322551267849)
        ·
          refine ⟨5145131763286741913450887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6860175684382322551267849 5145131763286741913450887)
          ·
            refine ⟨7717697644930112870176331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5145131763286741913450887 7717697644930112870176331)
            ·
              refine ⟨11576546467395169305264497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717697644930112870176331 11576546467395169305264497)
              ·
                refine ⟨8682409850546376978948373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11576546467395169305264497 8682409850546376978948373)
                ·
                  refine ⟨406987961744361420888205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8682409850546376978948373 406987961744361420888205)
                  ·
                    rfl

theorem cell22_3566728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_3566728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566728 prefixEnd_3566728 := by exact prefixLift 3566728
  have htrace : WordTrace (prefixWord ++ tailWord_3566728) baseStart_3566728 baseEnd_3566728 := by
    simpa [prefixWord, tailWord_3566728, baseEnd_3566728] using wordTrace_append hprefix tailTrace_3566728
  have hstable : (prefixWord ++ tailWord_3566728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566728).length < 2 ^ (prefixWord ++ tailWord_3566728).sum := by decide
  have hdescent : baseEnd_3566728 < baseStart_3566728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566739 : List Nat := [1, 1, 1, 2, 1, 2, 4, 10]
def baseStart_3566739 : Nat := 118140960795 + 3566739 * 2 ^ 59
def prefixEnd_3566739 : Nat := 4983230072969 + 3 ^ 40 * 3566739 * 2
def baseEnd_3566739 : Nat := 135663072306431544515509

theorem tailTrace_3566739 : CollatzResearch.WordTrace tailWord_3566739 prefixEnd_3566739 135663072306431544515509 := by
  unfold tailWord_3566739
  simp only [CollatzResearch.WordTrace]
  refine ⟨130089658625321228369359271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86726439083547485579572847 130089658625321228369359271)
  ·
    refine ⟨195134487937981842554038907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130089658625321228369359271 195134487937981842554038907)
    ·
      refine ⟨292701731906972763831058361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195134487937981842554038907 292701731906972763831058361)
      ·
        refine ⟨219526298930229572873293771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292701731906972763831058361 219526298930229572873293771)
        ·
          refine ⟨329289448395344359309940657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219526298930229572873293771 329289448395344359309940657)
          ·
            refine ⟨246967086296508269482455493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329289448395344359309940657 246967086296508269482455493)
            ·
              refine ⟨46306328680595300527960405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246967086296508269482455493 46306328680595300527960405)
              ·
                refine ⟨135663072306431544515509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46306328680595300527960405 135663072306431544515509)
                ·
                  rfl

theorem cell22_3566739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 10].length) (baseStart_3566739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566739 prefixEnd_3566739 := by exact prefixLift 3566739
  have htrace : WordTrace (prefixWord ++ tailWord_3566739) baseStart_3566739 baseEnd_3566739 := by
    simpa [prefixWord, tailWord_3566739, baseEnd_3566739] using wordTrace_append hprefix tailTrace_3566739
  have hstable : (prefixWord ++ tailWord_3566739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566739).length < 2 ^ (prefixWord ++ tailWord_3566739).sum := by decide
  have hdescent : baseEnd_3566739 < baseStart_3566739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566741 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_3566741 : Nat := 118140960795 + 3566741 * 2 ^ 59
def prefixEnd_3566741 : Nat := 4983230072969 + 3 ^ 40 * 3566741 * 2
def baseEnd_3566741 : Nat := 1220968335398756562089575

theorem tailTrace_3566741 : CollatzResearch.WordTrace tailWord_3566741 prefixEnd_3566741 1220968335398756562089575 := by
  unfold tailWord_3566741
  simp only [CollatzResearch.WordTrace]
  refine ⟨130089731571313982710932077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86726487714209321807288051 130089731571313982710932077)
  ·
    refine ⟨48783649339242743516599529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130089731571313982710932077 48783649339242743516599529)
    ·
      refine ⟨36587737004432057637449647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48783649339242743516599529 36587737004432057637449647)
      ·
        refine ⟨54881605506648086456174471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36587737004432057637449647 54881605506648086456174471)
        ·
          refine ⟨82322408259972129684261707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54881605506648086456174471 82322408259972129684261707)
          ·
            refine ⟨123483612389958194526392561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82322408259972129684261707 123483612389958194526392561)
            ·
              refine ⟨92612709292468645894794421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123483612389958194526392561 92612709292468645894794421)
              ·
                refine ⟨8682441496168935552636977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92612709292468645894794421 8682441496168935552636977)
                ·
                  refine ⟨6511831122126701664477733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8682441496168935552636977 6511831122126701664477733)
                  ·
                    refine ⟨1220968335398756562089575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6511831122126701664477733 1220968335398756562089575)
                    ·
                      rfl

theorem cell22_3566741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_3566741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566741 prefixEnd_3566741 := by exact prefixLift 3566741
  have htrace : WordTrace (prefixWord ++ tailWord_3566741) baseStart_3566741 baseEnd_3566741 := by
    simpa [prefixWord, tailWord_3566741, baseEnd_3566741] using wordTrace_append hprefix tailTrace_3566741
  have hstable : (prefixWord ++ tailWord_3566741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566741).length < 2 ^ (prefixWord ++ tailWord_3566741).sum := by decide
  have hdescent : baseEnd_3566741 < baseStart_3566741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566756 : List Nat := [2, 3, 1, 2, 3, 2, 9]
def baseStart_3566756 : Nat := 118140960795 + 3566756 * 2 ^ 59
def prefixEnd_3566756 : Nat := 4983230072969 + 3 ^ 40 * 3566756 * 2
def baseEnd_3566756 : Nat := 45221239637233389739427

theorem tailTrace_3566756 : CollatzResearch.WordTrace tailWord_3566756 prefixEnd_3566756 45221239637233389739427 := by
  unfold tailWord_3566756
  simp only [CollatzResearch.WordTrace]
  refine ⟨65045139333129820136364061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86726852444173093515152081 65045139333129820136364061)
  ·
    refine ⟨24391927249923682551136523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65045139333129820136364061 24391927249923682551136523)
    ·
      refine ⟨36587890874885523826704785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24391927249923682551136523 36587890874885523826704785)
      ·
        refine ⟨27440918156164142870028589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36587890874885523826704785 27440918156164142870028589)
        ·
          refine ⟨10290344308561553576260721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27440918156164142870028589 10290344308561553576260721)
          ·
            refine ⟨7717758231421165182195541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10290344308561553576260721 7717758231421165182195541)
            ·
              refine ⟨45221239637233389739427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7717758231421165182195541 45221239637233389739427)
              ·
                rfl

theorem cell22_3566756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 9].length) (baseStart_3566756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566756 prefixEnd_3566756 := by exact prefixLift 3566756
  have htrace : WordTrace (prefixWord ++ tailWord_3566756) baseStart_3566756 baseEnd_3566756 := by
    simpa [prefixWord, tailWord_3566756, baseEnd_3566756] using wordTrace_append hprefix tailTrace_3566756
  have hstable : (prefixWord ++ tailWord_3566756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566756).length < 2 ^ (prefixWord ++ tailWord_3566756).sum := by decide
  have hdescent : baseEnd_3566756 < baseStart_3566756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566835 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 5]
def baseStart_3566835 : Nat := 118140960795 + 3566835 * 2 ^ 59
def prefixEnd_3566835 : Nat := 4983230072969 + 3 ^ 40 * 3566835 * 2
def baseEnd_3566835 : Nat := 407000171173257216746429

theorem tailTrace_3566835 : CollatzResearch.WordTrace tailWord_3566835 prefixEnd_3566835 407000171173257216746429 := by
  unfold tailWord_3566835
  simp only [CollatzResearch.WordTrace]
  refine ⟨130093160032973436764853959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86728773355315624509902639 130093160032973436764853959)
  ·
    refine ⟨195139740049460155147280939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130093160032973436764853959 195139740049460155147280939)
    ·
      refine ⟨292709610074190232720921409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195139740049460155147280939 292709610074190232720921409)
      ·
        refine ⟨219532207555642674540691057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292709610074190232720921409 219532207555642674540691057)
        ·
          refine ⟨164649155666732005905518293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219532207555642674540691057 164649155666732005905518293)
          ·
            refine ⟨3858964585939031388410585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 164649155666732005905518293 3858964585939031388410585)
            ·
              refine ⟨2894223439454273541307939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3858964585939031388410585 2894223439454273541307939)
              ·
                refine ⟨4341335159181410311961909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894223439454273541307939 4341335159181410311961909)
                ·
                  refine ⟨407000171173257216746429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4341335159181410311961909 407000171173257216746429)
                  ·
                    rfl

theorem cell22_3566835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 5].length) (baseStart_3566835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566835 prefixEnd_3566835 := by exact prefixLift 3566835
  have htrace : WordTrace (prefixWord ++ tailWord_3566835) baseStart_3566835 baseEnd_3566835 := by
    simpa [prefixWord, tailWord_3566835, baseEnd_3566835] using wordTrace_append hprefix tailTrace_3566835
  have hstable : (prefixWord ++ tailWord_3566835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566835).length < 2 ^ (prefixWord ++ tailWord_3566835).sum := by decide
  have hdescent : baseEnd_3566835 < baseStart_3566835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566865 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 1, 4]
def baseStart_3566865 : Nat := 118140960795 + 3566865 * 2 ^ 59
def prefixEnd_3566865 : Nat := 4983230072969 + 3 ^ 40 * 3566865 * 2
def baseEnd_3566865 : Nat := 1221010783132861571989195

theorem tailTrace_3566865 : CollatzResearch.WordTrace tailWord_3566865 prefixEnd_3566865 1221010783132861571989195 := by
  unfold tailWord_3566865
  simp only [CollatzResearch.WordTrace]
  refine ⟨130094254222864751888446049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86729502815243167925630699 130094254222864751888446049)
  ·
    refine ⟨97570690667148563916334537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130094254222864751888446049 97570690667148563916334537)
    ·
      refine ⟨73178018000361422937250903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97570690667148563916334537 73178018000361422937250903)
      ·
        refine ⟨109767027000542134405876355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73178018000361422937250903 109767027000542134405876355)
        ·
          refine ⟨164650540500813201608814533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109767027000542134405876355 164650540500813201608814533)
          ·
            refine ⟨30871976343902475301652725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164650540500813201608814533 30871976343902475301652725)
            ·
              refine ⟨2894247782240857059529943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30871976343902475301652725 2894247782240857059529943)
              ·
                refine ⟨4341371673361285589294915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894247782240857059529943 4341371673361285589294915)
                ·
                  refine ⟨6512057510041928383942373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341371673361285589294915 6512057510041928383942373)
                  ·
                    refine ⟨1221010783132861571989195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6512057510041928383942373 1221010783132861571989195)
                    ·
                      rfl

theorem cell22_3566865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_3566865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3566865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3566865 prefixEnd_3566865 := by exact prefixLift 3566865
  have htrace : WordTrace (prefixWord ++ tailWord_3566865) baseStart_3566865 baseEnd_3566865 := by
    simpa [prefixWord, tailWord_3566865, baseEnd_3566865] using wordTrace_append hprefix tailTrace_3566865
  have hstable : (prefixWord ++ tailWord_3566865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566865).length < 2 ^ (prefixWord ++ tailWord_3566865).sum := by decide
  have hdescent : baseEnd_3566865 < baseStart_3566865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567047 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 2, 3]
def baseStart_3567047 : Nat := 118140960795 + 3567047 * 2 ^ 59
def prefixEnd_3567047 : Nat := 4983230072969 + 3 ^ 40 * 3567047 * 2
def baseEnd_3567047 : Nat := 1221073085452273763938637

theorem tailTrace_3567047 : CollatzResearch.WordTrace tailWord_3567047 prefixEnd_3567047 1221073085452273763938637 := by
  unfold tailWord_3567047
  simp only [CollatzResearch.WordTrace]
  refine ⟨130100892308205396971571395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86733928205470264647714263 130100892308205396971571395)
  ·
    refine ⟨195151338462308095457357093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130100892308205396971571395 195151338462308095457357093)
    ·
      refine ⟨36590875961682767898254455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195151338462308095457357093 36590875961682767898254455)
      ·
        refine ⟨54886313942524151847381683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36590875961682767898254455 54886313942524151847381683)
        ·
          refine ⟨82329470913786227771072525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54886313942524151847381683 82329470913786227771072525)
          ·
            refine ⟨30873551592669835414152197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82329470913786227771072525 30873551592669835414152197)
            ·
              refine ⟨5788790923625594140153537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30873551592669835414152197 5788790923625594140153537)
              ·
                refine ⟨4341593192719195605115153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5788790923625594140153537 4341593192719195605115153)
                ·
                  refine ⟨3256194894539396703836365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4341593192719195605115153 3256194894539396703836365)
                  ·
                    refine ⟨1221073085452273763938637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3256194894539396703836365 1221073085452273763938637)
                    ·
                      rfl

theorem cell22_3567047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_3567047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567047 prefixEnd_3567047 := by exact prefixLift 3567047
  have htrace : WordTrace (prefixWord ++ tailWord_3567047) baseStart_3567047 baseEnd_3567047 := by
    simpa [prefixWord, tailWord_3567047, baseEnd_3567047] using wordTrace_append hprefix tailTrace_3567047
  have hstable : (prefixWord ++ tailWord_3567047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567047).length < 2 ^ (prefixWord ++ tailWord_3567047).sum := by decide
  have hdescent : baseEnd_3567047 < baseStart_3567047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567077 : List Nat := [1, 3, 1, 5, 1, 2, 3, 6]
def baseStart_3567077 : Nat := 118140960795 + 3567077 * 2 ^ 59
def prefixEnd_3567077 : Nat := 4983230072969 + 3 ^ 40 * 3567077 * 2
def baseEnd_3567077 : Nat := 135675928340595965076505

theorem tailTrace_3567077 : CollatzResearch.WordTrace tailWord_3567077 prefixEnd_3567077 135675928340595965076505 := by
  unfold tailWord_3567077
  simp only [CollatzResearch.WordTrace]
  refine ⟨130101986498096712095163485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86734657665397808063442323 130101986498096712095163485)
  ·
    refine ⟨48788244936786267035686307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130101986498096712095163485 48788244936786267035686307)
    ·
      refine ⟨73182367405179400553529461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48788244936786267035686307 73182367405179400553529461)
      ·
        refine ⟨6860846944235568801893387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73182367405179400553529461 6860846944235568801893387)
        ·
          refine ⟨10291270416353353202840081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6860846944235568801893387 10291270416353353202840081)
          ·
            refine ⟨7718452812265014902130061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10291270416353353202840081 7718452812265014902130061)
            ·
              refine ⟨2894419804599380588298773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7718452812265014902130061 2894419804599380588298773)
              ·
                refine ⟨135675928340595965076505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2894419804599380588298773 135675928340595965076505)
                ·
                  rfl

theorem cell22_3567077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 6].length) (baseStart_3567077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567077 prefixEnd_3567077 := by exact prefixLift 3567077
  have htrace : WordTrace (prefixWord ++ tailWord_3567077) baseStart_3567077 baseEnd_3567077 := by
    simpa [prefixWord, tailWord_3567077, baseEnd_3567077] using wordTrace_append hprefix tailTrace_3567077
  have hstable : (prefixWord ++ tailWord_3567077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567077).length < 2 ^ (prefixWord ++ tailWord_3567077).sum := by decide
  have hdescent : baseEnd_3567077 < baseStart_3567077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567135 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 3, 4]
def baseStart_3567135 : Nat := 118140960795 + 3567135 * 2 ^ 59
def prefixEnd_3567135 : Nat := 4983230072969 + 3 ^ 40 * 3567135 * 2
def baseEnd_3567135 : Nat := 1221103209650670867738367

theorem tailTrace_3567135 : CollatzResearch.WordTrace tailWord_3567135 prefixEnd_3567135 1221103209650670867738367 := by
  unfold tailWord_3567135
  simp only [CollatzResearch.WordTrace]
  refine ⟨130104101931886588000774859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86736067954591058667183239 130104101931886588000774859)
  ·
    refine ⟨195156152897829882001162289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130104101931886588000774859 195156152897829882001162289)
    ·
      refine ⟨146367114673372411500871717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195156152897829882001162289 146367114673372411500871717)
      ·
        refine ⟨27443834001257327156413447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146367114673372411500871717 27443834001257327156413447)
        ·
          refine ⟨41165751001885990734620171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27443834001257327156413447 41165751001885990734620171)
          ·
            refine ⟨61748626502828986101930257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41165751001885990734620171 61748626502828986101930257)
            ·
              refine ⟨46311469877121739576447693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61748626502828986101930257 46311469877121739576447693)
              ·
                refine ⟨17366801203920652341167885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46311469877121739576447693 17366801203920652341167885)
                ·
                  refine ⟨6512550451470244627937957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17366801203920652341167885 6512550451470244627937957)
                  ·
                    refine ⟨1221103209650670867738367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6512550451470244627937957 1221103209650670867738367)
                    ·
                      rfl

theorem cell22_3567135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_3567135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567135 prefixEnd_3567135 := by exact prefixLift 3567135
  have htrace : WordTrace (prefixWord ++ tailWord_3567135) baseStart_3567135 baseEnd_3567135 := by
    simpa [prefixWord, tailWord_3567135, baseEnd_3567135] using wordTrace_append hprefix tailTrace_3567135
  have hstable : (prefixWord ++ tailWord_3567135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567135).length < 2 ^ (prefixWord ++ tailWord_3567135).sum := by decide
  have hdescent : baseEnd_3567135 < baseStart_3567135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567167 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 6]
def baseStart_3567167 : Nat := 118140960795 + 3567167 * 2 ^ 59
def prefixEnd_3567167 : Nat := 4983230072969 + 3 ^ 40 * 3567167 * 2
def baseEnd_3567167 : Nat := 407038054634877816979423

theorem tailTrace_3567167 : CollatzResearch.WordTrace tailWord_3567167 prefixEnd_3567167 407038054634877816979423 := by
  unfold tailWord_3567167
  simp only [CollatzResearch.WordTrace]
  refine ⟨130105269067770657465939755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86736846045180438310626503 130105269067770657465939755)
  ·
    refine ⟨195157903601655986198909633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130105269067770657465939755 195157903601655986198909633)
    ·
      refine ⟨146368427701241989649182225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195157903601655986198909633 146368427701241989649182225)
      ·
        refine ⟨109776320775931492236886669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146368427701241989649182225 109776320775931492236886669)
        ·
          refine ⟨41166120290974309588832501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109776320775931492236886669 41166120290974309588832501)
          ·
            refine ⟨3859323777278841523953047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41166120290974309588832501 3859323777278841523953047)
            ·
              refine ⟨5788985665918262285929571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3859323777278841523953047 5788985665918262285929571)
              ·
                refine ⟨8683478498877393428894357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788985665918262285929571 8683478498877393428894357)
                ·
                  refine ⟨407038054634877816979423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8683478498877393428894357 407038054634877816979423)
                  ·
                    rfl

theorem cell22_3567167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 6].length) (baseStart_3567167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567167 prefixEnd_3567167 := by exact prefixLift 3567167
  have htrace : WordTrace (prefixWord ++ tailWord_3567167) baseStart_3567167 baseEnd_3567167 := by
    simpa [prefixWord, tailWord_3567167, baseEnd_3567167] using wordTrace_append hprefix tailTrace_3567167
  have hstable : (prefixWord ++ tailWord_3567167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567167).length < 2 ^ (prefixWord ++ tailWord_3567167).sum := by decide
  have hdescent : baseEnd_3567167 < baseStart_3567167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567225 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_3567225 : Nat := 118140960795 + 3567225 * 2 ^ 59
def prefixEnd_3567225 : Nat := 4983230072969 + 3 ^ 40 * 3567225 * 2
def baseEnd_3567225 : Nat := 1221134018489940632988091

theorem tailTrace_3567225 : CollatzResearch.WordTrace tailWord_3567225 prefixEnd_3567225 1221134018489940632988091 := by
  unfold tailWord_3567225
  simp only [CollatzResearch.WordTrace]
  refine ⟨130107384501560533371551129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86738256334373688914367419 130107384501560533371551129)
  ·
    refine ⟨97580538376170400028663347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130107384501560533371551129 97580538376170400028663347)
    ·
      refine ⟨146370807564255600042995021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97580538376170400028663347 146370807564255600042995021)
      ·
        refine ⟨54889052836595850016123133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146370807564255600042995021 54889052836595850016123133)
        ·
          refine ⟨20583394813723443756046175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54889052836595850016123133 20583394813723443756046175)
          ·
            refine ⟨30875092220585165634069263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20583394813723443756046175 30875092220585165634069263)
            ·
              refine ⟨46312638330877748451103895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30875092220585165634069263 46312638330877748451103895)
              ·
                refine ⟨69468957496316622676655843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46312638330877748451103895 69468957496316622676655843)
                ·
                  refine ⟨104203436244474934014983765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69468957496316622676655843 104203436244474934014983765)
                  ·
                    refine ⟨1221134018489940632988091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104203436244474934014983765 1221134018489940632988091)
                    ·
                      rfl

theorem cell22_3567225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_3567225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567225 prefixEnd_3567225 := by exact prefixLift 3567225
  have htrace : WordTrace (prefixWord ++ tailWord_3567225) baseStart_3567225 baseEnd_3567225 := by
    simpa [prefixWord, tailWord_3567225, baseEnd_3567225] using wordTrace_append hprefix tailTrace_3567225
  have hstable : (prefixWord ++ tailWord_3567225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567225).length < 2 ^ (prefixWord ++ tailWord_3567225).sum := by decide
  have hdescent : baseEnd_3567225 < baseStart_3567225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567227 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 3, 3]
def baseStart_3567227 : Nat := 118140960795 + 3567227 * 2 ^ 59
def prefixEnd_3567227 : Nat := 4983230072969 + 3 ^ 40 * 3567227 * 2
def baseEnd_3567227 : Nat := 1221134703130813294438085

theorem tailTrace_3567227 : CollatzResearch.WordTrace tailWord_3567227 prefixEnd_3567227 1221134703130813294438085 := by
  unfold tailWord_3567227
  simp only [CollatzResearch.WordTrace]
  refine ⟨130107457447553287713123935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86738304965035525142082623 130107457447553287713123935)
  ·
    refine ⟨195161186171329931569685903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130107457447553287713123935 195161186171329931569685903)
    ·
      refine ⟨292741779256994897354528855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195161186171329931569685903 292741779256994897354528855)
      ·
        refine ⟨439112668885492346031793283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292741779256994897354528855 439112668885492346031793283)
        ·
          refine ⟨658669003328238519047689925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439112668885492346031793283 658669003328238519047689925)
          ·
            refine ⟨123500438124044722321441861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 658669003328238519047689925 123500438124044722321441861)
            ·
              refine ⟨23156332148258385435270349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123500438124044722321441861 23156332148258385435270349)
              ·
                refine ⟨8683624555596894538226381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23156332148258385435270349 8683624555596894538226381)
                ·
                  refine ⟨3256359208348835451834893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8683624555596894538226381 3256359208348835451834893)
                  ·
                    refine ⟨1221134703130813294438085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3256359208348835451834893 1221134703130813294438085)
                    ·
                      rfl

theorem cell22_3567227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 3].length) (baseStart_3567227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567227 prefixEnd_3567227 := by exact prefixLift 3567227
  have htrace : WordTrace (prefixWord ++ tailWord_3567227) baseStart_3567227 baseEnd_3567227 := by
    simpa [prefixWord, tailWord_3567227, baseEnd_3567227] using wordTrace_append hprefix tailTrace_3567227
  have hstable : (prefixWord ++ tailWord_3567227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567227).length < 2 ^ (prefixWord ++ tailWord_3567227).sum := by decide
  have hdescent : baseEnd_3567227 < baseStart_3567227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567278 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3567278 : Nat := 118140960795 + 3567278 * 2 ^ 59
def prefixEnd_3567278 : Nat := 4983230072969 + 3 ^ 40 * 3567278 * 2
def baseEnd_3567278 : Nat := 1221152161473066161412929

theorem tailTrace_3567278 : CollatzResearch.WordTrace tailWord_3567278 prefixEnd_3567278 1221152161473066161412929 := by
  unfold tailWord_3567278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16263664696296065427903811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86739545046912348948820325 16263664696296065427903811)
  ·
    refine ⟨24395497044444098141855717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16263664696296065427903811 24395497044444098141855717)
    ·
      refine ⟨4574155695833268401597947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24395497044444098141855717 4574155695833268401597947)
      ·
        refine ⟨6861233543749902602396921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4574155695833268401597947 6861233543749902602396921)
        ·
          refine ⟨5145925157812426951797691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6861233543749902602396921 5145925157812426951797691)
          ·
            refine ⟨7718887736718640427696537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5145925157812426951797691 7718887736718640427696537)
            ·
              refine ⟨5789165802538980320772403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7718887736718640427696537 5789165802538980320772403)
              ·
                refine ⟨8683748703808470481158605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5789165802538980320772403 8683748703808470481158605)
                ·
                  refine ⟨3256405763928176430434477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8683748703808470481158605 3256405763928176430434477)
                  ·
                    refine ⟨1221152161473066161412929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3256405763928176430434477 1221152161473066161412929)
                    ·
                      rfl

theorem cell22_3567278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3567278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567278 prefixEnd_3567278 := by exact prefixLift 3567278
  have htrace : WordTrace (prefixWord ++ tailWord_3567278) baseStart_3567278 baseEnd_3567278 := by
    simpa [prefixWord, tailWord_3567278, baseEnd_3567278] using wordTrace_append hprefix tailTrace_3567278
  have hstable : (prefixWord ++ tailWord_3567278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567278).length < 2 ^ (prefixWord ++ tailWord_3567278).sum := by decide
  have hdescent : baseEnd_3567278 < baseStart_3567278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567304 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 1, 4]
def baseStart_3567304 : Nat := 118140960795 + 3567304 * 2 ^ 59
def prefixEnd_3567304 : Nat := 4983230072969 + 3 ^ 40 * 3567304 * 2
def baseEnd_3567304 : Nat := 1221161061804410760262849

theorem tailTrace_3567304 : CollatzResearch.WordTrace tailWord_3567304 prefixEnd_3567304 1221161061804410760262849 := by
  unfold tailWord_3567304
  simp only [CollatzResearch.WordTrace]
  refine ⟨65055132934137164931838483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86740177245516219909117977 65055132934137164931838483)
  ·
    refine ⟨97582699401205747397757725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65055132934137164931838483 97582699401205747397757725)
    ·
      refine ⟨36593512275452155274159147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97582699401205747397757725 36593512275452155274159147)
      ·
        refine ⟨54890268413178232911238721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36593512275452155274159147 54890268413178232911238721)
        ·
          refine ⟨41167701309883674683429041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54890268413178232911238721 41167701309883674683429041)
          ·
            refine ⟨30875775982412756012571781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41167701309883674683429041 30875775982412756012571781)
            ·
              refine ⟨5789207996702391752357209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30875775982412756012571781 5789207996702391752357209)
              ·
                refine ⟨4341905997526793814267907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5789207996702391752357209 4341905997526793814267907)
                ·
                  refine ⟨6512858996290190721401861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341905997526793814267907 6512858996290190721401861)
                  ·
                    refine ⟨1221161061804410760262849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6512858996290190721401861 1221161061804410760262849)
                    ·
                      rfl

theorem cell22_3567304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_3567304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567304 prefixEnd_3567304 := by exact prefixLift 3567304
  have htrace : WordTrace (prefixWord ++ tailWord_3567304) baseStart_3567304 baseEnd_3567304 := by
    simpa [prefixWord, tailWord_3567304, baseEnd_3567304] using wordTrace_append hprefix tailTrace_3567304
  have hstable : (prefixWord ++ tailWord_3567304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567304).length < 2 ^ (prefixWord ++ tailWord_3567304).sum := by decide
  have hdescent : baseEnd_3567304 < baseStart_3567304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567351 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 2, 3]
def baseStart_3567351 : Nat := 118140960795 + 3567351 * 2 ^ 59
def prefixEnd_3567351 : Nat := 4983230072969 + 3 ^ 40 * 3567351 * 2
def baseEnd_3567351 : Nat := 1221177150864918304337705

theorem tailTrace_3567351 : CollatzResearch.WordTrace tailWord_3567351 prefixEnd_3567351 1221177150864918304337705 := by
  unfold tailWord_3567351
  simp only [CollatzResearch.WordTrace]
  refine ⟨130111980099104056890637907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86741320066069371260425271 130111980099104056890637907)
  ·
    refine ⟨195167970148656085335956861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130111980099104056890637907 195167970148656085335956861)
    ·
      refine ⟨73187988805746032000983823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195167970148656085335956861 73187988805746032000983823)
      ·
        refine ⟨109781983208619048001475735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73187988805746032000983823 109781983208619048001475735)
        ·
          refine ⟨164672974812928572002213603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109781983208619048001475735 164672974812928572002213603)
          ·
            refine ⟨247009462219392858003320405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164672974812928572002213603 247009462219392858003320405)
            ·
              refine ⟨2894642135383510054726411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 247009462219392858003320405 2894642135383510054726411)
              ·
                refine ⟨4341963203075265082089617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894642135383510054726411 4341963203075265082089617)
                ·
                  refine ⟨3256472402306448811567213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4341963203075265082089617 3256472402306448811567213)
                  ·
                    refine ⟨1221177150864918304337705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3256472402306448811567213 1221177150864918304337705)
                    ·
                      rfl

theorem cell22_3567351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_3567351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567351 prefixEnd_3567351 := by exact prefixLift 3567351
  have htrace : WordTrace (prefixWord ++ tailWord_3567351) baseStart_3567351 baseEnd_3567351 := by
    simpa [prefixWord, tailWord_3567351, baseEnd_3567351] using wordTrace_append hprefix tailTrace_3567351
  have hstable : (prefixWord ++ tailWord_3567351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567351).length < 2 ^ (prefixWord ++ tailWord_3567351).sum := by decide
  have hdescent : baseEnd_3567351 < baseStart_3567351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567407 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 2, 5]
def baseStart_3567407 : Nat := 118140960795 + 3567407 * 2 ^ 59
def prefixEnd_3567407 : Nat := 4983230072969 + 3 ^ 40 * 3567407 * 2
def baseEnd_3567407 : Nat := 1221196320809352824937533

theorem tailTrace_3567407 : CollatzResearch.WordTrace tailWord_3567407 prefixEnd_3567407 1221196320809352824937533 := by
  unfold tailWord_3567407
  simp only [CollatzResearch.WordTrace]
  refine ⟨130114022586901178454676475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86742681724600785636450983 130114022586901178454676475)
  ·
    refine ⟨195171033880351767682014713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130114022586901178454676475 195171033880351767682014713)
    ·
      refine ⟨146378275410263825761511035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195171033880351767682014713 146378275410263825761511035)
      ·
        refine ⟨219567413115395738642266553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146378275410263825761511035 219567413115395738642266553)
        ·
          refine ⟨164675559836546803981699915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219567413115395738642266553 164675559836546803981699915)
          ·
            refine ⟨247013339754820205972549873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164675559836546803981699915 247013339754820205972549873)
            ·
              refine ⟨185260004816115154479412405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247013339754820205972549873 185260004816115154479412405)
              ·
                refine ⟨17368125451510795732444913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185260004816115154479412405 17368125451510795732444913)
                ·
                  refine ⟨13026094088633096799333685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17368125451510795732444913 13026094088633096799333685)
                  ·
                    refine ⟨1221196320809352824937533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13026094088633096799333685 1221196320809352824937533)
                    ·
                      rfl

theorem cell22_3567407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_3567407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567407 prefixEnd_3567407 := by exact prefixLift 3567407
  have htrace : WordTrace (prefixWord ++ tailWord_3567407) baseStart_3567407 baseEnd_3567407 := by
    simpa [prefixWord, tailWord_3567407, baseEnd_3567407] using wordTrace_append hprefix tailTrace_3567407
  have hstable : (prefixWord ++ tailWord_3567407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567407).length < 2 ^ (prefixWord ++ tailWord_3567407).sum := by decide
  have hdescent : baseEnd_3567407 < baseStart_3567407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567409 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 5]
def baseStart_3567409 : Nat := 118140960795 + 3567409 * 2 ^ 59
def prefixEnd_3567409 : Nat := 4983230072969 + 3 ^ 40 * 3567409 * 2
def baseEnd_3567409 : Nat := 407065668483408495462509

theorem tailTrace_3567409 : CollatzResearch.WordTrace tailWord_3567409 prefixEnd_3567409 407065668483408495462509 := by
  unfold tailWord_3567409
  simp only [CollatzResearch.WordTrace]
  refine ⟨130114095532893932796249281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86742730355262621864166187 130114095532893932796249281)
  ·
    refine ⟨97585571649670449597186961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130114095532893932796249281 97585571649670449597186961)
    ·
      refine ⟨73189178737252837197890221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97585571649670449597186961 73189178737252837197890221)
      ·
        refine ⟨27445942026469813949208833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73189178737252837197890221 27445942026469813949208833)
        ·
          refine ⟨20584456519852360461906625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27445942026469813949208833 20584456519852360461906625)
          ·
            refine ⟨15438342389889270346429969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20584456519852360461906625 15438342389889270346429969)
            ·
              refine ⟨11578756792416952759822477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15438342389889270346429969 11578756792416952759822477)
              ·
                refine ⟨4342033797156357284933429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11578756792416952759822477 4342033797156357284933429)
                ·
                  refine ⟨407065668483408495462509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4342033797156357284933429 407065668483408495462509)
                  ·
                    rfl

theorem cell22_3567409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_3567409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567409 prefixEnd_3567409 := by exact prefixLift 3567409
  have htrace : WordTrace (prefixWord ++ tailWord_3567409) baseStart_3567409 baseEnd_3567409 := by
    simpa [prefixWord, tailWord_3567409, baseEnd_3567409] using wordTrace_append hprefix tailTrace_3567409
  have hstable : (prefixWord ++ tailWord_3567409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567409).length < 2 ^ (prefixWord ++ tailWord_3567409).sum := by decide
  have hdescent : baseEnd_3567409 < baseStart_3567409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567516 : List Nat := [2, 2, 3, 3, 1, 2, 2, 7]
def baseStart_3567516 : Nat := 118140960795 + 3567516 * 2 ^ 59
def prefixEnd_3567516 : Nat := 4983230072969 + 3 ^ 40 * 3567516 * 2
def baseEnd_3567516 : Nat := 135692625970768097106911

theorem tailTrace_3567516 : CollatzResearch.WordTrace tailWord_3567516 prefixEnd_3567516 135692625970768097106911 := by
  unfold tailWord_3567516
  simp only [CollatzResearch.WordTrace]
  refine ⟨65058999071753145035197201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86745332095670860046929601 65058999071753145035197201)
  ·
    refine ⟨48794249303814858776397901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65058999071753145035197201 48794249303814858776397901)
    ·
      refine ⟨18297843488930572041149213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48794249303814858776397901 18297843488930572041149213)
      ·
        refine ⟨6861691308348964515430955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18297843488930572041149213 6861691308348964515430955)
        ·
          refine ⟨10292536962523446773146433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6861691308348964515430955 10292536962523446773146433)
          ·
            refine ⟨7719402721892585079859825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10292536962523446773146433 7719402721892585079859825)
            ·
              refine ⟨5789552041419438809894869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7719402721892585079859825 5789552041419438809894869)
              ·
                refine ⟨135692625970768097106911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5789552041419438809894869 135692625970768097106911)
                ·
                  rfl

theorem cell22_3567516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 7].length) (baseStart_3567516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567516 prefixEnd_3567516 := by exact prefixLift 3567516
  have htrace : WordTrace (prefixWord ++ tailWord_3567516) baseStart_3567516 baseEnd_3567516 := by
    simpa [prefixWord, tailWord_3567516, baseEnd_3567516] using wordTrace_append hprefix tailTrace_3567516
  have hstable : (prefixWord ++ tailWord_3567516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567516).length < 2 ^ (prefixWord ++ tailWord_3567516).sum := by decide
  have hdescent : baseEnd_3567516 < baseStart_3567516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567559 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3567559 : Nat := 118140960795 + 3567559 * 2 ^ 59
def prefixEnd_3567559 : Nat := 4983230072969 + 3 ^ 40 * 3567559 * 2
def baseEnd_3567559 : Nat := 1221248353515675095137067

theorem tailTrace_3567559 : CollatzResearch.WordTrace tailWord_3567559 prefixEnd_3567559 1221248353515675095137067 := by
  unfold tailWord_3567559
  simp only [CollatzResearch.WordTrace]
  refine ⟨130119566482350508414209731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86746377654900338942806487 130119566482350508414209731)
  ·
    refine ⟨195179349723525762621314597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130119566482350508414209731 195179349723525762621314597)
    ·
      refine ⟨36596128073161080491496487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195179349723525762621314597 36596128073161080491496487)
      ·
        refine ⟨54894192109741620737244731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36596128073161080491496487 54894192109741620737244731)
        ·
          refine ⟨82341288164612431105867097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54894192109741620737244731 82341288164612431105867097)
          ·
            refine ⟨61755966123459323329400323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82341288164612431105867097 61755966123459323329400323)
            ·
              refine ⟨92633949185188984994100485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61755966123459323329400323 92633949185188984994100485)
              ·
                refine ⟨17368865472222934686393841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92633949185188984994100485 17368865472222934686393841)
                ·
                  refine ⟨13026649104167201014795381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17368865472222934686393841 13026649104167201014795381)
                  ·
                    refine ⟨1221248353515675095137067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13026649104167201014795381 1221248353515675095137067)
                    ·
                      rfl

theorem cell22_3567559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3567559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567559 prefixEnd_3567559 := by exact prefixLift 3567559
  have htrace : WordTrace (prefixWord ++ tailWord_3567559) baseStart_3567559 baseEnd_3567559 := by
    simpa [prefixWord, tailWord_3567559, baseEnd_3567559] using wordTrace_append hprefix tailTrace_3567559
  have hstable : (prefixWord ++ tailWord_3567559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567559).length < 2 ^ (prefixWord ++ tailWord_3567559).sum := by decide
  have hdescent : baseEnd_3567559 < baseStart_3567559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567608 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 1, 4]
def baseStart_3567608 : Nat := 118140960795 + 3567608 * 2 ^ 59
def prefixEnd_3567608 : Nat := 4983230072969 + 3 ^ 40 * 3567608 * 2
def baseEnd_3567608 : Nat := 1221265127217055300661917

theorem tailTrace_3567608 : CollatzResearch.WordTrace tailWord_3567608 prefixEnd_3567608 1221265127217055300661917 := by
  unfold tailWord_3567608
  simp only [CollatzResearch.WordTrace]
  refine ⟨65060676829586494891371739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86747569106115326521828985 65060676829586494891371739)
  ·
    refine ⟨97591015244379742337057609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65060676829586494891371739 97591015244379742337057609)
    ·
      refine ⟨73193261433284806752793207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97591015244379742337057609 73193261433284806752793207)
      ·
        refine ⟨109789892149927210129189811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73193261433284806752793207 109789892149927210129189811)
        ·
          refine ⟨164684838224890815193784717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109789892149927210129189811 164684838224890815193784717)
          ·
            refine ⟨61756814334334055697669269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164684838224890815193784717 61756814334334055697669269)
            ·
              refine ⟨2894850671921908860828247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61756814334334055697669269 2894850671921908860828247)
              ·
                refine ⟨4342276007882863291242371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894850671921908860828247 4342276007882863291242371)
                ·
                  refine ⟨6513414011824294936863557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342276007882863291242371 6513414011824294936863557)
                  ·
                    refine ⟨1221265127217055300661917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6513414011824294936863557 1221265127217055300661917)
                    ·
                      rfl

theorem cell22_3567608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_3567608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567608 prefixEnd_3567608 := by exact prefixLift 3567608
  have htrace : WordTrace (prefixWord ++ tailWord_3567608) baseStart_3567608 baseEnd_3567608 := by
    simpa [prefixWord, tailWord_3567608, baseEnd_3567608] using wordTrace_append hprefix tailTrace_3567608
  have hstable : (prefixWord ++ tailWord_3567608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567608).length < 2 ^ (prefixWord ++ tailWord_3567608).sum := by decide
  have hdescent : baseEnd_3567608 < baseStart_3567608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567623 : List Nat := [1, 1, 4, 3, 1, 2, 2, 4, 4]
def baseStart_3567623 : Nat := 118140960795 + 3567623 * 2 ^ 59
def prefixEnd_3567623 : Nat := 4983230072969 + 3 ^ 40 * 3567623 * 2
def baseEnd_3567623 : Nat := 407090087341200087178957

theorem tailTrace_3567623 : CollatzResearch.WordTrace tailWord_3567623 prefixEnd_3567623 407090087341200087178957 := by
  unfold tailWord_3567623
  simp only [CollatzResearch.WordTrace]
  refine ⟨130121900754118647344539523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86747933836079098229693015 130121900754118647344539523)
  ·
    refine ⟨195182851131177971016809285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130121900754118647344539523 195182851131177971016809285)
    ·
      refine ⟨36596784587095869565651741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195182851131177971016809285 36596784587095869565651741)
      ·
        refine ⟨13723794220160951087119403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36596784587095869565651741 13723794220160951087119403)
        ·
          refine ⟨20585691330241426630679105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13723794220160951087119403 20585691330241426630679105)
          ·
            refine ⟨15439268497681069973009329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20585691330241426630679105 15439268497681069973009329)
            ·
              refine ⟨11579451373260802479756997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15439268497681069973009329 11579451373260802479756997)
              ·
                refine ⟨2171147132486400464954437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11579451373260802479756997 2171147132486400464954437)
                ·
                  refine ⟨407090087341200087178957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2171147132486400464954437 407090087341200087178957)
                  ·
                    rfl

theorem cell22_3567623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 4].length) (baseStart_3567623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567623 prefixEnd_3567623 := by exact prefixLift 3567623
  have htrace : WordTrace (prefixWord ++ tailWord_3567623) baseStart_3567623 baseEnd_3567623 := by
    simpa [prefixWord, tailWord_3567623, baseEnd_3567623] using wordTrace_append hprefix tailTrace_3567623
  have hstable : (prefixWord ++ tailWord_3567623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567623).length < 2 ^ (prefixWord ++ tailWord_3567623).sum := by decide
  have hdescent : baseEnd_3567623 < baseStart_3567623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567629 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3567629 : Nat := 118140960795 + 3567629 * 2 ^ 59
def prefixEnd_3567629 : Nat := 4983230072969 + 3 ^ 40 * 3567629 * 2
def baseEnd_3567629 : Nat := 407090771982072748628951

theorem tailTrace_3567629 : CollatzResearch.WordTrace tailWord_3567629 prefixEnd_3567629 407090771982072748628951 := by
  unfold tailWord_3567629
  simp only [CollatzResearch.WordTrace]
  refine ⟨130122119592096910369257941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86748079728064606912838627 130122119592096910369257941)
  ·
    refine ⟨3049737177939771336779483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 130122119592096910369257941 3049737177939771336779483)
    ·
      refine ⟨4574605766909657005169225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3049737177939771336779483 4574605766909657005169225)
      ·
        refine ⟨3430954325182242753876919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4574605766909657005169225 3430954325182242753876919)
        ·
          refine ⟨5146431487773364130815379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3430954325182242753876919 5146431487773364130815379)
          ·
            refine ⟨7719647231660046196223069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5146431487773364130815379 7719647231660046196223069)
            ·
              refine ⟨2894867711872517323583651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7719647231660046196223069 2894867711872517323583651)
              ·
                refine ⟨4342301567808775985375477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894867711872517323583651 4342301567808775985375477)
                ·
                  refine ⟨407090771982072748628951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4342301567808775985375477 407090771982072748628951)
                  ·
                    rfl

theorem cell22_3567629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3567629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567629 prefixEnd_3567629 := by exact prefixLift 3567629
  have htrace : WordTrace (prefixWord ++ tailWord_3567629) baseStart_3567629 baseEnd_3567629 := by
    simpa [prefixWord, tailWord_3567629, baseEnd_3567629] using wordTrace_append hprefix tailTrace_3567629
  have hstable : (prefixWord ++ tailWord_3567629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567629).length < 2 ^ (prefixWord ++ tailWord_3567629).sum := by decide
  have hdescent : baseEnd_3567629 < baseStart_3567629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567734 : List Nat := [5, 1, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_3567734 : Nat := 118140960795 + 3567734 * 2 ^ 59
def prefixEnd_3567734 : Nat := 4983230072969 + 3 ^ 40 * 3567734 * 2
def baseEnd_3567734 : Nat := 1221308259592032972011531

theorem tailTrace_3567734 : CollatzResearch.WordTrace tailWord_3567734 prefixEnd_3567734 1221308259592032972011531 := by
  unfold tailWord_3567734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8132871828544782081364391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86750632837811008867886837 8132871828544782081364391)
  ·
    refine ⟨12199307742817173122046587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8132871828544782081364391 12199307742817173122046587)
    ·
      refine ⟨18298961614225759683069881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12199307742817173122046587 18298961614225759683069881)
      ·
        refine ⟨13724221210669319762302411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18298961614225759683069881 13724221210669319762302411)
        ·
          refine ⟨20586331816003979643453617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13724221210669319762302411 20586331816003979643453617)
          ·
            refine ⟨15439748862002984732590213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20586331816003979643453617 15439748862002984732590213)
            ·
              refine ⟨2894952911625559637360665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15439748862002984732590213 2894952911625559637360665)
              ·
                refine ⟨2171214683719169728020499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2894952911625559637360665 2171214683719169728020499)
                ·
                  refine ⟨3256822025578754592030749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171214683719169728020499 3256822025578754592030749)
                  ·
                    refine ⟨1221308259592032972011531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3256822025578754592030749 1221308259592032972011531)
                    ·
                      rfl

theorem cell22_3567734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_3567734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567734 prefixEnd_3567734 := by exact prefixLift 3567734
  have htrace : WordTrace (prefixWord ++ tailWord_3567734) baseStart_3567734 baseEnd_3567734 := by
    simpa [prefixWord, tailWord_3567734, baseEnd_3567734] using wordTrace_append hprefix tailTrace_3567734
  have hstable : (prefixWord ++ tailWord_3567734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567734).length < 2 ^ (prefixWord ++ tailWord_3567734).sum := by decide
  have hdescent : baseEnd_3567734 < baseStart_3567734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567771 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 6, 4]
def baseStart_3567771 : Nat := 118140960795 + 3567771 * 2 ^ 59
def prefixEnd_3567771 : Nat := 4983230072969 + 3 ^ 40 * 3567771 * 2
def baseEnd_3567771 : Nat := 1221320925448177208836417

theorem tailTrace_3567771 : CollatzResearch.WordTrace tailWord_3567771 prefixEnd_3567771 1221320925448177208836417 := by
  unfold tailWord_3567771
  simp only [CollatzResearch.WordTrace]
  refine ⟨130127298757582468620927167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86751532505054979080618111 130127298757582468620927167)
  ·
    refine ⟨195190948136373702931390751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130127298757582468620927167 195190948136373702931390751)
    ·
      refine ⟨292786422204560554397086127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195190948136373702931390751 292786422204560554397086127)
      ·
        refine ⟨439179633306840831595629191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292786422204560554397086127 439179633306840831595629191)
        ·
          refine ⟨658769449960261247393443787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439179633306840831595629191 658769449960261247393443787)
          ·
            refine ⟨988154174940391871090165681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658769449960261247393443787 988154174940391871090165681)
            ·
              refine ⟨741115631205293903317624261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988154174940391871090165681 741115631205293903317624261)
              ·
                refine ⟨138959180850992606872054549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741115631205293903317624261 138959180850992606872054549)
                ·
                  refine ⟨6513711602390278447127557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138959180850992606872054549 6513711602390278447127557)
                  ·
                    refine ⟨1221320925448177208836417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6513711602390278447127557 1221320925448177208836417)
                    ·
                      rfl

theorem cell22_3567771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 4].length) (baseStart_3567771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567771 prefixEnd_3567771 := by exact prefixLift 3567771
  have htrace : WordTrace (prefixWord ++ tailWord_3567771) baseStart_3567771 baseEnd_3567771 := by
    simpa [prefixWord, tailWord_3567771, baseEnd_3567771] using wordTrace_append hprefix tailTrace_3567771
  have hstable : (prefixWord ++ tailWord_3567771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567771).length < 2 ^ (prefixWord ++ tailWord_3567771).sum := by decide
  have hdescent : baseEnd_3567771 < baseStart_3567771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567773 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_3567773 : Nat := 118140960795 + 3567773 * 2 ^ 59
def prefixEnd_3567773 : Nat := 4983230072969 + 3 ^ 40 * 3567773 * 2
def baseEnd_3567773 : Nat := 1221321610089049870286411

theorem tailTrace_3567773 : CollatzResearch.WordTrace tailWord_3567773 prefixEnd_3567773 1221321610089049870286411 := by
  unfold tailWord_3567773
  simp only [CollatzResearch.WordTrace]
  refine ⟨130127371703575222962499973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86751581135716815308333315 130127371703575222962499973)
  ·
    refine ⟨24398882194420354305468745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130127371703575222962499973 24398882194420354305468745)
    ·
      refine ⟨18299161645815265729101559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24398882194420354305468745 18299161645815265729101559)
      ·
        refine ⟨27448742468722898593652339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18299161645815265729101559 27448742468722898593652339)
        ·
          refine ⟨41173113703084347890478509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27448742468722898593652339 41173113703084347890478509)
          ·
            refine ⟨15439917638656630458929441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41173113703084347890478509 15439917638656630458929441)
            ·
              refine ⟨11579938228992472844197081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15439917638656630458929441 11579938228992472844197081)
              ·
                refine ⟨8684953671744354633147811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11579938228992472844197081 8684953671744354633147811)
                ·
                  refine ⟨13027430507616531949721717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8684953671744354633147811 13027430507616531949721717)
                  ·
                    refine ⟨1221321610089049870286411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13027430507616531949721717 1221321610089049870286411)
                    ·
                      rfl

theorem cell22_3567773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_3567773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567773 prefixEnd_3567773 := by exact prefixLift 3567773
  have htrace : WordTrace (prefixWord ++ tailWord_3567773) baseStart_3567773 baseEnd_3567773 := by
    simpa [prefixWord, tailWord_3567773, baseEnd_3567773] using wordTrace_append hprefix tailTrace_3567773
  have hstable : (prefixWord ++ tailWord_3567773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567773).length < 2 ^ (prefixWord ++ tailWord_3567773).sum := by decide
  have hdescent : baseEnd_3567773 < baseStart_3567773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567775 : List Nat := [1, 1, 2, 6, 1, 1, 1, 5, 4]
def baseStart_3567775 : Nat := 118140960795 + 3567775 * 2 ^ 59
def prefixEnd_3567775 : Nat := 4983230072969 + 3 ^ 40 * 3567775 * 2
def baseEnd_3567775 : Nat := 407107431576640843912135

theorem tailTrace_3567775 : CollatzResearch.WordTrace tailWord_3567775 prefixEnd_3567775 407107431576640843912135 := by
  unfold tailWord_3567775
  simp only [CollatzResearch.WordTrace]
  refine ⟨130127444649567977304072779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86751629766378651536048519 130127444649567977304072779)
  ·
    refine ⟨195191166974351965956109169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130127444649567977304072779 195191166974351965956109169)
    ·
      refine ⟨146393375230763974467081877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195191166974351965956109169 146393375230763974467081877)
      ·
        refine ⟨6862189463942061303144463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146393375230763974467081877 6862189463942061303144463)
        ·
          refine ⟨10293284195913091954716695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6862189463942061303144463 10293284195913091954716695)
          ·
            refine ⟨15439926293869637932075043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10293284195913091954716695 15439926293869637932075043)
            ·
              refine ⟨23159889440804456898112565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15439926293869637932075043 23159889440804456898112565)
              ·
                refine ⟨2171239635075417834198053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23159889440804456898112565 2171239635075417834198053)
                ·
                  refine ⟨407107431576640843912135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2171239635075417834198053 407107431576640843912135)
                  ·
                    rfl

theorem cell22_3567775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 4].length) (baseStart_3567775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567775 prefixEnd_3567775 := by exact prefixLift 3567775
  have htrace : WordTrace (prefixWord ++ tailWord_3567775) baseStart_3567775 baseEnd_3567775 := by
    simpa [prefixWord, tailWord_3567775, baseEnd_3567775] using wordTrace_append hprefix tailTrace_3567775
  have hstable : (prefixWord ++ tailWord_3567775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567775).length < 2 ^ (prefixWord ++ tailWord_3567775).sum := by decide
  have hdescent : baseEnd_3567775 < baseStart_3567775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567777 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 1, 4]
def baseStart_3567777 : Nat := 118140960795 + 3567777 * 2 ^ 59
def prefixEnd_3567777 : Nat := 4983230072969 + 3 ^ 40 * 3567777 * 2
def baseEnd_3567777 : Nat := 1221322979370795193186399

theorem tailTrace_3567777 : CollatzResearch.WordTrace tailWord_3567777 prefixEnd_3567777 1221322979370795193186399 := by
  unfold tailWord_3567777
  simp only [CollatzResearch.WordTrace]
  refine ⟨130127517595560731645645585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86751678397040487763763723 130127517595560731645645585)
  ·
    refine ⟨97595638196670548734234189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130127517595560731645645585 97595638196670548734234189)
    ·
      refine ⟨36598364323751455775337821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97595638196670548734234189 36598364323751455775337821)
      ·
        refine ⟨13724386621406795915751683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36598364323751455775337821 13724386621406795915751683)
        ·
          refine ⟨20586579932110193873627525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13724386621406795915751683 20586579932110193873627525)
          ·
            refine ⟨3859983737270661351305161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20586579932110193873627525 3859983737270661351305161)
            ·
              refine ⟨2894987802952996013478871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3859983737270661351305161 2894987802952996013478871)
              ·
                refine ⟨4342481704429494020218307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894987802952996013478871 4342481704429494020218307)
                ·
                  refine ⟨6513722556644241030327461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342481704429494020218307 6513722556644241030327461)
                  ·
                    refine ⟨1221322979370795193186399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6513722556644241030327461 1221322979370795193186399)
                    ·
                      rfl

theorem cell22_3567777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_3567777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567777 prefixEnd_3567777 := by exact prefixLift 3567777
  have htrace : WordTrace (prefixWord ++ tailWord_3567777) baseStart_3567777 baseEnd_3567777 := by
    simpa [prefixWord, tailWord_3567777, baseEnd_3567777] using wordTrace_append hprefix tailTrace_3567777
  have hstable : (prefixWord ++ tailWord_3567777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567777).length < 2 ^ (prefixWord ++ tailWord_3567777).sum := by decide
  have hdescent : baseEnd_3567777 < baseStart_3567777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
