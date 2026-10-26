import V185TrunkScan23Chunk1144

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6782556 : List Nat := [2, 2, 4, 1, 2, 1, 4, 2, 5]
def baseStart_6782556 : Nat := 118140960795 + 6782556 * 2 ^ 59
def prefixEnd_6782556 : Nat := 4983230072969 + 3 ^ 40 * 6782556 * 2
def baseEnd_6782556 : Nat := 386967921559607828017511

theorem tailTrace_6782556 : CollatzResearch.WordTrace tailWord_6782556 prefixEnd_6782556 386967921559607828017511 := by
  unfold tailWord_6782556
  simp only [CollatzResearch.WordTrace]
  refine ⟨123690070207982727593747761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164920093610643636791663681 123690070207982727593747761)
  ·
    refine ⟨92767552655987045695310821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123690070207982727593747761 92767552655987045695310821)
    ·
      refine ⟨17393916122997571067870779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92767552655987045695310821 17393916122997571067870779)
      ·
        refine ⟨26090874184496356601806169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17393916122997571067870779 26090874184496356601806169)
        ·
          refine ⟨19568155638372267451354627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26090874184496356601806169 19568155638372267451354627)
          ·
            refine ⟨29352233457558401177031941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19568155638372267451354627 29352233457558401177031941)
            ·
              refine ⟨5503543773292200220693489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29352233457558401177031941 5503543773292200220693489)
              ·
                refine ⟨4127657829969150165520117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5503543773292200220693489 4127657829969150165520117)
                ·
                  refine ⟨386967921559607828017511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4127657829969150165520117 386967921559607828017511)
                  ·
                    rfl

theorem cell23_6782556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_6782556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782556 prefixEnd_6782556 := by exact prefixLift 6782556
  have htrace : WordTrace (prefixWord ++ tailWord_6782556) baseStart_6782556 baseEnd_6782556 := by
    simpa [prefixWord, tailWord_6782556, baseEnd_6782556] using wordTrace_append hprefix tailTrace_6782556
  have hstable : (prefixWord ++ tailWord_6782556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782556).length < 2 ^ (prefixWord ++ tailWord_6782556).sum := by decide
  have hdescent : baseEnd_6782556 < baseStart_6782556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782589 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_6782589 : Nat := 118140960795 + 6782589 * 2 ^ 59
def prefixEnd_6782589 : Nat := 4983230072969 + 3 ^ 40 * 6782589 * 2
def baseEnd_6782589 : Nat := 3482728238898068823044947

theorem tailTrace_6782589 : CollatzResearch.WordTrace tailWord_6782589 prefixEnd_6782589 3482728238898068823044947 := by
  unfold tailWord_6782589
  simp only [CollatzResearch.WordTrace]
  refine ⟨247381344024845901823446821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164920896016563934548964547 247381344024845901823446821)
  ·
    refine ⟨46384002004658606591896279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247381344024845901823446821 46384002004658606591896279)
    ·
      refine ⟨69576003006987909887844419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46384002004658606591896279 69576003006987909887844419)
      ·
        refine ⟨104364004510481864831766629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69576003006987909887844419 104364004510481864831766629)
        ·
          refine ⟨19568250845715349655956243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104364004510481864831766629 19568250845715349655956243)
          ·
            refine ⟨29352376268573024483934365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19568250845715349655956243 29352376268573024483934365)
            ·
              refine ⟨11007141100714884181475387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29352376268573024483934365 11007141100714884181475387)
              ·
                refine ⟨16510711651072326272213081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11007141100714884181475387 16510711651072326272213081)
                ·
                  refine ⟨12383033738304244704159811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16510711651072326272213081 12383033738304244704159811)
                  ·
                    refine ⟨18574550607456367056239717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12383033738304244704159811 18574550607456367056239717)
                    ·
                      refine ⟨3482728238898068823044947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18574550607456367056239717 3482728238898068823044947)
                      ·
                        rfl

theorem cell23_6782589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_6782589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782589 prefixEnd_6782589 := by exact prefixLift 6782589
  have htrace : WordTrace (prefixWord ++ tailWord_6782589) baseStart_6782589 baseEnd_6782589 := by
    simpa [prefixWord, tailWord_6782589, baseEnd_6782589] using wordTrace_append hprefix tailTrace_6782589
  have hstable : (prefixWord ++ tailWord_6782589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782589).length < 2 ^ (prefixWord ++ tailWord_6782589).sum := by decide
  have hdescent : baseEnd_6782589 < baseStart_6782589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782592 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 3]
def baseStart_6782592 : Nat := 118140960795 + 6782592 * 2 ^ 59
def prefixEnd_6782592 : Nat := 4983230072969 + 3 ^ 40 * 6782592 * 2
def baseEnd_6782592 : Nat := 3482729779340032311307433

theorem tailTrace_6782592 : CollatzResearch.WordTrace tailWord_6782592 prefixEnd_6782592 3482729779340032311307433 := by
  unfold tailWord_6782592
  simp only [CollatzResearch.WordTrace]
  refine ⟨123690726721917516667903015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164920968962556688890537353 123690726721917516667903015)
  ·
    refine ⟨185536090082876275001854523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123690726721917516667903015 185536090082876275001854523)
    ·
      refine ⟨278304135124314412502781785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185536090082876275001854523 278304135124314412502781785)
      ·
        refine ⟨208728101343235809377086339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278304135124314412502781785 208728101343235809377086339)
        ·
          refine ⟨313092152014853714065629509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208728101343235809377086339 313092152014853714065629509)
          ·
            refine ⟨58704778502785071387305533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313092152014853714065629509 58704778502785071387305533)
            ·
              refine ⟨22014291938544401770239575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58704778502785071387305533 22014291938544401770239575)
              ·
                refine ⟨33021437907816602655359363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22014291938544401770239575 33021437907816602655359363)
                ·
                  refine ⟨49532156861724903983039045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33021437907816602655359363 49532156861724903983039045)
                  ·
                    refine ⟨9287279411573419496819821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49532156861724903983039045 9287279411573419496819821)
                    ·
                      refine ⟨3482729779340032311307433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9287279411573419496819821 3482729779340032311307433)
                      ·
                        rfl

theorem cell23_6782592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_6782592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782592 prefixEnd_6782592 := by exact prefixLift 6782592
  have htrace : WordTrace (prefixWord ++ tailWord_6782592) baseStart_6782592 baseEnd_6782592 := by
    simpa [prefixWord, tailWord_6782592, baseEnd_6782592] using wordTrace_append hprefix tailTrace_6782592
  have hstable : (prefixWord ++ tailWord_6782592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782592).length < 2 ^ (prefixWord ++ tailWord_6782592).sum := by decide
  have hdescent : baseEnd_6782592 < baseStart_6782592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782595 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 8]
def baseStart_6782595 : Nat := 118140960795 + 6782595 * 2 ^ 59
def prefixEnd_6782595 : Nat := 4983230072969 + 3 ^ 40 * 6782595 * 2
def baseEnd_6782595 : Nat := 386970146642443977729991

theorem tailTrace_6782595 : CollatzResearch.WordTrace tailWord_6782595 prefixEnd_6782595 386970146642443977729991 := by
  unfold tailWord_6782595
  simp only [CollatzResearch.WordTrace]
  refine ⟨247381562862824164848165239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164921041908549443232110159 247381562862824164848165239)
  ·
    refine ⟨371072344294236247272247859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247381562862824164848165239 371072344294236247272247859)
    ·
      refine ⟨556608516441354370908371789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371072344294236247272247859 556608516441354370908371789)
      ·
        refine ⟨208728193665507889090639421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 556608516441354370908371789 208728193665507889090639421)
        ·
          refine ⟨78273072624565458408989783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208728193665507889090639421 78273072624565458408989783)
          ·
            refine ⟨117409608936848187613484675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78273072624565458408989783 117409608936848187613484675)
            ·
              refine ⟨176114413405272281420227013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117409608936848187613484675 176114413405272281420227013)
              ·
                refine ⟨33021452513488552766292565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176114413405272281420227013 33021452513488552766292565)
                ·
                  refine ⟨386970146642443977729991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33021452513488552766292565 386970146642443977729991)
                  ·
                    rfl

theorem cell23_6782595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 8].length) (baseStart_6782595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782595 prefixEnd_6782595 := by exact prefixLift 6782595
  have htrace : WordTrace (prefixWord ++ tailWord_6782595) baseStart_6782595 baseEnd_6782595 := by
    simpa [prefixWord, tailWord_6782595, baseEnd_6782595] using wordTrace_append hprefix tailTrace_6782595
  have hstable : (prefixWord ++ tailWord_6782595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782595).length < 2 ^ (prefixWord ++ tailWord_6782595).sum := by decide
  have hdescent : baseEnd_6782595 < baseStart_6782595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782602 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_6782602 : Nat := 118140960795 + 6782602 * 2 ^ 59
def prefixEnd_6782602 : Nat := 4983230072969 + 3 ^ 40 * 6782602 * 2
def baseEnd_6782602 : Nat := 3482734914146577272182387

theorem tailTrace_6782602 : CollatzResearch.WordTrace tailWord_6782602 prefixEnd_6782602 3482734914146577272182387 := by
  unfold tailWord_6782602
  simp only [CollatzResearch.WordTrace]
  refine ⟨61845454543449701260917515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164921212115865870029113373 61845454543449701260917515)
  ·
    refine ⟨92768181815174551891376273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61845454543449701260917515 92768181815174551891376273)
    ·
      refine ⟨69576136361380913918532205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92768181815174551891376273 69576136361380913918532205)
      ·
        refine ⟨26091051135517842719449577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69576136361380913918532205 26091051135517842719449577)
        ·
          refine ⟨19568288351638382039587183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26091051135517842719449577 19568288351638382039587183)
          ·
            refine ⟨29352432527457573059380775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19568288351638382039587183 29352432527457573059380775)
            ·
              refine ⟨44028648791186359589071163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29352432527457573059380775 44028648791186359589071163)
              ·
                refine ⟨66042973186779539383606745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44028648791186359589071163 66042973186779539383606745)
                ·
                  refine ⟨49532229890084654537705059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66042973186779539383606745 49532229890084654537705059)
                  ·
                    refine ⟨74298344835126981806557589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49532229890084654537705059 74298344835126981806557589)
                    ·
                      refine ⟨3482734914146577272182387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74298344835126981806557589 3482734914146577272182387)
                      ·
                        rfl

theorem cell23_6782602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_6782602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782602 prefixEnd_6782602 := by exact prefixLift 6782602
  have htrace : WordTrace (prefixWord ++ tailWord_6782602) baseStart_6782602 baseEnd_6782602 := by
    simpa [prefixWord, tailWord_6782602, baseEnd_6782602] using wordTrace_append hprefix tailTrace_6782602
  have hstable : (prefixWord ++ tailWord_6782602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782602).length < 2 ^ (prefixWord ++ tailWord_6782602).sum := by decide
  have hdescent : baseEnd_6782602 < baseStart_6782602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782616 : List Nat := [2, 1, 2, 4, 1, 2, 2, 4, 1, 4]
def baseStart_6782616 : Nat := 118140960795 + 6782616 * 2 ^ 59
def prefixEnd_6782616 : Nat := 4983230072969 + 3 ^ 40 * 6782616 * 2
def baseEnd_6782616 : Nat := 1160914034291913405802441

theorem tailTrace_6782616 : CollatzResearch.WordTrace tailWord_6782616 prefixEnd_6782616 1160914034291913405802441 := by
  unfold tailWord_6782616
  simp only [CollatzResearch.WordTrace]
  refine ⟨123691164397874042717339851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164921552530498723623119801 123691164397874042717339851)
  ·
    refine ⟨185536746596811064076009777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123691164397874042717339851 185536746596811064076009777)
    ·
      refine ⟨139152559947608298057007333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185536746596811064076009777 139152559947608298057007333)
      ·
        refine ⟨26091104990176555885688875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139152559947608298057007333 26091104990176555885688875)
        ·
          refine ⟨39136657485264833828533313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26091104990176555885688875 39136657485264833828533313)
          ·
            refine ⟨29352493113948625371399985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39136657485264833828533313 29352493113948625371399985)
            ·
              refine ⟨22014369835461469028549989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29352493113948625371399985 22014369835461469028549989)
              ·
                refine ⟨4127694344149025442853123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22014369835461469028549989 4127694344149025442853123)
                ·
                  refine ⟨6191541516223538164279685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127694344149025442853123 6191541516223538164279685)
                  ·
                    refine ⟨1160914034291913405802441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6191541516223538164279685 1160914034291913405802441)
                    ·
                      rfl

theorem cell23_6782616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_6782616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782616 prefixEnd_6782616 := by exact prefixLift 6782616
  have htrace : WordTrace (prefixWord ++ tailWord_6782616) baseStart_6782616 baseEnd_6782616 := by
    simpa [prefixWord, tailWord_6782616, baseEnd_6782616] using wordTrace_append hprefix tailTrace_6782616
  have hstable : (prefixWord ++ tailWord_6782616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782616).length < 2 ^ (prefixWord ++ tailWord_6782616).sum := by decide
  have hdescent : baseEnd_6782616 < baseStart_6782616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782639 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 3, 1, 3]
def baseStart_6782639 : Nat := 118140960795 + 6782639 * 2 ^ 59
def prefixEnd_6782639 : Nat := 4983230072969 + 3 ^ 40 * 6782639 * 2
def baseEnd_6782639 : Nat := 3482753912930793627419717

theorem tailTrace_6782639 : CollatzResearch.WordTrace tailWord_6782639 prefixEnd_6782639 3482753912930793627419717 := by
  unfold tailWord_6782639
  simp only [CollatzResearch.WordTrace]
  refine ⟨247383167674664760362766971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164922111783109840241844647 247383167674664760362766971)
  ·
    refine ⟨371074751511997140544150457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247383167674664760362766971 371074751511997140544150457)
    ·
      refine ⟨278306063633997855408112843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371074751511997140544150457 278306063633997855408112843)
      ·
        refine ⟨417459095450996783112169265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278306063633997855408112843 417459095450996783112169265)
        ·
          refine ⟨313094321588247587334126949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417459095450996783112169265 313094321588247587334126949)
          ·
            refine ⟨58705185297796422625148803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313094321588247587334126949 58705185297796422625148803)
            ·
              refine ⟨88057777946694633937723205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58705185297796422625148803 88057777946694633937723205)
              ·
                refine ⟨16510833365005243863323101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88057777946694633937723205 16510833365005243863323101)
                ·
                  refine ⟨6191562511876966448746163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16510833365005243863323101 6191562511876966448746163)
                  ·
                    refine ⟨9287343767815449673119245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6191562511876966448746163 9287343767815449673119245)
                    ·
                      refine ⟨3482753912930793627419717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9287343767815449673119245 3482753912930793627419717)
                      ·
                        rfl

theorem cell23_6782639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 1, 3].length) (baseStart_6782639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782639 prefixEnd_6782639 := by exact prefixLift 6782639
  have htrace : WordTrace (prefixWord ++ tailWord_6782639) baseStart_6782639 baseEnd_6782639 := by
    simpa [prefixWord, tailWord_6782639, baseEnd_6782639] using wordTrace_append hprefix tailTrace_6782639
  have hstable : (prefixWord ++ tailWord_6782639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782639).length < 2 ^ (prefixWord ++ tailWord_6782639).sum := by decide
  have hdescent : baseEnd_6782639 < baseStart_6782639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782642 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_6782642 : Nat := 118140960795 + 6782642 * 2 ^ 59
def prefixEnd_6782642 : Nat := 4983230072969 + 3 ^ 40 * 6782642 * 2
def baseEnd_6782642 : Nat := 1160918484457585705227401

theorem tailTrace_6782642 : CollatzResearch.WordTrace tailWord_6782642 prefixEnd_6782642 1160918484457585705227401 := by
  unfold tailWord_6782642
  simp only [CollatzResearch.WordTrace]
  refine ⟨61845819273413472968781545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164922184729102594583417453 61845819273413472968781545)
  ·
    refine ⟨46384364455060104726586159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61845819273413472968781545 46384364455060104726586159)
    ·
      refine ⟨69576546682590157089879239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46384364455060104726586159 69576546682590157089879239)
      ·
        refine ⟨104364820023885235634818859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69576546682590157089879239 104364820023885235634818859)
        ·
          refine ⟨156547230035827853452228289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104364820023885235634818859 156547230035827853452228289)
          ·
            refine ⟨117410422526870890089171217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156547230035827853452228289 117410422526870890089171217)
            ·
              refine ⟨88057816895153167566878413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117410422526870890089171217 88057816895153167566878413)
              ·
                refine ⟨33021681335682437837579405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88057816895153167566878413 33021681335682437837579405)
                ·
                  refine ⟨12383130500880914189092277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33021681335682437837579405 12383130500880914189092277)
                  ·
                    refine ⟨1160918484457585705227401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12383130500880914189092277 1160918484457585705227401)
                    ·
                      rfl

theorem cell23_6782642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_6782642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782642 prefixEnd_6782642 := by exact prefixLift 6782642
  have htrace : WordTrace (prefixWord ++ tailWord_6782642) baseStart_6782642 baseEnd_6782642 := by
    simpa [prefixWord, tailWord_6782642, baseEnd_6782642] using wordTrace_append hprefix tailTrace_6782642
  have hstable : (prefixWord ++ tailWord_6782642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782642).length < 2 ^ (prefixWord ++ tailWord_6782642).sum := by decide
  have hdescent : baseEnd_6782642 < baseStart_6782642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782649 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 1, 5, 2]
def baseStart_6782649 : Nat := 118140960795 + 6782649 * 2 ^ 59
def prefixEnd_6782649 : Nat := 4983230072969 + 3 ^ 40 * 6782649 * 2
def baseEnd_6782649 : Nat := 3482759047737338588294671

theorem tailTrace_6782649 : CollatzResearch.WordTrace tailWord_6782649 prefixEnd_6782649 3482759047737338588294671 := by
  unfold tailWord_6782649
  simp only [CollatzResearch.WordTrace]
  refine ⟨247383532404628532070631001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164922354936419021380420667 247383532404628532070631001)
  ·
    refine ⟨185537649303471399052973251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247383532404628532070631001 185537649303471399052973251)
    ·
      refine ⟨278306473955207098579459877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185537649303471399052973251 278306473955207098579459877)
      ·
        refine ⟨52182463866601330983648727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278306473955207098579459877 52182463866601330983648727)
        ·
          refine ⟨78273695799901996475473091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52182463866601330983648727 78273695799901996475473091)
          ·
            refine ⟨117410543699852994713209637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78273695799901996475473091 117410543699852994713209637)
            ·
              refine ⟨22014476943722436508726807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117410543699852994713209637 22014476943722436508726807)
              ·
                refine ⟨33021715415583654763090211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22014476943722436508726807 33021715415583654763090211)
                ·
                  refine ⟨49532573123375482144635317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33021715415583654763090211 49532573123375482144635317)
                  ·
                    refine ⟨4643678730316451451059561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49532573123375482144635317 4643678730316451451059561)
                    ·
                      refine ⟨3482759047737338588294671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4643678730316451451059561 3482759047737338588294671)
                      ·
                        rfl

theorem cell23_6782649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_6782649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782649 prefixEnd_6782649 := by exact prefixLift 6782649
  have htrace : WordTrace (prefixWord ++ tailWord_6782649) baseStart_6782649 baseEnd_6782649 := by
    simpa [prefixWord, tailWord_6782649, baseEnd_6782649] using wordTrace_append hprefix tailTrace_6782649
  have hstable : (prefixWord ++ tailWord_6782649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782649).length < 2 ^ (prefixWord ++ tailWord_6782649).sum := by decide
  have hdescent : baseEnd_6782649 < baseStart_6782649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782692 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_6782692 : Nat := 118140960795 + 6782692 * 2 ^ 59
def prefixEnd_6782692 : Nat := 4983230072969 + 3 ^ 40 * 6782692 * 2
def baseEnd_6782692 : Nat := 3482781127405481920056973

theorem tailTrace_6782692 : CollatzResearch.WordTrace tailWord_6782692 prefixEnd_6782692 3482781127405481920056973 := by
  unfold tailWord_6782692
  simp only [CollatzResearch.WordTrace]
  refine ⟨123692550371736375207223165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164923400495648500276297553 123692550371736375207223165)
  ·
    refine ⟨46384706389401140702708687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123692550371736375207223165 46384706389401140702708687)
    ·
      refine ⟨69577059584101711054063031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46384706389401140702708687 69577059584101711054063031)
      ·
        refine ⟨104365589376152566581094547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69577059584101711054063031 104365589376152566581094547)
        ·
          refine ⟨156548384064228849871641821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104365589376152566581094547 156548384064228849871641821)
          ·
            refine ⟨58705644024085818701865683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156548384064228849871641821 58705644024085818701865683)
            ·
              refine ⟨88058466036128728052798525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58705644024085818701865683 88058466036128728052798525)
              ·
                refine ⟨33021924763548273019799447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88058466036128728052798525 33021924763548273019799447)
                ·
                  refine ⟨49532887145322409529699171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33021924763548273019799447 49532887145322409529699171)
                  ·
                    refine ⟨74299330717983614294548757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49532887145322409529699171 74299330717983614294548757)
                    ·
                      refine ⟨3482781127405481920056973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74299330717983614294548757 3482781127405481920056973)
                      ·
                        rfl

theorem cell23_6782692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_6782692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782692 prefixEnd_6782692 := by exact prefixLift 6782692
  have htrace : WordTrace (prefixWord ++ tailWord_6782692) baseStart_6782692 baseEnd_6782692 := by
    simpa [prefixWord, tailWord_6782692, baseEnd_6782692] using wordTrace_append hprefix tailTrace_6782692
  have hstable : (prefixWord ++ tailWord_6782692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782692).length < 2 ^ (prefixWord ++ tailWord_6782692).sum := by decide
  have hdescent : baseEnd_6782692 < baseStart_6782692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782696 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_6782696 : Nat := 118140960795 + 6782696 * 2 ^ 59
def prefixEnd_6782696 : Nat := 4983230072969 + 3 ^ 40 * 6782696 * 2
def baseEnd_6782696 : Nat := 3482783181328099904406955

theorem tailTrace_6782696 : CollatzResearch.WordTrace tailWord_6782696 prefixEnd_6782696 3482783181328099904406955 := by
  unfold tailWord_6782696
  simp only [CollatzResearch.WordTrace]
  refine ⟨123692623317729129548795971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164923497756972172731727961 123692623317729129548795971)
  ·
    refine ⟨185538934976593694323193957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123692623317729129548795971 185538934976593694323193957)
    ·
      refine ⟨34788550308111317685598867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185538934976593694323193957 34788550308111317685598867)
      ·
        refine ⟨52182825462166976528398301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34788550308111317685598867 52182825462166976528398301)
        ·
          refine ⟨19568559548312616198149363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52182825462166976528398301 19568559548312616198149363)
          ·
            refine ⟨29352839322468924297224045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19568559548312616198149363 29352839322468924297224045)
            ·
              refine ⟨11007314745925846611459017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29352839322468924297224045 11007314745925846611459017)
              ·
                refine ⟨8255486059444384958594263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11007314745925846611459017 8255486059444384958594263)
                ·
                  refine ⟨12383229089166577437891395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8255486059444384958594263 12383229089166577437891395)
                  ·
                    refine ⟨18574843633749866156837093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12383229089166577437891395 18574843633749866156837093)
                    ·
                      refine ⟨3482783181328099904406955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18574843633749866156837093 3482783181328099904406955)
                      ·
                        rfl

theorem cell23_6782696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_6782696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782696 prefixEnd_6782696 := by exact prefixLift 6782696
  have htrace : WordTrace (prefixWord ++ tailWord_6782696) baseStart_6782696 baseEnd_6782696 := by
    simpa [prefixWord, tailWord_6782696, baseEnd_6782696] using wordTrace_append hprefix tailTrace_6782696
  have hstable : (prefixWord ++ tailWord_6782696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782696).length < 2 ^ (prefixWord ++ tailWord_6782696).sum := by decide
  have hdescent : baseEnd_6782696 < baseStart_6782696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782702 : List Nat := [4, 1, 2, 1, 1, 2, 1, 11]
def baseStart_6782702 : Nat := 118140960795 + 6782702 * 2 ^ 59
def prefixEnd_6782702 : Nat := 4983230072969 + 3 ^ 40 * 6782702 * 2
def baseEnd_6782702 : Nat := 128992083785630625219701

theorem tailTrace_6782702 : CollatzResearch.WordTrace tailWord_6782702 prefixEnd_6782702 128992083785630625219701 := by
  unfold tailWord_6782702
  simp only [CollatzResearch.WordTrace]
  refine ⟨30923183184179565265288795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164923643648957681414873573 30923183184179565265288795)
  ·
    refine ⟨46384774776269347897933193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30923183184179565265288795 46384774776269347897933193)
    ·
      refine ⟨34788581082202010923449895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46384774776269347897933193 34788581082202010923449895)
      ·
        refine ⟨52182871623303016385174843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34788581082202010923449895 52182871623303016385174843)
        ·
          refine ⟨78274307434954524577762265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52182871623303016385174843 78274307434954524577762265)
          ·
            refine ⟨58705730576215893433321699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78274307434954524577762265 58705730576215893433321699)
            ·
              refine ⟨88058595864323840149982549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58705730576215893433321699 88058595864323840149982549)
              ·
                refine ⟨128992083785630625219701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 88058595864323840149982549 128992083785630625219701)
                ·
                  rfl

theorem cell23_6782702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_6782702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782702 prefixEnd_6782702 := by exact prefixLift 6782702
  have htrace : WordTrace (prefixWord ++ tailWord_6782702) baseStart_6782702 baseEnd_6782702 := by
    simpa [prefixWord, tailWord_6782702, baseEnd_6782702] using wordTrace_append hprefix tailTrace_6782702
  have hstable : (prefixWord ++ tailWord_6782702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782702).length < 2 ^ (prefixWord ++ tailWord_6782702).sum := by decide
  have hdescent : baseEnd_6782702 < baseStart_6782702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782730 : List Nat := [3, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2]
def baseStart_6782730 : Nat := 118140960795 + 6782730 * 2 ^ 59
def prefixEnd_6782730 : Nat := 4983230072969 + 3 ^ 40 * 6782730 * 2
def baseEnd_6782730 : Nat := 3482800639670352771381799

theorem tailTrace_6782730 : CollatzResearch.WordTrace tailWord_6782730 prefixEnd_6782730 3482800639670352771381799 := by
  unfold tailWord_6782730
  simp only [CollatzResearch.WordTrace]
  refine ⟨61846621679333770726082411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164924324478223388602886429 61846621679333770726082411)
  ·
    refine ⟨92769932519000656089123617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61846621679333770726082411 92769932519000656089123617)
    ·
      refine ⟨69577449389250492066842713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92769932519000656089123617 69577449389250492066842713)
      ·
        refine ⟨52183087041937869050132035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69577449389250492066842713 52183087041937869050132035)
        ·
          refine ⟨78274630562906803575198053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52183087041937869050132035 78274630562906803575198053)
          ·
            refine ⟨14676493230545025670349635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78274630562906803575198053 14676493230545025670349635)
            ·
              refine ⟨22014739845817538505524453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14676493230545025670349635 22014739845817538505524453)
              ·
                refine ⟨4127763721090788469785835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22014739845817538505524453 4127763721090788469785835)
                ·
                  refine ⟨6191645581636182704678753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127763721090788469785835 6191645581636182704678753)
                  ·
                    refine ⟨4643734186227137028509065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6191645581636182704678753 4643734186227137028509065)
                    ·
                      refine ⟨3482800639670352771381799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4643734186227137028509065 3482800639670352771381799)
                      ·
                        rfl

theorem cell23_6782730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_6782730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782730 prefixEnd_6782730 := by exact prefixLift 6782730
  have htrace : WordTrace (prefixWord ++ tailWord_6782730) baseStart_6782730 baseEnd_6782730 := by
    simpa [prefixWord, tailWord_6782730, baseEnd_6782730] using wordTrace_append hprefix tailTrace_6782730
  have hstable : (prefixWord ++ tailWord_6782730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782730).length < 2 ^ (prefixWord ++ tailWord_6782730).sum := by decide
  have hdescent : baseEnd_6782730 < baseStart_6782730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782732 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_6782732 : Nat := 118140960795 + 6782732 * 2 ^ 59
def prefixEnd_6782732 : Nat := 4983230072969 + 3 ^ 40 * 6782732 * 2
def baseEnd_6782732 : Nat := 1160933888877220587852263

theorem tailTrace_6782732 : CollatzResearch.WordTrace tailWord_6782732 prefixEnd_6782732 1160933888877220587852263 := by
  unfold tailWord_6782732
  simp only [CollatzResearch.WordTrace]
  refine ⟨123693279831663918622951225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164924373108885224830601633 123693279831663918622951225)
  ·
    refine ⟨92769959873747938967213419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123693279831663918622951225 92769959873747938967213419)
    ·
      refine ⟨139154939810621908450820129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92769959873747938967213419 139154939810621908450820129)
      ·
        refine ⟨104366204857966431338115097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139154939810621908450820129 104366204857966431338115097)
        ·
          refine ⟨78274653643474823503586323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104366204857966431338115097 78274653643474823503586323)
          ·
            refine ⟨117411980465212235255379485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78274653643474823503586323 117411980465212235255379485)
            ·
              refine ⟨44029492674454588220767307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117411980465212235255379485 44029492674454588220767307)
              ·
                refine ⟨66044239011681882331150961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44029492674454588220767307 66044239011681882331150961)
                ·
                  refine ⟨49533179258761411748363221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66044239011681882331150961 49533179258761411748363221)
                  ·
                    refine ⟨1160933888877220587852263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49533179258761411748363221 1160933888877220587852263)
                    ·
                      rfl

theorem cell23_6782732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_6782732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782732 prefixEnd_6782732 := by exact prefixLift 6782732
  have htrace : WordTrace (prefixWord ++ tailWord_6782732) baseStart_6782732 baseEnd_6782732 := by
    simpa [prefixWord, tailWord_6782732, baseEnd_6782732] using wordTrace_append hprefix tailTrace_6782732
  have hstable : (prefixWord ++ tailWord_6782732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782732).length < 2 ^ (prefixWord ++ tailWord_6782732).sum := by decide
  have hdescent : baseEnd_6782732 < baseStart_6782732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782740 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_6782740 : Nat := 118140960795 + 6782740 * 2 ^ 59
def prefixEnd_6782740 : Nat := 4983230072969 + 3 ^ 40 * 6782740 * 2
def baseEnd_6782740 : Nat := 1160935258158965910752251

theorem tailTrace_6782740 : CollatzResearch.WordTrace tailWord_6782740 prefixEnd_6782740 1160935258158965910752251 := by
  unfold tailWord_6782740
  simp only [CollatzResearch.WordTrace]
  refine ⟨123693425723649427306096837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164924567631532569741462449 123693425723649427306096837)
  ·
    refine ⟨23192517323184267619893157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123693425723649427306096837 23192517323184267619893157)
    ·
      refine ⟨4348596998097050178729967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23192517323184267619893157 4348596998097050178729967)
      ·
        refine ⟨6522895497145575268094951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348596998097050178729967 6522895497145575268094951)
        ·
          refine ⟨9784343245718362902142427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6522895497145575268094951 9784343245718362902142427)
          ·
            refine ⟨14676514868577544353213641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9784343245718362902142427 14676514868577544353213641)
            ·
              refine ⟨11007386151433158264910231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14676514868577544353213641 11007386151433158264910231)
              ·
                refine ⟨16511079227149737397365347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11007386151433158264910231 16511079227149737397365347)
                ·
                  refine ⟨24766618840724606096048021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16511079227149737397365347 24766618840724606096048021)
                  ·
                    refine ⟨1160935258158965910752251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24766618840724606096048021 1160935258158965910752251)
                    ·
                      rfl

theorem cell23_6782740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_6782740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782740 prefixEnd_6782740 := by exact prefixLift 6782740
  have htrace : WordTrace (prefixWord ++ tailWord_6782740) baseStart_6782740 baseEnd_6782740 := by
    simpa [prefixWord, tailWord_6782740, baseEnd_6782740] using wordTrace_append hprefix tailTrace_6782740
  have hstable : (prefixWord ++ tailWord_6782740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782740).length < 2 ^ (prefixWord ++ tailWord_6782740).sum := by decide
  have hdescent : baseEnd_6782740 < baseStart_6782740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782746 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3]
def baseStart_6782746 : Nat := 118140960795 + 6782746 * 2 ^ 59
def prefixEnd_6782746 : Nat := 4983230072969 + 3 ^ 40 * 6782746 * 2
def baseEnd_6782746 : Nat := 3482808855360824708781725

theorem tailTrace_6782746 : CollatzResearch.WordTrace tailWord_6782746 prefixEnd_6782746 3482808855360824708781725 := by
  unfold tailWord_6782746
  simp only [CollatzResearch.WordTrace]
  refine ⟨61846767571319279409228023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164924713523518078424608061 61846767571319279409228023)
  ·
    refine ⟨92770151356978919113842035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61846767571319279409228023 92770151356978919113842035)
    ·
      refine ⟨139155227035468378670763053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92770151356978919113842035 139155227035468378670763053)
      ·
        refine ⟨52183210138300642001536145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139155227035468378670763053 52183210138300642001536145)
        ·
          refine ⟨39137407603725481501152109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52183210138300642001536145 39137407603725481501152109)
          ·
            refine ⟨14676527851397055562932041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39137407603725481501152109 14676527851397055562932041)
            ·
              refine ⟨11007395888547791672199031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14676527851397055562932041 11007395888547791672199031)
              ·
                refine ⟨16511093832821687508298547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11007395888547791672199031 16511093832821687508298547)
                ·
                  refine ⟨24766640749232531262447821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16511093832821687508298547 24766640749232531262447821)
                  ·
                    refine ⟨9287490280962199223417933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24766640749232531262447821 9287490280962199223417933)
                    ·
                      refine ⟨3482808855360824708781725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9287490280962199223417933 3482808855360824708781725)
                      ·
                        rfl

theorem cell23_6782746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_6782746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782746 prefixEnd_6782746 := by exact prefixLift 6782746
  have htrace : WordTrace (prefixWord ++ tailWord_6782746) baseStart_6782746 baseEnd_6782746 := by
    simpa [prefixWord, tailWord_6782746, baseEnd_6782746] using wordTrace_append hprefix tailTrace_6782746
  have hstable : (prefixWord ++ tailWord_6782746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782746).length < 2 ^ (prefixWord ++ tailWord_6782746).sum := by decide
  have hdescent : baseEnd_6782746 < baseStart_6782746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782797 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_6782797 : Nat := 118140960795 + 6782797 * 2 ^ 59
def prefixEnd_6782797 : Nat := 4983230072969 + 3 ^ 40 * 6782797 * 2
def baseEnd_6782797 : Nat := 3482835042874204009243991

theorem tailTrace_6782797 : CollatzResearch.WordTrace tailWord_6782797 prefixEnd_6782797 3482835042874204009243991 := by
  unfold tailWord_6782797
  simp only [CollatzResearch.WordTrace]
  refine ⟨247388930408092353347018645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164925953605394902231345763 247388930408092353347018645)
  ·
    refine ⟨11596356112879329063141499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 247388930408092353347018645 11596356112879329063141499)
    ·
      refine ⟨17394534169318993594712249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11596356112879329063141499 17394534169318993594712249)
      ·
        refine ⟨13045900626989245196034187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17394534169318993594712249 13045900626989245196034187)
        ·
          refine ⟨19568850940483867794051281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13045900626989245196034187 19568850940483867794051281)
          ·
            refine ⟨14676638205362900845538461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19568850940483867794051281 14676638205362900845538461)
            ·
              refine ⟨5503739327011087817076923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14676638205362900845538461 5503739327011087817076923)
              ·
                refine ⟨8255608990516631725615385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5503739327011087817076923 8255608990516631725615385)
                ·
                  refine ⟨6191706742887473794211539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8255608990516631725615385 6191706742887473794211539)
                  ·
                    refine ⟨9287560114331210691317309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6191706742887473794211539 9287560114331210691317309)
                    ·
                      refine ⟨3482835042874204009243991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9287560114331210691317309 3482835042874204009243991)
                      ·
                        rfl

theorem cell23_6782797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_6782797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782797 prefixEnd_6782797 := by exact prefixLift 6782797
  have htrace : WordTrace (prefixWord ++ tailWord_6782797) baseStart_6782797 baseEnd_6782797 := by
    simpa [prefixWord, tailWord_6782797, baseEnd_6782797] using wordTrace_append hprefix tailTrace_6782797
  have hstable : (prefixWord ++ tailWord_6782797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782797).length < 2 ^ (prefixWord ++ tailWord_6782797).sum := by decide
  have hdescent : baseEnd_6782797 < baseStart_6782797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782859 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 4]
def baseStart_6782859 : Nat := 118140960795 + 6782859 * 2 ^ 59
def prefixEnd_6782859 : Nat := 4983230072969 + 3 ^ 40 * 6782859 * 2
def baseEnd_6782859 : Nat := 3482866878674782766668705

theorem tailTrace_6782859 : CollatzResearch.WordTrace tailWord_6782859 prefixEnd_6782859 3482866878674782766668705 := by
  unfold tailWord_6782859
  simp only [CollatzResearch.WordTrace]
  refine ⟨247391191733867737935775631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164927461155911825290517087 247391191733867737935775631)
  ·
    refine ⟨371086787600801606903663447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247391191733867737935775631 371086787600801606903663447)
    ·
      refine ⟨556630181401202410355495171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371086787600801606903663447 556630181401202410355495171)
      ·
        refine ⟨834945272101803615533242757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556630181401202410355495171 834945272101803615533242757)
        ·
          refine ⟨156552238519088177912483017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 834945272101803615533242757 156552238519088177912483017)
          ·
            refine ⟨117414178889316133434362263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156552238519088177912483017 117414178889316133434362263)
            ·
              refine ⟨176121268333974200151543395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117414178889316133434362263 176121268333974200151543395)
              ·
                refine ⟨264181902500961300227315093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176121268333974200151543395 264181902500961300227315093)
                ·
                  refine ⟨12383526679732560948155395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 264181902500961300227315093 12383526679732560948155395)
                  ·
                    refine ⟨18575290019598841422233093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12383526679732560948155395 18575290019598841422233093)
                    ·
                      refine ⟨3482866878674782766668705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18575290019598841422233093 3482866878674782766668705)
                      ·
                        rfl

theorem cell23_6782859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 4].length) (baseStart_6782859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782859 prefixEnd_6782859 := by exact prefixLift 6782859
  have htrace : WordTrace (prefixWord ++ tailWord_6782859) baseStart_6782859 baseEnd_6782859 := by
    simpa [prefixWord, tailWord_6782859, baseEnd_6782859] using wordTrace_append hprefix tailTrace_6782859
  have hstable : (prefixWord ++ tailWord_6782859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782859).length < 2 ^ (prefixWord ++ tailWord_6782859).sum := by decide
  have hdescent : baseEnd_6782859 < baseStart_6782859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782960 : List Nat := [2, 1, 1, 1, 3, 2, 4, 4, 1, 1, 3]
def baseStart_6782960 : Nat := 118140960795 + 6782960 * 2 ^ 59
def prefixEnd_6782960 : Nat := 4983230072969 + 3 ^ 40 * 6782960 * 2
def baseEnd_6782960 : Nat := 3482918740220886871505741

theorem tailTrace_6782960 : CollatzResearch.WordTrace tailWord_6782960 prefixEnd_6782960 3482918740220886871505741 := by
  unfold tailWord_6782960
  simp only [CollatzResearch.WordTrace]
  refine ⟨123697437753250916092601167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164929917004334554790134889 123697437753250916092601167)
  ·
    refine ⟨185546156629876374138901751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123697437753250916092601167 185546156629876374138901751)
    ·
      refine ⟨278319234944814561208352627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185546156629876374138901751 278319234944814561208352627)
      ·
        refine ⟨417478852417221841812528941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278319234944814561208352627 417478852417221841812528941)
        ·
          refine ⟨156554569656458190679698353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 417478852417221841812528941 156554569656458190679698353)
          ·
            refine ⟨117415927242343643009773765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156554569656458190679698353 117415927242343643009773765)
            ·
              refine ⟨22015486357939433064332581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117415927242343643009773765 22015486357939433064332581)
              ·
                refine ⟨4127903692113643699562359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22015486357939433064332581 4127903692113643699562359)
                ·
                  refine ⟨6191855538170465549343539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127903692113643699562359 6191855538170465549343539)
                  ·
                    refine ⟨9287783307255698324015309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6191855538170465549343539 9287783307255698324015309)
                    ·
                      refine ⟨3482918740220886871505741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9287783307255698324015309 3482918740220886871505741)
                      ·
                        rfl

theorem cell23_6782960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 1, 1, 3].length) (baseStart_6782960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782960 prefixEnd_6782960 := by exact prefixLift 6782960
  have htrace : WordTrace (prefixWord ++ tailWord_6782960) baseStart_6782960 baseEnd_6782960 := by
    simpa [prefixWord, tailWord_6782960, baseEnd_6782960] using wordTrace_append hprefix tailTrace_6782960
  have hstable : (prefixWord ++ tailWord_6782960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782960).length < 2 ^ (prefixWord ++ tailWord_6782960).sum := by decide
  have hdescent : baseEnd_6782960 < baseStart_6782960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6782983 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_6782983 : Nat := 118140960795 + 6782983 * 2 ^ 59
def prefixEnd_6782983 : Nat := 4983230072969 + 3 ^ 40 * 6782983 * 2
def baseEnd_6782983 : Nat := 3482930550275940281518135

theorem tailTrace_6782983 : CollatzResearch.WordTrace tailWord_6782983 prefixEnd_6782983 3482930550275940281518135 := by
  unfold tailWord_6782983
  simp only [CollatzResearch.WordTrace]
  refine ⟨247395714385418507113289603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164930476256945671408859735 247395714385418507113289603)
  ·
    refine ⟨371093571578127760669934405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247395714385418507113289603 371093571578127760669934405)
    ·
      refine ⟨69580044670898955125612701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371093571578127760669934405 69580044670898955125612701)
      ·
        refine ⟨26092516751587108172104763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69580044670898955125612701 26092516751587108172104763)
        ·
          refine ⟨39138775127380662258157145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26092516751587108172104763 39138775127380662258157145)
          ·
            refine ⟨29354081345535496693617859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39138775127380662258157145 29354081345535496693617859)
            ·
              refine ⟨44031122018303245040426789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29354081345535496693617859 44031122018303245040426789)
              ·
                refine ⟨8255835378431858445080023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44031122018303245040426789 8255835378431858445080023)
                ·
                  refine ⟨12383753067647787667620035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8255835378431858445080023 12383753067647787667620035)
                  ·
                    refine ⟨18575629601471681501430053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12383753067647787667620035 18575629601471681501430053)
                    ·
                      refine ⟨3482930550275940281518135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18575629601471681501430053 3482930550275940281518135)
                      ·
                        rfl

theorem cell23_6782983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_6782983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6782983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6782983 prefixEnd_6782983 := by exact prefixLift 6782983
  have htrace : WordTrace (prefixWord ++ tailWord_6782983) baseStart_6782983 baseEnd_6782983 := by
    simpa [prefixWord, tailWord_6782983, baseEnd_6782983] using wordTrace_append hprefix tailTrace_6782983
  have hstable : (prefixWord ++ tailWord_6782983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6782983).length < 2 ^ (prefixWord ++ tailWord_6782983).sum := by decide
  have hdescent : baseEnd_6782983 < baseStart_6782983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6782983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783066 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_6783066 : Nat := 118140960795 + 6783066 * 2 ^ 59
def prefixEnd_6783066 : Nat := 4983230072969 + 3 ^ 40 * 6783066 * 2
def baseEnd_6783066 : Nat := 1160991056390087818926751

theorem tailTrace_6783066 : CollatzResearch.WordTrace tailWord_6783066 prefixEnd_6783066 1160991056390087818926751 := by
  unfold tailWord_6783066
  simp only [CollatzResearch.WordTrace]
  refine ⟨61849685411029453072140263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164932494429411874859040701 61849685411029453072140263)
  ·
    refine ⟨92774528116544179608210395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61849685411029453072140263 92774528116544179608210395)
    ·
      refine ⟨139161792174816269412315593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92774528116544179608210395 139161792174816269412315593)
      ·
        refine ⟨104371344131112202059236695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139161792174816269412315593 104371344131112202059236695)
        ·
          refine ⟨156557016196668303088855043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104371344131112202059236695 156557016196668303088855043)
          ·
            refine ⟨234835524295002454633282565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156557016196668303088855043 234835524295002454633282565)
            ·
              refine ⟨44031660805312960243740481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234835524295002454633282565 44031660805312960243740481)
              ·
                refine ⟨33023745603984720182805361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44031660805312960243740481 33023745603984720182805361)
                ·
                  refine ⟨24767809202988540137104021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33023745603984720182805361 24767809202988540137104021)
                  ·
                    refine ⟨1160991056390087818926751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24767809202988540137104021 1160991056390087818926751)
                    ·
                      rfl

theorem cell23_6783066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_6783066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783066 prefixEnd_6783066 := by exact prefixLift 6783066
  have htrace : WordTrace (prefixWord ++ tailWord_6783066) baseStart_6783066 baseEnd_6783066 := by
    simpa [prefixWord, tailWord_6783066, baseEnd_6783066] using wordTrace_append hprefix tailTrace_6783066
  have hstable : (prefixWord ++ tailWord_6783066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783066).length < 2 ^ (prefixWord ++ tailWord_6783066).sum := by decide
  have hdescent : baseEnd_6783066 < baseStart_6783066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783073 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 5, 4, 2]
def baseStart_6783073 : Nat := 118140960795 + 6783073 * 2 ^ 59
def prefixEnd_6783073 : Nat := 4983230072969 + 3 ^ 40 * 6783073 * 2
def baseEnd_6783073 : Nat := 3482976763534844929392721

theorem tailTrace_6783073 : CollatzResearch.WordTrace tailWord_6783073 prefixEnd_6783073 3482976763534844929392721 := by
  unfold tailWord_6783073
  simp only [CollatzResearch.WordTrace]
  refine ⟨247398996955092452484065873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164932664636728301656043915 247398996955092452484065873)
  ·
    refine ⟨185549247716319339363049405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247398996955092452484065873 185549247716319339363049405)
    ·
      refine ⟨69580967893619752261143527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185549247716319339363049405 69580967893619752261143527)
      ·
        refine ⟨104371451840429628391715291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69580967893619752261143527 104371451840429628391715291)
        ·
          refine ⟨156557177760644442587572937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104371451840429628391715291 156557177760644442587572937)
          ·
            refine ⟨117417883320483331940679703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156557177760644442587572937 117417883320483331940679703)
            ·
              refine ⟨176126824980724997911019555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117417883320483331940679703 176126824980724997911019555)
              ·
                refine ⟨264190237471087496866529333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176126824980724997911019555 264190237471087496866529333)
                ·
                  refine ⟨24767834762914452831237125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264190237471087496866529333 24767834762914452831237125)
                  ·
                    refine ⟨4643969018046459905856961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24767834762914452831237125 4643969018046459905856961)
                    ·
                      refine ⟨3482976763534844929392721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4643969018046459905856961 3482976763534844929392721)
                      ·
                        rfl

theorem cell23_6783073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_6783073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783073 prefixEnd_6783073 := by exact prefixLift 6783073
  have htrace : WordTrace (prefixWord ++ tailWord_6783073) baseStart_6783073 baseEnd_6783073 := by
    simpa [prefixWord, tailWord_6783073, baseEnd_6783073] using wordTrace_append hprefix tailTrace_6783073
  have hstable : (prefixWord ++ tailWord_6783073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783073).length < 2 ^ (prefixWord ++ tailWord_6783073).sum := by decide
  have hdescent : baseEnd_6783073 < baseStart_6783073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783076 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_6783076 : Nat := 118140960795 + 6783076 * 2 ^ 59
def prefixEnd_6783076 : Nat := 4983230072969 + 3 ^ 40 * 6783076 * 2
def baseEnd_6783076 : Nat := 3482978303976808417655207

theorem tailTrace_6783076 : CollatzResearch.WordTrace tailWord_6783076 prefixEnd_6783076 3482978303976808417655207 := by
  unfold tailWord_6783076
  simp only [CollatzResearch.WordTrace]
  refine ⟨123699553187040791998212541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164932737582721055997616721 123699553187040791998212541)
  ·
    refine ⟨46387332445140296999329703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123699553187040791998212541 46387332445140296999329703)
    ·
      refine ⟨69580998667710445498994555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46387332445140296999329703 69580998667710445498994555)
      ·
        refine ⟨104371498001565668248491833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69580998667710445498994555 104371498001565668248491833)
        ·
          refine ⟨78278623501174251186368875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104371498001565668248491833 78278623501174251186368875)
          ·
            refine ⟨117417935251761376779553313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78278623501174251186368875 117417935251761376779553313)
            ·
              refine ⟨88063451438821032584664985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117417935251761376779553313 88063451438821032584664985)
              ·
                refine ⟨66047588579115774438498739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88063451438821032584664985 66047588579115774438498739)
                ·
                  refine ⟨99071382868673661657748109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66047588579115774438498739 99071382868673661657748109)
                  ·
                    refine ⟨37151768575752623121655541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99071382868673661657748109 37151768575752623121655541)
                    ·
                      refine ⟨3482978303976808417655207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37151768575752623121655541 3482978303976808417655207)
                      ·
                        rfl

theorem cell23_6783076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_6783076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783076 prefixEnd_6783076 := by exact prefixLift 6783076
  have htrace : WordTrace (prefixWord ++ tailWord_6783076) baseStart_6783076 baseEnd_6783076 := by
    simpa [prefixWord, tailWord_6783076, baseEnd_6783076] using wordTrace_append hprefix tailTrace_6783076
  have hstable : (prefixWord ++ tailWord_6783076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783076).length < 2 ^ (prefixWord ++ tailWord_6783076).sum := by decide
  have hdescent : baseEnd_6783076 < baseStart_6783076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783090 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 1, 4, 2]
def baseStart_6783090 : Nat := 118140960795 + 6783090 * 2 ^ 59
def prefixEnd_6783090 : Nat := 4983230072969 + 3 ^ 40 * 6783090 * 2
def baseEnd_6783090 : Nat := 3482985492705971362880143

theorem tailTrace_6783090 : CollatzResearch.WordTrace tailWord_6783090 prefixEnd_6783090 3482985492705971362880143 := by
  unfold tailWord_6783090
  simp only [CollatzResearch.WordTrace]
  refine ⟨61849904249007716096858681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164933077997353909591623149 61849904249007716096858681)
  ·
    refine ⟨46387428186755787072644011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61849904249007716096858681 46387428186755787072644011)
    ·
      refine ⟨69581142280133680608966017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46387428186755787072644011 69581142280133680608966017)
      ·
        refine ⟨52185856710100260456724513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69581142280133680608966017 52185856710100260456724513)
        ·
          refine ⟨39139392532575195342543385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52185856710100260456724513 39139392532575195342543385)
          ·
            refine ⟨29354544399431396506907539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39139392532575195342543385 29354544399431396506907539)
            ·
              refine ⟨44031816599147094760361309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29354544399431396506907539 44031816599147094760361309)
              ·
                refine ⟨16511931224680160535135491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44031816599147094760361309 16511931224680160535135491)
                ·
                  refine ⟨24767896837020240802703237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16511931224680160535135491 24767896837020240802703237)
                  ·
                    refine ⟨4643980656941295150506857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24767896837020240802703237 4643980656941295150506857)
                    ·
                      refine ⟨3482985492705971362880143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4643980656941295150506857 3482985492705971362880143)
                      ·
                        rfl

theorem cell23_6783090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_6783090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783090 prefixEnd_6783090 := by exact prefixLift 6783090
  have htrace : WordTrace (prefixWord ++ tailWord_6783090) baseStart_6783090 baseEnd_6783090 := by
    simpa [prefixWord, tailWord_6783090, baseEnd_6783090] using wordTrace_append hprefix tailTrace_6783090
  have hstable : (prefixWord ++ tailWord_6783090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783090).length < 2 ^ (prefixWord ++ tailWord_6783090).sum := by decide
  have hdescent : baseEnd_6783090 < baseStart_6783090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783130 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 7]
def baseStart_6783130 : Nat := 118140960795 + 6783130 * 2 ^ 59
def prefixEnd_6783130 : Nat := 4983230072969 + 3 ^ 40 * 6783130 * 2
def baseEnd_6783130 : Nat := 387000670214683467375551

theorem tailTrace_6783130 : CollatzResearch.WordTrace tailWord_6783130 prefixEnd_6783130 387000670214683467375551 := by
  unfold tailWord_6783130
  simp only [CollatzResearch.WordTrace]
  refine ⟨61850268978971487804722711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164934050610590634145927229 61850268978971487804722711)
  ·
    refine ⟨92775403468457231707084067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61850268978971487804722711 92775403468457231707084067)
    ·
      refine ⟨139163105202685847560626101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92775403468457231707084067 139163105202685847560626101)
      ·
        refine ⟨13046541112751798208808697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139163105202685847560626101 13046541112751798208808697)
        ·
          refine ⟨9784905834563848656606523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13046541112751798208808697 9784905834563848656606523)
          ·
            refine ⟨14677358751845772984909785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9784905834563848656606523 14677358751845772984909785)
            ·
              refine ⟨11008019063884329738682339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14677358751845772984909785 11008019063884329738682339)
              ·
                refine ⟨16512028595826494608023509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11008019063884329738682339 16512028595826494608023509)
                ·
                  refine ⟨387000670214683467375551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16512028595826494608023509 387000670214683467375551)
                  ·
                    rfl

theorem cell23_6783130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_6783130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783130 prefixEnd_6783130 := by exact prefixLift 6783130
  have htrace : WordTrace (prefixWord ++ tailWord_6783130) baseStart_6783130 baseEnd_6783130 := by
    simpa [prefixWord, tailWord_6783130, baseEnd_6783130] using wordTrace_append hprefix tailTrace_6783130
  have hstable : (prefixWord ++ tailWord_6783130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783130).length < 2 ^ (prefixWord ++ tailWord_6783130).sum := by decide
  have hdescent : baseEnd_6783130 < baseStart_6783130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783163 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 4]
def baseStart_6783163 : Nat := 118140960795 + 6783163 * 2 ^ 59
def prefixEnd_6783163 : Nat := 4983230072969 + 3 ^ 40 * 6783163 * 2
def baseEnd_6783163 : Nat := 3483022976793749577267307

theorem tailTrace_6783163 : CollatzResearch.WordTrace tailWord_6783163 prefixEnd_6783163 3483022976793749577267307 := by
  unfold tailWord_6783163
  simp only [CollatzResearch.WordTrace]
  refine ⟨247402279524766397854842143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164934853016510931903228095 247402279524766397854842143)
  ·
    refine ⟨371103419287149596782263215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247402279524766397854842143 371103419287149596782263215)
    ·
      refine ⟨556655128930724395173394823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371103419287149596782263215 556655128930724395173394823)
      ·
        refine ⟨834982693396086592760092235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556655128930724395173394823 834982693396086592760092235)
        ·
          refine ⟨1252474040094129889140138353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834982693396086592760092235 1252474040094129889140138353)
          ·
            refine ⟨939355530070597416855103765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1252474040094129889140138353 939355530070597416855103765)
            ·
              refine ⟨44032290472059253915082989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 939355530070597416855103765 44032290472059253915082989)
              ·
                refine ⟨16512108927022220218156121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44032290472059253915082989 16512108927022220218156121)
                ·
                  refine ⟨12384081695266665163617091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16512108927022220218156121 12384081695266665163617091)
                  ·
                    refine ⟨18576122542899997745425637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12384081695266665163617091 18576122542899997745425637)
                    ·
                      refine ⟨3483022976793749577267307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18576122542899997745425637 3483022976793749577267307)
                      ·
                        rfl

theorem cell23_6783163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 4].length) (baseStart_6783163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783163 prefixEnd_6783163 := by exact prefixLift 6783163
  have htrace : WordTrace (prefixWord ++ tailWord_6783163) baseStart_6783163 baseEnd_6783163 := by
    simpa [prefixWord, tailWord_6783163, baseEnd_6783163] using wordTrace_append hprefix tailTrace_6783163
  have hstable : (prefixWord ++ tailWord_6783163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783163).length < 2 ^ (prefixWord ++ tailWord_6783163).sum := by decide
  have hdescent : baseEnd_6783163 < baseStart_6783163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783164 : List Nat := [2, 2, 2, 3, 4, 1, 1, 3, 5]
def baseStart_6783164 : Nat := 118140960795 + 6783164 * 2 ^ 59
def prefixEnd_6783164 : Nat := 4983230072969 + 3 ^ 40 * 6783164 * 2
def baseEnd_6783164 : Nat := 387002610030489341483867

theorem tailTrace_6783164 : CollatzResearch.WordTrace tailWord_6783164 prefixEnd_6783164 387002610030489341483867 := by
  unfold tailWord_6783164
  simp only [CollatzResearch.WordTrace]
  refine ⟨123701157998881387512814273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164934877331841850017085697 123701157998881387512814273)
  ·
    refine ⟨92775868499161040634610705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123701157998881387512814273 92775868499161040634610705)
    ·
      refine ⟨69581901374370780475958029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92775868499161040634610705 69581901374370780475958029)
      ·
        refine ⟨26093213015389042678484261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69581901374370780475958029 26093213015389042678484261)
        ·
          refine ⟨4892477440385445502215799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26093213015389042678484261 4892477440385445502215799)
          ·
            refine ⟨7338716160578168253323699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892477440385445502215799 7338716160578168253323699)
            ·
              refine ⟨11008074240867252379985549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7338716160578168253323699 11008074240867252379985549)
              ·
                refine ⟨4128027840325219642494581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11008074240867252379985549 4128027840325219642494581)
                ·
                  refine ⟨387002610030489341483867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4128027840325219642494581 387002610030489341483867)
                  ·
                    rfl

theorem cell23_6783164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_6783164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783164 prefixEnd_6783164 := by exact prefixLift 6783164
  have htrace : WordTrace (prefixWord ++ tailWord_6783164) baseStart_6783164 baseEnd_6783164 := by
    simpa [prefixWord, tailWord_6783164, baseEnd_6783164] using wordTrace_append hprefix tailTrace_6783164
  have hstable : (prefixWord ++ tailWord_6783164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783164).length < 2 ^ (prefixWord ++ tailWord_6783164).sum := by decide
  have hdescent : baseEnd_6783164 < baseStart_6783164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783173 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 5, 4]
def baseStart_6783173 : Nat := 118140960795 + 6783173 * 2 ^ 59
def prefixEnd_6783173 : Nat := 4983230072969 + 3 ^ 40 * 6783173 * 2
def baseEnd_6783173 : Nat := 1161009370533431512714087

theorem tailTrace_6783173 : CollatzResearch.WordTrace tailWord_6783173 prefixEnd_6783173 1161009370533431512714087 := by
  unfold tailWord_6783173
  simp only [CollatzResearch.WordTrace]
  refine ⟨247402644254730169562706173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164935096169820113041804115 247402644254730169562706173)
  ·
    refine ⟨92775991595523813586014815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247402644254730169562706173 92775991595523813586014815)
    ·
      refine ⟨139163987393285720379022223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92775991595523813586014815 139163987393285720379022223)
      ·
        refine ⟨208745981089928580568533335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139163987393285720379022223 208745981089928580568533335)
        ·
          refine ⟨313118971634892870852800003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208745981089928580568533335 313118971634892870852800003)
          ·
            refine ⟨469678457452339306279200005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313118971634892870852800003 469678457452339306279200005)
            ·
              refine ⟨88064710772313619927350001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 469678457452339306279200005 88064710772313619927350001)
              ·
                refine ⟨66048533079235214945512501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88064710772313619927350001 66048533079235214945512501)
                ·
                  refine ⟨6192049976178301401141797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66048533079235214945512501 6192049976178301401141797)
                  ·
                    refine ⟨1161009370533431512714087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6192049976178301401141797 1161009370533431512714087)
                    ·
                      rfl

theorem cell23_6783173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_6783173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783173 prefixEnd_6783173 := by exact prefixLift 6783173
  have htrace : WordTrace (prefixWord ++ tailWord_6783173) baseStart_6783173 baseEnd_6783173 := by
    simpa [prefixWord, tailWord_6783173, baseEnd_6783173] using wordTrace_append hprefix tailTrace_6783173
  have hstable : (prefixWord ++ tailWord_6783173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783173).length < 2 ^ (prefixWord ++ tailWord_6783173).sum := by decide
  have hdescent : baseEnd_6783173 < baseStart_6783173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783274 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_6783274 : Nat := 118140960795 + 6783274 * 2 ^ 59
def prefixEnd_6783274 : Nat := 4983230072969 + 3 ^ 40 * 6783274 * 2
def baseEnd_6783274 : Nat := 3483079973146398642979297

theorem tailTrace_6783274 : CollatzResearch.WordTrace tailWord_6783274 prefixEnd_6783274 3483079973146398642979297 := by
  unfold tailWord_6783274
  simp only [CollatzResearch.WordTrace]
  refine ⟨61851582006841065953033219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164937552018242842541421917 61851582006841065953033219)
  ·
    refine ⟨92777373010261598929549829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61851582006841065953033219 92777373010261598929549829)
    ·
      refine ⟨17395757439424049799290593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92777373010261598929549829 17395757439424049799290593)
      ·
        refine ⟨13046818079568037349467945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17395757439424049799290593 13046818079568037349467945)
        ·
          refine ⟨9785113559676028012100959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13046818079568037349467945 9785113559676028012100959)
          ·
            refine ⟨14677670339514042018151439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9785113559676028012100959 14677670339514042018151439)
            ·
              refine ⟨22016505509271063027227159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14677670339514042018151439 22016505509271063027227159)
              ·
                refine ⟨33024758263906594540840739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22016505509271063027227159 33024758263906594540840739)
                ·
                  refine ⟨49537137395859891811261109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33024758263906594540840739 49537137395859891811261109)
                  ·
                    refine ⟨4644106630861864857305729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49537137395859891811261109 4644106630861864857305729)
                    ·
                      refine ⟨3483079973146398642979297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644106630861864857305729 3483079973146398642979297)
                      ·
                        rfl

theorem cell23_6783274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_6783274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783274 prefixEnd_6783274 := by exact prefixLift 6783274
  have htrace : WordTrace (prefixWord ++ tailWord_6783274) baseStart_6783274 baseEnd_6783274 := by
    simpa [prefixWord, tailWord_6783274, baseEnd_6783274] using wordTrace_append hprefix tailTrace_6783274
  have hstable : (prefixWord ++ tailWord_6783274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783274).length < 2 ^ (prefixWord ++ tailWord_6783274).sum := by decide
  have hdescent : baseEnd_6783274 < baseStart_6783274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783281 : List Nat := [1, 2, 2, 3, 4, 1, 2, 3, 1, 1, 3]
def baseStart_6783281 : Nat := 118140960795 + 6783281 * 2 ^ 59
def prefixEnd_6783281 : Nat := 4983230072969 + 3 ^ 40 * 6783281 * 2
def baseEnd_6783281 : Nat := 3483083567510980115591765

theorem tailTrace_6783281 : CollatzResearch.WordTrace tailWord_6783281 prefixEnd_6783281 3483083567510980115591765 := by
  unfold tailWord_6783281
  simp only [CollatzResearch.WordTrace]
  refine ⟨247406583338338904007637697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164937722225559269338425131 247406583338338904007637697)
  ·
    refine ⟨185554937503754178005728273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247406583338338904007637697 185554937503754178005728273)
    ·
      refine ⟨139166203127815633504296205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185554937503754178005728273 139166203127815633504296205)
      ·
        refine ⟨52187326172930862564111077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139166203127815633504296205 52187326172930862564111077)
        ·
          refine ⟨9785123657424536730770827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52187326172930862564111077 9785123657424536730770827)
          ·
            refine ⟨14677685486136805096156241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9785123657424536730770827 14677685486136805096156241)
            ·
              refine ⟨11008264114602603822117181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14677685486136805096156241 11008264114602603822117181)
              ·
                refine ⟨4128099042975976433293943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11008264114602603822117181 4128099042975976433293943)
                ·
                  refine ⟨6192148564463964649940915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4128099042975976433293943 6192148564463964649940915)
                  ·
                    refine ⟨9288222846695946974911373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6192148564463964649940915 9288222846695946974911373)
                    ·
                      refine ⟨3483083567510980115591765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9288222846695946974911373 3483083567510980115591765)
                      ·
                        rfl

theorem cell23_6783281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_6783281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783281 prefixEnd_6783281 := by exact prefixLift 6783281
  have htrace : WordTrace (prefixWord ++ tailWord_6783281) baseStart_6783281 baseEnd_6783281 := by
    simpa [prefixWord, tailWord_6783281, baseEnd_6783281] using wordTrace_append hprefix tailTrace_6783281
  have hstable : (prefixWord ++ tailWord_6783281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783281).length < 2 ^ (prefixWord ++ tailWord_6783281).sum := by decide
  have hdescent : baseEnd_6783281 < baseStart_6783281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783284 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_6783284 : Nat := 118140960795 + 6783284 * 2 ^ 59
def prefixEnd_6783284 : Nat := 4983230072969 + 3 ^ 40 * 6783284 * 2
def baseEnd_6783284 : Nat := 1161028369317647867951417

theorem tailTrace_6783284 : CollatzResearch.WordTrace tailWord_6783284 prefixEnd_6783284 1161028369317647867951417 := by
  unfold tailWord_6783284
  simp only [CollatzResearch.WordTrace]
  refine ⟨123703346378664017759998453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164937795171552023679997937 123703346378664017759998453)
  ·
    refine ⟨11597188722999751664999855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123703346378664017759998453 11597188722999751664999855)
    ·
      refine ⟨17395783084499627497499783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11597188722999751664999855 17395783084499627497499783)
      ·
        refine ⟨26093674626749441246249675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17395783084499627497499783 26093674626749441246249675)
        ·
          refine ⟨39140511940124161869374513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26093674626749441246249675 39140511940124161869374513)
          ·
            refine ⟨29355383955093121402030885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39140511940124161869374513 29355383955093121402030885)
            ·
              refine ⟨5504134491579960262880791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29355383955093121402030885 5504134491579960262880791)
              ·
                refine ⟨8256201737369940394321187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5504134491579960262880791 8256201737369940394321187)
                ·
                  refine ⟨12384302606054910591481781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8256201737369940394321187 12384302606054910591481781)
                  ·
                    refine ⟨1161028369317647867951417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12384302606054910591481781 1161028369317647867951417)
                    ·
                      rfl

theorem cell23_6783284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_6783284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783284 prefixEnd_6783284 := by exact prefixLift 6783284
  have htrace : WordTrace (prefixWord ++ tailWord_6783284) baseStart_6783284 baseEnd_6783284 := by
    simpa [prefixWord, tailWord_6783284, baseEnd_6783284] using wordTrace_append hprefix tailTrace_6783284
  have hstable : (prefixWord ++ tailWord_6783284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783284).length < 2 ^ (prefixWord ++ tailWord_6783284).sum := by decide
  have hdescent : baseEnd_6783284 < baseStart_6783284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783320 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 1, 3, 3]
def baseStart_6783320 : Nat := 118140960795 + 6783320 * 2 ^ 59
def prefixEnd_6783320 : Nat := 4983230072969 + 3 ^ 40 * 6783320 * 2
def baseEnd_6783320 : Nat := 3483103593256505463004085

theorem tailTrace_6783320 : CollatzResearch.WordTrace tailWord_6783320 prefixEnd_6783320 3483103593256505463004085 := by
  unfold tailWord_6783320
  simp only [CollatzResearch.WordTrace]
  refine ⟨123704002892598806834153707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164938670523465075778871609 123704002892598806834153707)
  ·
    refine ⟨185556004338898210251230561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123704002892598806834153707 185556004338898210251230561)
    ·
      refine ⟨139167003254173657688422921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185556004338898210251230561 139167003254173657688422921)
      ·
        refine ⟨104375252440630243266317191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139167003254173657688422921 104375252440630243266317191)
        ·
          refine ⟨156562878660945364899475787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104375252440630243266317191 156562878660945364899475787)
          ·
            refine ⟨234844317991418047349213681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156562878660945364899475787 234844317991418047349213681)
            ·
              refine ⟨176133238493563535511910261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234844317991418047349213681 176133238493563535511910261)
              ·
                refine ⟨16512491108771581454241587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176133238493563535511910261 16512491108771581454241587)
                ·
                  refine ⟨24768736663157372181362381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16512491108771581454241587 24768736663157372181362381)
                  ·
                    refine ⟨9288276248684014568010893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24768736663157372181362381 9288276248684014568010893)
                    ·
                      refine ⟨3483103593256505463004085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9288276248684014568010893 3483103593256505463004085)
                      ·
                        rfl

theorem cell23_6783320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_6783320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783320 prefixEnd_6783320 := by exact prefixLift 6783320
  have htrace : WordTrace (prefixWord ++ tailWord_6783320) baseStart_6783320 baseEnd_6783320 := by
    simpa [prefixWord, tailWord_6783320, baseEnd_6783320] using wordTrace_append hprefix tailTrace_6783320
  have hstable : (prefixWord ++ tailWord_6783320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783320).length < 2 ^ (prefixWord ++ tailWord_6783320).sum := by decide
  have hdescent : baseEnd_6783320 < baseStart_6783320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783338 : List Nat := [3, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_6783338 : Nat := 118140960795 + 6783338 * 2 ^ 59
def prefixEnd_6783338 : Nat := 4983230072969 + 3 ^ 40 * 6783338 * 2
def baseEnd_6783338 : Nat := 3483112835908286392579003

theorem tailTrace_6783338 : CollatzResearch.WordTrace tailWord_6783338 prefixEnd_6783338 3483112835908286392579003 := by
  unfold tailWord_6783338
  simp only [CollatzResearch.WordTrace]
  refine ⟨61852165574783100685615667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164939108199421601828308445 61852165574783100685615667)
  ·
    refine ⟨92778248362174651028423501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61852165574783100685615667 92778248362174651028423501)
    ·
      refine ⟨34791843135815494135658813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92778248362174651028423501 34791843135815494135658813)
      ·
        refine ⟨13046941175930810300872055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34791843135815494135658813 13046941175930810300872055)
        ·
          refine ⟨19570411763896215451308083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13046941175930810300872055 19570411763896215451308083)
          ·
            refine ⟨29355617645844323176962125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19570411763896215451308083 29355617645844323176962125)
            ·
              refine ⟨11008356617191621191360797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29355617645844323176962125 11008356617191621191360797)
              ·
                refine ⟨4128133731446857946760299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11008356617191621191360797 4128133731446857946760299)
                ·
                  refine ⟨6192200597170286920140449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4128133731446857946760299 6192200597170286920140449)
                  ·
                    refine ⟨4644150447877715190105337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6192200597170286920140449 4644150447877715190105337)
                    ·
                      refine ⟨3483112835908286392579003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644150447877715190105337 3483112835908286392579003)
                      ·
                        rfl

theorem cell23_6783338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_6783338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783338 prefixEnd_6783338 := by exact prefixLift 6783338
  have htrace : WordTrace (prefixWord ++ tailWord_6783338) baseStart_6783338 baseEnd_6783338 := by
    simpa [prefixWord, tailWord_6783338, baseEnd_6783338] using wordTrace_append hprefix tailTrace_6783338
  have hstable : (prefixWord ++ tailWord_6783338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783338).length < 2 ^ (prefixWord ++ tailWord_6783338).sum := by decide
  have hdescent : baseEnd_6783338 < baseStart_6783338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783371 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 2, 1, 3]
def baseStart_6783371 : Nat := 118140960795 + 6783371 * 2 ^ 59
def prefixEnd_6783371 : Nat := 4983230072969 + 3 ^ 40 * 6783371 * 2
def baseEnd_6783371 : Nat := 3483129780769884763466351

theorem tailTrace_6783371 : CollatzResearch.WordTrace tailWord_6783371 prefixEnd_6783371 3483129780769884763466351 := by
  unfold tailWord_6783371
  simp only [CollatzResearch.WordTrace]
  refine ⟨247409865908012849378413967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164939910605341899585609311 247409865908012849378413967)
  ·
    refine ⟨371114798862019274067620951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247409865908012849378413967 371114798862019274067620951)
    ·
      refine ⟨556672198293028911101431427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371114798862019274067620951 556672198293028911101431427)
      ·
        refine ⟨835008297439543366652147141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556672198293028911101431427 835008297439543366652147141)
        ·
          refine ⟨156564055769914381247277589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 835008297439543366652147141 156564055769914381247277589)
          ·
            refine ⟨7338940114214736620966137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156564055769914381247277589 7338940114214736620966137)
            ·
              refine ⟨5504205085661052465724603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7338940114214736620966137 5504205085661052465724603)
              ·
                refine ⟨8256307628491578698586905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5504205085661052465724603 8256307628491578698586905)
                ·
                  refine ⟨6192230721368684023940179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8256307628491578698586905 6192230721368684023940179)
                  ·
                    refine ⟨9288346082053026035910269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6192230721368684023940179 9288346082053026035910269)
                    ·
                      refine ⟨3483129780769884763466351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9288346082053026035910269 3483129780769884763466351)
                      ·
                        rfl

theorem cell23_6783371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 2, 1, 3].length) (baseStart_6783371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783371 prefixEnd_6783371 := by exact prefixLift 6783371
  have htrace : WordTrace (prefixWord ++ tailWord_6783371) baseStart_6783371 baseEnd_6783371 := by
    simpa [prefixWord, tailWord_6783371, baseEnd_6783371] using wordTrace_append hprefix tailTrace_6783371
  have hstable : (prefixWord ++ tailWord_6783371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783371).length < 2 ^ (prefixWord ++ tailWord_6783371).sum := by decide
  have hdescent : baseEnd_6783371 < baseStart_6783371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783394 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_6783394 : Nat := 118140960795 + 6783394 * 2 ^ 59
def prefixEnd_6783394 : Nat := 4983230072969 + 3 ^ 40 * 6783394 * 2
def baseEnd_6783394 : Nat := 3483141590824938173478745

theorem tailTrace_6783394 : CollatzResearch.WordTrace tailWord_6783394 prefixEnd_6783394 3483141590824938173478745 := by
  unfold tailWord_6783394
  simp only [CollatzResearch.WordTrace]
  refine ⟨61852676196732381076625309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164940469857953016204334157 61852676196732381076625309)
  ·
    refine ⟨23194753573774642903734491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61852676196732381076625309 23194753573774642903734491)
    ·
      refine ⟨34792130360661964355601737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23194753573774642903734491 34792130360661964355601737)
      ·
        refine ⟨26094097770496473266701303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34792130360661964355601737 26094097770496473266701303)
        ·
          refine ⟨39141146655744709900051955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26094097770496473266701303 39141146655744709900051955)
          ·
            refine ⟨58711719983617064850077933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39141146655744709900051955 58711719983617064850077933)
            ·
              refine ⟨22016894993856399318779225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58711719983617064850077933 22016894993856399318779225)
              ·
                refine ⟨16512671245392299489084419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22016894993856399318779225 16512671245392299489084419)
                ·
                  refine ⟨24769006868088449233626629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16512671245392299489084419 24769006868088449233626629)
                  ·
                    refine ⟨4644188787766584231304993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24769006868088449233626629 4644188787766584231304993)
                    ·
                      refine ⟨3483141590824938173478745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644188787766584231304993 3483141590824938173478745)
                      ·
                        rfl

theorem cell23_6783394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_6783394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783394 prefixEnd_6783394 := by exact prefixLift 6783394
  have htrace : WordTrace (prefixWord ++ tailWord_6783394) baseStart_6783394 baseEnd_6783394 := by
    simpa [prefixWord, tailWord_6783394, baseEnd_6783394] using wordTrace_append hprefix tailTrace_6783394
  have hstable : (prefixWord ++ tailWord_6783394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783394).length < 2 ^ (prefixWord ++ tailWord_6783394).sum := by decide
  have hdescent : baseEnd_6783394 < baseStart_6783394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783467 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 4, 4, 2]
def baseStart_6783467 : Nat := 118140960795 + 6783467 * 2 ^ 59
def prefixEnd_6783467 : Nat := 4983230072969 + 3 ^ 40 * 6783467 * 2
def baseEnd_6783467 : Nat := 3483179074912716387865909

theorem tailTrace_6783467 : CollatzResearch.WordTrace tailWord_6783467 prefixEnd_6783467 3483179074912716387865909 := by
  unfold tailWord_6783467
  simp only [CollatzResearch.WordTrace]
  refine ⟨247413367315665057773908655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164942244877110038515939103 247413367315665057773908655)
  ·
    refine ⟨371120050973497586660862983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247413367315665057773908655 371120050973497586660862983)
    ·
      refine ⟨556680076460246379991294475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371120050973497586660862983 556680076460246379991294475)
      ·
        refine ⟨835020114690369569986941713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556680076460246379991294475 835020114690369569986941713)
        ·
          refine ⟨626265086017777177490206285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835020114690369569986941713 626265086017777177490206285)
          ·
            refine ⟨234849407256666441558827357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 626265086017777177490206285 234849407256666441558827357)
            ·
              refine ⟨88068527721249915584560259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234849407256666441558827357 88068527721249915584560259)
              ·
                refine ⟨132102791581874873376840389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88068527721249915584560259 132102791581874873376840389)
                ·
                  refine ⟨24769273421601538758157573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132102791581874873376840389 24769273421601538758157573)
                  ·
                    refine ⟨4644238766550288517154545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24769273421601538758157573 4644238766550288517154545)
                    ·
                      refine ⟨3483179074912716387865909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644238766550288517154545 3483179074912716387865909)
                      ·
                        rfl

theorem cell23_6783467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 4, 2].length) (baseStart_6783467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783467 prefixEnd_6783467 := by exact prefixLift 6783467
  have htrace : WordTrace (prefixWord ++ tailWord_6783467) baseStart_6783467 baseEnd_6783467 := by
    simpa [prefixWord, tailWord_6783467, baseEnd_6783467] using wordTrace_append hprefix tailTrace_6783467
  have hstable : (prefixWord ++ tailWord_6783467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783467).length < 2 ^ (prefixWord ++ tailWord_6783467).sum := by decide
  have hdescent : baseEnd_6783467 < baseStart_6783467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783480 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_6783480 : Nat := 118140960795 + 6783480 * 2 ^ 59
def prefixEnd_6783480 : Nat := 4983230072969 + 3 ^ 40 * 6783480 * 2
def baseEnd_6783480 : Nat := 3483185750161224837003349

theorem tailTrace_6783480 : CollatzResearch.WordTrace tailWord_6783480 prefixEnd_6783480 3483185750161224837003349 := by
  unfold tailWord_6783480
  simp only [CollatzResearch.WordTrace]
  refine ⟨123706920732308980497065947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164942560976411973996087929 123706920732308980497065947)
  ·
    refine ⟨185560381098463470745598921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123706920732308980497065947 185560381098463470745598921)
    ·
      refine ⟨139170285823847603059199191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185560381098463470745598921 139170285823847603059199191)
      ·
        refine ⟨208755428735771404588798787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139170285823847603059199191 208755428735771404588798787)
        ·
          refine ⟨313133143103657106883198181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208755428735771404588798787 313133143103657106883198181)
          ·
            refine ⟨58712464331935707540599659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313133143103657106883198181 58712464331935707540599659)
            ·
              refine ⟨88068696497903561310899489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58712464331935707540599659 88068696497903561310899489)
              ·
                refine ⟨66051522373427670983174617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88068696497903561310899489 66051522373427670983174617)
                ·
                  refine ⟨49538641780070753237380963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66051522373427670983174617 49538641780070753237380963)
                  ·
                    refine ⟨74307962670106129856071445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49538641780070753237380963 74307962670106129856071445)
                    ·
                      refine ⟨3483185750161224837003349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74307962670106129856071445 3483185750161224837003349)
                      ·
                        rfl

theorem cell23_6783480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_6783480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783480 prefixEnd_6783480 := by exact prefixLift 6783480
  have htrace : WordTrace (prefixWord ++ tailWord_6783480) baseStart_6783480 baseEnd_6783480 := by
    simpa [prefixWord, tailWord_6783480, baseEnd_6783480] using wordTrace_append hprefix tailTrace_6783480
  have hstable : (prefixWord ++ tailWord_6783480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783480).length < 2 ^ (prefixWord ++ tailWord_6783480).sum := by decide
  have hdescent : baseEnd_6783480 < baseStart_6783480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783501 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6783501 : Nat := 118140960795 + 6783501 * 2 ^ 59
def prefixEnd_6783501 : Nat := 4983230072969 + 3 ^ 40 * 6783501 * 2
def baseEnd_6783501 : Nat := 3483196533254969254840753

theorem tailTrace_6783501 : CollatzResearch.WordTrace tailWord_6783501 prefixEnd_6783501 3483196533254969254840753 := by
  unfold tailWord_6783501
  simp only [CollatzResearch.WordTrace]
  refine ⟨247414607397541881580646357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164943071598361254387097571 247414607397541881580646357)
  ·
    refine ⟨5798779860879887849546399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 247414607397541881580646357 5798779860879887849546399)
    ·
      refine ⟨8698169791319831774319599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5798779860879887849546399 8698169791319831774319599)
      ·
        refine ⟨13047254686979747661479399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8698169791319831774319599 13047254686979747661479399)
        ·
          refine ⟨19570882030469621492219099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13047254686979747661479399 19570882030469621492219099)
          ·
            refine ⟨29356323045704432238328649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19570882030469621492219099 29356323045704432238328649)
            ·
              refine ⟨22017242284278324178746487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29356323045704432238328649 22017242284278324178746487)
              ·
                refine ⟨33025863426417486268119731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22017242284278324178746487 33025863426417486268119731)
                ·
                  refine ⟨49538795139626229402179597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33025863426417486268119731 49538795139626229402179597)
                  ·
                    refine ⟨18577048177359836025817349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49538795139626229402179597 18577048177359836025817349)
                    ·
                      refine ⟨3483196533254969254840753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18577048177359836025817349 3483196533254969254840753)
                      ·
                        rfl

theorem cell23_6783501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6783501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783501 prefixEnd_6783501 := by exact prefixLift 6783501
  have htrace : WordTrace (prefixWord ++ tailWord_6783501) baseStart_6783501 baseEnd_6783501 := by
    simpa [prefixWord, tailWord_6783501, baseEnd_6783501] using wordTrace_append hprefix tailTrace_6783501
  have hstable : (prefixWord ++ tailWord_6783501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783501).length < 2 ^ (prefixWord ++ tailWord_6783501).sum := by decide
  have hdescent : baseEnd_6783501 < baseStart_6783501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783544 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 4, 3, 2]
def baseStart_6783544 : Nat := 118140960795 + 6783544 * 2 ^ 59
def prefixEnd_6783544 : Nat := 4983230072969 + 3 ^ 40 * 6783544 * 2
def baseEnd_6783544 : Nat := 3483218612923112586603055

theorem tailTrace_6783544 : CollatzResearch.WordTrace tailWord_6783544 prefixEnd_6783544 3483218612923112586603055 := by
  unfold tailWord_6783544
  simp only [CollatzResearch.WordTrace]
  refine ⟨123708087868193049962230843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164944117157590733282974457 123708087868193049962230843)
  ·
    refine ⟨185562131802289574943346265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123708087868193049962230843 185562131802289574943346265)
    ·
      refine ⟨139171598851717181207509699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185562131802289574943346265 139171598851717181207509699)
      ·
        refine ⟨208757398277575771811264549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139171598851717181207509699 208757398277575771811264549)
        ·
          refine ⟨39142012177045457214612103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208757398277575771811264549 39142012177045457214612103)
          ·
            refine ⟨58713018265568185821918155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39142012177045457214612103 58713018265568185821918155)
            ·
              refine ⟨88069527398352278732877233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58713018265568185821918155 88069527398352278732877233)
              ·
                refine ⟨66052145548764209049657925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88069527398352278732877233 66052145548764209049657925)
                ·
                  refine ⟨12384777290393289196810861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66052145548764209049657925 12384777290393289196810861)
                  ·
                    refine ⟨4644291483897483448804073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12384777290393289196810861 4644291483897483448804073)
                    ·
                      refine ⟨3483218612923112586603055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644291483897483448804073 3483218612923112586603055)
                      ·
                        rfl

theorem cell23_6783544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 3, 2].length) (baseStart_6783544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783544 prefixEnd_6783544 := by exact prefixLift 6783544
  have htrace : WordTrace (prefixWord ++ tailWord_6783544) baseStart_6783544 baseEnd_6783544 := by
    simpa [prefixWord, tailWord_6783544, baseEnd_6783544] using wordTrace_append hprefix tailTrace_6783544
  have hstable : (prefixWord ++ tailWord_6783544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783544).length < 2 ^ (prefixWord ++ tailWord_6783544).sum := by decide
  have hdescent : baseEnd_6783544 < baseStart_6783544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783567 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 6, 4]
def baseStart_6783567 : Nat := 118140960795 + 6783567 * 2 ^ 59
def prefixEnd_6783567 : Nat := 4983230072969 + 3 ^ 40 * 6783567 * 2
def baseEnd_6783567 : Nat := 1161076807659388665538483

theorem tailTrace_6783567 : CollatzResearch.WordTrace tailWord_6783567 prefixEnd_6783567 1161076807659388665538483 := by
  unfold tailWord_6783567
  simp only [CollatzResearch.WordTrace]
  refine ⟨247417014615302774852548955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164944676410201849901699303 247417014615302774852548955)
  ·
    refine ⟨371125521922954162278823433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247417014615302774852548955 371125521922954162278823433)
    ·
      refine ⟨278344141442215621709117575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371125521922954162278823433 278344141442215621709117575)
      ·
        refine ⟨417516212163323432563676363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278344141442215621709117575 417516212163323432563676363)
        ·
          refine ⟨626274318244985148845514545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417516212163323432563676363 626274318244985148845514545)
          ·
            refine ⟨469705738683738861634135909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626274318244985148845514545 469705738683738861634135909)
            ·
              refine ⟨88069826003201036556400483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 469705738683738861634135909 88069826003201036556400483)
              ·
                refine ⟨132104739004801554834600725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88069826003201036556400483 132104739004801554834600725)
                ·
                  refine ⟨6192409640850072882871909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132104739004801554834600725 6192409640850072882871909)
                  ·
                    refine ⟨1161076807659388665538483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6192409640850072882871909 1161076807659388665538483)
                    ·
                      rfl

theorem cell23_6783567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 4].length) (baseStart_6783567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783567 prefixEnd_6783567 := by exact prefixLift 6783567
  have htrace : WordTrace (prefixWord ++ tailWord_6783567) baseStart_6783567 baseEnd_6783567 := by
    simpa [prefixWord, tailWord_6783567, baseEnd_6783567] using wordTrace_append hprefix tailTrace_6783567
  have hstable : (prefixWord ++ tailWord_6783567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783567).length < 2 ^ (prefixWord ++ tailWord_6783567).sum := by decide
  have hdescent : baseEnd_6783567 < baseStart_6783567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783584 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 2, 4]
def baseStart_6783584 : Nat := 118140960795 + 6783584 * 2 ^ 59
def prefixEnd_6783584 : Nat := 4983230072969 + 3 ^ 40 * 6783584 * 2
def baseEnd_6783584 : Nat := 1161079717383097476700957

theorem tailTrace_6783584 : CollatzResearch.WordTrace tailWord_6783584 prefixEnd_6783584 1161079717383097476700957 := by
  unfold tailWord_6783584
  simp only [CollatzResearch.WordTrace]
  refine ⟨123708817328120593377958903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164945089770827457837278537 123708817328120593377958903)
  ·
    refine ⟨185563225992180890066938355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123708817328120593377958903 185563225992180890066938355)
    ·
      refine ⟨278344838988271335100407533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185563225992180890066938355 278344838988271335100407533)
      ·
        refine ⟨104379314620601750662652825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278344838988271335100407533 104379314620601750662652825)
        ·
          refine ⟨78284485965451312996989619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104379314620601750662652825 78284485965451312996989619)
          ·
            refine ⟨117426728948176969495484429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78284485965451312996989619 117426728948176969495484429)
            ·
              refine ⟨44035023355566363560806661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117426728948176969495484429 44035023355566363560806661)
              ·
                refine ⟨8256566879168693167651249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44035023355566363560806661 8256566879168693167651249)
                ·
                  refine ⟨6192425159376519875738437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8256566879168693167651249 6192425159376519875738437)
                  ·
                    refine ⟨1161079717383097476700957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6192425159376519875738437 1161079717383097476700957)
                    ·
                      rfl

theorem cell23_6783584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2, 4].length) (baseStart_6783584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783584 prefixEnd_6783584 := by exact prefixLift 6783584
  have htrace : WordTrace (prefixWord ++ tailWord_6783584) baseStart_6783584 baseEnd_6783584 := by
    simpa [prefixWord, tailWord_6783584, baseEnd_6783584] using wordTrace_append hprefix tailTrace_6783584
  have hstable : (prefixWord ++ tailWord_6783584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783584).length < 2 ^ (prefixWord ++ tailWord_6783584).sum := by decide
  have hdescent : baseEnd_6783584 < baseStart_6783584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783585 : List Nat := [1, 2, 3, 1, 1, 6, 2, 2, 1, 1, 3]
def baseStart_6783585 : Nat := 118140960795 + 6783585 * 2 ^ 59
def prefixEnd_6783585 : Nat := 4983230072969 + 3 ^ 40 * 6783585 * 2
def baseEnd_6783585 : Nat := 3483239665629946926190367

theorem tailTrace_6783585 : CollatzResearch.WordTrace tailWord_6783585 prefixEnd_6783585 3483239665629946926190367 := by
  unfold tailWord_6783585
  simp only [CollatzResearch.WordTrace]
  refine ⟨247417671129237563926704209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164945114086158375951136139 247417671129237563926704209)
  ·
    refine ⟨185563253346928172945028157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247417671129237563926704209 185563253346928172945028157)
    ·
      refine ⟨69586220005098064854385559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185563253346928172945028157 69586220005098064854385559)
      ·
        refine ⟨104379330007647097281578339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69586220005098064854385559 104379330007647097281578339)
        ·
          refine ⟨156568995011470645922367509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104379330007647097281578339 156568995011470645922367509)
          ·
            refine ⟨7339171641162686527610977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156568995011470645922367509 7339171641162686527610977)
            ·
              refine ⟨5504378730872014895708233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7339171641162686527610977 5504378730872014895708233)
              ·
                refine ⟨4128284048154011171781175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5504378730872014895708233 4128284048154011171781175)
                ·
                  refine ⟨6192426072231016757671763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4128284048154011171781175 6192426072231016757671763)
                  ·
                    refine ⟨9288639108346525136507645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6192426072231016757671763 9288639108346525136507645)
                    ·
                      refine ⟨3483239665629946926190367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9288639108346525136507645 3483239665629946926190367)
                      ·
                        rfl

theorem cell23_6783585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_6783585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783585 prefixEnd_6783585 := by exact prefixLift 6783585
  have htrace : WordTrace (prefixWord ++ tailWord_6783585) baseStart_6783585 baseEnd_6783585 := by
    simpa [prefixWord, tailWord_6783585, baseEnd_6783585] using wordTrace_append hprefix tailTrace_6783585
  have hstable : (prefixWord ++ tailWord_6783585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783585).length < 2 ^ (prefixWord ++ tailWord_6783585).sum := by decide
  have hdescent : baseEnd_6783585 < baseStart_6783585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783587 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 4]
def baseStart_6783587 : Nat := 118140960795 + 6783587 * 2 ^ 59
def prefixEnd_6783587 : Nat := 4983230072969 + 3 ^ 40 * 6783587 * 2
def baseEnd_6783587 : Nat := 3483240692591255918365357

theorem tailTrace_6783587 : CollatzResearch.WordTrace tailWord_6783587 prefixEnd_6783587 3483240692591255918365357 := by
  unfold tailWord_6783587
  simp only [CollatzResearch.WordTrace]
  refine ⟨247417744075230318268277015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164945162716820212178851343 247417744075230318268277015)
  ·
    refine ⟨371126616112845477402415523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247417744075230318268277015 371126616112845477402415523)
    ·
      refine ⟨556689924169268216103623285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371126616112845477402415523 556689924169268216103623285)
      ·
        refine ⟨52189680390868895259714683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 556689924169268216103623285 52189680390868895259714683)
        ·
          refine ⟨78284520586303342889572025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52189680390868895259714683 78284520586303342889572025)
          ·
            refine ⟨58713390439727507167179019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78284520586303342889572025 58713390439727507167179019)
            ·
              refine ⟨88070085659591260750768529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58713390439727507167179019 88070085659591260750768529)
              ·
                refine ⟨66052564244693445563076397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88070085659591260750768529 66052564244693445563076397)
                ·
                  refine ⟨24769711591760042086153649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66052564244693445563076397 24769711591760042086153649)
                  ·
                    refine ⟨18577283693820031564615237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24769711591760042086153649 18577283693820031564615237)
                    ·
                      refine ⟨3483240692591255918365357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18577283693820031564615237 3483240692591255918365357)
                      ·
                        rfl

theorem cell23_6783587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_6783587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783587 prefixEnd_6783587 := by exact prefixLift 6783587
  have htrace : WordTrace (prefixWord ++ tailWord_6783587) baseStart_6783587 baseEnd_6783587 := by
    simpa [prefixWord, tailWord_6783587, baseEnd_6783587] using wordTrace_append hprefix tailTrace_6783587
  have hstable : (prefixWord ++ tailWord_6783587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783587).length < 2 ^ (prefixWord ++ tailWord_6783587).sum := by decide
  have hdescent : baseEnd_6783587 < baseStart_6783587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783591 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_6783591 : Nat := 118140960795 + 6783591 * 2 ^ 59
def prefixEnd_6783591 : Nat := 4983230072969 + 3 ^ 40 * 6783591 * 2
def baseEnd_6783591 : Nat := 3483242746513873902715339

theorem tailTrace_6783591 : CollatzResearch.WordTrace tailWord_6783591 prefixEnd_6783591 3483242746513873902715339 := by
  unfold tailWord_6783591
  simp only [CollatzResearch.WordTrace]
  refine ⟨247417889967215826951422627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164945259978143884634281751 247417889967215826951422627)
  ·
    refine ⟨371126834950823740427133941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247417889967215826951422627 371126834950823740427133941)
    ·
      refine ⟨34793140776639725665043807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 371126834950823740427133941 34793140776639725665043807)
      ·
        refine ⟨52189711164959588497565711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34793140776639725665043807 52189711164959588497565711)
        ·
          refine ⟨78284566747439382746348567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52189711164959588497565711 78284566747439382746348567)
          ·
            refine ⟨117426850121159074119522851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78284566747439382746348567 117426850121159074119522851)
            ·
              refine ⟨176140275181738611179284277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117426850121159074119522851 176140275181738611179284277)
              ·
                refine ⟨16513150798287994798057901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176140275181738611179284277 16513150798287994798057901)
                ·
                  refine ⟨6192431549357998049271713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16513150798287994798057901 6192431549357998049271713)
                  ·
                    refine ⟨4644323662018498536953785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6192431549357998049271713 4644323662018498536953785)
                    ·
                      refine ⟨3483242746513873902715339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644323662018498536953785 3483242746513873902715339)
                      ·
                        rfl

theorem cell23_6783591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_6783591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783591 prefixEnd_6783591 := by exact prefixLift 6783591
  have htrace : WordTrace (prefixWord ++ tailWord_6783591) baseStart_6783591 baseEnd_6783591 := by
    simpa [prefixWord, tailWord_6783591, baseEnd_6783591] using wordTrace_append hprefix tailTrace_6783591
  have hstable : (prefixWord ++ tailWord_6783591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783591).length < 2 ^ (prefixWord ++ tailWord_6783591).sum := by decide
  have hdescent : baseEnd_6783591 < baseStart_6783591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783594 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_6783594 : Nat := 118140960795 + 6783594 * 2 ^ 59
def prefixEnd_6783594 : Nat := 4983230072969 + 3 ^ 40 * 6783594 * 2
def baseEnd_6783594 : Nat := 3483244286955837390977825

theorem tailTrace_6783594 : CollatzResearch.WordTrace tailWord_6783594 prefixEnd_6783594 3483244286955837390977825 := by
  unfold tailWord_6783594
  simp only [CollatzResearch.WordTrace]
  refine ⟨61854499846551239615945459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164945332924136638975854557 61854499846551239615945459)
  ·
    refine ⟨92781749769826859423918189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61854499846551239615945459 92781749769826859423918189)
    ·
      refine ⟨34793156163685072283969321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92781749769826859423918189 34793156163685072283969321)
      ·
        refine ⟨26094867122763804212976991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34793156163685072283969321 26094867122763804212976991)
        ·
          refine ⟨39142300684145706319465487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26094867122763804212976991 39142300684145706319465487)
          ·
            refine ⟨58713451026218559479198231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39142300684145706319465487 58713451026218559479198231)
            ·
              refine ⟨88070176539327839218797347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58713451026218559479198231 88070176539327839218797347)
              ·
                refine ⟨132105264808991758828196021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88070176539327839218797347 132105264808991758828196021)
                ·
                  refine ⟨12384868575842977390143377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132105264808991758828196021 12384868575842977390143377)
                  ·
                    refine ⟨9288651431882233042607533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12384868575842977390143377 9288651431882233042607533)
                    ·
                      refine ⟨3483244286955837390977825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9288651431882233042607533 3483244286955837390977825)
                      ·
                        rfl

theorem cell23_6783594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_6783594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783594 prefixEnd_6783594 := by exact prefixLift 6783594
  have htrace : WordTrace (prefixWord ++ tailWord_6783594) baseStart_6783594 baseEnd_6783594 := by
    simpa [prefixWord, tailWord_6783594, baseEnd_6783594] using wordTrace_append hprefix tailTrace_6783594
  have hstable : (prefixWord ++ tailWord_6783594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783594).length < 2 ^ (prefixWord ++ tailWord_6783594).sum := by decide
  have hdescent : baseEnd_6783594 < baseStart_6783594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783655 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_6783655 : Nat := 118140960795 + 6783655 * 2 ^ 59
def prefixEnd_6783655 : Nat := 4983230072969 + 3 ^ 40 * 6783655 * 2
def baseEnd_6783655 : Nat := 3483275609275761652315045

theorem tailTrace_6783655 : CollatzResearch.WordTrace tailWord_6783655 prefixEnd_6783655 3483275609275761652315045 := by
  unfold tailWord_6783655
  simp only [CollatzResearch.WordTrace]
  refine ⟨247420224238983965881752419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164946816159322643921168279 247420224238983965881752419)
  ·
    refine ⟨371130336358475948822628629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247420224238983965881752419 371130336358475948822628629)
    ·
      refine ⟨17396734516803560101060717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 371130336358475948822628629 17396734516803560101060717)
      ·
        refine ⟨6523775443801335037897769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17396734516803560101060717 6523775443801335037897769)
        ·
          refine ⟨4892831582851001278423327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6523775443801335037897769 4892831582851001278423327)
          ·
            refine ⟨7339247374276501917634991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892831582851001278423327 7339247374276501917634991)
            ·
              refine ⟨11008871061414752876452487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7339247374276501917634991 11008871061414752876452487)
              ·
                refine ⟨16513306592122129314678731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11008871061414752876452487 16513306592122129314678731)
                ·
                  refine ⟨24769959888183193972018097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16513306592122129314678731 24769959888183193972018097)
                  ·
                    refine ⟨18577469916137395479013573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24769959888183193972018097 18577469916137395479013573)
                    ·
                      refine ⟨3483275609275761652315045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18577469916137395479013573 3483275609275761652315045)
                      ·
                        rfl

theorem cell23_6783655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_6783655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783655 prefixEnd_6783655 := by exact prefixLift 6783655
  have htrace : WordTrace (prefixWord ++ tailWord_6783655) baseStart_6783655 baseEnd_6783655 := by
    simpa [prefixWord, tailWord_6783655, baseEnd_6783655] using wordTrace_append hprefix tailTrace_6783655
  have hstable : (prefixWord ++ tailWord_6783655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783655).length < 2 ^ (prefixWord ++ tailWord_6783655).sum := by decide
  have hdescent : baseEnd_6783655 < baseStart_6783655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783684 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_6783684 : Nat := 118140960795 + 6783684 * 2 ^ 59
def prefixEnd_6783684 : Nat := 4983230072969 + 3 ^ 40 * 6783684 * 2
def baseEnd_6783684 : Nat := 3483290500214742038852411

theorem tailTrace_6783684 : CollatzResearch.WordTrace tailWord_6783684 prefixEnd_6783684 3483290500214742038852411 := by
  unfold tailWord_6783684
  simp only [CollatzResearch.WordTrace]
  refine ⟨123710640977939451917279053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164947521303919269223038737 123710640977939451917279053)
  ·
    refine ⟨46391490366727294468979645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123710640977939451917279053 46391490366727294468979645)
    ·
      refine ⟨17396808887522735425867367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46391490366727294468979645 17396808887522735425867367)
      ·
        refine ⟨26095213331284103138801051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17396808887522735425867367 26095213331284103138801051)
        ·
          refine ⟨39142819996926154708201577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26095213331284103138801051 39142819996926154708201577)
          ·
            refine ⟨29357114997694616031151183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39142819996926154708201577 29357114997694616031151183)
            ·
              refine ⟨44035672496541924046726775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29357114997694616031151183 44035672496541924046726775)
              ·
                refine ⟨66053508744812886070090163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44035672496541924046726775 66053508744812886070090163)
                ·
                  refine ⟨99080263117219329105135245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66053508744812886070090163 99080263117219329105135245)
                  ·
                    refine ⟨37155098668957248414425717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99080263117219329105135245 37155098668957248414425717)
                    ·
                      refine ⟨3483290500214742038852411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37155098668957248414425717 3483290500214742038852411)
                      ·
                        rfl

theorem cell23_6783684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_6783684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783684 prefixEnd_6783684 := by exact prefixLift 6783684
  have htrace : WordTrace (prefixWord ++ tailWord_6783684) baseStart_6783684 baseEnd_6783684 := by
    simpa [prefixWord, tailWord_6783684, baseEnd_6783684] using wordTrace_append hprefix tailTrace_6783684
  have hstable : (prefixWord ++ tailWord_6783684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783684).length < 2 ^ (prefixWord ++ tailWord_6783684).sum := by decide
  have hdescent : baseEnd_6783684 < baseStart_6783684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783697 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_6783697 : Nat := 118140960795 + 6783697 * 2 ^ 59
def prefixEnd_6783697 : Nat := 4983230072969 + 3 ^ 40 * 6783697 * 2
def baseEnd_6783697 : Nat := 3483297175463250487989851

theorem tailTrace_6783697 : CollatzResearch.WordTrace tailWord_6783697 prefixEnd_6783697 3483297175463250487989851 := by
  unfold tailWord_6783697
  simp only [CollatzResearch.WordTrace]
  refine ⟨247421756104831807054781345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164947837403221204703187563 247421756104831807054781345)
  ·
    refine ⟨185566317078623855291086009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247421756104831807054781345 185566317078623855291086009)
    ·
      refine ⟨139174737808967891468314507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185566317078623855291086009 139174737808967891468314507)
      ·
        refine ⟨208762106713451837202471761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139174737808967891468314507 208762106713451837202471761)
        ·
          refine ⟨156571580035088877901853821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208762106713451837202471761 156571580035088877901853821)
          ·
            refine ⟨58714342513158329213195183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156571580035088877901853821 58714342513158329213195183)
            ·
              refine ⟨88071513769737493819792775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58714342513158329213195183 88071513769737493819792775)
              ·
                refine ⟨132107270654606240729689163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88071513769737493819792775 132107270654606240729689163)
                ·
                  refine ⟨198160905981909361094533745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132107270654606240729689163 198160905981909361094533745)
                  ·
                    refine ⟨148620679486432020820900309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198160905981909361094533745 148620679486432020820900309)
                    ·
                      refine ⟨3483297175463250487989851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148620679486432020820900309 3483297175463250487989851)
                      ·
                        rfl

theorem cell23_6783697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_6783697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783697 prefixEnd_6783697 := by exact prefixLift 6783697
  have htrace : WordTrace (prefixWord ++ tailWord_6783697) baseStart_6783697 baseEnd_6783697 := by
    simpa [prefixWord, tailWord_6783697, baseEnd_6783697] using wordTrace_append hprefix tailTrace_6783697
  have hstable : (prefixWord ++ tailWord_6783697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783697).length < 2 ^ (prefixWord ++ tailWord_6783697).sum := by decide
  have hdescent : baseEnd_6783697 < baseStart_6783697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783704 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 7]
def baseStart_6783704 : Nat := 118140960795 + 6783704 * 2 ^ 59
def prefixEnd_6783704 : Nat := 4983230072969 + 3 ^ 40 * 6783704 * 2
def baseEnd_6783704 : Nat := 387033418869759106733591

theorem tailTrace_6783704 : CollatzResearch.WordTrace tailWord_6783704 prefixEnd_6783704 387033418869759106733591 := by
  unfold tailWord_6783704
  simp only [CollatzResearch.WordTrace]
  refine ⟨123711005707903223625143083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164948007610537631500190777 123711005707903223625143083)
  ·
    refine ⟨185566508561854835437714625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123711005707903223625143083 185566508561854835437714625)
    ·
      refine ⟨139174881421391126578285969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185566508561854835437714625 139174881421391126578285969)
      ·
        refine ⟨104381161066043344933714477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139174881421391126578285969 104381161066043344933714477)
        ·
          refine ⟨39142935399766254350142929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104381161066043344933714477 39142935399766254350142929)
          ·
            refine ⟨29357201549824690762607197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39142935399766254350142929 29357201549824690762607197)
            ·
              refine ⟨11008950581184259035977699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29357201549824690762607197 11008950581184259035977699)
              ·
                refine ⟨16513425871776388553966549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11008950581184259035977699 16513425871776388553966549)
                ·
                  refine ⟨387033418869759106733591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16513425871776388553966549 387033418869759106733591)
                  ·
                    rfl

theorem cell23_6783704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 7].length) (baseStart_6783704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783704 prefixEnd_6783704 := by exact prefixLift 6783704
  have htrace : WordTrace (prefixWord ++ tailWord_6783704) baseStart_6783704 baseEnd_6783704 := by
    simpa [prefixWord, tailWord_6783704, baseEnd_6783704] using wordTrace_append hprefix tailTrace_6783704
  have hstable : (prefixWord ++ tailWord_6783704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783704).length < 2 ^ (prefixWord ++ tailWord_6783704).sum := by decide
  have hdescent : baseEnd_6783704 < baseStart_6783704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783715 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 2, 2, 2]
def baseStart_6783715 : Nat := 118140960795 + 6783715 * 2 ^ 59
def prefixEnd_6783715 : Nat := 4983230072969 + 3 ^ 40 * 6783715 * 2
def baseEnd_6783715 : Nat := 3483306418115031417564769

theorem tailTrace_6783715 : CollatzResearch.WordTrace tailWord_6783715 prefixEnd_6783715 3483306418115031417564769 := by
  unfold tailWord_6783715
  simp only [CollatzResearch.WordTrace]
  refine ⟨247422412618766596128936599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164948275079177730752624399 247422412618766596128936599)
  ·
    refine ⟨371133618928149894193404899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247422412618766596128936599 371133618928149894193404899)
    ·
      refine ⟨556700428392224841290107349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371133618928149894193404899 556700428392224841290107349)
      ·
        refine ⟨13047666290442769717736891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 556700428392224841290107349 13047666290442769717736891)
        ·
          refine ⟨19571499435664154576605337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13047666290442769717736891 19571499435664154576605337)
          ·
            refine ⟨14678624576748115932454003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19571499435664154576605337 14678624576748115932454003)
            ·
              refine ⟨22017936865122173898681005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14678624576748115932454003 22017936865122173898681005)
              ·
                refine ⟨8256726324420815212005377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22017936865122173898681005 8256726324420815212005377)
                ·
                  refine ⟨6192544743315611409004033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8256726324420815212005377 6192544743315611409004033)
                  ·
                    refine ⟨4644408557486708556753025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6192544743315611409004033 4644408557486708556753025)
                    ·
                      refine ⟨3483306418115031417564769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644408557486708556753025 3483306418115031417564769)
                      ·
                        rfl

theorem cell23_6783715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_6783715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783715 prefixEnd_6783715 := by exact prefixLift 6783715
  have htrace : WordTrace (prefixWord ++ tailWord_6783715) baseStart_6783715 baseEnd_6783715 := by
    simpa [prefixWord, tailWord_6783715, baseEnd_6783715] using wordTrace_append hprefix tailTrace_6783715
  have hstable : (prefixWord ++ tailWord_6783715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783715).length < 2 ^ (prefixWord ++ tailWord_6783715).sum := by decide
  have hdescent : baseEnd_6783715 < baseStart_6783715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783732 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6783732 : Nat := 118140960795 + 6783732 * 2 ^ 59
def prefixEnd_6783732 : Nat := 4983230072969 + 3 ^ 40 * 6783732 * 2
def baseEnd_6783732 : Nat := 3483315147286157851052191

theorem tailTrace_6783732 : CollatzResearch.WordTrace tailWord_6783732 prefixEnd_6783732 3483315147286157851052191 := by
  unfold tailWord_6783732
  simp only [CollatzResearch.WordTrace]
  refine ⟨123711516329852504016152725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164948688439803338688203633 123711516329852504016152725)
  ·
    refine ⟨5798977327961836125757159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 123711516329852504016152725 5798977327961836125757159)
    ·
      refine ⟨8698465991942754188635739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5798977327961836125757159 8698465991942754188635739)
      ·
        refine ⟨13047698987914131282953609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8698465991942754188635739 13047698987914131282953609)
        ·
          refine ⟨9785774240935598462215207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13047698987914131282953609 9785774240935598462215207)
          ·
            refine ⟨14678661361403397693322811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9785774240935598462215207 14678661361403397693322811)
            ·
              refine ⟨22017992042105096539984217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14678661361403397693322811 22017992042105096539984217)
              ·
                refine ⟨16513494031578822404988163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22017992042105096539984217 16513494031578822404988163)
                ·
                  refine ⟨24770241047368233607482245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16513494031578822404988163 24770241047368233607482245)
                  ·
                    refine ⟨4644420196381543801402921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24770241047368233607482245 4644420196381543801402921)
                    ·
                      refine ⟨3483315147286157851052191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644420196381543801402921 3483315147286157851052191)
                      ·
                        rfl

theorem cell23_6783732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6783732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783732 prefixEnd_6783732 := by exact prefixLift 6783732
  have htrace : WordTrace (prefixWord ++ tailWord_6783732) baseStart_6783732 baseEnd_6783732 := by
    simpa [prefixWord, tailWord_6783732, baseEnd_6783732] using wordTrace_append hprefix tailTrace_6783732
  have hstable : (prefixWord ++ tailWord_6783732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783732).length < 2 ^ (prefixWord ++ tailWord_6783732).sum := by decide
  have hdescent : baseEnd_6783732 < baseStart_6783732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783751 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 2, 5]
def baseStart_6783751 : Nat := 118140960795 + 6783751 * 2 ^ 59
def prefixEnd_6783751 : Nat := 4983230072969 + 3 ^ 40 * 6783751 * 2
def baseEnd_6783751 : Nat := 1161108301139531092238201

theorem tailTrace_6783751 : CollatzResearch.WordTrace tailWord_6783751 prefixEnd_6783751 1161108301139531092238201 := by
  unfold tailWord_6783751
  simp only [CollatzResearch.WordTrace]
  refine ⟨247423725646636174277247107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164949150431090782851498071 247423725646636174277247107)
  ·
    refine ⟨371135588469954261415870661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247423725646636174277247107 371135588469954261415870661)
    ·
      refine ⟨69587922838116424015475749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371135588469954261415870661 69587922838116424015475749)
      ·
        refine ⟨13047735532146829502901703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69587922838116424015475749 13047735532146829502901703)
        ·
          refine ⟨19571603298220244254352555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13047735532146829502901703 19571603298220244254352555)
          ·
            refine ⟨29357404947330366381528833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19571603298220244254352555 29357404947330366381528833)
            ·
              refine ⟨22018053710497774786146625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29357404947330366381528833 22018053710497774786146625)
              ·
                refine ⟨16513540282873331089609969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22018053710497774786146625 16513540282873331089609969)
                ·
                  refine ⟨12385155212154998317207477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16513540282873331089609969 12385155212154998317207477)
                  ·
                    refine ⟨1161108301139531092238201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12385155212154998317207477 1161108301139531092238201)
                    ·
                      rfl

theorem cell23_6783751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_6783751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783751 prefixEnd_6783751 := by exact prefixLift 6783751
  have htrace : WordTrace (prefixWord ++ tailWord_6783751) baseStart_6783751 baseEnd_6783751 := by
    simpa [prefixWord, tailWord_6783751, baseEnd_6783751] using wordTrace_append hprefix tailTrace_6783751
  have hstable : (prefixWord ++ tailWord_6783751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783751).length < 2 ^ (prefixWord ++ tailWord_6783751).sum := by decide
  have hdescent : baseEnd_6783751 < baseStart_6783751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783781 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 3, 4]
def baseStart_6783781 : Nat := 118140960795 + 6783781 * 2 ^ 59
def prefixEnd_6783781 : Nat := 4983230072969 + 3 ^ 40 * 6783781 * 2
def baseEnd_6783781 : Nat := 1161113435946076053113155

theorem tailTrace_6783781 : CollatzResearch.WordTrace tailWord_6783781 prefixEnd_6783781 1161113435946076053113155 := by
  unfold tailWord_6783781
  simp only [CollatzResearch.WordTrace]
  refine ⟨247424819836527489400839197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164949879891018326267226131 247424819836527489400839197)
  ·
    refine ⟨92784307438697808525314699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247424819836527489400839197 92784307438697808525314699)
    ·
      refine ⟨139176461158046712787972049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92784307438697808525314699 139176461158046712787972049)
      ·
        refine ⟨104382345868535034590979037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139176461158046712787972049 104382345868535034590979037)
        ·
          refine ⟨39143379700700637971617139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104382345868535034590979037 39143379700700637971617139)
          ·
            refine ⟨58715069551050956957425709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39143379700700637971617139 58715069551050956957425709)
            ·
              refine ⟨22018151081644108859034641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58715069551050956957425709 22018151081644108859034641)
              ·
                refine ⟨16513613311233081644275981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22018151081644108859034641 16513613311233081644275981)
                ·
                  refine ⟨6192604991712405616603493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16513613311233081644275981 6192604991712405616603493)
                  ·
                    refine ⟨1161113435946076053113155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6192604991712405616603493 1161113435946076053113155)
                    ·
                      rfl

theorem cell23_6783781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_6783781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783781 prefixEnd_6783781 := by exact prefixLift 6783781
  have htrace : WordTrace (prefixWord ++ tailWord_6783781) baseStart_6783781 baseEnd_6783781 := by
    simpa [prefixWord, tailWord_6783781, baseEnd_6783781] using wordTrace_append hprefix tailTrace_6783781
  have hstable : (prefixWord ++ tailWord_6783781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783781).length < 2 ^ (prefixWord ++ tailWord_6783781).sum := by decide
  have hdescent : baseEnd_6783781 < baseStart_6783781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783794 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 8]
def baseStart_6783794 : Nat := 118140960795 + 6783794 * 2 ^ 59
def prefixEnd_6783794 : Nat := 4983230072969 + 3 ^ 40 * 6783794 * 2
def baseEnd_6783794 : Nat := 387038553676304067608545

theorem tailTrace_6783794 : CollatzResearch.WordTrace tailWord_6783794 prefixEnd_6783794 387038553676304067608545 := by
  unfold tailWord_6783794
  simp only [CollatzResearch.WordTrace]
  refine ⟨61856323496370098155265609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164950195990320261747374957 61856323496370098155265609)
  ·
    refine ⟨46392242622277573616449207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61856323496370098155265609 46392242622277573616449207)
    ·
      refine ⟨69588363933416360424673811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46392242622277573616449207 69588363933416360424673811)
      ·
        refine ⟨104382545900124540637010717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69588363933416360424673811 104382545900124540637010717)
        ·
          refine ⟨39143454712546702738879019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104382545900124540637010717 39143454712546702738879019)
          ·
            refine ⟨58715182068820054108318529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39143454712546702738879019 58715182068820054108318529)
            ·
              refine ⟨44036386551615040581238897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58715182068820054108318529 44036386551615040581238897)
              ·
                refine ⟨33027289913711280435929173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44036386551615040581238897 33027289913711280435929173)
                ·
                  refine ⟨387038553676304067608545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33027289913711280435929173 387038553676304067608545)
                  ·
                    rfl

theorem cell23_6783794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_6783794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783794 prefixEnd_6783794 := by exact prefixLift 6783794
  have htrace : WordTrace (prefixWord ++ tailWord_6783794) baseStart_6783794 baseEnd_6783794 := by
    simpa [prefixWord, tailWord_6783794, baseEnd_6783794] using wordTrace_append hprefix tailTrace_6783794
  have hstable : (prefixWord ++ tailWord_6783794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783794).length < 2 ^ (prefixWord ++ tailWord_6783794).sum := by decide
  have hdescent : baseEnd_6783794 < baseStart_6783794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783824 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 5, 5]
def baseStart_6783824 : Nat := 118140960795 + 6783824 * 2 ^ 59
def prefixEnd_6783824 : Nat := 4983230072969 + 3 ^ 40 * 6783824 * 2
def baseEnd_6783824 : Nat := 1161120795835457163700589

theorem tailTrace_6783824 : CollatzResearch.WordTrace tailWord_6783824 prefixEnd_6783824 1161120795835457163700589 := by
  unfold tailWord_6783824
  simp only [CollatzResearch.WordTrace]
  refine ⟨123713194087685853872327263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164950925450247805163103017 123713194087685853872327263)
  ·
    refine ⟨185569791131528780808490895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123713194087685853872327263 185569791131528780808490895)
    ·
      refine ⟨278354686697293171212736343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185569791131528780808490895 278354686697293171212736343)
      ·
        refine ⟨417532030045939756819104515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278354686697293171212736343 417532030045939756819104515)
        ·
          refine ⟨626298045068909635228656773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417532030045939756819104515 626298045068909635228656773)
          ·
            refine ⟨117430883450420556605373145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 626298045068909635228656773 117430883450420556605373145)
            ·
              refine ⟨88073162587815417454029859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117430883450420556605373145 88073162587815417454029859)
              ·
                refine ⟨132109743881723126181044789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88073162587815417454029859 132109743881723126181044789)
                ·
                  refine ⟨12385288488911543079472949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132109743881723126181044789 12385288488911543079472949)
                  ·
                    refine ⟨1161120795835457163700589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12385288488911543079472949 1161120795835457163700589)
                    ·
                      rfl

theorem cell23_6783824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_6783824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783824 prefixEnd_6783824 := by exact prefixLift 6783824
  have htrace : WordTrace (prefixWord ++ tailWord_6783824) baseStart_6783824 baseEnd_6783824 := by
    simpa [prefixWord, tailWord_6783824, baseEnd_6783824] using wordTrace_append hprefix tailTrace_6783824
  have hstable : (prefixWord ++ tailWord_6783824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783824).length < 2 ^ (prefixWord ++ tailWord_6783824).sum := by decide
  have hdescent : baseEnd_6783824 < baseStart_6783824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783848 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_6783848 : Nat := 118140960795 + 6783848 * 2 ^ 59
def prefixEnd_6783848 : Nat := 4983230072969 + 3 ^ 40 * 6783848 * 2
def baseEnd_6783848 : Nat := 3483374711042079397201657

theorem tailTrace_6783848 : CollatzResearch.WordTrace tailWord_6783848 prefixEnd_6783848 3483374711042079397201657 := by
  unfold tailWord_6783848
  simp only [CollatzResearch.WordTrace]
  refine ⟨123713631763642379921764099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164951509018189839895685465 123713631763642379921764099)
  ·
    refine ⟨185570447645463569882646149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123713631763642379921764099 185570447645463569882646149)
    ·
      refine ⟨34794458933524419352996153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185570447645463569882646149 34794458933524419352996153)
      ·
        refine ⟨26095844200143314514747115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34794458933524419352996153 26095844200143314514747115)
        ·
          refine ⟨39143766300214971772120673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26095844200143314514747115 39143766300214971772120673)
          ·
            refine ⟨29357824725161228829090505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39143766300214971772120673 29357824725161228829090505)
            ·
              refine ⟨22018368543870921621817879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29357824725161228829090505 22018368543870921621817879)
              ·
                refine ⟨33027552815806382432726819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22018368543870921621817879 33027552815806382432726819)
                ·
                  refine ⟨49541329223709573649090229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33027552815806382432726819 49541329223709573649090229)
                  ·
                    refine ⟨4644499614722772529602209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49541329223709573649090229 4644499614722772529602209)
                    ·
                      refine ⟨3483374711042079397201657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644499614722772529602209 3483374711042079397201657)
                      ·
                        rfl

theorem cell23_6783848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_6783848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783848 prefixEnd_6783848 := by exact prefixLift 6783848
  have htrace : WordTrace (prefixWord ++ tailWord_6783848) baseStart_6783848 baseEnd_6783848 := by
    simpa [prefixWord, tailWord_6783848, baseEnd_6783848] using wordTrace_append hprefix tailTrace_6783848
  have hstable : (prefixWord ++ tailWord_6783848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783848).length < 2 ^ (prefixWord ++ tailWord_6783848).sum := by decide
  have hdescent : baseEnd_6783848 < baseStart_6783848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783871 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 4, 4]
def baseStart_6783871 : Nat := 118140960795 + 6783871 * 2 ^ 59
def prefixEnd_6783871 : Nat := 4983230072969 + 3 ^ 40 * 6783871 * 2
def baseEnd_6783871 : Nat := 1161128840365710935738017

theorem tailTrace_6783871 : CollatzResearch.WordTrace tailWord_6783871 prefixEnd_6783871 1161128840365710935738017 := by
  unfold tailWord_6783871
  simp only [CollatzResearch.WordTrace]
  refine ⟨247428102406201434771615467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164952068270800956514410311 247428102406201434771615467)
  ·
    refine ⟨371142153609302152157423201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247428102406201434771615467 371142153609302152157423201)
    ·
      refine ⟨278356615206976614118067401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371142153609302152157423201 278356615206976614118067401)
      ·
        refine ⟨208767461405232460588550551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278356615206976614118067401 208767461405232460588550551)
        ·
          refine ⟨313151192107848690882825827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208767461405232460588550551 313151192107848690882825827)
          ·
            refine ⟨469726788161773036324238741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313151192107848690882825827 469726788161773036324238741)
            ·
              refine ⟨22018443195083111077698691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 469726788161773036324238741 22018443195083111077698691)
              ·
                refine ⟨33027664792624666616548037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22018443195083111077698691 33027664792624666616548037)
                ·
                  refine ⟨6192687148617124990602757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33027664792624666616548037 6192687148617124990602757)
                  ·
                    refine ⟨1161128840365710935738017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6192687148617124990602757 1161128840365710935738017)
                    ·
                      rfl

theorem cell23_6783871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 4].length) (baseStart_6783871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783871 prefixEnd_6783871 := by exact prefixLift 6783871
  have htrace : WordTrace (prefixWord ++ tailWord_6783871) baseStart_6783871 baseEnd_6783871 := by
    simpa [prefixWord, tailWord_6783871, baseEnd_6783871] using wordTrace_append hprefix tailTrace_6783871
  have hstable : (prefixWord ++ tailWord_6783871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783871).length < 2 ^ (prefixWord ++ tailWord_6783871).sum := by decide
  have hdescent : baseEnd_6783871 < baseStart_6783871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783881 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 5]
def baseStart_6783881 : Nat := 118140960795 + 6783881 * 2 ^ 59
def prefixEnd_6783881 : Nat := 4983230072969 + 3 ^ 40 * 6783881 * 2
def baseEnd_6783881 : Nat := 3483391655903677768089005

theorem tailTrace_6783881 : CollatzResearch.WordTrace tailWord_6783881 prefixEnd_6783881 3483391655903677768089005 := by
  unfold tailWord_6783881
  simp only [CollatzResearch.WordTrace]
  refine ⟨247428467136165206479479497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164952311424110137652986331 247428467136165206479479497)
  ·
    refine ⟨185571350352123904859609623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247428467136165206479479497 185571350352123904859609623)
    ·
      refine ⟨278357025528185857289414435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185571350352123904859609623 278357025528185857289414435)
      ·
        refine ⟨417535538292278785934121653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278357025528185857289414435 417535538292278785934121653)
        ·
          refine ⟨39143956714901136181323905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 417535538292278785934121653 39143956714901136181323905)
          ·
            refine ⟨29357967536175852135992929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39143956714901136181323905 29357967536175852135992929)
            ·
              refine ⟨22018475652131889101994697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29357967536175852135992929 22018475652131889101994697)
              ·
                refine ⟨16513856739098916826496023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22018475652131889101994697 16513856739098916826496023)
                ·
                  refine ⟨24770785108648375239744035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16513856739098916826496023 24770785108648375239744035)
                  ·
                    refine ⟨37156177662972562859616053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24770785108648375239744035 37156177662972562859616053)
                    ·
                      refine ⟨3483391655903677768089005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37156177662972562859616053 3483391655903677768089005)
                      ·
                        rfl

theorem cell23_6783881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_6783881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783881 prefixEnd_6783881 := by exact prefixLift 6783881
  have htrace : WordTrace (prefixWord ++ tailWord_6783881) baseStart_6783881 baseEnd_6783881 := by
    simpa [prefixWord, tailWord_6783881, baseEnd_6783881] using wordTrace_append hprefix tailTrace_6783881
  have hstable : (prefixWord ++ tailWord_6783881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783881).length < 2 ^ (prefixWord ++ tailWord_6783881).sum := by decide
  have hdescent : baseEnd_6783881 < baseStart_6783881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783884 : List Nat := [2, 2, 1, 2, 1, 2, 3, 10]
def baseStart_6783884 : Nat := 118140960795 + 6783884 * 2 ^ 59
def prefixEnd_6783884 : Nat := 4983230072969 + 3 ^ 40 * 6783884 * 2
def baseEnd_6783884 : Nat := 129014562827616342827833

theorem tailTrace_6783884 : CollatzResearch.WordTrace tailWord_6783884 prefixEnd_6783884 129014562827616342827833 := by
  unfold tailWord_6783884
  simp only [CollatzResearch.WordTrace]
  refine ⟨123714288277577168995919353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164952384370102891994559137 123714288277577168995919353)
  ·
    refine ⟨92785716208182876746939515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123714288277577168995919353 92785716208182876746939515)
    ·
      refine ⟨139178574312274315120409273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92785716208182876746939515 139178574312274315120409273)
      ·
        refine ⟨104383930734205736340306955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139178574312274315120409273 104383930734205736340306955)
        ·
          refine ⟨156575896101308604510460433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104383930734205736340306955 156575896101308604510460433)
          ·
            refine ⟨117431922075981453382845325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156575896101308604510460433 117431922075981453382845325)
            ·
              refine ⟨44036970778493045018566997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117431922075981453382845325 44036970778493045018566997)
              ·
                refine ⟨129014562827616342827833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44036970778493045018566997 129014562827616342827833)
                ·
                  rfl

theorem cell23_6783884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 10].length) (baseStart_6783884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783884 prefixEnd_6783884 := by exact prefixLift 6783884
  have htrace : WordTrace (prefixWord ++ tailWord_6783884) baseStart_6783884 baseEnd_6783884 := by
    simpa [prefixWord, tailWord_6783884, baseEnd_6783884] using wordTrace_append hprefix tailTrace_6783884
  have hstable : (prefixWord ++ tailWord_6783884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783884).length < 2 ^ (prefixWord ++ tailWord_6783884).sum := by decide
  have hdescent : baseEnd_6783884 < baseStart_6783884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783929 : List Nat := [1, 2, 1, 4, 2, 2, 4, 2, 1, 2, 2]
def baseStart_6783929 : Nat := 118140960795 + 6783929 * 2 ^ 59
def prefixEnd_6783929 : Nat := 4983230072969 + 3 ^ 40 * 6783929 * 2
def baseEnd_6783929 : Nat := 3483416302975093580288785

theorem tailTrace_6783929 : CollatzResearch.WordTrace tailWord_6783929 prefixEnd_6783929 3483416302975093580288785 := by
  unfold tailWord_6783929
  simp only [CollatzResearch.WordTrace]
  refine ⟨247430217839991310677226841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164953478559994207118151227 247430217839991310677226841)
  ·
    refine ⟨185572663379993483007920131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247430217839991310677226841 185572663379993483007920131)
    ·
      refine ⟨278358995069990224511880197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185572663379993483007920131 278358995069990224511880197)
      ·
        refine ⟨52192311575623167095977537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278358995069990224511880197 52192311575623167095977537)
        ·
          refine ⟨39144233681717375321983153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52192311575623167095977537 39144233681717375321983153)
          ·
            refine ⟨29358175261288031491487365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39144233681717375321983153 29358175261288031491487365)
            ·
              refine ⟨5504657861491505904653881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29358175261288031491487365 5504657861491505904653881)
              ·
                refine ⟨4128493396118629428490411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5504657861491505904653881 4128493396118629428490411)
                ·
                  refine ⟨6192740094177944142735617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4128493396118629428490411 6192740094177944142735617)
                  ·
                    refine ⟨4644555070633458107051713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6192740094177944142735617 4644555070633458107051713)
                    ·
                      refine ⟨3483416302975093580288785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644555070633458107051713 3483416302975093580288785)
                      ·
                        rfl

theorem cell23_6783929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_6783929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783929 prefixEnd_6783929 := by exact prefixLift 6783929
  have htrace : WordTrace (prefixWord ++ tailWord_6783929) baseStart_6783929 baseEnd_6783929 := by
    simpa [prefixWord, tailWord_6783929, baseEnd_6783929] using wordTrace_append hprefix tailTrace_6783929
  have hstable : (prefixWord ++ tailWord_6783929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783929).length < 2 ^ (prefixWord ++ tailWord_6783929).sum := by decide
  have hdescent : baseEnd_6783929 < baseStart_6783929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6783971 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 5]
def baseStart_6783971 : Nat := 118140960795 + 6783971 * 2 ^ 59
def prefixEnd_6783971 : Nat := 4983230072969 + 3 ^ 40 * 6783971 * 2
def baseEnd_6783971 : Nat := 3483437869162582415963591

theorem tailTrace_6783971 : CollatzResearch.WordTrace tailWord_6783971 prefixEnd_6783971 3483437869162582415963591 := by
  unfold tailWord_6783971
  simp only [CollatzResearch.WordTrace]
  refine ⟨247431749705839151850255767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164954499803892767900170511 247431749705839151850255767)
  ·
    refine ⟨371147624558758727775383651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247431749705839151850255767 371147624558758727775383651)
    ·
      refine ⟨556721436838138091663075477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371147624558758727775383651 556721436838138091663075477)
      ·
        refine ⟨26096317351787723046706663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 556721436838138091663075477 26096317351787723046706663)
        ·
          refine ⟨39144476027681584570059995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26096317351787723046706663 39144476027681584570059995)
          ·
            refine ⟨58716714041522376855089993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39144476027681584570059995 58716714041522376855089993)
            ·
              refine ⟨44037535531141782641317495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58716714041522376855089993 44037535531141782641317495)
              ·
                refine ⟨66056303296712673961976243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44037535531141782641317495 66056303296712673961976243)
                ·
                  refine ⟨99084454945069010942964365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66056303296712673961976243 99084454945069010942964365)
                  ·
                    refine ⟨37156670604400879103611637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99084454945069010942964365 37156670604400879103611637)
                    ·
                      refine ⟨3483437869162582415963591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37156670604400879103611637 3483437869162582415963591)
                      ·
                        rfl

theorem cell23_6783971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_6783971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6783971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6783971 prefixEnd_6783971 := by exact prefixLift 6783971
  have htrace : WordTrace (prefixWord ++ tailWord_6783971) baseStart_6783971 baseEnd_6783971 := by
    simpa [prefixWord, tailWord_6783971, baseEnd_6783971] using wordTrace_append hprefix tailTrace_6783971
  have hstable : (prefixWord ++ tailWord_6783971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6783971).length < 2 ^ (prefixWord ++ tailWord_6783971).sum := by decide
  have hdescent : baseEnd_6783971 < baseStart_6783971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6783971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784042 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 7]
def baseStart_6784042 : Nat := 118140960795 + 6784042 * 2 ^ 59
def prefixEnd_6784042 : Nat := 4983230072969 + 3 ^ 40 * 6784042 * 2
def baseEnd_6784042 : Nat := 387052702921005737575085

theorem tailTrace_6784042 : CollatzResearch.WordTrace tailWord_6784042 prefixEnd_6784042 387052702921005737575085 := by
  unfold tailWord_6784042
  simp only [CollatzResearch.WordTrace]
  refine ⟨61858584822145482744022595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164956226192387953984060253 61858584822145482744022595)
  ·
    refine ⟨92787877233218224116033893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61858584822145482744022595 92787877233218224116033893)
    ·
      refine ⟨17397726981228417021756355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92787877233218224116033893 17397726981228417021756355)
      ·
        refine ⟨26096590471842625532634533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17397726981228417021756355 26096590471842625532634533)
        ·
          refine ⟨4893110713470492287368975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26096590471842625532634533 4893110713470492287368975)
          ·
            refine ⟨7339666070205738431053463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893110713470492287368975 7339666070205738431053463)
            ·
              refine ⟨11009499105308607646580195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7339666070205738431053463 11009499105308607646580195)
              ·
                refine ⟨16514248657962911469870293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11009499105308607646580195 16514248657962911469870293)
                ·
                  refine ⟨387052702921005737575085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16514248657962911469870293 387052702921005737575085)
                  ·
                    rfl

theorem cell23_6784042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_6784042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784042 prefixEnd_6784042 := by exact prefixLift 6784042
  have htrace : WordTrace (prefixWord ++ tailWord_6784042) baseStart_6784042 baseEnd_6784042 := by
    simpa [prefixWord, tailWord_6784042, baseEnd_6784042] using wordTrace_append hprefix tailTrace_6784042
  have hstable : (prefixWord ++ tailWord_6784042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784042).length < 2 ^ (prefixWord ++ tailWord_6784042).sum := by decide
  have hdescent : baseEnd_6784042 < baseStart_6784042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784081 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 10]
def baseStart_6784081 : Nat := 118140960795 + 6784081 * 2 ^ 59
def prefixEnd_6784081 : Nat := 4983230072969 + 3 ^ 40 * 6784081 * 2
def baseEnd_6784081 : Nat := 387054928003841887287565

theorem tailTrace_6784081 : CollatzResearch.WordTrace tailWord_6784081 prefixEnd_6784081 387054928003841887287565 := by
  unfold tailWord_6784081
  simp only [CollatzResearch.WordTrace]
  refine ⟨247435761735440640636760097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164957174490293760424506731 247435761735440640636760097)
  ·
    refine ⟨185576821301580480477570073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247435761735440640636760097 185576821301580480477570073)
    ·
      refine ⟨139182615976185360358177555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185576821301580480477570073 139182615976185360358177555)
      ·
        refine ⟨208773923964278040537266333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139182615976185360358177555 208773923964278040537266333)
        ·
          refine ⟨78290221486604265201474875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208773923964278040537266333 78290221486604265201474875)
          ·
            refine ⟨117435332229906397802212313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78290221486604265201474875 117435332229906397802212313)
            ·
              refine ⟨88076499172429798351659235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117435332229906397802212313 88076499172429798351659235)
              ·
                refine ⟨132114748758644697527488853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88076499172429798351659235 132114748758644697527488853)
                ·
                  refine ⟨387054928003841887287565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 132114748758644697527488853 387054928003841887287565)
                  ·
                    rfl

theorem cell23_6784081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 10].length) (baseStart_6784081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784081 prefixEnd_6784081 := by exact prefixLift 6784081
  have htrace : WordTrace (prefixWord ++ tailWord_6784081) baseStart_6784081 baseEnd_6784081 := by
    simpa [prefixWord, tailWord_6784081, baseEnd_6784081] using wordTrace_append hprefix tailTrace_6784081
  have hstable : (prefixWord ++ tailWord_6784081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784081).length < 2 ^ (prefixWord ++ tailWord_6784081).sum := by decide
  have hdescent : baseEnd_6784081 < baseStart_6784081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784128 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 3, 5]
def baseStart_6784128 : Nat := 118140960795 + 6784128 * 2 ^ 59
def prefixEnd_6784128 : Nat := 4983230072969 + 3 ^ 40 * 6784128 * 2
def baseEnd_6784128 : Nat := 1161172828541779433900123

theorem tailTrace_6784128 : CollatzResearch.WordTrace tailWord_6784128 prefixEnd_6784128 1161172828541779433900123 := by
  unfold tailWord_6784128
  simp only [CollatzResearch.WordTrace]
  refine ⟨123718737983135183831860519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164958317310846911775814025 123718737983135183831860519)
  ·
    refine ⟨185578106974702775747790779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123718737983135183831860519 185578106974702775747790779)
    ·
      refine ⟨278367160462054163621686169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185578106974702775747790779 278367160462054163621686169)
      ·
        refine ⟨208775370346540622716264627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278367160462054163621686169 208775370346540622716264627)
        ·
          refine ⟨313163055519810934074396941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208775370346540622716264627 313163055519810934074396941)
          ·
            refine ⟨117436145819929100277898853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313163055519810934074396941 117436145819929100277898853)
            ·
              refine ⟨22019277341236706302106035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117436145819929100277898853 22019277341236706302106035)
              ·
                refine ⟨33028916011855059453159053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22019277341236706302106035 33028916011855059453159053)
                ·
                  refine ⟨12385843504445647294934645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33028916011855059453159053 12385843504445647294934645)
                  ·
                    refine ⟨1161172828541779433900123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12385843504445647294934645 1161172828541779433900123)
                    ·
                      rfl

theorem cell23_6784128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_6784128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784128 prefixEnd_6784128 := by exact prefixLift 6784128
  have htrace : WordTrace (prefixWord ++ tailWord_6784128) baseStart_6784128 baseEnd_6784128 := by
    simpa [prefixWord, tailWord_6784128, baseEnd_6784128] using wordTrace_append hprefix tailTrace_6784128
  have hstable : (prefixWord ++ tailWord_6784128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784128).length < 2 ^ (prefixWord ++ tailWord_6784128).sum := by decide
  have hdescent : baseEnd_6784128 < baseStart_6784128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784159 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 3, 1, 3]
def baseStart_6784159 : Nat := 118140960795 + 6784159 * 2 ^ 59
def prefixEnd_6784159 : Nat := 4983230072969 + 3 ^ 40 * 6784159 * 2
def baseEnd_6784159 : Nat := 3483534403525627680412727

theorem tailTrace_6784159 : CollatzResearch.WordTrace tailWord_6784159 prefixEnd_6784159 3483534403525627680412727 := by
  unfold tailWord_6784159
  simp only [CollatzResearch.WordTrace]
  refine ⟨247438606629158059958099531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164959071086105373305399687 247438606629158059958099531)
  ·
    refine ⟨371157909943737089937149297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247438606629158059958099531 371157909943737089937149297)
    ·
      refine ⟨278368432457802817452861973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371157909943737089937149297 278368432457802817452861973)
      ·
        refine ⟨13048520271459507068102905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 278368432457802817452861973 13048520271459507068102905)
        ·
          refine ⟨9786390203594630301077179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13048520271459507068102905 9786390203594630301077179)
          ·
            refine ⟨14679585305391945451615769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9786390203594630301077179 14679585305391945451615769)
            ·
              refine ⟨11009688979043959088711827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14679585305391945451615769 11009688979043959088711827)
              ·
                refine ⟨16514533468565938633067741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11009688979043959088711827 16514533468565938633067741)
                ·
                  refine ⟨6192950050712226987400403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16514533468565938633067741 6192950050712226987400403)
                  ·
                    refine ⟨9289425076068340481100605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6192950050712226987400403 9289425076068340481100605)
                    ·
                      refine ⟨3483534403525627680412727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9289425076068340481100605 3483534403525627680412727)
                      ·
                        rfl

theorem cell23_6784159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_6784159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784159 prefixEnd_6784159 := by exact prefixLift 6784159
  have htrace : WordTrace (prefixWord ++ tailWord_6784159) baseStart_6784159 baseEnd_6784159 := by
    simpa [prefixWord, tailWord_6784159, baseEnd_6784159] using wordTrace_append hprefix tailTrace_6784159
  have hstable : (prefixWord ++ tailWord_6784159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784159).length < 2 ^ (prefixWord ++ tailWord_6784159).sum := by decide
  have hdescent : baseEnd_6784159 < baseStart_6784159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784175 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 2, 4]
def baseStart_6784175 : Nat := 118140960795 + 6784175 * 2 ^ 59
def prefixEnd_6784175 : Nat := 4983230072969 + 3 ^ 40 * 6784175 * 2
def baseEnd_6784175 : Nat := 1161180873072033205937551

theorem tailTrace_6784175 : CollatzResearch.WordTrace tailWord_6784175 prefixEnd_6784175 1161180873072033205937551 := by
  unfold tailWord_6784175
  simp only [CollatzResearch.WordTrace]
  refine ⟨247439190197100094690681979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164959460131400063127121319 247439190197100094690681979)
  ·
    refine ⟨371158785295650142036022969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247439190197100094690681979 371158785295650142036022969)
    ·
      refine ⟨278369088971737606527017227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371158785295650142036022969 278369088971737606527017227)
      ·
        refine ⟨417553633457606409790525841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278369088971737606527017227 417553633457606409790525841)
        ·
          refine ⟨313165225093204807342894381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417553633457606409790525841 313165225093204807342894381)
          ·
            refine ⟨117436959409951802753585393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313165225093204807342894381 117436959409951802753585393)
            ·
              refine ⟨88077719557463852065189045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117436959409951802753585393 88077719557463852065189045)
              ·
                refine ⟨8257286208512236131111473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88077719557463852065189045 8257286208512236131111473)
                ·
                  refine ⟨6192964656384177098333605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8257286208512236131111473 6192964656384177098333605)
                  ·
                    refine ⟨1161180873072033205937551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6192964656384177098333605 1161180873072033205937551)
                    ·
                      rfl

theorem cell23_6784175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 4].length) (baseStart_6784175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784175 prefixEnd_6784175 := by exact prefixLift 6784175
  have htrace : WordTrace (prefixWord ++ tailWord_6784175) baseStart_6784175 baseEnd_6784175 := by
    simpa [prefixWord, tailWord_6784175, baseEnd_6784175] using wordTrace_append hprefix tailTrace_6784175
  have hstable : (prefixWord ++ tailWord_6784175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784175).length < 2 ^ (prefixWord ++ tailWord_6784175).sum := by decide
  have hdescent : baseEnd_6784175 < baseStart_6784175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784193 : List Nat := [1, 2, 6, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_6784193 : Nat := 118140960795 + 6784193 * 2 ^ 59
def prefixEnd_6784193 : Nat := 4983230072969 + 3 ^ 40 * 6784193 * 2
def baseEnd_6784193 : Nat := 3483551861867880547387571

theorem tailTrace_6784193 : CollatzResearch.WordTrace tailWord_6784193 prefixEnd_6784193 3483551861867880547387571 := by
  unfold tailWord_6784193
  simp only [CollatzResearch.WordTrace]
  refine ⟨247439846711034883764837233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164959897807356589176558155 247439846711034883764837233)
  ·
    refine ⟨185579885033276162823627925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247439846711034883764837233 185579885033276162823627925)
    ·
      refine ⟨8699057110934820132357559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185579885033276162823627925 8699057110934820132357559)
      ·
        refine ⟨13048585666402230198536339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8699057110934820132357559 13048585666402230198536339)
        ·
          refine ⟨19572878499603345297804509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13048585666402230198536339 19572878499603345297804509)
          ·
            refine ⟨7339829437351254486676691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19572878499603345297804509 7339829437351254486676691)
            ·
              refine ⟨11009744156026881730015037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7339829437351254486676691 11009744156026881730015037)
              ·
                refine ⟨4128654058510080648755639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11009744156026881730015037 4128654058510080648755639)
                ·
                  refine ⟨6192981087765120973133459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4128654058510080648755639 6192981087765120973133459)
                  ·
                    refine ⟨9289471631647681459700189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6192981087765120973133459 9289471631647681459700189)
                    ·
                      refine ⟨3483551861867880547387571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9289471631647681459700189 3483551861867880547387571)
                      ·
                        rfl

theorem cell23_6784193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_6784193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784193 prefixEnd_6784193 := by exact prefixLift 6784193
  have htrace : WordTrace (prefixWord ++ tailWord_6784193) baseStart_6784193 baseEnd_6784193 := by
    simpa [prefixWord, tailWord_6784193, baseEnd_6784193] using wordTrace_append hprefix tailTrace_6784193
  have hstable : (prefixWord ++ tailWord_6784193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784193).length < 2 ^ (prefixWord ++ tailWord_6784193).sum := by decide
  have hdescent : baseEnd_6784193 < baseStart_6784193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784202 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_6784202 : Nat := 118140960795 + 6784202 * 2 ^ 59
def prefixEnd_6784202 : Nat := 4983230072969 + 3 ^ 40 * 6784202 * 2
def baseEnd_6784202 : Nat := 3483556483193771012175029

theorem tailTrace_6784202 : CollatzResearch.WordTrace tailWord_6784202 prefixEnd_6784202 3483556483193771012175029 := by
  unfold tailWord_6784202
  simp only [CollatzResearch.WordTrace]
  refine ⟨61860043742000569575478715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164960116645334852201276573 61860043742000569575478715)
  ·
    refine ⟨92790065613000854363218073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61860043742000569575478715 92790065613000854363218073)
    ·
      refine ⟨69592549209750640772413555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92790065613000854363218073 69592549209750640772413555)
      ·
        refine ⟨104388823814625961158620333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69592549209750640772413555 104388823814625961158620333)
        ·
          refine ⟨39145808930484735434482625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104388823814625961158620333 39145808930484735434482625)
          ·
            refine ⟨29359356697863551575861969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39145808930484735434482625 29359356697863551575861969)
            ·
              refine ⟨22019517523397663681896477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29359356697863551575861969 22019517523397663681896477)
              ·
                refine ⟨8257319071274123880711179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22019517523397663681896477 8257319071274123880711179)
                ·
                  refine ⟨12385978606911185821066769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8257319071274123880711179 12385978606911185821066769)
                  ·
                    refine ⟨9289483955183389365800077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12385978606911185821066769 9289483955183389365800077)
                    ·
                      refine ⟨3483556483193771012175029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9289483955183389365800077 3483556483193771012175029)
                      ·
                        rfl

theorem cell23_6784202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_6784202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784202 prefixEnd_6784202 := by exact prefixLift 6784202
  have htrace : WordTrace (prefixWord ++ tailWord_6784202) baseStart_6784202 baseEnd_6784202 := by
    simpa [prefixWord, tailWord_6784202, baseEnd_6784202] using wordTrace_append hprefix tailTrace_6784202
  have hstable : (prefixWord ++ tailWord_6784202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784202).length < 2 ^ (prefixWord ++ tailWord_6784202).sum := by decide
  have hdescent : baseEnd_6784202 < baseStart_6784202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784216 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 3, 2, 2]
def baseStart_6784216 : Nat := 118140960795 + 6784216 * 2 ^ 59
def prefixEnd_6784216 : Nat := 4983230072969 + 3 ^ 40 * 6784216 * 2
def baseEnd_6784216 : Nat := 3483563671922933957399965

theorem tailTrace_6784216 : CollatzResearch.WordTrace tailWord_6784216 prefixEnd_6784216 3483563671922933957399965 := by
  unfold tailWord_6784216
  simp only [CollatzResearch.WordTrace]
  refine ⟨123720342794975779346462251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164960457059967705795283001 123720342794975779346462251)
  ·
    refine ⟨185580514192463669019693377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123720342794975779346462251 185580514192463669019693377)
    ·
      refine ⟨139185385644347751764770033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185580514192463669019693377 139185385644347751764770033)
      ·
        refine ⟨104389039233260813823577525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139185385644347751764770033 104389039233260813823577525)
        ·
          refine ⟨9786472428118201295960393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104389039233260813823577525 9786472428118201295960393)
          ·
            refine ⟨7339854321088650971970295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9786472428118201295960393 7339854321088650971970295)
            ·
              refine ⟨11009781481632976457955443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7339854321088650971970295 11009781481632976457955443)
              ·
                refine ⟨16514672222449464686933165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11009781481632976457955443 16514672222449464686933165)
                ·
                  refine ⟨6193002083418549257599937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16514672222449464686933165 6193002083418549257599937)
                  ·
                    refine ⟨4644751562563911943199953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6193002083418549257599937 4644751562563911943199953)
                    ·
                      refine ⟨3483563671922933957399965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644751562563911943199953 3483563671922933957399965)
                      ·
                        rfl

theorem cell23_6784216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_6784216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784216 prefixEnd_6784216 := by exact prefixLift 6784216
  have htrace : WordTrace (prefixWord ++ tailWord_6784216) baseStart_6784216 baseEnd_6784216 := by
    simpa [prefixWord, tailWord_6784216, baseEnd_6784216] using wordTrace_append hprefix tailTrace_6784216
  have hstable : (prefixWord ++ tailWord_6784216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784216).length < 2 ^ (prefixWord ++ tailWord_6784216).sum := by decide
  have hdescent : baseEnd_6784216 < baseStart_6784216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784218 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_6784218 : Nat := 118140960795 + 6784218 * 2 ^ 59
def prefixEnd_6784218 : Nat := 4983230072969 + 3 ^ 40 * 6784218 * 2
def baseEnd_6784218 : Nat := 1161188232961414316524985

theorem tailTrace_6784218 : CollatzResearch.WordTrace tailWord_6784218 prefixEnd_6784218 1161188232961414316524985 := by
  unfold tailWord_6784218
  simp only [CollatzResearch.WordTrace]
  refine ⟨61860189633986078258624327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164960505690629542022998205 61860189633986078258624327)
  ·
    refine ⟨92790284450979117387936491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61860189633986078258624327 92790284450979117387936491)
    ·
      refine ⟨139185426676468676081904737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92790284450979117387936491 139185426676468676081904737)
      ·
        refine ⟨104389070007351507061428553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139185426676468676081904737 104389070007351507061428553)
        ·
          refine ⟨78291802505513630296071415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104389070007351507061428553 78291802505513630296071415)
          ·
            refine ⟨117437703758270445444107123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78291802505513630296071415 117437703758270445444107123)
            ·
              refine ⟨176156555637405668166160685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117437703758270445444107123 176156555637405668166160685)
              ·
                refine ⟨66058708364027125562310257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176156555637405668166160685 66058708364027125562310257)
                ·
                  refine ⟨49544031273020344171732693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66058708364027125562310257 49544031273020344171732693)
                  ·
                    refine ⟨1161188232961414316524985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49544031273020344171732693 1161188232961414316524985)
                    ·
                      rfl

theorem cell23_6784218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_6784218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784218 prefixEnd_6784218 := by exact prefixLift 6784218
  have htrace : WordTrace (prefixWord ++ tailWord_6784218) baseStart_6784218 baseEnd_6784218 := by
    simpa [prefixWord, tailWord_6784218, baseEnd_6784218] using wordTrace_append hprefix tailTrace_6784218
  have hstable : (prefixWord ++ tailWord_6784218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784218).length < 2 ^ (prefixWord ++ tailWord_6784218).sum := by decide
  have hdescent : baseEnd_6784218 < baseStart_6784218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784248 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 6, 6]
def baseStart_6784248 : Nat := 118140960795 + 6784248 * 2 ^ 59
def prefixEnd_6784248 : Nat := 4983230072969 + 3 ^ 40 * 6784248 * 2
def baseEnd_6784248 : Nat := 1161193367767959277399939

theorem tailTrace_6784248 : CollatzResearch.WordTrace tailWord_6784248 prefixEnd_6784248 1161193367767959277399939 := by
  unfold tailWord_6784248
  simp only [CollatzResearch.WordTrace]
  refine ⟨123720926362917814079044699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164961235150557085438726265 123720926362917814079044699)
  ·
    refine ⟨185581389544376721118567049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123720926362917814079044699 185581389544376721118567049)
    ·
      refine ⟨139186042158282540838925287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185581389544376721118567049 139186042158282540838925287)
      ·
        refine ⟨208779063237423811258387931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139186042158282540838925287 208779063237423811258387931)
        ·
          refine ⟨313168594856135716887581897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208779063237423811258387931 313168594856135716887581897)
          ·
            refine ⟨234876446142101787665686423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313168594856135716887581897 234876446142101787665686423)
            ·
              refine ⟨352314669213152681498529635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234876446142101787665686423 352314669213152681498529635)
              ·
                refine ⟨528472003819729022247794453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352314669213152681498529635 528472003819729022247794453)
                ·
                  refine ⟨24772125179049797917865365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 528472003819729022247794453 24772125179049797917865365)
                  ·
                    refine ⟨1161193367767959277399939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24772125179049797917865365 1161193367767959277399939)
                    ·
                      rfl

theorem cell23_6784248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_6784248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784248 prefixEnd_6784248 := by exact prefixLift 6784248
  have htrace : WordTrace (prefixWord ++ tailWord_6784248) baseStart_6784248 baseEnd_6784248 := by
    simpa [prefixWord, tailWord_6784248, baseEnd_6784248] using wordTrace_append hprefix tailTrace_6784248
  have hstable : (prefixWord ++ tailWord_6784248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784248).length < 2 ^ (prefixWord ++ tailWord_6784248).sum := by decide
  have hdescent : baseEnd_6784248 < baseStart_6784248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784272 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 10, 2, 2]
def baseStart_6784272 : Nat := 118140960795 + 6784272 * 2 ^ 59
def prefixEnd_6784272 : Nat := 4983230072969 + 3 ^ 40 * 6784272 * 2
def baseEnd_6784272 : Nat := 3483592426839585738299707

theorem tailTrace_6784272 : CollatzResearch.WordTrace tailWord_6784272 prefixEnd_6784272 3483592426839585738299707 := by
  unfold tailWord_6784272
  simp only [CollatzResearch.WordTrace]
  refine ⟨123721364038874340128481535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164961818718499120171308713 123721364038874340128481535)
  ·
    refine ⟨185582046058311510192722303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123721364038874340128481535 185582046058311510192722303)
    ·
      refine ⟨278373069087467265289083455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185582046058311510192722303 278373069087467265289083455)
      ·
        refine ⟨417559603631200897933625183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278373069087467265289083455 417559603631200897933625183)
        ·
          refine ⟨626339405446801346900437775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417559603631200897933625183 626339405446801346900437775)
          ·
            refine ⟨939509108170202020350656663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626339405446801346900437775 939509108170202020350656663)
            ·
              refine ⟨1409263662255303030525984995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939509108170202020350656663 1409263662255303030525984995)
              ·
                refine ⟨2113895493382954545788977493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409263662255303030525984995 2113895493382954545788977493)
                ·
                  refine ⟨6193053203270374645866145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 2113895493382954545788977493 6193053203270374645866145)
                  ·
                    refine ⟨4644789902452780984399609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6193053203270374645866145 4644789902452780984399609)
                    ·
                      refine ⟨3483592426839585738299707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644789902452780984399609 3483592426839585738299707)
                      ·
                        rfl

theorem cell23_6784272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10, 2, 2].length) (baseStart_6784272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784272 prefixEnd_6784272 := by exact prefixLift 6784272
  have htrace : WordTrace (prefixWord ++ tailWord_6784272) baseStart_6784272 baseEnd_6784272 := by
    simpa [prefixWord, tailWord_6784272, baseEnd_6784272] using wordTrace_append hprefix tailTrace_6784272
  have hstable : (prefixWord ++ tailWord_6784272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784272).length < 2 ^ (prefixWord ++ tailWord_6784272).sum := by decide
  have hdescent : baseEnd_6784272 < baseStart_6784272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784325 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_6784325 : Nat := 118140960795 + 6784325 * 2 ^ 59
def prefixEnd_6784325 : Nat := 4983230072969 + 3 ^ 40 * 6784325 * 2
def baseEnd_6784325 : Nat := 1161206547104758010312321

theorem tailTrace_6784325 : CollatzResearch.WordTrace tailWord_6784325 prefixEnd_6784325 1161206547104758010312321 := by
  unfold tailWord_6784325
  simp only [CollatzResearch.WordTrace]
  refine ⟨247444661146556670308642429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164963107431037780205761619 247444661146556670308642429)
  ·
    refine ⟨92791747929958751365740911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247444661146556670308642429 92791747929958751365740911)
    ·
      refine ⟨139187621894938127048611367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92791747929958751365740911 139187621894938127048611367)
      ·
        refine ⟨208781432842407190572917051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139187621894938127048611367 208781432842407190572917051)
        ·
          refine ⟨313172149263610785859375577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208781432842407190572917051 313172149263610785859375577)
          ·
            refine ⟨234879111947708089394531683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313172149263610785859375577 234879111947708089394531683)
            ·
              refine ⟨352318667921562134091797525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234879111947708089394531683 352318667921562134091797525)
              ·
                refine ⟨16514937558823225035553009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 352318667921562134091797525 16514937558823225035553009)
                ·
                  refine ⟨12386203169117418776664757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16514937558823225035553009 12386203169117418776664757)
                  ·
                    refine ⟨1161206547104758010312321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12386203169117418776664757 1161206547104758010312321)
                    ·
                      rfl

theorem cell23_6784325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_6784325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784325 prefixEnd_6784325 := by exact prefixLift 6784325
  have htrace : WordTrace (prefixWord ++ tailWord_6784325) baseStart_6784325 baseEnd_6784325 := by
    simpa [prefixWord, tailWord_6784325, baseEnd_6784325] using wordTrace_append hprefix tailTrace_6784325
  have hstable : (prefixWord ++ tailWord_6784325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784325).length < 2 ^ (prefixWord ++ tailWord_6784325).sum := by decide
  have hdescent : baseEnd_6784325 < baseStart_6784325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784345 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 4]
def baseStart_6784345 : Nat := 118140960795 + 6784345 * 2 ^ 59
def prefixEnd_6784345 : Nat := 4983230072969 + 3 ^ 40 * 6784345 * 2
def baseEnd_6784345 : Nat := 3483629910927363952686871

theorem tailTrace_6784345 : CollatzResearch.WordTrace tailWord_6784345 prefixEnd_6784345 3483629910927363952686871 := by
  unfold tailWord_6784345
  simp only [CollatzResearch.WordTrace]
  refine ⟨247445390606484213724370489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164963593737656142482913659 247445390606484213724370489)
  ·
    refine ⟨185584042954863160293277867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247445390606484213724370489 185584042954863160293277867)
    ·
      refine ⟨278376064432294740439916801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185584042954863160293277867 278376064432294740439916801)
      ·
        refine ⟨208782048324221055329937601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278376064432294740439916801 208782048324221055329937601)
        ·
          refine ⟨156586536243165791497453201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208782048324221055329937601 156586536243165791497453201)
          ·
            refine ⟨117439902182374343623089901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156586536243165791497453201 117439902182374343623089901)
            ·
              refine ⟨44039963318390378858658713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117439902182374343623089901 44039963318390378858658713)
              ·
                refine ⟨33029972488792784143994035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44039963318390378858658713 33029972488792784143994035)
                ·
                  refine ⟨49544958733189176215991053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33029972488792784143994035 49544958733189176215991053)
                  ·
                    refine ⟨18579359524945941080996645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49544958733189176215991053 18579359524945941080996645)
                    ·
                      refine ⟨3483629910927363952686871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18579359524945941080996645 3483629910927363952686871)
                      ·
                        rfl

theorem cell23_6784345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_6784345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784345 prefixEnd_6784345 := by exact prefixLift 6784345
  have htrace : WordTrace (prefixWord ++ tailWord_6784345) baseStart_6784345 baseEnd_6784345 := by
    simpa [prefixWord, tailWord_6784345, baseEnd_6784345] using wordTrace_append hprefix tailTrace_6784345
  have hstable : (prefixWord ++ tailWord_6784345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784345).length < 2 ^ (prefixWord ++ tailWord_6784345).sum := by decide
  have hdescent : baseEnd_6784345 < baseStart_6784345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784389 : List Nat := [1, 3, 1, 1, 3, 1, 2, 6, 1, 4]
def baseStart_6784389 : Nat := 118140960795 + 6784389 * 2 ^ 59
def prefixEnd_6784389 : Nat := 4983230072969 + 3 ^ 40 * 6784389 * 2
def baseEnd_6784389 : Nat := 1161217501358720593512223

theorem tailTrace_6784389 : CollatzResearch.WordTrace tailWord_6784389 prefixEnd_6784389 1161217501358720593512223 := by
  unfold tailWord_6784389
  simp only [CollatzResearch.WordTrace]
  refine ⟨247446995418324809238972221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164964663612216539492648147 247446995418324809238972221)
  ·
    refine ⟨92792623281871803464614583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247446995418324809238972221 92792623281871803464614583)
    ·
      refine ⟨139188934922807705196921875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92792623281871803464614583 139188934922807705196921875)
      ·
        refine ⟨208783402384211557795382813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139188934922807705196921875 208783402384211557795382813)
        ·
          refine ⟨78293775894079334173268555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208783402384211557795382813 78293775894079334173268555)
          ·
            refine ⟨117440663841119001259902833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78293775894079334173268555 117440663841119001259902833)
            ·
              refine ⟨88080497880839250944927125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117440663841119001259902833 88080497880839250944927125)
              ·
                refine ⟨4128773338164339888043459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88080497880839250944927125 4128773338164339888043459)
                ·
                  refine ⟨6193160007246509832065189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4128773338164339888043459 6193160007246509832065189)
                  ·
                    refine ⟨1161217501358720593512223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6193160007246509832065189 1161217501358720593512223)
                    ·
                      rfl

theorem cell23_6784389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_6784389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784389 prefixEnd_6784389 := by exact prefixLift 6784389
  have htrace : WordTrace (prefixWord ++ tailWord_6784389) baseStart_6784389 baseEnd_6784389 := by
    simpa [prefixWord, tailWord_6784389, baseEnd_6784389] using wordTrace_append hprefix tailTrace_6784389
  have hstable : (prefixWord ++ tailWord_6784389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784389).length < 2 ^ (prefixWord ++ tailWord_6784389).sum := by decide
  have hdescent : baseEnd_6784389 < baseStart_6784389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784405 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_6784405 : Nat := 118140960795 + 6784405 * 2 ^ 59
def prefixEnd_6784405 : Nat := 4983230072969 + 3 ^ 40 * 6784405 * 2
def baseEnd_6784405 : Nat := 3483660719766633717936595

theorem tailTrace_6784405 : CollatzResearch.WordTrace tailWord_6784405 prefixEnd_6784405 3483660719766633717936595 := by
  unfold tailWord_6784405
  simp only [CollatzResearch.WordTrace]
  refine ⟨247447578986266843971554669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164965052657511229314369779 247447578986266843971554669)
  ·
    refine ⟨92792842119850066489333001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247447578986266843971554669 92792842119850066489333001)
    ·
      refine ⟨69594631589887549866999751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92792842119850066489333001 69594631589887549866999751)
      ·
        refine ⟨104391947384831324800499627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69594631589887549866999751 104391947384831324800499627)
        ·
          refine ⟨156587921077246987200749441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104391947384831324800499627 156587921077246987200749441)
          ·
            refine ⟨117440940807935240400562081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156587921077246987200749441 117440940807935240400562081)
            ·
              refine ⟨88080705605951430300421561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117440940807935240400562081 88080705605951430300421561)
              ·
                refine ⟨66060529204463572725316171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88080705605951430300421561 66060529204463572725316171)
                ·
                  refine ⟨99090793806695359087974257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66060529204463572725316171 99090793806695359087974257)
                  ·
                    refine ⟨74318095355021519315980693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99090793806695359087974257 74318095355021519315980693)
                    ·
                      refine ⟨3483660719766633717936595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74318095355021519315980693 3483660719766633717936595)
                      ·
                        rfl

theorem cell23_6784405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_6784405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784405 prefixEnd_6784405 := by exact prefixLift 6784405
  have htrace : WordTrace (prefixWord ++ tailWord_6784405) baseStart_6784405 baseEnd_6784405 := by
    simpa [prefixWord, tailWord_6784405, baseEnd_6784405] using wordTrace_append hprefix tailTrace_6784405
  have hstable : (prefixWord ++ tailWord_6784405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784405).length < 2 ^ (prefixWord ++ tailWord_6784405).sum := by decide
  have hdescent : baseEnd_6784405 < baseStart_6784405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784439 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 2, 3, 2]
def baseStart_6784439 : Nat := 118140960795 + 6784439 * 2 ^ 59
def prefixEnd_6784439 : Nat := 4983230072969 + 3 ^ 40 * 6784439 * 2
def baseEnd_6784439 : Nat := 3483678178108886584911439

theorem tailTrace_6784439 : CollatzResearch.WordTrace tailWord_6784439 prefixEnd_6784439 3483678178108886584911439 := by
  unfold tailWord_6784439
  simp only [CollatzResearch.WordTrace]
  refine ⟨247448819068143667778292371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164965879378762445185528247 247448819068143667778292371)
  ·
    refine ⟨371173228602215501667438557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247448819068143667778292371 371173228602215501667438557)
    ·
      refine ⟨139189960725830813125289459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371173228602215501667438557 139189960725830813125289459)
      ·
        refine ⟨208784941088746219687934189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139189960725830813125289459 208784941088746219687934189)
        ·
          refine ⟨78294352908279832382975321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208784941088746219687934189 78294352908279832382975321)
          ·
            refine ⟨58720764681209874287231491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78294352908279832382975321 58720764681209874287231491)
            ·
              refine ⟨88081147021814811430847237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58720764681209874287231491 88081147021814811430847237)
              ·
                refine ⟨16515215066590277143283857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88081147021814811430847237 16515215066590277143283857)
                ·
                  refine ⟨12386411299942707857462893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16515215066590277143283857 12386411299942707857462893)
                  ·
                    refine ⟨4644904237478515446548585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12386411299942707857462893 4644904237478515446548585)
                    ·
                      refine ⟨3483678178108886584911439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4644904237478515446548585 3483678178108886584911439)
                      ·
                        rfl

theorem cell23_6784439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 3, 2].length) (baseStart_6784439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784439 prefixEnd_6784439 := by exact prefixLift 6784439
  have htrace : WordTrace (prefixWord ++ tailWord_6784439) baseStart_6784439 baseEnd_6784439 := by
    simpa [prefixWord, tailWord_6784439, baseEnd_6784439] using wordTrace_append hprefix tailTrace_6784439
  have hstable : (prefixWord ++ tailWord_6784439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784439).length < 2 ^ (prefixWord ++ tailWord_6784439).sum := by decide
  have hdescent : baseEnd_6784439 < baseStart_6784439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784462 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_6784462 : Nat := 118140960795 + 6784462 * 2 ^ 59
def prefixEnd_6784462 : Nat := 4983230072969 + 3 ^ 40 * 6784462 * 2
def baseEnd_6784462 : Nat := 1161229996054646664974611

theorem tailTrace_6784462 : CollatzResearch.WordTrace tailWord_6784462 prefixEnd_6784462 1161229996054646664974611 := by
  unfold tailWord_6784462
  simp only [CollatzResearch.WordTrace]
  refine ⟨30931207243382542838297455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164966438631373561804253093 30931207243382542838297455)
  ·
    refine ⟨46396810865073814257446183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30931207243382542838297455 46396810865073814257446183)
    ·
      refine ⟨69595216297610721386169275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46396810865073814257446183 69595216297610721386169275)
      ·
        refine ⟨104392824446416082079253913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69595216297610721386169275 104392824446416082079253913)
        ·
          refine ⟨78294618334812061559440435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104392824446416082079253913 78294618334812061559440435)
          ·
            refine ⟨117441927502218092339160653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78294618334812061559440435 117441927502218092339160653)
            ·
              refine ⟨44040722813331784627185245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117441927502218092339160653 44040722813331784627185245)
              ·
                refine ⟨16515271054999419235194467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44040722813331784627185245 16515271054999419235194467)
                ·
                  refine ⟨24772906582499128852791701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16515271054999419235194467 24772906582499128852791701)
                  ·
                    refine ⟨1161229996054646664974611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24772906582499128852791701 1161229996054646664974611)
                    ·
                      rfl

theorem cell23_6784462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_6784462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784462 prefixEnd_6784462 := by exact prefixLift 6784462
  have htrace : WordTrace (prefixWord ++ tailWord_6784462) baseStart_6784462 baseEnd_6784462 := by
    simpa [prefixWord, tailWord_6784462, baseEnd_6784462] using wordTrace_append hprefix tailTrace_6784462
  have hstable : (prefixWord ++ tailWord_6784462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784462).length < 2 ^ (prefixWord ++ tailWord_6784462).sum := by decide
  have hdescent : baseEnd_6784462 < baseStart_6784462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784469 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_6784469 : Nat := 118140960795 + 6784469 * 2 ^ 59
def prefixEnd_6784469 : Nat := 4983230072969 + 3 ^ 40 * 6784469 * 2
def baseEnd_6784469 : Nat := 3483693582528521467536301

theorem tailTrace_6784469 : CollatzResearch.WordTrace tailWord_6784469 prefixEnd_6784469 3483693582528521467536301 := by
  unfold tailWord_6784469
  simp only [CollatzResearch.WordTrace]
  refine ⟨247449913258034982901884461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164966608838689988601256307 247449913258034982901884461)
  ·
    refine ⟨92793717471763118588206673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247449913258034982901884461 92793717471763118588206673)
    ·
      refine ⟨69595288103822338941155005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92793717471763118588206673 69595288103822338941155005)
      ·
        refine ⟨26098233038933377102933127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69595288103822338941155005 26098233038933377102933127)
        ·
          refine ⟨39147349558400065654399691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26098233038933377102933127 39147349558400065654399691)
          ·
            refine ⟨58721024337600098481599537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39147349558400065654399691 58721024337600098481599537)
            ·
              refine ⟨44040768253200073861199653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58721024337600098481599537 44040768253200073861199653)
              ·
                refine ⟨8257644047475013848974935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44040768253200073861199653 8257644047475013848974935)
                ·
                  refine ⟨12386466071212520773462403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8257644047475013848974935 12386466071212520773462403)
                  ·
                    refine ⟨18579699106818781160193605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12386466071212520773462403 18579699106818781160193605)
                    ·
                      refine ⟨3483693582528521467536301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18579699106818781160193605 3483693582528521467536301)
                      ·
                        rfl

theorem cell23_6784469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_6784469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784469 prefixEnd_6784469 := by exact prefixLift 6784469
  have htrace : WordTrace (prefixWord ++ tailWord_6784469) baseStart_6784469 baseEnd_6784469 := by
    simpa [prefixWord, tailWord_6784469, baseEnd_6784469] using wordTrace_append hprefix tailTrace_6784469
  have hstable : (prefixWord ++ tailWord_6784469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784469).length < 2 ^ (prefixWord ++ tailWord_6784469).sum := by decide
  have hdescent : baseEnd_6784469 < baseStart_6784469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784496 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 2, 4]
def baseStart_6784496 : Nat := 118140960795 + 6784496 * 2 ^ 59
def prefixEnd_6784496 : Nat := 4983230072969 + 3 ^ 40 * 6784496 * 2
def baseEnd_6784496 : Nat := 1161235815502064287299559

theorem tailTrace_6784496 : CollatzResearch.WordTrace tailWord_6784496 prefixEnd_6784496 1161235815502064287299559 := by
  unfold tailWord_6784496
  simp only [CollatzResearch.WordTrace]
  refine ⟨123725449014468583256558671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164967265352624777675411561 123725449014468583256558671)
  ·
    refine ⟨185588173521702874884838007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123725449014468583256558671 185588173521702874884838007)
    ·
      refine ⟨278382260282554312327257011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185588173521702874884838007 278382260282554312327257011)
      ·
        refine ⟨417573390423831468490885517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278382260282554312327257011 417573390423831468490885517)
        ·
          refine ⟨156590021408936800684082069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 417573390423831468490885517 156590021408936800684082069)
          ·
            refine ⟨7340157253543912532066347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156590021408936800684082069 7340157253543912532066347)
            ·
              refine ⟨11010235880315868798099521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7340157253543912532066347 11010235880315868798099521)
              ·
                refine ⟨8257676910236901598574641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11010235880315868798099521 8257676910236901598574641)
                ·
                  refine ⟨6193257682677676198930981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8257676910236901598574641 6193257682677676198930981)
                  ·
                    refine ⟨1161235815502064287299559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6193257682677676198930981 1161235815502064287299559)
                    ·
                      rfl

theorem cell23_6784496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2, 4].length) (baseStart_6784496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784496 prefixEnd_6784496 := by exact prefixLift 6784496
  have htrace : WordTrace (prefixWord ++ tailWord_6784496) baseStart_6784496 baseEnd_6784496 := by
    simpa [prefixWord, tailWord_6784496, baseEnd_6784496] using wordTrace_append hprefix tailTrace_6784496
  have hstable : (prefixWord ++ tailWord_6784496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784496).length < 2 ^ (prefixWord ++ tailWord_6784496).sum := by decide
  have hdescent : baseEnd_6784496 < baseStart_6784496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784513 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 2, 4]
def baseStart_6784513 : Nat := 118140960795 + 6784513 * 2 ^ 59
def prefixEnd_6784513 : Nat := 4983230072969 + 3 ^ 40 * 6784513 * 2
def baseEnd_6784513 : Nat := 1161238725225773098462033

theorem tailTrace_6784513 : CollatzResearch.WordTrace tailWord_6784513 prefixEnd_6784513 1161238725225773098462033 := by
  unfold tailWord_6784513
  simp only [CollatzResearch.WordTrace]
  refine ⟨247451518069875578416486193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164967678713250385610990795 247451518069875578416486193)
  ·
    refine ⟨185588638552406683812364645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247451518069875578416486193 185588638552406683812364645)
    ·
      refine ⟨34797869728576253214818371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185588638552406683812364645 34797869728576253214818371)
      ·
        refine ⟨52196804592864379822227557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34797869728576253214818371 52196804592864379822227557)
        ·
          refine ⟨9786900861162071216667667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52196804592864379822227557 9786900861162071216667667)
          ·
            refine ⟨14680351291743106825001501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9786900861162071216667667 14680351291743106825001501)
            ·
              refine ⟨5505131734403665059375563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14680351291743106825001501 5505131734403665059375563)
              ·
                refine ⟨8257697601605497589063345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505131734403665059375563 8257697601605497589063345)
                ·
                  refine ⟨6193273201204123191797509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8257697601605497589063345 6193273201204123191797509)
                  ·
                    refine ⟨1161238725225773098462033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6193273201204123191797509 1161238725225773098462033)
                    ·
                      rfl

theorem cell23_6784513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_6784513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784513 prefixEnd_6784513 := by exact prefixLift 6784513
  have htrace : WordTrace (prefixWord ++ tailWord_6784513) baseStart_6784513 baseEnd_6784513 := by
    simpa [prefixWord, tailWord_6784513, baseEnd_6784513] using wordTrace_append hprefix tailTrace_6784513
  have hstable : (prefixWord ++ tailWord_6784513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784513).length < 2 ^ (prefixWord ++ tailWord_6784513).sum := by decide
  have hdescent : baseEnd_6784513 < baseStart_6784513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784526 : List Nat := [4, 1, 1, 2, 4, 2, 2, 7]
def baseStart_6784526 : Nat := 118140960795 + 6784526 * 2 ^ 59
def prefixEnd_6784526 : Nat := 4983230072969 + 3 ^ 40 * 6784526 * 2
def baseEnd_6784526 : Nat := 129026772256512138686057

theorem tailTrace_6784526 : CollatzResearch.WordTrace tailWord_6784526 prefixEnd_6784526 129026772256512138686057 := by
  unfold tailWord_6784526
  simp only [CollatzResearch.WordTrace]
  refine ⟨30931499027353560204588679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164967994812552321091139621 30931499027353560204588679)
  ·
    refine ⟨46397248541030340306883019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30931499027353560204588679 46397248541030340306883019)
    ·
      refine ⟨69595872811545510460324529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46397248541030340306883019 69595872811545510460324529)
      ·
        refine ⟨52196904608659132845243397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69595872811545510460324529 52196904608659132845243397)
        ·
          refine ⟨9786919614123587408483137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52196904608659132845243397 9786919614123587408483137)
          ·
            refine ⟨7340189710592690556362353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9786919614123587408483137 7340189710592690556362353)
            ·
              refine ⟨5505142282944517917271765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7340189710592690556362353 5505142282944517917271765)
              ·
                refine ⟨129026772256512138686057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5505142282944517917271765 129026772256512138686057)
                ·
                  rfl

theorem cell23_6784526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_6784526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784526 prefixEnd_6784526 := by exact prefixLift 6784526
  have htrace : WordTrace (prefixWord ++ tailWord_6784526) baseStart_6784526 baseEnd_6784526 := by
    simpa [prefixWord, tailWord_6784526, baseEnd_6784526] using wordTrace_append hprefix tailTrace_6784526
  have hstable : (prefixWord ++ tailWord_6784526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784526).length < 2 ^ (prefixWord ++ tailWord_6784526).sum := by decide
  have hdescent : baseEnd_6784526 < baseStart_6784526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784562 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_6784562 : Nat := 118140960795 + 6784562 * 2 ^ 59
def prefixEnd_6784562 : Nat := 4983230072969 + 3 ^ 40 * 6784562 * 2
def baseEnd_6784562 : Nat := 3483741336229389603673373

theorem tailTrace_6784562 : CollatzResearch.WordTrace tailWord_6784562 prefixEnd_6784562 3483741336229389603673373 := by
  unfold tailWord_6784562
  simp only [CollatzResearch.WordTrace]
  refine ⟨61863326311674514946254985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164968870164465373190013293 61863326311674514946254985)
  ·
    refine ⟨46397494733755886209691239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61863326311674514946254985 46397494733755886209691239)
    ·
      refine ⟨69596242100633829314536859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46397494733755886209691239 69596242100633829314536859)
      ·
        refine ⟨104394363150950743971805289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69596242100633829314536859 104394363150950743971805289)
        ·
          refine ⟨78295772363213057978853967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104394363150950743971805289 78295772363213057978853967)
          ·
            refine ⟨117443658544819586968280951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78295772363213057978853967 117443658544819586968280951)
            ·
              refine ⟨176165487817229380452421427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117443658544819586968280951 176165487817229380452421427)
              ·
                refine ⟨264248231725844070678632141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176165487817229380452421427 264248231725844070678632141)
                ·
                  refine ⟨99093086897191526504487053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264248231725844070678632141 99093086897191526504487053)
                  ·
                    refine ⟨37159907586446822439182645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99093086897191526504487053 37159907586446822439182645)
                    ·
                      refine ⟨3483741336229389603673373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37159907586446822439182645 3483741336229389603673373)
                      ·
                        rfl

theorem cell23_6784562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_6784562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784562 prefixEnd_6784562 := by exact prefixLift 6784562
  have htrace : WordTrace (prefixWord ++ tailWord_6784562) baseStart_6784562 baseEnd_6784562 := by
    simpa [prefixWord, tailWord_6784562, baseEnd_6784562] using wordTrace_append hprefix tailTrace_6784562
  have hstable : (prefixWord ++ tailWord_6784562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784562).length < 2 ^ (prefixWord ++ tailWord_6784562).sum := by decide
  have hdescent : baseEnd_6784562 < baseStart_6784562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784609 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_6784609 : Nat := 118140960795 + 6784609 * 2 ^ 59
def prefixEnd_6784609 : Nat := 4983230072969 + 3 ^ 40 * 6784609 * 2
def baseEnd_6784609 : Nat := 3483765469820150919785657

theorem tailTrace_6784609 : CollatzResearch.WordTrace tailWord_6784609 prefixEnd_6784609 3483765469820150919785657 := by
  unfold tailWord_6784609
  simp only [CollatzResearch.WordTrace]
  refine ⟨247455019477527786811980881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164970012985018524541320587 247455019477527786811980881)
  ·
    refine ⟨185591264608145840108985661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247455019477527786811980881 185591264608145840108985661)
    ·
      refine ⟨69596724228054690040869623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185591264608145840108985661 69596724228054690040869623)
      ·
        refine ⟨104395086342082035061304435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69596724228054690040869623 104395086342082035061304435)
        ·
          refine ⟨156592629513123052591956653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104395086342082035061304435 156592629513123052591956653)
          ·
            refine ⟨58722236067421144721983745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156592629513123052591956653 58722236067421144721983745)
            ·
              refine ⟨44041677050565858541487809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58722236067421144721983745 44041677050565858541487809)
              ·
                refine ⟨33031257787924393906115857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44041677050565858541487809 33031257787924393906115857)
                ·
                  refine ⟨24773443340943295429586893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33031257787924393906115857 24773443340943295429586893)
                  ·
                    refine ⟨9290041252853735786095085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24773443340943295429586893 9290041252853735786095085)
                    ·
                      refine ⟨3483765469820150919785657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9290041252853735786095085 3483765469820150919785657)
                      ·
                        rfl

theorem cell23_6784609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_6784609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784609 prefixEnd_6784609 := by exact prefixLift 6784609
  have htrace : WordTrace (prefixWord ++ tailWord_6784609) baseStart_6784609 baseEnd_6784609 := by
    simpa [prefixWord, tailWord_6784609, baseEnd_6784609] using wordTrace_append hprefix tailTrace_6784609
  have hstable : (prefixWord ++ tailWord_6784609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784609).length < 2 ^ (prefixWord ++ tailWord_6784609).sum := by decide
  have hdescent : baseEnd_6784609 < baseStart_6784609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784626 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_6784626 : Nat := 118140960795 + 6784626 * 2 ^ 59
def prefixEnd_6784626 : Nat := 4983230072969 + 3 ^ 40 * 6784626 * 2
def baseEnd_6784626 : Nat := 3483774198991277353273079

theorem tailTrace_6784626 : CollatzResearch.WordTrace tailWord_6784626 prefixEnd_6784626 3483774198991277353273079 := by
  unfold tailWord_6784626
  simp only [CollatzResearch.WordTrace]
  refine ⟨61863909879616549678837433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164970426345644132476899821 61863909879616549678837433)
  ·
    refine ⟨46397932409712412259128075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61863909879616549678837433 46397932409712412259128075)
    ·
      refine ⟨69596898614568618388692113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46397932409712412259128075 69596898614568618388692113)
      ·
        refine ⟨52197673960926463791519085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69596898614568618388692113 52197673960926463791519085)
        ·
          refine ⟨19574127735347423921819657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52197673960926463791519085 19574127735347423921819657)
          ·
            refine ⟨14680595801510567941364743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19574127735347423921819657 14680595801510567941364743)
            ·
              refine ⟨22020893702265851912047115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14680595801510567941364743 22020893702265851912047115)
              ·
                refine ⟨33031340553398777868070673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22020893702265851912047115 33031340553398777868070673)
                ·
                  refine ⟨24773505415049083401053005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33031340553398777868070673 24773505415049083401053005)
                  ·
                    refine ⟨9290064530643406275394877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24773505415049083401053005 9290064530643406275394877)
                    ·
                      refine ⟨3483774198991277353273079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9290064530643406275394877 3483774198991277353273079)
                      ·
                        rfl

theorem cell23_6784626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_6784626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784626 prefixEnd_6784626 := by exact prefixLift 6784626
  have htrace : WordTrace (prefixWord ++ tailWord_6784626) baseStart_6784626 baseEnd_6784626 := by
    simpa [prefixWord, tailWord_6784626, baseEnd_6784626] using wordTrace_append hprefix tailTrace_6784626
  have hstable : (prefixWord ++ tailWord_6784626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784626).length < 2 ^ (prefixWord ++ tailWord_6784626).sum := by decide
  have hdescent : baseEnd_6784626 < baseStart_6784626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784676 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_6784676 : Nat := 118140960795 + 6784676 * 2 ^ 59
def prefixEnd_6784676 : Nat := 4983230072969 + 3 ^ 40 * 6784676 * 2
def baseEnd_6784676 : Nat := 1161266624341334052549283

theorem tailTrace_6784676 : CollatzResearch.WordTrace tailWord_6784676 prefixEnd_6784676 1161266624341334052549283 := by
  unfold tailWord_6784676
  simp only [CollatzResearch.WordTrace]
  refine ⟨123728731584142528627334941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164971642112190038169779921 123728731584142528627334941)
  ·
    refine ⟨46398274344053448235250603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123728731584142528627334941 46398274344053448235250603)
    ·
      refine ⟨69597411516080172352875905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46398274344053448235250603 69597411516080172352875905)
      ·
        refine ⟨52198058637060129264656929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69597411516080172352875905 52198058637060129264656929)
        ·
          refine ⟨39148543977795096948492697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52198058637060129264656929 39148543977795096948492697)
          ·
            refine ⟨29361407983346322711369523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39148543977795096948492697 29361407983346322711369523)
            ·
              refine ⟨44042111975019484067054285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29361407983346322711369523 44042111975019484067054285)
              ·
                refine ⟨16515791990632306525145357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44042111975019484067054285 16515791990632306525145357)
                ·
                  refine ⟨6193421996487114946929509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16515791990632306525145357 6193421996487114946929509)
                  ·
                    refine ⟨1161266624341334052549283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6193421996487114946929509 1161266624341334052549283)
                    ·
                      rfl

theorem cell23_6784676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_6784676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784676 prefixEnd_6784676 := by exact prefixLift 6784676
  have htrace : WordTrace (prefixWord ++ tailWord_6784676) baseStart_6784676 baseEnd_6784676 := by
    simpa [prefixWord, tailWord_6784676, baseEnd_6784676] using wordTrace_append hprefix tailTrace_6784676
  have hstable : (prefixWord ++ tailWord_6784676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784676).length < 2 ^ (prefixWord ++ tailWord_6784676).sum := by decide
  have hdescent : baseEnd_6784676 < baseStart_6784676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784753 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 1, 5]
def baseStart_6784753 : Nat := 118140960795 + 6784753 * 2 ^ 59
def prefixEnd_6784753 : Nat := 4983230072969 + 3 ^ 40 * 6784753 * 2
def baseEnd_6784753 : Nat := 1161279803678132785461665

theorem tailTrace_6784753 : CollatzResearch.WordTrace tailWord_6784753 prefixEnd_6784753 1161279803678132785461665 := by
  unfold tailWord_6784753
  simp only [CollatzResearch.WordTrace]
  refine ⟨247460271589006099405222913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164973514392670732936815275 247460271589006099405222913)
  ·
    refine ⟨185595203691754574553917185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247460271589006099405222913 185595203691754574553917185)
    ·
      refine ⟨139196402768815930915437889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185595203691754574553917185 139196402768815930915437889)
      ·
        refine ⟨104397302076611948186578417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139196402768815930915437889 104397302076611948186578417)
        ·
          refine ⟨78297976557458961139933813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104397302076611948186578417 78297976557458961139933813)
          ·
            refine ⟨7340435302261777606868795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78297976557458961139933813 7340435302261777606868795)
            ·
              refine ⟨11010652953392666410303193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7340435302261777606868795 11010652953392666410303193)
              ·
                refine ⟨8257989715044499807727395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11010652953392666410303193 8257989715044499807727395)
                ·
                  refine ⟨12386984572566749711591093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8257989715044499807727395 12386984572566749711591093)
                  ·
                    refine ⟨1161279803678132785461665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12386984572566749711591093 1161279803678132785461665)
                    ·
                      rfl

theorem cell23_6784753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_6784753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784753 prefixEnd_6784753 := by exact prefixLift 6784753
  have htrace : WordTrace (prefixWord ++ tailWord_6784753) baseStart_6784753 baseEnd_6784753 := by
    simpa [prefixWord, tailWord_6784753, baseEnd_6784753] using wordTrace_append hprefix tailTrace_6784753
  have hstable : (prefixWord ++ tailWord_6784753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784753).length < 2 ^ (prefixWord ++ tailWord_6784753).sum := by decide
  have hdescent : baseEnd_6784753 < baseStart_6784753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784759 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_6784759 : Nat := 118140960795 + 6784759 * 2 ^ 59
def prefixEnd_6784759 : Nat := 4983230072969 + 3 ^ 40 * 6784759 * 2
def baseEnd_6784759 : Nat := 3483842491918325332909967

theorem tailTrace_6784759 : CollatzResearch.WordTrace tailWord_6784759 prefixEnd_6784759 3483842491918325332909967 := by
  unfold tailWord_6784759
  simp only [CollatzResearch.WordTrace]
  refine ⟨247460490426984362429941331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164973660284656241619960887 247460490426984362429941331)
  ·
    refine ⟨371190735640476543644911997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247460490426984362429941331 371190735640476543644911997)
    ·
      refine ⟨139196525865178703866841999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371190735640476543644911997 139196525865178703866841999)
      ·
        refine ⟨208794788797768055800262999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139196525865178703866841999 208794788797768055800262999)
        ·
          refine ⟨313192183196652083700394499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208794788797768055800262999 313192183196652083700394499)
          ·
            refine ⟨469788274794978125550591749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313192183196652083700394499 469788274794978125550591749)
            ·
              refine ⟨88085301524058398540735953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 469788274794978125550591749 88085301524058398540735953)
              ·
                refine ⟨66063976143043798905551965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88085301524058398540735953 66063976143043798905551965)
                ·
                  refine ⟨24773991053641424589581987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66063976143043798905551965 24773991053641424589581987)
                  ·
                    refine ⟨37160986580462136884372981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24773991053641424589581987 37160986580462136884372981)
                    ·
                      refine ⟨3483842491918325332909967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37160986580462136884372981 3483842491918325332909967)
                      ·
                        rfl

theorem cell23_6784759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_6784759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784759 prefixEnd_6784759 := by exact prefixLift 6784759
  have htrace : WordTrace (prefixWord ++ tailWord_6784759) baseStart_6784759 baseEnd_6784759 := by
    simpa [prefixWord, tailWord_6784759, baseEnd_6784759] using wordTrace_append hprefix tailTrace_6784759
  have hstable : (prefixWord ++ tailWord_6784759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784759).length < 2 ^ (prefixWord ++ tailWord_6784759).sum := by decide
  have hdescent : baseEnd_6784759 < baseStart_6784759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784770 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_6784770 : Nat := 118140960795 + 6784770 * 2 ^ 59
def prefixEnd_6784770 : Nat := 4983230072969 + 3 ^ 40 * 6784770 * 2
def baseEnd_6784770 : Nat := 1161282713401841596624139

theorem tailTrace_6784770 : CollatzResearch.WordTrace tailWord_6784770 prefixEnd_6784770 1161282713401841596624139 := by
  unfold tailWord_6784770
  simp only [CollatzResearch.WordTrace]
  refine ⟨61865222907486127827147941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164973927753296340872394509 61865222907486127827147941)
  ·
    refine ⟨11599729295153648967590239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61865222907486127827147941 11599729295153648967590239)
    ·
      refine ⟨17399593942730473451385359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11599729295153648967590239 17399593942730473451385359)
      ·
        refine ⟨26099390914095710177078039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17399593942730473451385359 26099390914095710177078039)
        ·
          refine ⟨39149086371143565265617059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26099390914095710177078039 39149086371143565265617059)
          ·
            refine ⟨58723629556715347898425589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39149086371143565265617059 58723629556715347898425589)
            ·
              refine ⟨5505340270942063865477399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58723629556715347898425589 5505340270942063865477399)
              ·
                refine ⟨8258010406413095798216099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505340270942063865477399 8258010406413095798216099)
                ·
                  refine ⟨12387015609619643697324149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8258010406413095798216099 12387015609619643697324149)
                  ·
                    refine ⟨1161282713401841596624139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12387015609619643697324149 1161282713401841596624139)
                    ·
                      rfl

theorem cell23_6784770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_6784770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784770 prefixEnd_6784770 := by exact prefixLift 6784770
  have htrace : WordTrace (prefixWord ++ tailWord_6784770) baseStart_6784770 baseEnd_6784770 := by
    simpa [prefixWord, tailWord_6784770, baseEnd_6784770] using wordTrace_append hprefix tailTrace_6784770
  have hstable : (prefixWord ++ tailWord_6784770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784770).length < 2 ^ (prefixWord ++ tailWord_6784770).sum := by decide
  have hdescent : baseEnd_6784770 < baseStart_6784770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784840 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_6784840 : Nat := 118140960795 + 6784840 * 2 ^ 59
def prefixEnd_6784840 : Nat := 4983230072969 + 3 ^ 40 * 6784840 * 2
def baseEnd_6784840 : Nat := 3483884083851339515997095

theorem tailTrace_6784840 : CollatzResearch.WordTrace tailWord_6784840 prefixEnd_6784840 3483884083851339515997095 := by
  unfold tailWord_6784840
  simp only [CollatzResearch.WordTrace]
  refine ⟨123731722369845456631819987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164975629826460608842426649 123731722369845456631819987)
  ·
    refine ⟨185597583554768184947729981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123731722369845456631819987 185597583554768184947729981)
    ·
      refine ⟨69599093833038069355398743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185597583554768184947729981 69599093833038069355398743)
      ·
        refine ⟨104398640749557104033098115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69599093833038069355398743 104398640749557104033098115)
        ·
          refine ⟨156597961124335656049647173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104398640749557104033098115 156597961124335656049647173)
          ·
            refine ⟨29362117710812935509308845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156597961124335656049647173 29362117710812935509308845)
            ·
              refine ⟨11010794141554850815990817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29362117710812935509308845 11010794141554850815990817)
              ·
                refine ⟨8258095606166138111993113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11010794141554850815990817 8258095606166138111993113)
                ·
                  refine ⟨6193571704624603583994835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8258095606166138111993113 6193571704624603583994835)
                  ·
                    refine ⟨9290357556936905375992253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6193571704624603583994835 9290357556936905375992253)
                    ·
                      refine ⟨3483884083851339515997095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9290357556936905375992253 3483884083851339515997095)
                      ·
                        rfl

theorem cell23_6784840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_6784840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784840 prefixEnd_6784840 := by exact prefixLift 6784840
  have htrace : WordTrace (prefixWord ++ tailWord_6784840) baseStart_6784840 baseEnd_6784840 := by
    simpa [prefixWord, tailWord_6784840, baseEnd_6784840] using wordTrace_append hprefix tailTrace_6784840
  have hstable : (prefixWord ++ tailWord_6784840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784840).length < 2 ^ (prefixWord ++ tailWord_6784840).sum := by decide
  have hdescent : baseEnd_6784840 < baseStart_6784840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784867 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 1, 3, 2]
def baseStart_6784867 : Nat := 118140960795 + 6784867 * 2 ^ 59
def prefixEnd_6784867 : Nat := 4983230072969 + 3 ^ 40 * 6784867 * 2
def baseEnd_6784867 : Nat := 3483897947829010910359471

theorem tailTrace_6784867 : CollatzResearch.WordTrace tailWord_6784867 prefixEnd_6784867 3483897947829010910359471 := by
  unfold tailWord_6784867
  simp only [CollatzResearch.WordTrace]
  refine ⟨247464429510593096874872855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164976286340395397916581903 247464429510593096874872855)
  ·
    refine ⟨371196644265889645312309283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247464429510593096874872855 371196644265889645312309283)
    ·
      refine ⟨556794966398834467968463925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371196644265889645312309283 556794966398834467968463925)
      ·
        refine ⟨52199528099890731372043493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 556794966398834467968463925 52199528099890731372043493)
        ·
          refine ⟨9787411518729512132258155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52199528099890731372043493 9787411518729512132258155)
          ·
            refine ⟨14681117278094268198387233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9787411518729512132258155 14681117278094268198387233)
            ·
              refine ⟨11010837958570701148790425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14681117278094268198387233 11010837958570701148790425)
              ·
                refine ⟨8258128468928025861592819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11010837958570701148790425 8258128468928025861592819)
                ·
                  refine ⟨12387192703392038792389229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8258128468928025861592819 12387192703392038792389229)
                  ·
                    refine ⟨4645197263772014547145961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12387192703392038792389229 4645197263772014547145961)
                    ·
                      refine ⟨3483897947829010910359471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645197263772014547145961 3483897947829010910359471)
                      ·
                        rfl

theorem cell23_6784867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_6784867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784867 prefixEnd_6784867 := by exact prefixLift 6784867
  have htrace : WordTrace (prefixWord ++ tailWord_6784867) baseStart_6784867 baseEnd_6784867 := by
    simpa [prefixWord, tailWord_6784867, baseEnd_6784867] using wordTrace_append hprefix tailTrace_6784867
  have hstable : (prefixWord ++ tailWord_6784867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784867).length < 2 ^ (prefixWord ++ tailWord_6784867).sum := by decide
  have hdescent : baseEnd_6784867 < baseStart_6784867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784914 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_6784914 : Nat := 118140960795 + 6784914 * 2 ^ 59
def prefixEnd_6784914 : Nat := 4983230072969 + 3 ^ 40 * 6784914 * 2
def baseEnd_6784914 : Nat := 3483922081419772226471755

theorem tailTrace_6784914 : CollatzResearch.WordTrace tailWord_6784914 prefixEnd_6784914 3483922081419772226471755 := by
  unfold tailWord_6784914
  simp only [CollatzResearch.WordTrace]
  refine ⟨61866535935355705975458449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164977429160948549267889197 61866535935355705975458449)
  ·
    refine ⟨46399901951516779481593837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61866535935355705975458449 46399901951516779481593837)
    ·
      refine ⟨17399963231818792305597689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46399901951516779481593837 17399963231818792305597689)
      ·
        refine ⟨13049972423864094229198267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17399963231818792305597689 13049972423864094229198267)
        ·
          refine ⟨19574958635796141343797401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13049972423864094229198267 19574958635796141343797401)
          ·
            refine ⟨14681218976847106007848051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19574958635796141343797401 14681218976847106007848051)
            ·
              refine ⟨22021828465270659011772077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14681218976847106007848051 22021828465270659011772077)
              ·
                refine ⟨8258185674476497129414529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22021828465270659011772077 8258185674476497129414529)
                ·
                  refine ⟨6193639255857372847060897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8258185674476497129414529 6193639255857372847060897)
                  ·
                    refine ⟨4645229441893029635295673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6193639255857372847060897 4645229441893029635295673)
                    ·
                      refine ⟨3483922081419772226471755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645229441893029635295673 3483922081419772226471755)
                      ·
                        rfl

theorem cell23_6784914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_6784914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784914 prefixEnd_6784914 := by exact prefixLift 6784914
  have htrace : WordTrace (prefixWord ++ tailWord_6784914) baseStart_6784914 baseEnd_6784914 := by
    simpa [prefixWord, tailWord_6784914, baseEnd_6784914] using wordTrace_append hprefix tailTrace_6784914
  have hstable : (prefixWord ++ tailWord_6784914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784914).length < 2 ^ (prefixWord ++ tailWord_6784914).sum := by decide
  have hdescent : baseEnd_6784914 < baseStart_6784914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784918 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_6784918 : Nat := 118140960795 + 6784918 * 2 ^ 59
def prefixEnd_6784918 : Nat := 4983230072969 + 3 ^ 40 * 6784918 * 2
def baseEnd_6784918 : Nat := 3483924135342390210821737

theorem tailTrace_6784918 : CollatzResearch.WordTrace tailWord_6784918 prefixEnd_6784918 3483924135342390210821737 := by
  unfold tailWord_6784918
  simp only [CollatzResearch.WordTrace]
  refine ⟨15466643102088020786561213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164977526422272221723319605 15466643102088020786561213)
  ·
    refine ⟨5799991163283007794960455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15466643102088020786561213 5799991163283007794960455)
    ·
      refine ⟨8699986744924511692440683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5799991163283007794960455 8699986744924511692440683)
      ·
        refine ⟨13049980117386767538661025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8699986744924511692440683 13049980117386767538661025)
        ·
          refine ⟨9787485088040075653995769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13049980117386767538661025 9787485088040075653995769)
          ·
            refine ⟨7340613816030056740496827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9787485088040075653995769 7340613816030056740496827)
            ·
              refine ⟨11010920724045085110745241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7340613816030056740496827 11010920724045085110745241)
              ·
                refine ⟨8258190543033813833058931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11010920724045085110745241 8258190543033813833058931)
                ·
                  refine ⟨12387285814550720749588397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8258190543033813833058931 12387285814550720749588397)
                  ·
                    refine ⟨4645232180456520281095649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12387285814550720749588397 4645232180456520281095649)
                    ·
                      refine ⟨3483924135342390210821737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645232180456520281095649 3483924135342390210821737)
                      ·
                        rfl

theorem cell23_6784918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_6784918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784918 prefixEnd_6784918 := by exact prefixLift 6784918
  have htrace : WordTrace (prefixWord ++ tailWord_6784918) baseStart_6784918 baseEnd_6784918 := by
    simpa [prefixWord, tailWord_6784918, baseEnd_6784918] using wordTrace_append hprefix tailTrace_6784918
  have hstable : (prefixWord ++ tailWord_6784918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784918).length < 2 ^ (prefixWord ++ tailWord_6784918).sum := by decide
  have hdescent : baseEnd_6784918 < baseStart_6784918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784953 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 4]
def baseStart_6784953 : Nat := 118140960795 + 6784953 * 2 ^ 59
def prefixEnd_6784953 : Nat := 4983230072969 + 3 ^ 40 * 6784953 * 2
def baseEnd_6784953 : Nat := 3483942107165297573884075

theorem tailTrace_6784953 : CollatzResearch.WordTrace tailWord_6784953 prefixEnd_6784953 3483942107165297573884075 := by
  unfold tailWord_6784953
  simp only [CollatzResearch.WordTrace]
  refine ⟨247467566188281533562503513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164978377458854355708335675 247467566188281533562503513)
  ·
    refine ⟨185600674641211150171877635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247467566188281533562503513 185600674641211150171877635)
    ·
      refine ⟨278401011961816725257816453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185600674641211150171877635 278401011961816725257816453)
      ·
        refine ⟨52200189742840635985840585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278401011961816725257816453 52200189742840635985840585)
        ·
          refine ⟨39150142307130476989380439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52200189742840635985840585 39150142307130476989380439)
          ·
            refine ⟨58725213460695715484070659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39150142307130476989380439 58725213460695715484070659)
            ·
              refine ⟨88087820191043573226105989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58725213460695715484070659 88087820191043573226105989)
              ·
                refine ⟨16516466285820669979894873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88087820191043573226105989 16516466285820669979894873)
                ·
                  refine ⟨12387349714365502484921155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16516466285820669979894873 12387349714365502484921155)
                  ·
                    refine ⟨18581024571548253727381733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12387349714365502484921155 18581024571548253727381733)
                    ·
                      refine ⟨3483942107165297573884075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18581024571548253727381733 3483942107165297573884075)
                      ·
                        rfl

theorem cell23_6784953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_6784953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784953 prefixEnd_6784953 := by exact prefixLift 6784953
  have htrace : WordTrace (prefixWord ++ tailWord_6784953) baseStart_6784953 baseEnd_6784953 := by
    simpa [prefixWord, tailWord_6784953, baseEnd_6784953] using wordTrace_append hprefix tailTrace_6784953
  have hstable : (prefixWord ++ tailWord_6784953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784953).length < 2 ^ (prefixWord ++ tailWord_6784953).sum := by decide
  have hdescent : baseEnd_6784953 < baseStart_6784953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784980 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_6784980 : Nat := 118140960795 + 6784980 * 2 ^ 59
def prefixEnd_6784980 : Nat := 4983230072969 + 3 ^ 40 * 6784980 * 2
def baseEnd_6784980 : Nat := 1161318657047656322748817

theorem tailTrace_6784980 : CollatzResearch.WordTrace tailWord_6784980 prefixEnd_6784980 1161318657047656322748817 := by
  unfold tailWord_6784980
  simp only [CollatzResearch.WordTrace]
  refine ⟨123734275479591858586868197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164979033972789144782490929 123734275479591858586868197)
  ·
    refine ⟨23200176652423473485037787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123734275479591858586868197 23200176652423473485037787)
    ·
      refine ⟨34800264978635210227556681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23200176652423473485037787 34800264978635210227556681)
      ·
        refine ⟨26100198733976407670667511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34800264978635210227556681 26100198733976407670667511)
        ·
          refine ⟨39150298100964611506001267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26100198733976407670667511 39150298100964611506001267)
          ·
            refine ⟨58725447151446917259001901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39150298100964611506001267 58725447151446917259001901)
            ·
              refine ⟨22022042681792593972125713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58725447151446917259001901 22022042681792593972125713)
              ·
                refine ⟨16516532011344445479094285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22022042681792593972125713 16516532011344445479094285)
                ·
                  refine ⟨6193699504254167054660357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16516532011344445479094285 6193699504254167054660357)
                  ·
                    refine ⟨1161318657047656322748817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6193699504254167054660357 1161318657047656322748817)
                    ·
                      rfl

theorem cell23_6784980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_6784980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6784980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6784980 prefixEnd_6784980 := by exact prefixLift 6784980
  have htrace : WordTrace (prefixWord ++ tailWord_6784980) baseStart_6784980 baseEnd_6784980 := by
    simpa [prefixWord, tailWord_6784980, baseEnd_6784980] using wordTrace_append hprefix tailTrace_6784980
  have hstable : (prefixWord ++ tailWord_6784980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784980).length < 2 ^ (prefixWord ++ tailWord_6784980).sum := by decide
  have hdescent : baseEnd_6784980 < baseStart_6784980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785043 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 4]
def baseStart_6785043 : Nat := 118140960795 + 6785043 * 2 ^ 59
def prefixEnd_6785043 : Nat := 4983230072969 + 3 ^ 40 * 6785043 * 2
def baseEnd_6785043 : Nat := 3483988320424202221758661

theorem tailTrace_6785043 : CollatzResearch.WordTrace tailWord_6785043 prefixEnd_6785043 3483988320424202221758661 := by
  unfold tailWord_6785043
  simp only [CollatzResearch.WordTrace]
  refine ⟨247470848757955478933279783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164980565838636985955519855 247470848757955478933279783)
  ·
    refine ⟨371206273136933218399919675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247470848757955478933279783 371206273136933218399919675)
    ·
      refine ⟨556809409705399827599879513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371206273136933218399919675 556809409705399827599879513)
      ·
        refine ⟨417607057279049870699909635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556809409705399827599879513 417607057279049870699909635)
        ·
          refine ⟨626410585918574806049864453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417607057279049870699909635 626410585918574806049864453)
          ·
            refine ⟨117451984859732776134349585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 626410585918574806049864453 117451984859732776134349585)
            ·
              refine ⟨88088988644799582100762189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117451984859732776134349585 88088988644799582100762189)
              ·
                refine ⟨33033370741799843287785821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88088988644799582100762189 33033370741799843287785821)
                ·
                  refine ⟨12387514028174941232919683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33033370741799843287785821 12387514028174941232919683)
                  ·
                    refine ⟨18581271042262411849379525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12387514028174941232919683 18581271042262411849379525)
                    ·
                      refine ⟨3483988320424202221758661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18581271042262411849379525 3483988320424202221758661)
                      ·
                        rfl

theorem cell23_6785043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_6785043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785043 prefixEnd_6785043 := by exact prefixLift 6785043
  have htrace : WordTrace (prefixWord ++ tailWord_6785043) baseStart_6785043 baseEnd_6785043 := by
    simpa [prefixWord, tailWord_6785043, baseEnd_6785043] using wordTrace_append hprefix tailTrace_6785043
  have hstable : (prefixWord ++ tailWord_6785043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785043).length < 2 ^ (prefixWord ++ tailWord_6785043).sum := by decide
  have hdescent : baseEnd_6785043 < baseStart_6785043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785073 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_6785073 : Nat := 118140960795 + 6785073 * 2 ^ 59
def prefixEnd_6785073 : Nat := 4983230072969 + 3 ^ 40 * 6785073 * 2
def baseEnd_6785073 : Nat := 3484003724843837104383523

theorem tailTrace_6785073 : CollatzResearch.WordTrace tailWord_6785073 prefixEnd_6785073 3484003724843837104383523 := by
  unfold tailWord_6785073
  simp only [CollatzResearch.WordTrace]
  refine ⟨247471942947846794056871873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164981295298564529371247915 247471942947846794056871873)
  ·
    refine ⟨185603957210885095542653905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247471942947846794056871873 185603957210885095542653905)
    ·
      refine ⟨139202967908163821656990429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185603957210885095542653905 139202967908163821656990429)
      ·
        refine ⟨52201112965561433121371411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139202967908163821656990429 52201112965561433121371411)
        ·
          refine ⟨78301669448342149682057117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52201112965561433121371411 78301669448342149682057117)
          ·
            refine ⟨29363126043128306130771419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78301669448342149682057117 29363126043128306130771419)
            ·
              refine ⟨44044689064692459196157129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29363126043128306130771419 44044689064692459196157129)
              ·
                refine ⟨33033516798519344397117847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44044689064692459196157129 33033516798519344397117847)
                ·
                  refine ⟨49550275197779016595676771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33033516798519344397117847 49550275197779016595676771)
                  ·
                    refine ⟨74325412796668524893515157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49550275197779016595676771 74325412796668524893515157)
                    ·
                      refine ⟨3484003724843837104383523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74325412796668524893515157 3484003724843837104383523)
                      ·
                        rfl

theorem cell23_6785073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_6785073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785073 prefixEnd_6785073 := by exact prefixLift 6785073
  have htrace : WordTrace (prefixWord ++ tailWord_6785073) baseStart_6785073 baseEnd_6785073 := by
    simpa [prefixWord, tailWord_6785073, baseEnd_6785073] using wordTrace_append hprefix tailTrace_6785073
  have hstable : (prefixWord ++ tailWord_6785073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785073).length < 2 ^ (prefixWord ++ tailWord_6785073).sum := by decide
  have hdescent : baseEnd_6785073 < baseStart_6785073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785087 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 2, 4]
def baseStart_6785087 : Nat := 118140960795 + 6785087 * 2 ^ 59
def prefixEnd_6785087 : Nat := 4983230072969 + 3 ^ 40 * 6785087 * 2
def baseEnd_6785087 : Nat := 1161336971191000016536153

theorem tailTrace_6785087 : CollatzResearch.WordTrace tailWord_6785087 prefixEnd_6785087 1161336971191000016536153 := by
  unfold tailWord_6785087
  simp only [CollatzResearch.WordTrace]
  refine ⟨247472453569796074447881515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164981635713197382965254343 247472453569796074447881515)
  ·
    refine ⟨371208680354694111671822273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247472453569796074447881515 371208680354694111671822273)
    ·
      refine ⟨278406510266020583753866705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371208680354694111671822273 278406510266020583753866705)
      ·
        refine ⟨208804882699515437815400029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278406510266020583753866705 208804882699515437815400029)
        ·
          refine ⟨78301831012318289180775011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208804882699515437815400029 78301831012318289180775011)
          ·
            refine ⟨117452746518477433771162517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78301831012318289180775011 117452746518477433771162517)
            ·
              refine ⟨5505597493053629708023243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117452746518477433771162517 5505597493053629708023243)
              ·
                refine ⟨8258396239580444562034865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505597493053629708023243 8258396239580444562034865)
                ·
                  refine ⟨6193797179685333421526149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8258396239580444562034865 6193797179685333421526149)
                  ·
                    refine ⟨1161336971191000016536153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6193797179685333421526149 1161336971191000016536153)
                    ·
                      rfl

theorem cell23_6785087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 2, 4].length) (baseStart_6785087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785087 prefixEnd_6785087 := by exact prefixLift 6785087
  have htrace : WordTrace (prefixWord ++ tailWord_6785087) baseStart_6785087 baseEnd_6785087 := by
    simpa [prefixWord, tailWord_6785087, baseEnd_6785087] using wordTrace_append hprefix tailTrace_6785087
  have hstable : (prefixWord ++ tailWord_6785087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785087).length < 2 ^ (prefixWord ++ tailWord_6785087).sum := by decide
  have hdescent : baseEnd_6785087 < baseStart_6785087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785123 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 5]
def baseStart_6785123 : Nat := 118140960795 + 6785123 * 2 ^ 59
def prefixEnd_6785123 : Nat := 4983230072969 + 3 ^ 40 * 6785123 * 2
def baseEnd_6785123 : Nat := 3484029398876561908758293

theorem tailTrace_6785123 : CollatzResearch.WordTrace tailWord_6785123 prefixEnd_6785123 3484029398876561908758293 := by
  unfold tailWord_6785123
  simp only [CollatzResearch.WordTrace]
  refine ⟨247473766597665652596192023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164982511065110435064128015 247473766597665652596192023)
  ·
    refine ⟨371210649896498478894288035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247473766597665652596192023 371210649896498478894288035)
    ·
      refine ⟨556815974844747718341432053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371210649896498478894288035 556815974844747718341432053)
      ·
        refine ⟨52201497641695098594509255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 556815974844747718341432053 52201497641695098594509255)
        ·
          refine ⟨78302246462542647891763883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52201497641695098594509255 78302246462542647891763883)
          ·
            refine ⟨117453369693813971837645825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78302246462542647891763883 117453369693813971837645825)
            ·
              refine ⟨88090027270360478878234369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117453369693813971837645825 88090027270360478878234369)
              ·
                refine ⟨66067520452770359158675777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88090027270360478878234369 66067520452770359158675777)
                ·
                  refine ⟨49550640339577769369006833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66067520452770359158675777 49550640339577769369006833)
                  ·
                    refine ⟨37162980254683327026755125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49550640339577769369006833 37162980254683327026755125)
                    ·
                      refine ⟨3484029398876561908758293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37162980254683327026755125 3484029398876561908758293)
                      ·
                        rfl

theorem cell23_6785123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_6785123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785123 prefixEnd_6785123 := by exact prefixLift 6785123
  have htrace : WordTrace (prefixWord ++ tailWord_6785123) baseStart_6785123 baseEnd_6785123 := by
    simpa [prefixWord, tailWord_6785123, baseEnd_6785123] using wordTrace_append hprefix tailTrace_6785123
  have hstable : (prefixWord ++ tailWord_6785123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785123).length < 2 ^ (prefixWord ++ tailWord_6785123).sum := by decide
  have hdescent : baseEnd_6785123 < baseStart_6785123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785143 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 1, 8]
def baseStart_6785143 : Nat := 118140960795 + 6785143 * 2 ^ 59
def prefixEnd_6785143 : Nat := 4983230072969 + 3 ^ 40 * 6785143 * 2
def baseEnd_6785143 : Nat := 1161346556163217276836067

theorem tailTrace_6785143 : CollatzResearch.WordTrace tailWord_6785143 prefixEnd_6785143 1161346556163217276836067 := by
  unfold tailWord_6785143
  simp only [CollatzResearch.WordTrace]
  refine ⟨247474496057593196011920083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164982997371728797341280055 247474496057593196011920083)
  ·
    refine ⟨371211744086389794017880125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247474496057593196011920083 371211744086389794017880125)
    ·
      refine ⟨139204404032396172756705047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371211744086389794017880125 139204404032396172756705047)
      ·
        refine ⟨208806606048594259135057571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139204404032396172756705047 208806606048594259135057571)
        ·
          refine ⟨313209909072891388702586357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208806606048594259135057571 313209909072891388702586357)
          ·
            refine ⟨29363428975583567690867471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 313209909072891388702586357 29363428975583567690867471)
            ·
              refine ⟨44045143463375351536301207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29363428975583567690867471 44045143463375351536301207)
              ·
                refine ⟨66067715195063027304451811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44045143463375351536301207 66067715195063027304451811)
                ·
                  refine ⟨99101572792594540956677717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66067715195063027304451811 99101572792594540956677717)
                  ·
                    refine ⟨1161346556163217276836067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99101572792594540956677717 1161346556163217276836067)
                    ·
                      rfl

theorem cell23_6785143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_6785143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785143 prefixEnd_6785143 := by exact prefixLift 6785143
  have htrace : WordTrace (prefixWord ++ tailWord_6785143) baseStart_6785143 baseEnd_6785143 := by
    simpa [prefixWord, tailWord_6785143, baseEnd_6785143] using wordTrace_append hprefix tailTrace_6785143
  have hstable : (prefixWord ++ tailWord_6785143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785143).length < 2 ^ (prefixWord ++ tailWord_6785143).sum := by decide
  have hdescent : baseEnd_6785143 < baseStart_6785143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785170 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_6785170 : Nat := 118140960795 + 6785170 * 2 ^ 59
def prefixEnd_6785170 : Nat := 4983230072969 + 3 ^ 40 * 6785170 * 2
def baseEnd_6785170 : Nat := 3484053532467323224870577

theorem tailTrace_6785170 : CollatzResearch.WordTrace tailWord_6785170 prefixEnd_6785170 3484053532467323224870577 := by
  unfold tailWord_6785170
  simp only [CollatzResearch.WordTrace]
  refine ⟨61868870207123844905788241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164983653885663586415435309 61868870207123844905788241)
  ·
    refine ⟨46401652655342883679341181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61868870207123844905788241 46401652655342883679341181)
    ·
      refine ⟨17400619745753581379752943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46401652655342883679341181 17400619745753581379752943)
      ·
        refine ⟨26100929618630372069629415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17400619745753581379752943 26100929618630372069629415)
        ·
          refine ⟨39151394427945558104444123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26100929618630372069629415 39151394427945558104444123)
          ·
            refine ⟨58727091641918337156666185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39151394427945558104444123 58727091641918337156666185)
            ·
              refine ⟨44045318731438752867499639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58727091641918337156666185 44045318731438752867499639)
              ·
                refine ⟨66067978097158129301249459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44045318731438752867499639 66067978097158129301249459)
                ·
                  refine ⟨99101967145737193951874189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66067978097158129301249459 99101967145737193951874189)
                  ·
                    refine ⟨37163237679651447731952821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99101967145737193951874189 37163237679651447731952821)
                    ·
                      refine ⟨3484053532467323224870577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37163237679651447731952821 3484053532467323224870577)
                      ·
                        rfl

theorem cell23_6785170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_6785170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785170 prefixEnd_6785170 := by exact prefixLift 6785170
  have htrace : WordTrace (prefixWord ++ tailWord_6785170) baseStart_6785170 baseEnd_6785170 := by
    simpa [prefixWord, tailWord_6785170, baseEnd_6785170] using wordTrace_append hprefix tailTrace_6785170
  have hstable : (prefixWord ++ tailWord_6785170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785170).length < 2 ^ (prefixWord ++ tailWord_6785170).sum := by decide
  have hdescent : baseEnd_6785170 < baseStart_6785170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785173 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 9]
def baseStart_6785173 : Nat := 118140960795 + 6785173 * 2 ^ 59
def prefixEnd_6785173 : Nat := 4983230072969 + 3 ^ 40 * 6785173 * 2
def baseEnd_6785173 : Nat := 387117230323254079237007

theorem tailTrace_6785173 : CollatzResearch.WordTrace tailWord_6785173 prefixEnd_6785173 387117230323254079237007 := by
  unfold tailWord_6785173
  simp only [CollatzResearch.WordTrace]
  refine ⟨247475590247484511135512173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164983726831656340757008115 247475590247484511135512173)
  ·
    refine ⟨92803346342806691675817065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247475590247484511135512173 92803346342806691675817065)
    ·
      refine ⟨69602509757105018756862799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92803346342806691675817065 69602509757105018756862799)
      ·
        refine ⟨104403764635657528135294199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69602509757105018756862799 104403764635657528135294199)
        ·
          refine ⟨156605646953486292202941299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104403764635657528135294199 156605646953486292202941299)
          ·
            refine ⟨234908470430229438304411949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156605646953486292202941299 234908470430229438304411949)
            ·
              refine ⟨88090676411336039364154481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234908470430229438304411949 88090676411336039364154481)
              ·
                refine ⟨66068007308502029523115861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88090676411336039364154481 66068007308502029523115861)
                ·
                  refine ⟨387117230323254079237007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66068007308502029523115861 387117230323254079237007)
                  ·
                    rfl

theorem cell23_6785173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_6785173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785173 prefixEnd_6785173 := by exact prefixLift 6785173
  have htrace : WordTrace (prefixWord ++ tailWord_6785173) baseStart_6785173 baseEnd_6785173 := by
    simpa [prefixWord, tailWord_6785173, baseEnd_6785173] using wordTrace_append hprefix tailTrace_6785173
  have hstable : (prefixWord ++ tailWord_6785173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785173).length < 2 ^ (prefixWord ++ tailWord_6785173).sum := by decide
  have hdescent : baseEnd_6785173 < baseStart_6785173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785178 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3]
def baseStart_6785178 : Nat := 118140960795 + 6785178 * 2 ^ 59
def prefixEnd_6785178 : Nat := 4983230072969 + 3 ^ 40 * 6785178 * 2
def baseEnd_6785178 : Nat := 3484057640312559193570541

theorem tailTrace_6785178 : CollatzResearch.WordTrace tailWord_6785178 prefixEnd_6785178 3484057640312559193570541 := by
  unfold tailWord_6785178
  simp only [CollatzResearch.WordTrace]
  refine ⟨61868943153116599247361047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164983848408310931326296125 61868943153116599247361047)
  ·
    refine ⟨92803414729674898871041571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61868943153116599247361047 92803414729674898871041571)
    ·
      refine ⟨139205122094512348306562357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92803414729674898871041571 139205122094512348306562357)
      ·
        refine ⟨13050480196360532653740221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139205122094512348306562357 13050480196360532653740221)
        ·
          refine ⟨4893930073635199745152583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13050480196360532653740221 4893930073635199745152583)
          ·
            refine ⟨7340895110452799617728875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893930073635199745152583 7340895110452799617728875)
            ·
              refine ⟨11011342665679199426593313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7340895110452799617728875 11011342665679199426593313)
              ·
                refine ⟨8258506999259399569944985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11011342665679199426593313 8258506999259399569944985)
                ·
                  refine ⟨6193880249444549677458739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8258506999259399569944985 6193880249444549677458739)
                  ·
                    refine ⟨9290820374166824516188109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6193880249444549677458739 9290820374166824516188109)
                    ·
                      refine ⟨3484057640312559193570541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9290820374166824516188109 3484057640312559193570541)
                      ·
                        rfl

theorem cell23_6785178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_6785178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785178 prefixEnd_6785178 := by exact prefixLift 6785178
  have htrace : WordTrace (prefixWord ++ tailWord_6785178) baseStart_6785178 baseEnd_6785178 := by
    simpa [prefixWord, tailWord_6785178, baseEnd_6785178] using wordTrace_append hprefix tailTrace_6785178
  have hstable : (prefixWord ++ tailWord_6785178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785178).length < 2 ^ (prefixWord ++ tailWord_6785178).sum := by decide
  have hdescent : baseEnd_6785178 < baseStart_6785178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785180 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6785180 : Nat := 118140960795 + 6785180 * 2 ^ 59
def prefixEnd_6785180 : Nat := 4983230072969 + 3 ^ 40 * 6785180 * 2
def baseEnd_6785180 : Nat := 3484058667273868185745531

theorem tailTrace_6785180 : CollatzResearch.WordTrace tailWord_6785180 prefixEnd_6785180 3484058667273868185745531 := by
  unfold tailWord_6785180
  simp only [CollatzResearch.WordTrace]
  refine ⟨123737922779229575665508497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164983897038972767554011329 123737922779229575665508497)
  ·
    refine ⟨92803442084422181749131373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123737922779229575665508497 92803442084422181749131373)
    ·
      refine ⟨34801290781658318155924265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92803442084422181749131373 34801290781658318155924265)
      ·
        refine ⟨26100968086243738616943199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34801290781658318155924265 26100968086243738616943199)
        ·
          refine ⟨39151452129365607925414799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26100968086243738616943199 39151452129365607925414799)
          ·
            refine ⟨58727178194048411888122199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39151452129365607925414799 58727178194048411888122199)
            ·
              refine ⟨88090767291072617832183299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58727178194048411888122199 88090767291072617832183299)
              ·
                refine ⟨132136150936608926748274949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88090767291072617832183299 132136150936608926748274949)
                ·
                  refine ⟨24775528300614173765301553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132136150936608926748274949 24775528300614173765301553)
                  ·
                    refine ⟨18581646225460630323976165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24775528300614173765301553 18581646225460630323976165)
                    ·
                      refine ⟨3484058667273868185745531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18581646225460630323976165 3484058667273868185745531)
                      ·
                        rfl

theorem cell23_6785180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6785180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785180 prefixEnd_6785180 := by exact prefixLift 6785180
  have htrace : WordTrace (prefixWord ++ tailWord_6785180) baseStart_6785180 baseEnd_6785180 := by
    simpa [prefixWord, tailWord_6785180, baseEnd_6785180] using wordTrace_append hprefix tailTrace_6785180
  have hstable : (prefixWord ++ tailWord_6785180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785180).length < 2 ^ (prefixWord ++ tailWord_6785180).sum := by decide
  have hdescent : baseEnd_6785180 < baseStart_6785180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785184 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 4, 2, 2]
def baseStart_6785184 : Nat := 118140960795 + 6785184 * 2 ^ 59
def prefixEnd_6785184 : Nat := 4983230072969 + 3 ^ 40 * 6785184 * 2
def baseEnd_6785184 : Nat := 3484060721196486170095513

theorem tailTrace_6785184 : CollatzResearch.WordTrace tailWord_6785184 prefixEnd_6785184 3484060721196486170095513 := by
  unfold tailWord_6785184
  simp only [CollatzResearch.WordTrace]
  refine ⟨123737995725222330007081303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164983994300296440009441737 123737995725222330007081303)
  ·
    refine ⟨185606993587833495010621955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123737995725222330007081303 185606993587833495010621955)
    ·
      refine ⟨278410490381750242515932933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185606993587833495010621955 278410490381750242515932933)
      ·
        refine ⟨52201966946578170471737425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278410490381750242515932933 52201966946578170471737425)
        ·
          refine ⟨39151475209933627853803069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52201966946578170471737425 39151475209933627853803069)
          ·
            refine ⟨14681803203725110445176151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39151475209933627853803069 14681803203725110445176151)
            ·
              refine ⟨22022704805587665667764227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14681803203725110445176151 22022704805587665667764227)
              ·
                refine ⟨33034057208381498501646341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22022704805587665667764227 33034057208381498501646341)
                ·
                  refine ⟨6193885726571530969058689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33034057208381498501646341 6193885726571530969058689)
                  ·
                    refine ⟨4645414294928648226794017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6193885726571530969058689 4645414294928648226794017)
                    ·
                      refine ⟨3484060721196486170095513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645414294928648226794017 3484060721196486170095513)
                      ·
                        rfl

theorem cell23_6785184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_6785184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785184 prefixEnd_6785184 := by exact prefixLift 6785184
  have htrace : WordTrace (prefixWord ++ tailWord_6785184) baseStart_6785184 baseEnd_6785184 := by
    simpa [prefixWord, tailWord_6785184, baseEnd_6785184] using wordTrace_append hprefix tailTrace_6785184
  have hstable : (prefixWord ++ tailWord_6785184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785184).length < 2 ^ (prefixWord ++ tailWord_6785184).sum := by decide
  have hdescent : baseEnd_6785184 < baseStart_6785184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785197 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_6785197 : Nat := 118140960795 + 6785197 * 2 ^ 59
def prefixEnd_6785197 : Nat := 4983230072969 + 3 ^ 40 * 6785197 * 2
def baseEnd_6785197 : Nat := 3484067396444994619232953

theorem tailTrace_6785197 : CollatzResearch.WordTrace tailWord_6785197 prefixEnd_6785197 3484067396444994619232953 := by
  unfold tailWord_6785197
  simp only [CollatzResearch.WordTrace]
  refine ⟨247476465599397563234385845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164984310399598375489590563 247476465599397563234385845)
  ·
    refine ⟨23200918649943521553223673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247476465599397563234385845 23200918649943521553223673)
    ·
      refine ⟨17400688987457641164917755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23200918649943521553223673 17400688987457641164917755)
      ·
        refine ⟨26101033481186461747376633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17400688987457641164917755 26101033481186461747376633)
        ·
          refine ⟨19575775110889846310532475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26101033481186461747376633 19575775110889846310532475)
          ·
            refine ⟨29363662666334769465798713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19575775110889846310532475 29363662666334769465798713)
            ·
              refine ⟨22022746999751077099349035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29363662666334769465798713 22022746999751077099349035)
              ·
                refine ⟨33034120499626615649023553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22022746999751077099349035 33034120499626615649023553)
                ·
                  refine ⟨24775590374719961736767665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33034120499626615649023553 24775590374719961736767665)
                  ·
                    refine ⟨18581692781039971302575749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24775590374719961736767665 18581692781039971302575749)
                    ·
                      refine ⟨3484067396444994619232953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18581692781039971302575749 3484067396444994619232953)
                      ·
                        rfl

theorem cell23_6785197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_6785197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785197 prefixEnd_6785197 := by exact prefixLift 6785197
  have htrace : WordTrace (prefixWord ++ tailWord_6785197) baseStart_6785197 baseEnd_6785197 := by
    simpa [prefixWord, tailWord_6785197, baseEnd_6785197] using wordTrace_append hprefix tailTrace_6785197
  have hstable : (prefixWord ++ tailWord_6785197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785197).length < 2 ^ (prefixWord ++ tailWord_6785197).sum := by decide
  have hdescent : baseEnd_6785197 < baseStart_6785197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785201 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 1, 4, 2]
def baseStart_6785201 : Nat := 118140960795 + 6785201 * 2 ^ 59
def prefixEnd_6785201 : Nat := 4983230072969 + 3 ^ 40 * 6785201 * 2
def baseEnd_6785201 : Nat := 3484069450367612603582935

theorem tailTrace_6785201 : CollatzResearch.WordTrace tailWord_6785201 prefixEnd_6785201 3484069450367612603582935 := by
  unfold tailWord_6785201
  simp only [CollatzResearch.WordTrace]
  refine ⟨247476611491383071917531457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164984407660922047945020971 247476611491383071917531457)
  ·
    refine ⟨185607458618537303938148593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247476611491383071917531457 185607458618537303938148593)
    ·
      refine ⟨139205593963902977953611445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185607458618537303938148593 139205593963902977953611445)
      ·
        refine ⟨13050524434115904183151073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139205593963902977953611445 13050524434115904183151073)
        ·
          refine ⟨9787893325586928137363305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13050524434115904183151073 9787893325586928137363305)
          ·
            refine ⟨7340919994190196103022479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9787893325586928137363305 7340919994190196103022479)
            ·
              refine ⟨11011379991285294154533719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7340919994190196103022479 11011379991285294154533719)
              ·
                refine ⟨16517069986927941231800579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11011379991285294154533719 16517069986927941231800579)
                ·
                  refine ⟨24775604980391911847700869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16517069986927941231800579 24775604980391911847700869)
                  ·
                    refine ⟨4645425933823483471443913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24775604980391911847700869 4645425933823483471443913)
                    ·
                      refine ⟨3484069450367612603582935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645425933823483471443913 3484069450367612603582935)
                      ·
                        rfl

theorem cell23_6785201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_6785201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785201 prefixEnd_6785201 := by exact prefixLift 6785201
  have htrace : WordTrace (prefixWord ++ tailWord_6785201) baseStart_6785201 baseEnd_6785201 := by
    simpa [prefixWord, tailWord_6785201, baseEnd_6785201] using wordTrace_append hprefix tailTrace_6785201
  have hstable : (prefixWord ++ tailWord_6785201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785201).length < 2 ^ (prefixWord ++ tailWord_6785201).sum := by decide
  have hdescent : baseEnd_6785201 < baseStart_6785201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785218 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_6785218 : Nat := 118140960795 + 6785218 * 2 ^ 59
def prefixEnd_6785218 : Nat := 4983230072969 + 3 ^ 40 * 6785218 * 2
def baseEnd_6785218 : Nat := 3484078179538739037070357

theorem tailTrace_6785218 : CollatzResearch.WordTrace tailWord_6785218 prefixEnd_6785218 3484078179538739037070357 := by
  unfold tailWord_6785218
  simp only [CollatzResearch.WordTrace]
  refine ⟨61869307883080370955225077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164984821021547655880600205 61869307883080370955225077)
  ·
    refine ⟨5800247614038784777052351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61869307883080370955225077 5800247614038784777052351)
    ·
      refine ⟨8700371421058177165578527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5800247614038784777052351 8700371421058177165578527)
      ·
        refine ⟨13050557131587265748367791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8700371421058177165578527 13050557131587265748367791)
        ·
          refine ⟨19575835697380898622551687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13050557131587265748367791 19575835697380898622551687)
          ·
            refine ⟨29363753546071347933827531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19575835697380898622551687 29363753546071347933827531)
            ·
              refine ⟨44045630319107021900741297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29363753546071347933827531 44045630319107021900741297)
              ·
                refine ⟨33034222739330266425555973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44045630319107021900741297 33034222739330266425555973)
                ·
                  refine ⟨6193916763624424954791745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33034222739330266425555973 6193916763624424954791745)
                  ·
                    refine ⟨4645437572718318716093809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6193916763624424954791745 4645437572718318716093809)
                    ·
                      refine ⟨3484078179538739037070357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645437572718318716093809 3484078179538739037070357)
                      ·
                        rfl

theorem cell23_6785218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_6785218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785218 prefixEnd_6785218 := by exact prefixLift 6785218
  have htrace : WordTrace (prefixWord ++ tailWord_6785218) baseStart_6785218 baseEnd_6785218 := by
    simpa [prefixWord, tailWord_6785218, baseEnd_6785218] using wordTrace_append hprefix tailTrace_6785218
  have hstable : (prefixWord ++ tailWord_6785218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785218).length < 2 ^ (prefixWord ++ tailWord_6785218).sum := by decide
  have hdescent : baseEnd_6785218 < baseStart_6785218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785297 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 6]
def baseStart_6785297 : Nat := 118140960795 + 6785297 * 2 ^ 59
def prefixEnd_6785297 : Nat := 4983230072969 + 3 ^ 40 * 6785297 * 2
def baseEnd_6785297 : Nat := 387124304945604914220277

theorem tailTrace_6785297 : CollatzResearch.WordTrace tailWord_6785297 prefixEnd_6785297 387124304945604914220277 := by
  unfold tailWord_6785297
  simp only [CollatzResearch.WordTrace]
  refine ⟨247480112899035280313026145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164986741932690186875350763 247480112899035280313026145)
  ·
    refine ⟨185610084674276460234769609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247480112899035280313026145 185610084674276460234769609)
    ·
      refine ⟨139207563505707345176077207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185610084674276460234769609 139207563505707345176077207)
      ·
        refine ⟨208811345258561017764115811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139207563505707345176077207 208811345258561017764115811)
        ·
          refine ⟨313217017887841526646173717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208811345258561017764115811 313217017887841526646173717)
          ·
            refine ⟨14682047713492571561539393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 313217017887841526646173717 14682047713492571561539393)
            ·
              refine ⟨11011535785119428671154545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14682047713492571561539393 11011535785119428671154545)
              ·
                refine ⟨8258651838839571503365909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11011535785119428671154545 8258651838839571503365909)
                ·
                  refine ⟨387124304945604914220277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8258651838839571503365909 387124304945604914220277)
                  ·
                    rfl

theorem cell23_6785297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 6].length) (baseStart_6785297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785297 prefixEnd_6785297 := by exact prefixLift 6785297
  have htrace : WordTrace (prefixWord ++ tailWord_6785297) baseStart_6785297 baseEnd_6785297 := by
    simpa [prefixWord, tailWord_6785297, baseEnd_6785297] using wordTrace_append hprefix tailTrace_6785297
  have hstable : (prefixWord ++ tailWord_6785297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785297).length < 2 ^ (prefixWord ++ tailWord_6785297).sum := by decide
  have hdescent : baseEnd_6785297 < baseStart_6785297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785301 : List Nat := [1, 3, 2, 1, 2, 1, 6, 2, 1, 4]
def baseStart_6785301 : Nat := 118140960795 + 6785301 * 2 ^ 59
def prefixEnd_6785301 : Nat := 4983230072969 + 3 ^ 40 * 6785301 * 2
def baseEnd_6785301 : Nat := 1161373599477687404110825

theorem tailTrace_6785301 : CollatzResearch.WordTrace tailWord_6785301 prefixEnd_6785301 1161373599477687404110825 := by
  unfold tailWord_6785301
  simp only [CollatzResearch.WordTrace]
  refine ⟨247480258791020788996171757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164986839194013859330781171 247480258791020788996171757)
  ·
    refine ⟨92805097046632795873564409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247480258791020788996171757 92805097046632795873564409)
    ·
      refine ⟨69603822784974596905173307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92805097046632795873564409 69603822784974596905173307)
      ·
        refine ⟨104405734177461895357759961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69603822784974596905173307 104405734177461895357759961)
        ·
          refine ⟨78304300633096421518319971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104405734177461895357759961 78304300633096421518319971)
          ·
            refine ⟨117456450949644632277479957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78304300633096421518319971 117456450949644632277479957)
            ·
              refine ⟨5505771138264592138006873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117456450949644632277479957 5505771138264592138006873)
              ·
                refine ⟨4129328353698444103505155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5505771138264592138006873 4129328353698444103505155)
                ·
                  refine ⟨6193992530547666155257733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4129328353698444103505155 6193992530547666155257733)
                  ·
                    refine ⟨1161373599477687404110825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6193992530547666155257733 1161373599477687404110825)
                    ·
                      rfl

theorem cell23_6785301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_6785301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785301 prefixEnd_6785301 := by exact prefixLift 6785301
  have htrace : WordTrace (prefixWord ++ tailWord_6785301) baseStart_6785301 baseEnd_6785301 := by
    simpa [prefixWord, tailWord_6785301, baseEnd_6785301] using wordTrace_append hprefix tailTrace_6785301
  have hstable : (prefixWord ++ tailWord_6785301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785301).length < 2 ^ (prefixWord ++ tailWord_6785301).sum := by decide
  have hdescent : baseEnd_6785301 < baseStart_6785301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785348 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 6]
def baseStart_6785348 : Nat := 118140960795 + 6785348 * 2 ^ 59
def prefixEnd_6785348 : Nat := 4983230072969 + 3 ^ 40 * 6785348 * 2
def baseEnd_6785348 : Nat := 387127214669313725382751

theorem tailTrace_6785348 : CollatzResearch.WordTrace tailWord_6785348 prefixEnd_6785348 387127214669313725382751 := by
  unfold tailWord_6785348
  simp only [CollatzResearch.WordTrace]
  refine ⟨123740986510925258011566349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164987982014567010682088465 123740986510925258011566349)
  ·
    refine ⟨46402869941596971754337381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123740986510925258011566349 46402869941596971754337381)
    ·
      refine ⟨8700538114049432203938259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46402869941596971754337381 8700538114049432203938259)
      ·
        refine ⟨13050807171074148305907389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8700538114049432203938259 13050807171074148305907389)
        ·
          refine ⟨4894052689152805614715271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13050807171074148305907389 4894052689152805614715271)
          ·
            refine ⟨7341079033729208422072907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4894052689152805614715271 7341079033729208422072907)
            ·
              refine ⟨11011618550593812633109361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7341079033729208422072907 11011618550593812633109361)
              ·
                refine ⟨8258713912945359474832021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11011618550593812633109361 8258713912945359474832021)
                ·
                  refine ⟨387127214669313725382751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8258713912945359474832021 387127214669313725382751)
                  ·
                    rfl

theorem cell23_6785348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_6785348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785348 prefixEnd_6785348 := by exact prefixLift 6785348
  have htrace : WordTrace (prefixWord ++ tailWord_6785348) baseStart_6785348 baseEnd_6785348 := by
    simpa [prefixWord, tailWord_6785348, baseEnd_6785348] using wordTrace_append hprefix tailTrace_6785348
  have hstable : (prefixWord ++ tailWord_6785348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785348).length < 2 ^ (prefixWord ++ tailWord_6785348).sum := by decide
  have hdescent : baseEnd_6785348 < baseStart_6785348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785367 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_6785367 : Nat := 118140960795 + 6785367 * 2 ^ 59
def prefixEnd_6785367 : Nat := 4983230072969 + 3 ^ 40 * 6785367 * 2
def baseEnd_6785367 : Nat := 3484154688156258954107171

theorem tailTrace_6785367 : CollatzResearch.WordTrace tailWord_6785367 prefixEnd_6785367 3484154688156258954107171 := by
  unfold tailWord_6785367
  simp only [CollatzResearch.WordTrace]
  refine ⟨247482666008781682268074355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164988444005854454845382903 247482666008781682268074355)
  ·
    refine ⟨371223999013172523402111533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247482666008781682268074355 371223999013172523402111533)
    ·
      refine ⟨139208999629939696275791825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371223999013172523402111533 139208999629939696275791825)
      ·
        refine ⟨104406749722454772206843869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139208999629939696275791825 104406749722454772206843869)
        ·
          refine ⟨39152531145920539577566451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104406749722454772206843869 39152531145920539577566451)
          ·
            refine ⟨58728796718880809366349677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39152531145920539577566451 58728796718880809366349677)
            ·
              refine ⟨22023298769580303512381129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58728796718880809366349677 22023298769580303512381129)
              ·
                refine ⟨16517474077185227634285847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22023298769580303512381129 16517474077185227634285847)
                ·
                  refine ⟨24776211115777841451428771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16517474077185227634285847 24776211115777841451428771)
                  ·
                    refine ⟨37164316673666762177143157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24776211115777841451428771 37164316673666762177143157)
                    ·
                      refine ⟨3484154688156258954107171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37164316673666762177143157 3484154688156258954107171)
                      ·
                        rfl

theorem cell23_6785367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_6785367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785367 prefixEnd_6785367 := by exact prefixLift 6785367
  have htrace : WordTrace (prefixWord ++ tailWord_6785367) baseStart_6785367 baseEnd_6785367 := by
    simpa [prefixWord, tailWord_6785367, baseEnd_6785367] using wordTrace_append hprefix tailTrace_6785367
  have hstable : (prefixWord ++ tailWord_6785367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785367).length < 2 ^ (prefixWord ++ tailWord_6785367).sum := by decide
  have hdescent : baseEnd_6785367 < baseStart_6785367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785370 : List Nat := [3, 1, 1, 2, 1, 2, 1, 12]
def baseStart_6785370 : Nat := 118140960795 + 6785370 * 2 ^ 59
def prefixEnd_6785370 : Nat := 4983230072969 + 3 ^ 40 * 6785370 * 2
def baseEnd_6785370 : Nat := 129042823281415646013691

theorem tailTrace_6785370 : CollatzResearch.WordTrace tailWord_6785370 prefixEnd_6785370 129042823281415646013691 := by
  unfold tailWord_6785370
  simp only [CollatzResearch.WordTrace]
  refine ⟨61870693856942703445108391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164988516951847209186955709 61870693856942703445108391)
  ·
    refine ⟨92806040785414055167662587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61870693856942703445108391 92806040785414055167662587)
    ·
      refine ⟨139209061178121082751493881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92806040785414055167662587 139209061178121082751493881)
      ·
        refine ⟨104406795883590812063620411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139209061178121082751493881 104406795883590812063620411)
        ·
          refine ⟨156610193825386218095430617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104406795883590812063620411 156610193825386218095430617)
          ·
            refine ⟨117457645369039663571572963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156610193825386218095430617 117457645369039663571572963)
            ·
              refine ⟨176186468053559495357359445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117457645369039663571572963 176186468053559495357359445)
              ·
                refine ⟨129042823281415646013691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 176186468053559495357359445 129042823281415646013691)
                ·
                  rfl

theorem cell23_6785370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 12].length) (baseStart_6785370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785370 prefixEnd_6785370 := by exact prefixLift 6785370
  have htrace : WordTrace (prefixWord ++ tailWord_6785370) baseStart_6785370 baseEnd_6785370 := by
    simpa [prefixWord, tailWord_6785370, baseEnd_6785370] using wordTrace_append hprefix tailTrace_6785370
  have hstable : (prefixWord ++ tailWord_6785370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785370).length < 2 ^ (prefixWord ++ tailWord_6785370).sum := by decide
  have hdescent : baseEnd_6785370 < baseStart_6785370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785381 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 3, 2, 2]
def baseStart_6785381 : Nat := 118140960795 + 6785381 * 2 ^ 59
def prefixEnd_6785381 : Nat := 4983230072969 + 3 ^ 40 * 6785381 * 2
def baseEnd_6785381 : Nat := 3484161876885421899332107

theorem tailTrace_6785381 : CollatzResearch.WordTrace tailWord_6785381 prefixEnd_6785381 3484161876885421899332107 := by
  unfold tailWord_6785381
  simp only [CollatzResearch.WordTrace]
  refine ⟨247483176630730962659083997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164988784420487308439389331 247483176630730962659083997)
  ·
    refine ⟨92806191236524110997156499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247483176630730962659083997 92806191236524110997156499)
    ·
      refine ⟨139209286854786166495734749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92806191236524110997156499 139209286854786166495734749)
      ·
        refine ⟨52203482570544812435900531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139209286854786166495734749 52203482570544812435900531)
        ·
          refine ⟨78305223855817218653850797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52203482570544812435900531 78305223855817218653850797)
          ·
            refine ⟨29364458945931456995194049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78305223855817218653850797 29364458945931456995194049)
            ·
              refine ⟨22023344209448592746395537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29364458945931456995194049 22023344209448592746395537)
              ·
                refine ⟨16517508157086444559796653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22023344209448592746395537 16517508157086444559796653)
                ·
                  refine ⟨6194065558907416709923745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16517508157086444559796653 6194065558907416709923745)
                  ·
                    refine ⟨4645549169180562532442809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6194065558907416709923745 4645549169180562532442809)
                    ·
                      refine ⟨3484161876885421899332107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645549169180562532442809 3484161876885421899332107)
                      ·
                        rfl

theorem cell23_6785381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_6785381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785381 prefixEnd_6785381 := by exact prefixLift 6785381
  have htrace : WordTrace (prefixWord ++ tailWord_6785381) baseStart_6785381 baseEnd_6785381 := by
    simpa [prefixWord, tailWord_6785381, baseEnd_6785381] using wordTrace_append hprefix tailTrace_6785381
  have hstable : (prefixWord ++ tailWord_6785381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785381).length < 2 ^ (prefixWord ++ tailWord_6785381).sum := by decide
  have hdescent : baseEnd_6785381 < baseStart_6785381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785415 : List Nat := [1, 1, 4, 2, 2, 1, 5, 2, 1, 2, 2]
def baseStart_6785415 : Nat := 118140960795 + 6785415 * 2 ^ 59
def prefixEnd_6785415 : Nat := 4983230072969 + 3 ^ 40 * 6785415 * 2
def baseEnd_6785415 : Nat := 3484179335227674766306951

theorem tailTrace_6785415 : CollatzResearch.WordTrace tailWord_6785415 prefixEnd_6785415 3484179335227674766306951 := by
  unfold tailWord_6785415
  simp only [CollatzResearch.WordTrace]
  refine ⟨247484416712607786465821699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164989611141738524310547799 247484416712607786465821699)
  ·
    refine ⟨371226625068911679698732549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247484416712607786465821699 371226625068911679698732549)
    ·
      refine ⟨69604992200420939943512353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371226625068911679698732549 69604992200420939943512353)
      ·
        refine ⟨52203744150315704957634265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69604992200420939943512353 52203744150315704957634265)
        ·
          refine ⟨39152808112736778718225699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52203744150315704957634265 39152808112736778718225699)
          ·
            refine ⟨58729212169105168077338549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39152808112736778718225699 58729212169105168077338549)
            ·
              refine ⟨5505863640853609507250489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58729212169105168077338549 5505863640853609507250489)
              ·
                refine ⟨4129397730640207130437867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5505863640853609507250489 4129397730640207130437867)
                ·
                  refine ⟨6194096595960310695656801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4129397730640207130437867 6194096595960310695656801)
                  ·
                    refine ⟨4645572446970233021742601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6194096595960310695656801 4645572446970233021742601)
                    ·
                      refine ⟨3484179335227674766306951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645572446970233021742601 3484179335227674766306951)
                      ·
                        rfl

theorem cell23_6785415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_6785415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785415 prefixEnd_6785415 := by exact prefixLift 6785415
  have htrace : WordTrace (prefixWord ++ tailWord_6785415) baseStart_6785415 baseEnd_6785415 := by
    simpa [prefixWord, tailWord_6785415, baseEnd_6785415] using wordTrace_append hprefix tailTrace_6785415
  have hstable : (prefixWord ++ tailWord_6785415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785415).length < 2 ^ (prefixWord ++ tailWord_6785415).sum := by decide
  have hdescent : baseEnd_6785415 < baseStart_6785415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785458 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2]
def baseStart_6785458 : Nat := 118140960795 + 6785458 * 2 ^ 59
def prefixEnd_6785458 : Nat := 4983230072969 + 3 ^ 40 * 6785458 * 2
def baseEnd_6785458 : Nat := 3484201414895818098069253

theorem tailTrace_6785458 : CollatzResearch.WordTrace tailWord_6785458 prefixEnd_6785458 3484201414895818098069253 := by
  unfold tailWord_6785458
  simp only [CollatzResearch.WordTrace]
  refine ⟨61871496262863001202409257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164990656700968003206424685 61871496262863001202409257)
  ·
    refine ⟨46403622197147250901806943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61871496262863001202409257 46403622197147250901806943)
    ·
      refine ⟨69605433295720876352710415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46403622197147250901806943 69605433295720876352710415)
      ·
        refine ⟨104408149943581314529065623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69605433295720876352710415 104408149943581314529065623)
        ·
          refine ⟨156612224915371971793598435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104408149943581314529065623 156612224915371971793598435)
          ·
            refine ⟨234918337373057957690397653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156612224915371971793598435 234918337373057957690397653)
            ·
              refine ⟨5505898532181045883368695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 234918337373057957690397653 5505898532181045883368695)
              ·
                refine ⟨8258847798271568825053043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505898532181045883368695 8258847798271568825053043)
                ·
                  refine ⟨12388271697407353237579565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8258847798271568825053043 12388271697407353237579565)
                  ·
                    refine ⟨4645601886527757464092337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12388271697407353237579565 4645601886527757464092337)
                    ·
                      refine ⟨3484201414895818098069253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645601886527757464092337 3484201414895818098069253)
                      ·
                        rfl

theorem cell23_6785458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_6785458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785458 prefixEnd_6785458 := by exact prefixLift 6785458
  have htrace : WordTrace (prefixWord ++ tailWord_6785458) baseStart_6785458 baseEnd_6785458 := by
    simpa [prefixWord, tailWord_6785458, baseEnd_6785458] using wordTrace_append hprefix tailTrace_6785458
  have hstable : (prefixWord ++ tailWord_6785458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785458).length < 2 ^ (prefixWord ++ tailWord_6785458).sum := by decide
  have hdescent : baseEnd_6785458 < baseStart_6785458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785511 : List Nat := [1, 1, 5, 2, 1, 1, 4, 3, 5]
def baseStart_6785511 : Nat := 118140960795 + 6785511 * 2 ^ 59
def prefixEnd_6785511 : Nat := 4983230072969 + 3 ^ 40 * 6785511 * 2
def baseEnd_6785511 : Nat := 387136514374500710078501

theorem tailTrace_6785511 : CollatzResearch.WordTrace tailWord_6785511 prefixEnd_6785511 387136514374500710078501 := by
  unfold tailWord_6785511
  simp only [CollatzResearch.WordTrace]
  refine ⟨247487918120259994861316387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164991945413506663240877591 247487918120259994861316387)
  ·
    refine ⟨371231877180389992291974581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247487918120259994861316387 371231877180389992291974581)
    ·
      refine ⟨34802988485661561777372617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 371231877180389992291974581 34802988485661561777372617)
      ·
        refine ⟨26102241364246171333029463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34802988485661561777372617 26102241364246171333029463)
        ·
          refine ⟨39153362046369256999544195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26102241364246171333029463 39153362046369256999544195)
          ·
            refine ⟨58730043069553885499316293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39153362046369256999544195 58730043069553885499316293)
            ·
              refine ⟨11011883075541353531121805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58730043069553885499316293 11011883075541353531121805)
              ·
                refine ⟨4129456153328007574170677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11011883075541353531121805 4129456153328007574170677)
                ·
                  refine ⟨387136514374500710078501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4129456153328007574170677 387136514374500710078501)
                  ·
                    rfl

theorem cell23_6785511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 5].length) (baseStart_6785511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785511 prefixEnd_6785511 := by exact prefixLift 6785511
  have htrace : WordTrace (prefixWord ++ tailWord_6785511) baseStart_6785511 baseEnd_6785511 := by
    simpa [prefixWord, tailWord_6785511, baseEnd_6785511] using wordTrace_append hprefix tailTrace_6785511
  have hstable : (prefixWord ++ tailWord_6785511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785511).length < 2 ^ (prefixWord ++ tailWord_6785511).sum := by decide
  have hdescent : baseEnd_6785511 < baseStart_6785511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785522 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 2, 2, 2]
def baseStart_6785522 : Nat := 118140960795 + 6785522 * 2 ^ 59
def prefixEnd_6785522 : Nat := 4983230072969 + 3 ^ 40 * 6785522 * 2
def baseEnd_6785522 : Nat := 3484234277657705847668959

theorem tailTrace_6785522 : CollatzResearch.WordTrace tailWord_6785522 prefixEnd_6785522 3484234277657705847668959 := by
  unfold tailWord_6785522
  simp only [CollatzResearch.WordTrace]
  refine ⟨61872079830805035934991705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164992212882146762493311213 61872079830805035934991705)
  ·
    refine ⟨46404059873103776951243779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61872079830805035934991705 46404059873103776951243779)
    ·
      refine ⟨69606089809655665426865669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46404059873103776951243779 69606089809655665426865669)
      ·
        refine ⟨13051141839310437267537313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69606089809655665426865669 13051141839310437267537313)
        ·
          refine ⟨9788356379482827950652985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13051141839310437267537313 9788356379482827950652985)
          ·
            refine ⟨7341267284612120962989739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9788356379482827950652985 7341267284612120962989739)
            ·
              refine ⟨11011900926918181444484609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7341267284612120962989739 11011900926918181444484609)
              ·
                refine ⟨8258925695188636083363457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11011900926918181444484609 8258925695188636083363457)
                ·
                  refine ⟨6194194271391477062522593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8258925695188636083363457 6194194271391477062522593)
                  ·
                    refine ⟨4645645703543607796891945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6194194271391477062522593 4645645703543607796891945)
                    ·
                      refine ⟨3484234277657705847668959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645645703543607796891945 3484234277657705847668959)
                      ·
                        rfl

theorem cell23_6785522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_6785522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785522 prefixEnd_6785522 := by exact prefixLift 6785522
  have htrace : WordTrace (prefixWord ++ tailWord_6785522) baseStart_6785522 baseEnd_6785522 := by
    simpa [prefixWord, tailWord_6785522, baseEnd_6785522] using wordTrace_append hprefix tailTrace_6785522
  have hstable : (prefixWord ++ tailWord_6785522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785522).length < 2 ^ (prefixWord ++ tailWord_6785522).sum := by decide
  have hdescent : baseEnd_6785522 < baseStart_6785522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785601 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 6]
def baseStart_6785601 : Nat := 118140960795 + 6785601 * 2 ^ 59
def prefixEnd_6785601 : Nat := 4983230072969 + 3 ^ 40 * 6785601 * 2
def baseEnd_6785601 : Nat := 387141649181045670953455

theorem tailTrace_6785601 : CollatzResearch.WordTrace tailWord_6785601 prefixEnd_6785601 387141649181045670953455 := by
  unfold tailWord_6785601
  simp only [CollatzResearch.WordTrace]
  refine ⟨247491200689933940232092657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164994133793289293488061771 247491200689933940232092657)
  ·
    refine ⟨185618400517450455174069493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247491200689933940232092657 185618400517450455174069493)
    ·
      refine ⟨17401725048510980172569015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185618400517450455174069493 17401725048510980172569015)
      ·
        refine ⟨26102587572766470258853523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17401725048510980172569015 26102587572766470258853523)
        ·
          refine ⟨39153881359149705388280285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26102587572766470258853523 39153881359149705388280285)
          ·
            refine ⟨14682705509681139520605107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39153881359149705388280285 14682705509681139520605107)
            ·
              refine ⟨22024058264521709280907661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14682705509681139520605107 22024058264521709280907661)
              ·
                refine ⟨8259021849195640980340373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22024058264521709280907661 8259021849195640980340373)
                ·
                  refine ⟨387141649181045670953455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8259021849195640980340373 387141649181045670953455)
                  ·
                    rfl

theorem cell23_6785601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 6].length) (baseStart_6785601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785601 prefixEnd_6785601 := by exact prefixLift 6785601
  have htrace : WordTrace (prefixWord ++ tailWord_6785601) baseStart_6785601 baseEnd_6785601 := by
    simpa [prefixWord, tailWord_6785601, baseEnd_6785601] using wordTrace_append hprefix tailTrace_6785601
  have hstable : (prefixWord ++ tailWord_6785601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785601).length < 2 ^ (prefixWord ++ tailWord_6785601).sum := by decide
  have hdescent : baseEnd_6785601 < baseStart_6785601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785611 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 3, 1, 3]
def baseStart_6785611 : Nat := 118140960795 + 6785611 * 2 ^ 59
def prefixEnd_6785611 : Nat := 4983230072969 + 3 ^ 40 * 6785611 * 2
def baseEnd_6785611 : Nat := 3484279977435955999456049

theorem tailTrace_6785611 : CollatzResearch.WordTrace tailWord_6785611 prefixEnd_6785611 3484279977435955999456049 := by
  unfold tailWord_6785611
  simp only [CollatzResearch.WordTrace]
  refine ⟨247491565419897711939956687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164994376946598474626637791 247491565419897711939956687)
  ·
    refine ⟨371237348129846567909935031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247491565419897711939956687 371237348129846567909935031)
    ·
      refine ⟨556856022194769851864902547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371237348129846567909935031 556856022194769851864902547)
      ·
        refine ⟨835284033292154777797353821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556856022194769851864902547 835284033292154777797353821)
        ·
          refine ⟨313231512484558041674007683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 835284033292154777797353821 313231512484558041674007683)
          ·
            refine ⟨469847268726837062511011525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313231512484558041674007683 469847268726837062511011525)
            ·
              refine ⟨88096362886281949220814661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 469847268726837062511011525 88096362886281949220814661)
              ·
                refine ⟨16518068041177865478902749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88096362886281949220814661 16518068041177865478902749)
                ·
                  refine ⟨6194275515441699554588531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16518068041177865478902749 6194275515441699554588531)
                  ·
                    refine ⟨9291413273162549331882797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6194275515441699554588531 9291413273162549331882797)
                    ·
                      refine ⟨3484279977435955999456049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9291413273162549331882797 3484279977435955999456049)
                      ·
                        rfl

theorem cell23_6785611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 1, 3].length) (baseStart_6785611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785611 prefixEnd_6785611 := by exact prefixLift 6785611
  have htrace : WordTrace (prefixWord ++ tailWord_6785611) baseStart_6785611 baseEnd_6785611 := by
    simpa [prefixWord, tailWord_6785611, baseEnd_6785611] using wordTrace_append hprefix tailTrace_6785611
  have hstable : (prefixWord ++ tailWord_6785611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785611).length < 2 ^ (prefixWord ++ tailWord_6785611).sum := by decide
  have hdescent : baseEnd_6785611 < baseStart_6785611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785621 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 1, 5, 2]
def baseStart_6785621 : Nat := 118140960795 + 6785621 * 2 ^ 59
def prefixEnd_6785621 : Nat := 4983230072969 + 3 ^ 40 * 6785621 * 2
def baseEnd_6785621 : Nat := 3484285112242500960331003

theorem tailTrace_6785621 : CollatzResearch.WordTrace tailWord_6785621 prefixEnd_6785621 3484285112242500960331003 := by
  unfold tailWord_6785621
  simp only [CollatzResearch.WordTrace]
  refine ⟨247491930149861483647820717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164994620099907655765213811 247491930149861483647820717)
  ·
    refine ⟨92809473806198056367932769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247491930149861483647820717 92809473806198056367932769)
    ·
      refine ⟨69607105354648542275949577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92809473806198056367932769 69607105354648542275949577)
      ·
        refine ⟨52205329015986406706962183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69607105354648542275949577 52205329015986406706962183)
        ·
          refine ⟨78307993523979610060443275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52205329015986406706962183 78307993523979610060443275)
          ·
            refine ⟨117461990285969415090664913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78307993523979610060443275 117461990285969415090664913)
            ·
              refine ⟨88096492714477061317998685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117461990285969415090664913 88096492714477061317998685)
              ·
                refine ⟨33036184767928897994249507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88096492714477061317998685 33036184767928897994249507)
                ·
                  refine ⟨49554277151893346991374261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33036184767928897994249507 49554277151893346991374261)
                  ·
                    refine ⟨4645713482990001280441337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49554277151893346991374261 4645713482990001280441337)
                    ·
                      refine ⟨3484285112242500960331003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645713482990001280441337 3484285112242500960331003)
                      ·
                        rfl

theorem cell23_6785621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_6785621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785621 prefixEnd_6785621 := by exact prefixLift 6785621
  have htrace : WordTrace (prefixWord ++ tailWord_6785621) baseStart_6785621 baseEnd_6785621 := by
    simpa [prefixWord, tailWord_6785621, baseEnd_6785621] using wordTrace_append hprefix tailTrace_6785621
  have hstable : (prefixWord ++ tailWord_6785621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785621).length < 2 ^ (prefixWord ++ tailWord_6785621).sum := by decide
  have hdescent : baseEnd_6785621 < baseStart_6785621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785666 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6785666 : Nat := 118140960795 + 6785666 * 2 ^ 59
def prefixEnd_6785666 : Nat := 4983230072969 + 3 ^ 40 * 6785666 * 2
def baseEnd_6785666 : Nat := 3484308218871953284268297

theorem tailTrace_6785666 : CollatzResearch.WordTrace tailWord_6785666 prefixEnd_6785666 3484308218871953284268297 := by
  unfold tailWord_6785666
  simp only [CollatzResearch.WordTrace]
  refine ⟨61873392858674614083302213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164995714289798970888805901 61873392858674614083302213)
  ·
    refine ⟨11601261161001490140619165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61873392858674614083302213 11601261161001490140619165)
    ·
      refine ⟨4350472935375558802732187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11601261161001490140619165 4350472935375558802732187)
      ·
        refine ⟨6525709403063338204098281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4350472935375558802732187 6525709403063338204098281)
        ·
          refine ⟨4894282052297503653073711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6525709403063338204098281 4894282052297503653073711)
          ·
            refine ⟨7341423078446255479610567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4894282052297503653073711 7341423078446255479610567)
            ·
              refine ⟨11012134617669383219415851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7341423078446255479610567 11012134617669383219415851)
              ·
                refine ⟨16518201926504074829123777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11012134617669383219415851 16518201926504074829123777)
                ·
                  refine ⟨12388651444878056121842833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16518201926504074829123777 12388651444878056121842833)
                  ·
                    refine ⟨9291488583658542091382125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12388651444878056121842833 9291488583658542091382125)
                    ·
                      refine ⟨3484308218871953284268297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9291488583658542091382125 3484308218871953284268297)
                      ·
                        rfl

theorem cell23_6785666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6785666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785666 prefixEnd_6785666 := by exact prefixLift 6785666
  have htrace : WordTrace (prefixWord ++ tailWord_6785666) baseStart_6785666 baseEnd_6785666 := by
    simpa [prefixWord, tailWord_6785666, baseEnd_6785666] using wordTrace_append hprefix tailTrace_6785666
  have hstable : (prefixWord ++ tailWord_6785666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785666).length < 2 ^ (prefixWord ++ tailWord_6785666).sum := by decide
  have hdescent : baseEnd_6785666 < baseStart_6785666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785671 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_6785671 : Nat := 118140960795 + 6785671 * 2 ^ 59
def prefixEnd_6785671 : Nat := 4983230072969 + 3 ^ 40 * 6785671 * 2
def baseEnd_6785671 : Nat := 3484310786275225764705773

theorem tailTrace_6785671 : CollatzResearch.WordTrace tailWord_6785671 prefixEnd_6785671 3484310786275225764705773 := by
  unfold tailWord_6785671
  simp only [CollatzResearch.WordTrace]
  refine ⟨247493753799680342187140867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164995835866453561458093911 247493753799680342187140867)
  ·
    refine ⟨371240630699520513280711301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247493753799680342187140867 371240630699520513280711301)
    ·
      refine ⟨69607618256160096240133369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371240630699520513280711301 69607618256160096240133369)
      ·
        refine ⟨52205713692120072180100027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69607618256160096240133369 52205713692120072180100027)
        ·
          refine ⟨78308570538180108270150041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52205713692120072180100027 78308570538180108270150041)
          ·
            refine ⟨58731427903635081202612531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78308570538180108270150041 58731427903635081202612531)
            ·
              refine ⟨88097141855452621803918797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58731427903635081202612531 88097141855452621803918797)
              ·
                refine ⟨33036428195794733176469549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88097141855452621803918797 33036428195794733176469549)
                ·
                  refine ⟨12388660573423024941176081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33036428195794733176469549 12388660573423024941176081)
                  ·
                    refine ⟨9291495430067268705882061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12388660573423024941176081 9291495430067268705882061)
                    ·
                      refine ⟨3484310786275225764705773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9291495430067268705882061 3484310786275225764705773)
                      ·
                        rfl

theorem cell23_6785671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_6785671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785671 prefixEnd_6785671 := by exact prefixLift 6785671
  have htrace : WordTrace (prefixWord ++ tailWord_6785671) baseStart_6785671 baseEnd_6785671 := by
    simpa [prefixWord, tailWord_6785671, baseEnd_6785671] using wordTrace_append hprefix tailTrace_6785671
  have hstable : (prefixWord ++ tailWord_6785671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785671).length < 2 ^ (prefixWord ++ tailWord_6785671).sum := by decide
  have hdescent : baseEnd_6785671 < baseStart_6785671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785688 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 1, 2, 3]
def baseStart_6785688 : Nat := 118140960795 + 6785688 * 2 ^ 59
def prefixEnd_6785688 : Nat := 4983230072969 + 3 ^ 40 * 6785688 * 2
def baseEnd_6785688 : Nat := 3484319515446352198193195

theorem tailTrace_6785688 : CollatzResearch.WordTrace tailWord_6785688 prefixEnd_6785688 3484319515446352198193195 := by
  unfold tailWord_6785688
  simp only [CollatzResearch.WordTrace]
  refine ⟨123747186920309377045254859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164996249227079169393673145 123747186920309377045254859)
  ·
    refine ⟨185620780380464065567882289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123747186920309377045254859 185620780380464065567882289)
    ·
      refine ⟨139215585285348049175911717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185620780380464065567882289 139215585285348049175911717)
      ·
        refine ⟨26102922241002759220483447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139215585285348049175911717 26102922241002759220483447)
        ·
          refine ⟨39154383361504138830725171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26102922241002759220483447 39154383361504138830725171)
          ·
            refine ⟨58731575042256208246087757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39154383361504138830725171 58731575042256208246087757)
            ·
              refine ⟨22024340640846078092282909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58731575042256208246087757 22024340640846078092282909)
              ·
                refine ⟨8259127740317279284606091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22024340640846078092282909 8259127740317279284606091)
                ·
                  refine ⟨12388691610475918926909137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8259127740317279284606091 12388691610475918926909137)
                  ·
                    refine ⟨9291518707856939195181853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12388691610475918926909137 9291518707856939195181853)
                    ·
                      refine ⟨3484319515446352198193195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9291518707856939195181853 3484319515446352198193195)
                      ·
                        rfl

theorem cell23_6785688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_6785688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785688 prefixEnd_6785688 := by exact prefixLift 6785688
  have htrace : WordTrace (prefixWord ++ tailWord_6785688) baseStart_6785688 baseEnd_6785688 := by
    simpa [prefixWord, tailWord_6785688, baseEnd_6785688] using wordTrace_append hprefix tailTrace_6785688
  have hstable : (prefixWord ++ tailWord_6785688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785688).length < 2 ^ (prefixWord ++ tailWord_6785688).sum := by decide
  have hdescent : baseEnd_6785688 < baseStart_6785688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785791 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 3]
def baseStart_6785791 : Nat := 118140960795 + 6785791 * 2 ^ 59
def prefixEnd_6785791 : Nat := 4983230072969 + 3 ^ 40 * 6785791 * 2
def baseEnd_6785791 : Nat := 3484372403953765295205221

theorem tailTrace_6785791 : CollatzResearch.WordTrace tailWord_6785791 prefixEnd_6785791 3484372403953765295205221 := by
  unfold tailWord_6785791
  simp only [CollatzResearch.WordTrace]
  refine ⟨247498130559245602681509227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164998753706163735121006151 247498130559245602681509227)
  ·
    refine ⟨371247195838868404022263841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247498130559245602681509227 371247195838868404022263841)
    ·
      refine ⟨278435396879151303016697881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371247195838868404022263841 278435396879151303016697881)
      ·
        refine ⟨208826547659363477262523411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278435396879151303016697881 208826547659363477262523411)
        ·
          refine ⟨313239821489045215893785117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208826547659363477262523411 313239821489045215893785117)
          ·
            refine ⟨117464933058391955960169419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313239821489045215893785117 117464933058391955960169419)
            ·
              refine ⟨176197399587587933940254129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117464933058391955960169419 176197399587587933940254129)
              ·
                refine ⟨132148049690690950455190597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176197399587587933940254129 132148049690690950455190597)
                ·
                  refine ⟨24777759317004553210348237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132148049690690950455190597 24777759317004553210348237)
                  ·
                    refine ⟨9291659743876707453880589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24777759317004553210348237 9291659743876707453880589)
                    ·
                      refine ⟨3484372403953765295205221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9291659743876707453880589 3484372403953765295205221)
                      ·
                        rfl

theorem cell23_6785791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_6785791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785791 prefixEnd_6785791 := by exact prefixLift 6785791
  have htrace : WordTrace (prefixWord ++ tailWord_6785791) baseStart_6785791 baseEnd_6785791 := by
    simpa [prefixWord, tailWord_6785791, baseEnd_6785791] using wordTrace_append hprefix tailTrace_6785791
  have hstable : (prefixWord ++ tailWord_6785791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785791).length < 2 ^ (prefixWord ++ tailWord_6785791).sum := by decide
  have hdescent : baseEnd_6785791 < baseStart_6785791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785811 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 2, 5]
def baseStart_6785811 : Nat := 118140960795 + 6785811 * 2 ^ 59
def prefixEnd_6785811 : Nat := 4983230072969 + 3 ^ 40 * 6785811 * 2
def baseEnd_6785811 : Nat := 1161460891188951738985043

theorem tailTrace_6785811 : CollatzResearch.WordTrace tailWord_6785811 prefixEnd_6785811 1161460891188951738985043 := by
  unfold tailWord_6785811
  simp only [CollatzResearch.WordTrace]
  refine ⟨247498860019173146097237287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164999240012782097398158191 247498860019173146097237287)
  ·
    refine ⟨371248290028759719145855931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247498860019173146097237287 371248290028759719145855931)
    ·
      refine ⟨556872435043139578718783897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371248290028759719145855931 556872435043139578718783897)
      ·
        refine ⟨417654326282354684039087923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556872435043139578718783897 417654326282354684039087923)
        ·
          refine ⟨626481489423532026058631885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417654326282354684039087923 626481489423532026058631885)
          ·
            refine ⟨234930558533824509771986957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 626481489423532026058631885 234930558533824509771986957)
            ·
              refine ⟨88098959450184191164495109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234930558533824509771986957 88098959450184191164495109)
              ·
                refine ⟨16518554896909535843342833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88098959450184191164495109 16518554896909535843342833)
                ·
                  refine ⟨12388916172682151882507125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16518554896909535843342833 12388916172682151882507125)
                  ·
                    refine ⟨1161460891188951738985043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12388916172682151882507125 1161460891188951738985043)
                    ·
                      rfl

theorem cell23_6785811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 5].length) (baseStart_6785811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785811 prefixEnd_6785811 := by exact prefixLift 6785811
  have htrace : WordTrace (prefixWord ++ tailWord_6785811) baseStart_6785811 baseEnd_6785811 := by
    simpa [prefixWord, tailWord_6785811, baseEnd_6785811] using wordTrace_append hprefix tailTrace_6785811
  have hstable : (prefixWord ++ tailWord_6785811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785811).length < 2 ^ (prefixWord ++ tailWord_6785811).sum := by decide
  have hdescent : baseEnd_6785811 < baseStart_6785811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785815 : List Nat := [1, 1, 3, 4, 3, 1, 1, 4, 5]
def baseStart_6785815 : Nat := 118140960795 + 6785815 * 2 ^ 59
def prefixEnd_6785815 : Nat := 4983230072969 + 3 ^ 40 * 6785815 * 2
def baseEnd_6785815 : Nat := 387153858609941466811679

theorem tailTrace_6785815 : CollatzResearch.WordTrace tailWord_6785815 prefixEnd_6785815 387153858609941466811679 := by
  unfold tailWord_6785815
  simp only [CollatzResearch.WordTrace]
  refine ⟨247499005911158654780382899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164999337274105769853588599 247499005911158654780382899)
  ·
    refine ⟨371248508866737982170574349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247499005911158654780382899 371248508866737982170574349)
    ·
      refine ⟨139218190825026743313965381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371248508866737982170574349 139218190825026743313965381)
      ·
        refine ⟨26103410779692514371368509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139218190825026743313965381 26103410779692514371368509)
        ·
          refine ⟨9788779042384692889263191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26103410779692514371368509 9788779042384692889263191)
          ·
            refine ⟨14683168563577039333894787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9788779042384692889263191 14683168563577039333894787)
            ·
              refine ⟨22024752845365559000842181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14683168563577039333894787 22024752845365559000842181)
              ·
                refine ⟨4129641158506042312657909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22024752845365559000842181 4129641158506042312657909)
                ·
                  refine ⟨387153858609941466811679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4129641158506042312657909 387153858609941466811679)
                  ·
                    rfl

theorem cell23_6785815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 5].length) (baseStart_6785815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785815 prefixEnd_6785815 := by exact prefixLift 6785815
  have htrace : WordTrace (prefixWord ++ tailWord_6785815) baseStart_6785815 baseEnd_6785815 := by
    simpa [prefixWord, tailWord_6785815, baseEnd_6785815] using wordTrace_append hprefix tailTrace_6785815
  have hstable : (prefixWord ++ tailWord_6785815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785815).length < 2 ^ (prefixWord ++ tailWord_6785815).sum := by decide
  have hdescent : baseEnd_6785815 < baseStart_6785815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785818 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2]
def baseStart_6785818 : Nat := 118140960795 + 6785818 * 2 ^ 59
def prefixEnd_6785818 : Nat := 4983230072969 + 3 ^ 40 * 6785818 * 2
def baseEnd_6785818 : Nat := 3484386267931436689567597

theorem tailTrace_6785818 : CollatzResearch.WordTrace tailWord_6785818 prefixEnd_6785818 3484386267931436689567597 := by
  unfold tailWord_6785818
  simp only [CollatzResearch.WordTrace]
  refine ⟨61874778832536946573185527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164999410220098524195161405 61874778832536946573185527)
  ·
    refine ⟨92812168248805419859778291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61874778832536946573185527 92812168248805419859778291)
    ·
      refine ⟨139218252373208129789667437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92812168248805419859778291 139218252373208129789667437)
      ·
        refine ⟨52206844639953048671125289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139218252373208129789667437 52206844639953048671125289)
        ·
          refine ⟨39155133479964786503343967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52206844639953048671125289 39155133479964786503343967)
          ·
            refine ⟨58732700219947179755015951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39155133479964786503343967 58732700219947179755015951)
            ·
              refine ⟨88099050329920769632523927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58732700219947179755015951 88099050329920769632523927)
              ·
                refine ⟨132148575494881154448785891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88099050329920769632523927 132148575494881154448785891)
                ·
                  refine ⟨198222863242321731673178837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132148575494881154448785891 198222863242321731673178837)
                  ·
                    refine ⟨4645848357241915586090129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 198222863242321731673178837 4645848357241915586090129)
                    ·
                      refine ⟨3484386267931436689567597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645848357241915586090129 3484386267931436689567597)
                      ·
                        rfl

theorem cell23_6785818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_6785818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785818 prefixEnd_6785818 := by exact prefixLift 6785818
  have htrace : WordTrace (prefixWord ++ tailWord_6785818) baseStart_6785818 baseEnd_6785818 := by
    simpa [prefixWord, tailWord_6785818, baseEnd_6785818] using wordTrace_append hprefix tailTrace_6785818
  have hstable : (prefixWord ++ tailWord_6785818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785818).length < 2 ^ (prefixWord ++ tailWord_6785818).sum := by decide
  have hdescent : baseEnd_6785818 < baseStart_6785818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785845 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 2, 5]
def baseStart_6785845 : Nat := 118140960795 + 6785845 * 2 ^ 59
def prefixEnd_6785845 : Nat := 4983230072969 + 3 ^ 40 * 6785845 * 2
def baseEnd_6785845 : Nat := 1161466710636369361309991

theorem tailTrace_6785845 : CollatzResearch.WordTrace tailWord_6785845 prefixEnd_6785845 1161466710636369361309991 := by
  unfold tailWord_6785845
  simp only [CollatzResearch.WordTrace]
  refine ⟨247500100101049969903974989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165000066734033313269316659 247500100101049969903974989)
  ·
    refine ⟨92812537537893738713990621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247500100101049969903974989 92812537537893738713990621)
    ·
      refine ⟨34804701576710152017746483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92812537537893738713990621 34804701576710152017746483)
      ·
        refine ⟨52207052365065228026619725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34804701576710152017746483 52207052365065228026619725)
        ·
          refine ⟨19577644636899460509982397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52207052365065228026619725 19577644636899460509982397)
          ·
            refine ⟨7341616738837297691243399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19577644636899460509982397 7341616738837297691243399)
            ·
              refine ⟨11012425108255946536865099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7341616738837297691243399 11012425108255946536865099)
              ·
                refine ⟨16518637662383919805297649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11012425108255946536865099 16518637662383919805297649)
                ·
                  refine ⟨12388978246787939853973237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16518637662383919805297649 12388978246787939853973237)
                  ·
                    refine ⟨1161466710636369361309991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12388978246787939853973237 1161466710636369361309991)
                    ·
                      rfl

theorem cell23_6785845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_6785845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785845 prefixEnd_6785845 := by exact prefixLift 6785845
  have htrace : WordTrace (prefixWord ++ tailWord_6785845) baseStart_6785845 baseEnd_6785845 := by
    simpa [prefixWord, tailWord_6785845, baseEnd_6785845] using wordTrace_append hprefix tailTrace_6785845
  have hstable : (prefixWord ++ tailWord_6785845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785845).length < 2 ^ (prefixWord ++ tailWord_6785845).sum := by decide
  have hdescent : baseEnd_6785845 < baseStart_6785845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785848 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 1, 6, 2]
def baseStart_6785848 : Nat := 118140960795 + 6785848 * 2 ^ 59
def prefixEnd_6785848 : Nat := 4983230072969 + 3 ^ 40 * 6785848 * 2
def baseEnd_6785848 : Nat := 3484401672351071572192459

theorem tailTrace_6785848 : CollatzResearch.WordTrace tailWord_6785848 prefixEnd_6785848 3484401672351071572192459 := by
  unfold tailWord_6785848
  simp only [CollatzResearch.WordTrace]
  refine ⟨123750104760019550708167099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165000139680026067610889465 123750104760019550708167099)
  ·
    refine ⟨185625157140029326062250649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123750104760019550708167099 185625157140029326062250649)
    ·
      refine ⟨139218867855021994546687987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185625157140029326062250649 139218867855021994546687987)
      ·
        refine ⟨208828301782532991820031981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139218867855021994546687987 208828301782532991820031981)
        ·
          refine ⟨78310613168449871932511993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208828301782532991820031981 78310613168449871932511993)
          ·
            refine ⟨58732959876337403949383995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78310613168449871932511993 58732959876337403949383995)
            ·
              refine ⟨88099439814506105924075993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58732959876337403949383995 88099439814506105924075993)
              ·
                refine ⟨66074579860879579443056995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88099439814506105924075993 66074579860879579443056995)
                ·
                  refine ⟨99111869791319369164585493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66074579860879579443056995 99111869791319369164585493)
                  ·
                    refine ⟨4645868896468095429589945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99111869791319369164585493 4645868896468095429589945)
                    ·
                      refine ⟨3484401672351071572192459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645868896468095429589945 3484401672351071572192459)
                      ·
                        rfl

theorem cell23_6785848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 6, 2].length) (baseStart_6785848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785848 prefixEnd_6785848 := by exact prefixLift 6785848
  have htrace : WordTrace (prefixWord ++ tailWord_6785848) baseStart_6785848 baseEnd_6785848 := by
    simpa [prefixWord, tailWord_6785848, baseEnd_6785848] using wordTrace_append hprefix tailTrace_6785848
  have hstable : (prefixWord ++ tailWord_6785848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785848).length < 2 ^ (prefixWord ++ tailWord_6785848).sum := by decide
  have hdescent : baseEnd_6785848 < baseStart_6785848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785909 : List Nat := [1, 3, 4, 1, 1, 4, 1, 3, 1, 4]
def baseStart_6785909 : Nat := 118140960795 + 6785909 * 2 ^ 59
def prefixEnd_6785909 : Nat := 4983230072969 + 3 ^ 40 * 6785909 * 2
def baseEnd_6785909 : Nat := 1161477664890331944509893

theorem tailTrace_6785909 : CollatzResearch.WordTrace tailWord_6785909 prefixEnd_6785909 1161477664890331944509893 := by
  unfold tailWord_6785909
  simp only [CollatzResearch.WordTrace]
  refine ⟨247502434372818108834304781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165001622915212072556203187 247502434372818108834304781)
  ·
    refine ⟨92813412889806790812864293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247502434372818108834304781 92813412889806790812864293)
    ·
      refine ⟨17402514916838773277412055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92813412889806790812864293 17402514916838773277412055)
      ·
        refine ⟨26103772375258159916118083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17402514916838773277412055 26103772375258159916118083)
        ·
          refine ⟨39155658562887239874177125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26103772375258159916118083 39155658562887239874177125)
          ·
            refine ⟨7341685980541357476408211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39155658562887239874177125 7341685980541357476408211)
            ·
              refine ⟨11012528970812036214612317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7341685980541357476408211 11012528970812036214612317)
              ·
                refine ⟨4129698364054513580479619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11012528970812036214612317 4129698364054513580479619)
                ·
                  refine ⟨6194547546081770370719429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4129698364054513580479619 6194547546081770370719429)
                  ·
                    refine ⟨1161477664890331944509893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6194547546081770370719429 1161477664890331944509893)
                    ·
                      rfl

theorem cell23_6785909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_6785909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785909 prefixEnd_6785909 := by exact prefixLift 6785909
  have htrace : WordTrace (prefixWord ++ tailWord_6785909) baseStart_6785909 baseEnd_6785909 := by
    simpa [prefixWord, tailWord_6785909, baseEnd_6785909] using wordTrace_append hprefix tailTrace_6785909
  have hstable : (prefixWord ++ tailWord_6785909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785909).length < 2 ^ (prefixWord ++ tailWord_6785909).sum := by decide
  have hdescent : baseEnd_6785909 < baseStart_6785909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785925 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 4, 3, 2]
def baseStart_6785925 : Nat := 118140960795 + 6785925 * 2 ^ 59
def prefixEnd_6785925 : Nat := 4983230072969 + 3 ^ 40 * 6785925 * 2
def baseEnd_6785925 : Nat := 3484441210361467770929605

theorem tailTrace_6785925 : CollatzResearch.WordTrace tailWord_6785925 prefixEnd_6785925 3484441210361467770929605 := by
  unfold tailWord_6785925
  simp only [CollatzResearch.WordTrace]
  refine ⟨247503017940760143566887229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165002011960506762377924819 247503017940760143566887229)
  ·
    refine ⟨92813631727785053837582711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247503017940760143566887229 92813631727785053837582711)
    ·
      refine ⟨139220447591677580756374067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92813631727785053837582711 139220447591677580756374067)
      ·
        refine ⟨208830671387516371134561101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139220447591677580756374067 208830671387516371134561101)
        ·
          refine ⟨78311501770318639175460413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208830671387516371134561101 78311501770318639175460413)
          ·
            refine ⟨29366813163869489690797655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78311501770318639175460413 29366813163869489690797655)
            ·
              refine ⟨44050219745804234536196483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29366813163869489690797655 44050219745804234536196483)
              ·
                refine ⟨66075329618706351804294725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44050219745804234536196483 66075329618706351804294725)
                ·
                  refine ⟨12389124303507440963305261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66075329618706351804294725 12389124303507440963305261)
                  ·
                    refine ⟨4645921613815290361239473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12389124303507440963305261 4645921613815290361239473)
                    ·
                      refine ⟨3484441210361467770929605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645921613815290361239473 3484441210361467770929605)
                      ·
                        rfl

theorem cell23_6785925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 3, 2].length) (baseStart_6785925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785925 prefixEnd_6785925 := by exact prefixLift 6785925
  have htrace : WordTrace (prefixWord ++ tailWord_6785925) baseStart_6785925 baseEnd_6785925 := by
    simpa [prefixWord, tailWord_6785925, baseEnd_6785925] using wordTrace_append hprefix tailTrace_6785925
  have hstable : (prefixWord ++ tailWord_6785925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785925).length < 2 ^ (prefixWord ++ tailWord_6785925).sum := by decide
  have hdescent : baseEnd_6785925 < baseStart_6785925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785932 : List Nat := [2, 2, 1, 2, 1, 2, 2, 6, 1, 1, 3]
def baseStart_6785932 : Nat := 118140960795 + 6785932 * 2 ^ 59
def prefixEnd_6785932 : Nat := 4983230072969 + 3 ^ 40 * 6785932 * 2
def baseEnd_6785932 : Nat := 3484444804726049243542073

theorem tailTrace_6785932 : CollatzResearch.WordTrace tailWord_6785932 prefixEnd_6785932 3484444804726049243542073 := by
  unfold tailWord_6785932
  simp only [CollatzResearch.WordTrace]
  refine ⟨123751636625867391881196025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165002182167823189174928033 123751636625867391881196025)
  ·
    refine ⟨92813727469400543910897019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123751636625867391881196025 92813727469400543910897019)
    ·
      refine ⟨139220591204100815866345529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92813727469400543910897019 139220591204100815866345529)
      ·
        refine ⟨104415443403075611899759147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139220591204100815866345529 104415443403075611899759147)
        ·
          refine ⟨156623165104613417849638721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104415443403075611899759147 156623165104613417849638721)
          ·
            refine ⟨117467373828460063387229041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156623165104613417849638721 117467373828460063387229041)
            ·
              refine ⟨88100530371345047540421781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117467373828460063387229041 88100530371345047540421781)
              ·
                refine ⟨4129712361156799103457271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88100530371345047540421781 4129712361156799103457271)
                ·
                  refine ⟨6194568541735198655185907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4129712361156799103457271 6194568541735198655185907)
                  ·
                    refine ⟨9291852812602797982778861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6194568541735198655185907 9291852812602797982778861)
                    ·
                      refine ⟨3484444804726049243542073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9291852812602797982778861 3484444804726049243542073)
                      ·
                        rfl

theorem cell23_6785932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_6785932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785932 prefixEnd_6785932 := by exact prefixLift 6785932
  have htrace : WordTrace (prefixWord ++ tailWord_6785932) baseStart_6785932 baseEnd_6785932 := by
    simpa [prefixWord, tailWord_6785932, baseEnd_6785932] using wordTrace_append hprefix tailTrace_6785932
  have hstable : (prefixWord ++ tailWord_6785932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785932).length < 2 ^ (prefixWord ++ tailWord_6785932).sum := by decide
  have hdescent : baseEnd_6785932 < baseStart_6785932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785955 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 4]
def baseStart_6785955 : Nat := 118140960795 + 6785955 * 2 ^ 59
def prefixEnd_6785955 : Nat := 4983230072969 + 3 ^ 40 * 6785955 * 2
def baseEnd_6785955 : Nat := 3484456614781102653554467

theorem tailTrace_6785955 : CollatzResearch.WordTrace tailWord_6785955 prefixEnd_6785955 3484456614781102653554467 := by
  unfold tailWord_6785955
  simp only [CollatzResearch.WordTrace]
  refine ⟨247504112130651458690479319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165002741420434305793652879 247504112130651458690479319)
  ·
    refine ⟨371256168195977188035718979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247504112130651458690479319 371256168195977188035718979)
    ·
      refine ⟨556884252293965782053578469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371256168195977188035718979 556884252293965782053578469)
      ·
        refine ⟨104415797305118584135045963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 556884252293965782053578469 104415797305118584135045963)
        ·
          refine ⟨156623695957677876202568945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104415797305118584135045963 156623695957677876202568945)
          ·
            refine ⟨117467771968258407151926709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156623695957677876202568945 117467771968258407151926709)
            ·
              refine ⟨11012603622024225670493129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117467771968258407151926709 11012603622024225670493129)
              ·
                refine ⟨8259452716518169252869847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11012603622024225670493129 8259452716518169252869847)
                ·
                  refine ⟨12389179074777253879304771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8259452716518169252869847 12389179074777253879304771)
                  ·
                    refine ⟨18583768612165880818957157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12389179074777253879304771 18583768612165880818957157)
                    ·
                      refine ⟨3484456614781102653554467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18583768612165880818957157 3484456614781102653554467)
                      ·
                        rfl

theorem cell23_6785955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_6785955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785955 prefixEnd_6785955 := by exact prefixLift 6785955
  have htrace : WordTrace (prefixWord ++ tailWord_6785955) baseStart_6785955 baseEnd_6785955 := by
    simpa [prefixWord, tailWord_6785955, baseEnd_6785955] using wordTrace_append hprefix tailTrace_6785955
  have hstable : (prefixWord ++ tailWord_6785955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785955).length < 2 ^ (prefixWord ++ tailWord_6785955).sum := by decide
  have hdescent : baseEnd_6785955 < baseStart_6785955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785959 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_6785959 : Nat := 118140960795 + 6785959 * 2 ^ 59
def prefixEnd_6785959 : Nat := 4983230072969 + 3 ^ 40 * 6785959 * 2
def baseEnd_6785959 : Nat := 3484458668703720637904449

theorem tailTrace_6785959 : CollatzResearch.WordTrace tailWord_6785959 prefixEnd_6785959 3484458668703720637904449 := by
  unfold tailWord_6785959
  simp only [CollatzResearch.WordTrace]
  refine ⟨247504258022636967373624931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165002838681757978249083287 247504258022636967373624931)
  ·
    refine ⟨371256387033955451060437397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247504258022636967373624931 371256387033955451060437397)
    ·
      refine ⟨17402643142216661768458003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 371256387033955451060437397 17402643142216661768458003)
      ·
        refine ⟨26103964713324992652687005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17402643142216661768458003 26103964713324992652687005)
        ·
          refine ⟨9788986767496872244757627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26103964713324992652687005 9788986767496872244757627)
          ·
            refine ⟨14683480151245308367136441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9788986767496872244757627 14683480151245308367136441)
            ·
              refine ⟨11012610113433981275352331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14683480151245308367136441 11012610113433981275352331)
              ·
                refine ⟨16518915170150971913028497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11012610113433981275352331 16518915170150971913028497)
                ·
                  refine ⟨12389186377613228934771373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16518915170150971913028497 12389186377613228934771373)
                  ·
                    refine ⟨4645944891604960850539265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12389186377613228934771373 4645944891604960850539265)
                    ·
                      refine ⟨3484458668703720637904449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645944891604960850539265 3484458668703720637904449)
                      ·
                        rfl

theorem cell23_6785959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_6785959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785959 prefixEnd_6785959 := by exact prefixLift 6785959
  have htrace : WordTrace (prefixWord ++ tailWord_6785959) baseStart_6785959 baseEnd_6785959 := by
    simpa [prefixWord, tailWord_6785959, baseEnd_6785959] using wordTrace_append hprefix tailTrace_6785959
  have hstable : (prefixWord ++ tailWord_6785959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785959).length < 2 ^ (prefixWord ++ tailWord_6785959).sum := by decide
  have hdescent : baseEnd_6785959 < baseStart_6785959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785961 : List Nat := [1, 2, 1, 1, 1, 1, 5, 11]
def baseStart_6785961 : Nat := 118140960795 + 6785961 * 2 ^ 59
def prefixEnd_6785961 : Nat := 4983230072969 + 3 ^ 40 * 6785961 * 2
def baseEnd_6785961 : Nat := 129054062802408504817757

theorem tailTrace_6785961 : CollatzResearch.WordTrace tailWord_6785961 prefixEnd_6785961 129054062802408504817757 := by
  unfold tailWord_6785961
  simp only [CollatzResearch.WordTrace]
  refine ⟨247504330968629721715197737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165002887312419814476798491 247504330968629721715197737)
  ·
    refine ⟨185628248226472291286398303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247504330968629721715197737 185628248226472291286398303)
    ·
      refine ⟨278442372339708436929597455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185628248226472291286398303 278442372339708436929597455)
      ·
        refine ⟨417663558509562655394396183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278442372339708436929597455 417663558509562655394396183)
        ·
          refine ⟨626495337764343983091594275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417663558509562655394396183 626495337764343983091594275)
          ·
            refine ⟨939743006646515974637391413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626495337764343983091594275 939743006646515974637391413)
            ·
              refine ⟨88100906873110872622255445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 939743006646515974637391413 88100906873110872622255445)
              ·
                refine ⟨129054062802408504817757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 88100906873110872622255445 129054062802408504817757)
                ·
                  rfl

theorem cell23_6785961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 11].length) (baseStart_6785961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785961 prefixEnd_6785961 := by exact prefixLift 6785961
  have htrace : WordTrace (prefixWord ++ tailWord_6785961) baseStart_6785961 baseEnd_6785961 := by
    simpa [prefixWord, tailWord_6785961, baseEnd_6785961] using wordTrace_append hprefix tailTrace_6785961
  have hstable : (prefixWord ++ tailWord_6785961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785961).length < 2 ^ (prefixWord ++ tailWord_6785961).sum := by decide
  have hdescent : baseEnd_6785961 < baseStart_6785961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785975 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 1, 2, 3]
def baseStart_6785975 : Nat := 118140960795 + 6785975 * 2 ^ 59
def prefixEnd_6785975 : Nat := 4983230072969 + 3 ^ 40 * 6785975 * 2
def baseEnd_6785975 : Nat := 3484466884394192575304375

theorem tailTrace_6785975 : CollatzResearch.WordTrace tailWord_6785975 prefixEnd_6785975 3484466884394192575304375 := by
  unfold tailWord_6785975
  simp only [CollatzResearch.WordTrace]
  refine ⟨247504841590579002106207379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165003227727052668070804919 247504841590579002106207379)
  ·
    refine ⟨371257262385868503159311069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247504841590579002106207379 371257262385868503159311069)
    ·
      refine ⟨139221473394700688684741651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371257262385868503159311069 139221473394700688684741651)
      ·
        refine ⟨208832210092051033027112477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139221473394700688684741651 208832210092051033027112477)
        ·
          refine ⟨78312078784519137385167179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208832210092051033027112477 78312078784519137385167179)
          ·
            refine ⟨117468118176778706077750769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78312078784519137385167179 117468118176778706077750769)
            ·
              refine ⟨88101088632584029558313077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117468118176778706077750769 88101088632584029558313077)
              ·
                refine ⟨8259477059304752771091851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88101088632584029558313077 8259477059304752771091851)
                ·
                  refine ⟨12389215588957129156637777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8259477059304752771091851 12389215588957129156637777)
                  ·
                    refine ⟨9291911691717846867478333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12389215588957129156637777 9291911691717846867478333)
                    ·
                      refine ⟨3484466884394192575304375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9291911691717846867478333 3484466884394192575304375)
                      ·
                        rfl

theorem cell23_6785975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_6785975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785975 prefixEnd_6785975 := by exact prefixLift 6785975
  have htrace : WordTrace (prefixWord ++ tailWord_6785975) baseStart_6785975 baseEnd_6785975 := by
    simpa [prefixWord, tailWord_6785975, baseEnd_6785975] using wordTrace_append hprefix tailTrace_6785975
  have hstable : (prefixWord ++ tailWord_6785975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785975).length < 2 ^ (prefixWord ++ tailWord_6785975).sum := by decide
  have hdescent : baseEnd_6785975 < baseStart_6785975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6785982 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_6785982 : Nat := 118140960795 + 6785982 * 2 ^ 59
def prefixEnd_6785982 : Nat := 4983230072969 + 3 ^ 40 * 6785982 * 2
def baseEnd_6785982 : Nat := 1161490159586258015972281

theorem tailTrace_6785982 : CollatzResearch.WordTrace tailWord_6785982 prefixEnd_6785982 1161490159586258015972281 := by
  unfold tailWord_6785982
  simp only [CollatzResearch.WordTrace]
  refine ⟨30938137112694205287714025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165003397934369094867808133 30938137112694205287714025)
  ·
    refine ⟨23203602834520653965785519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30938137112694205287714025 23203602834520653965785519)
    ·
      refine ⟨34805404251780980948678279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23203602834520653965785519 34805404251780980948678279)
      ·
        refine ⟨52208106377671471423017419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34805404251780980948678279 52208106377671471423017419)
        ·
          refine ⟨78312159566507207134526129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52208106377671471423017419 78312159566507207134526129)
          ·
            refine ⟨58734119674880405350894597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78312159566507207134526129 58734119674880405350894597)
            ·
              refine ⟨11012647439040076003292737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58734119674880405350894597 11012647439040076003292737)
              ·
                refine ⟨8259485579280057002469553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11012647439040076003292737 8259485579280057002469553)
                ·
                  refine ⟨6194614184460042751852165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8259485579280057002469553 6194614184460042751852165)
                  ·
                    refine ⟨1161490159586258015972281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6194614184460042751852165 1161490159586258015972281)
                    ·
                      rfl

theorem cell23_6785982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_6785982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6785982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6785982 prefixEnd_6785982 := by exact prefixLift 6785982
  have htrace : WordTrace (prefixWord ++ tailWord_6785982) baseStart_6785982 baseEnd_6785982 := by
    simpa [prefixWord, tailWord_6785982, baseEnd_6785982] using wordTrace_append hprefix tailTrace_6785982
  have hstable : (prefixWord ++ tailWord_6785982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6785982).length < 2 ^ (prefixWord ++ tailWord_6785982).sum := by decide
  have hdescent : baseEnd_6785982 < baseStart_6785982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6785982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786002 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_6786002 : Nat := 118140960795 + 6786002 * 2 ^ 59
def prefixEnd_6786002 : Nat := 4983230072969 + 3 ^ 40 * 6786002 * 2
def baseEnd_6786002 : Nat := 3484480748371863969666751

theorem tailTrace_6786002 : CollatzResearch.WordTrace tailWord_6786002 prefixEnd_6786002 3484480748371863969666751 := by
  unfold tailWord_6786002
  simp only [CollatzResearch.WordTrace]
  refine ⟨61876456590370296429360065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165003884240987457144960173 61876456590370296429360065)
  ·
    refine ⟨46407342442777722322020049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61876456590370296429360065 46407342442777722322020049)
    ·
      refine ⟨34805506832083291741515037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46407342442777722322020049 34805506832083291741515037)
      ·
        refine ⟨13052065062031234403068139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34805506832083291741515037 13052065062031234403068139)
        ·
          refine ⟨19578097593046851604602209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13052065062031234403068139 19578097593046851604602209)
          ·
            refine ⟨14683573194785138703451657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19578097593046851604602209 14683573194785138703451657)
            ·
              refine ⟨11012679896088854027588743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14683573194785138703451657 11012679896088854027588743)
              ·
                refine ⟨16519019844133281041383115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11012679896088854027588743 16519019844133281041383115)
                ·
                  refine ⟨24778529766199921562074673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16519019844133281041383115 24778529766199921562074673)
                  ·
                    refine ⟨18583897324649941171556005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24778529766199921562074673 18583897324649941171556005)
                    ·
                      refine ⟨3484480748371863969666751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18583897324649941171556005 3484480748371863969666751)
                      ·
                        rfl

theorem cell23_6786002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_6786002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786002 prefixEnd_6786002 := by exact prefixLift 6786002
  have htrace : WordTrace (prefixWord ++ tailWord_6786002) baseStart_6786002 baseEnd_6786002 := by
    simpa [prefixWord, tailWord_6786002, baseEnd_6786002] using wordTrace_append hprefix tailTrace_6786002
  have hstable : (prefixWord ++ tailWord_6786002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786002).length < 2 ^ (prefixWord ++ tailWord_6786002).sum := by decide
  have hdescent : baseEnd_6786002 < baseStart_6786002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786006 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_6786006 : Nat := 118140960795 + 6786006 * 2 ^ 59
def prefixEnd_6786006 : Nat := 4983230072969 + 3 ^ 40 * 6786006 * 2
def baseEnd_6786006 : Nat := 3484482802294481954016733

theorem tailTrace_6786006 : CollatzResearch.WordTrace tailWord_6786006 prefixEnd_6786006 3484482802294481954016733 := by
  unfold tailWord_6786006
  simp only [CollatzResearch.WordTrace]
  refine ⟨15469123265841668400036617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165003981502311129600390581 15469123265841668400036617)
  ·
    refine ⟨11601842449381251300027463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15469123265841668400036617 11601842449381251300027463)
    ·
      refine ⟨17402763674071876950041195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11601842449381251300027463 17402763674071876950041195)
      ·
        refine ⟨26104145511107815425061793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17402763674071876950041195 26104145511107815425061793)
        ·
          refine ⟨19578109133330861568796345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26104145511107815425061793 19578109133330861568796345)
          ·
            refine ⟨14683581849998146176597259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19578109133330861568796345 14683581849998146176597259)
            ·
              refine ⟨22025372774997219264895889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14683581849998146176597259 22025372774997219264895889)
              ·
                refine ⟨16519029581247914448671917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22025372774997219264895889 16519029581247914448671917)
                ·
                  refine ⟨6194636092967967918251969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16519029581247914448671917 6194636092967967918251969)
                  ·
                    refine ⟨4645977069725975938688977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6194636092967967918251969 4645977069725975938688977)
                    ·
                      refine ⟨3484482802294481954016733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4645977069725975938688977 3484482802294481954016733)
                      ·
                        rfl

theorem cell23_6786006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_6786006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786006 prefixEnd_6786006 := by exact prefixLift 6786006
  have htrace : WordTrace (prefixWord ++ tailWord_6786006) baseStart_6786006 baseEnd_6786006 := by
    simpa [prefixWord, tailWord_6786006, baseEnd_6786006] using wordTrace_append hprefix tailTrace_6786006
  have hstable : (prefixWord ++ tailWord_6786006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786006).length < 2 ^ (prefixWord ++ tailWord_6786006).sum := by decide
  have hdescent : baseEnd_6786006 < baseStart_6786006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786102 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_6786102 : Nat := 118140960795 + 6786102 * 2 ^ 59
def prefixEnd_6786102 : Nat := 4983230072969 + 3 ^ 40 * 6786102 * 2
def baseEnd_6786102 : Nat := 387170232937479286490699

theorem tailTrace_6786102 : CollatzResearch.WordTrace tailWord_6786102 prefixEnd_6786102 387170232937479286490699 := by
  unfold tailWord_6786102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15469342103819931424755035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165006315774079268530720373 15469342103819931424755035)
  ·
    refine ⟨23204013155729897137132553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15469342103819931424755035 23204013155729897137132553)
    ·
      refine ⟨17403009866797422852849415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23204013155729897137132553 17403009866797422852849415)
      ·
        refine ⟨26104514800196134279274123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17403009866797422852849415 26104514800196134279274123)
        ·
          refine ⟨39156772200294201418911185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26104514800196134279274123 39156772200294201418911185)
          ·
            refine ⟨29367579150220651064183389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39156772200294201418911185 29367579150220651064183389)
            ·
              refine ⟨11012842181332744149068771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29367579150220651064183389 11012842181332744149068771)
              ·
                refine ⟨16519263271999116223603157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11012842181332744149068771 16519263271999116223603157)
                ·
                  refine ⟨387170232937479286490699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16519263271999116223603157 387170232937479286490699)
                  ·
                    rfl

theorem cell23_6786102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_6786102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786102 prefixEnd_6786102 := by exact prefixLift 6786102
  have htrace : WordTrace (prefixWord ++ tailWord_6786102) baseStart_6786102 baseEnd_6786102 := by
    simpa [prefixWord, tailWord_6786102, baseEnd_6786102] using wordTrace_append hprefix tailTrace_6786102
  have hstable : (prefixWord ++ tailWord_6786102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786102).length < 2 ^ (prefixWord ++ tailWord_6786102).sum := by decide
  have hdescent : baseEnd_6786102 < baseStart_6786102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786128 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 2, 8]
def baseStart_6786128 : Nat := 118140960795 + 6786128 * 2 ^ 59
def prefixEnd_6786128 : Nat := 4983230072969 + 3 ^ 40 * 6786128 * 2
def baseEnd_6786128 : Nat := 1161515148978110158897057

theorem tailTrace_6786128 : CollatzResearch.WordTrace tailWord_6786128 prefixEnd_6786128 1161515148978110158897057 := by
  unfold tailWord_6786128
  simp only [CollatzResearch.WordTrace]
  refine ⟨123755210979512354618263519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165006947972683139491018025 123755210979512354618263519)
  ·
    refine ⟨185632816469268531927395279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123755210979512354618263519 185632816469268531927395279)
    ·
      refine ⟨278449224703902797891092919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185632816469268531927395279 278449224703902797891092919)
      ·
        refine ⟨417673837055854196836639379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278449224703902797891092919 417673837055854196836639379)
        ·
          refine ⟨626510755583781295254959069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417673837055854196836639379 626510755583781295254959069)
          ·
            refine ⟨234941533343917985720609651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 626510755583781295254959069 234941533343917985720609651)
            ·
              refine ⟨352412300015876978580914477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234941533343917985720609651 352412300015876978580914477)
              ·
                refine ⟨132154612505953866967842929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352412300015876978580914477 132154612505953866967842929)
                ·
                  refine ⟨99115959379465400225882197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132154612505953866967842929 99115959379465400225882197)
                  ·
                    refine ⟨1161515148978110158897057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99115959379465400225882197 1161515148978110158897057)
                    ·
                      rfl

theorem cell23_6786128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_6786128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786128 prefixEnd_6786128 := by exact prefixLift 6786128
  have htrace : WordTrace (prefixWord ++ tailWord_6786128) baseStart_6786128 baseEnd_6786128 := by
    simpa [prefixWord, tailWord_6786128, baseEnd_6786128] using wordTrace_append hprefix tailTrace_6786128
  have hstable : (prefixWord ++ tailWord_6786128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786128).length < 2 ^ (prefixWord ++ tailWord_6786128).sum := by decide
  have hdescent : baseEnd_6786128 < baseStart_6786128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786162 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_6786162 : Nat := 118140960795 + 6786162 * 2 ^ 59
def prefixEnd_6786162 : Nat := 4983230072969 + 3 ^ 40 * 6786162 * 2
def baseEnd_6786162 : Nat := 1161520968425527781222005

theorem tailTrace_6786162 : CollatzResearch.WordTrace tailWord_6786162 prefixEnd_6786162 1161520968425527781222005 := by
  unfold tailWord_6786162
  simp only [CollatzResearch.WordTrace]
  refine ⟨61877915510225383260816185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165007774693934355362176493 61877915510225383260816185)
  ·
    refine ⟨46408436632669037445612139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61877915510225383260816185 46408436632669037445612139)
    ·
      refine ⟨69612654949003556168418209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46408436632669037445612139 69612654949003556168418209)
      ·
        refine ⟨52209491211752667126313657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69612654949003556168418209 52209491211752667126313657)
        ·
          refine ⟨39157118408814500344735243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52209491211752667126313657 39157118408814500344735243)
          ·
            refine ⟨58735677613221750517102865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39157118408814500344735243 58735677613221750517102865)
            ·
              refine ⟨44051758209916312887827149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58735677613221750517102865 44051758209916312887827149)
              ·
                refine ⟨16519409328718617332935181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44051758209916312887827149 16519409328718617332935181)
                ·
                  refine ⟨6194778498269481499850693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16519409328718617332935181 6194778498269481499850693)
                  ·
                    refine ⟨1161520968425527781222005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6194778498269481499850693 1161520968425527781222005)
                    ·
                      rfl

theorem cell23_6786162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_6786162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786162 prefixEnd_6786162 := by exact prefixLift 6786162
  have htrace : WordTrace (prefixWord ++ tailWord_6786162) baseStart_6786162 baseEnd_6786162 := by
    simpa [prefixWord, tailWord_6786162, baseEnd_6786162] using wordTrace_append hprefix tailTrace_6786162
  have hstable : (prefixWord ++ tailWord_6786162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786162).length < 2 ^ (prefixWord ++ tailWord_6786162).sum := by decide
  have hdescent : baseEnd_6786162 < baseStart_6786162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786169 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 2, 4, 2]
def baseStart_6786169 : Nat := 118140960795 + 6786169 * 2 ^ 59
def prefixEnd_6786169 : Nat := 4983230072969 + 3 ^ 40 * 6786169 * 2
def baseEnd_6786169 : Nat := 3484566499641164816278483

theorem tailTrace_6786169 : CollatzResearch.WordTrace tailWord_6786169 prefixEnd_6786169 3484566499641164816278483 := by
  unfold tailWord_6786169
  simp only [CollatzResearch.WordTrace]
  refine ⟨247511917351876173238769561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165007944901250782159179707 247511917351876173238769561)
  ·
    refine ⟨185633938013907129929077171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247511917351876173238769561 185633938013907129929077171)
    ·
      refine ⟨278450907020860694893615757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185633938013907129929077171 278450907020860694893615757)
      ·
        refine ⟨104419090132822760585105909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278450907020860694893615757 104419090132822760585105909)
        ·
          refine ⟨9789289699952133804853679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104419090132822760585105909 9789289699952133804853679)
          ·
            refine ⟨14683934549928200707280519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9789289699952133804853679 14683934549928200707280519)
            ·
              refine ⟨22025901824892301060920779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14683934549928200707280519 22025901824892301060920779)
              ·
                refine ⟨33038852737338451591381169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22025901824892301060920779 33038852737338451591381169)
                ·
                  refine ⟨24779139553003838693535877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33038852737338451591381169 24779139553003838693535877)
                  ·
                    refine ⟨4646088666188219755037977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24779139553003838693535877 4646088666188219755037977)
                    ·
                      refine ⟨3484566499641164816278483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4646088666188219755037977 3484566499641164816278483)
                      ·
                        rfl

theorem cell23_6786169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_6786169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786169 prefixEnd_6786169 := by exact prefixLift 6786169
  have htrace : WordTrace (prefixWord ++ tailWord_6786169) baseStart_6786169 baseEnd_6786169 := by
    simpa [prefixWord, tailWord_6786169, baseEnd_6786169] using wordTrace_append hprefix tailTrace_6786169
  have hstable : (prefixWord ++ tailWord_6786169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786169).length < 2 ^ (prefixWord ++ tailWord_6786169).sum := by decide
  have hdescent : baseEnd_6786169 < baseStart_6786169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786235 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 1, 6]
def baseStart_6786235 : Nat := 118140960795 + 6786235 * 2 ^ 59
def prefixEnd_6786235 : Nat := 4983230072969 + 3 ^ 40 * 6786235 * 2
def baseEnd_6786235 : Nat := 1161533463121453852684393

theorem tailTrace_6786235 : CollatzResearch.WordTrace tailWord_6786235 prefixEnd_6786235 1161533463121453852684393 := by
  unfold tailWord_6786235
  simp only [CollatzResearch.WordTrace]
  refine ⟨247514324569637066510672159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165009549713091377673781439 247514324569637066510672159)
  ·
    refine ⟨371271486854455599766008239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247514324569637066510672159 371271486854455599766008239)
    ·
      refine ⟨556907230281683399649012359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371271486854455599766008239 556907230281683399649012359)
      ·
        refine ⟨835360845422525099473518539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556907230281683399649012359 835360845422525099473518539)
        ·
          refine ⟨1253041268133787649210277809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835360845422525099473518539 1253041268133787649210277809)
          ·
            refine ⟨939780951100340736907708357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253041268133787649210277809 939780951100340736907708357)
            ·
              refine ⟨176208928331313888170195317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 939780951100340736907708357 176208928331313888170195317)
              ·
                refine ⟨16519587031060677015955811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176208928331313888170195317 16519587031060677015955811)
                ·
                  refine ⟨24779380546591015523933717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16519587031060677015955811 24779380546591015523933717)
                  ·
                    refine ⟨1161533463121453852684393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24779380546591015523933717 1161533463121453852684393)
                    ·
                      rfl

theorem cell23_6786235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 6].length) (baseStart_6786235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786235 prefixEnd_6786235 := by exact prefixLift 6786235
  have htrace : WordTrace (prefixWord ++ tailWord_6786235) baseStart_6786235 baseEnd_6786235 := by
    simpa [prefixWord, tailWord_6786235, baseEnd_6786235] using wordTrace_append hprefix tailTrace_6786235
  have hstable : (prefixWord ++ tailWord_6786235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786235).length < 2 ^ (prefixWord ++ tailWord_6786235).sum := by decide
  have hdescent : baseEnd_6786235 < baseStart_6786235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786245 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_6786245 : Nat := 118140960795 + 6786245 * 2 ^ 59
def prefixEnd_6786245 : Nat := 4983230072969 + 3 ^ 40 * 6786245 * 2
def baseEnd_6786245 : Nat := 3484605524170906518928133

theorem tailTrace_6786245 : CollatzResearch.WordTrace tailWord_6786245 prefixEnd_6786245 3484605524170906518928133 := by
  unfold tailWord_6786245
  simp only [CollatzResearch.WordTrace]
  refine ⟨247514689299600838218536189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165009792866400558812357459 247514689299600838218536189)
  ·
    refine ⟨92818008487350314331951071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247514689299600838218536189 92818008487350314331951071)
    ·
      refine ⟨139227012731025471497926607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92818008487350314331951071 139227012731025471497926607)
      ·
        refine ⟨208840519096538207246889911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139227012731025471497926607 208840519096538207246889911)
        ·
          refine ⟨313260778644807310870334867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208840519096538207246889911 313260778644807310870334867)
          ·
            refine ⟨469891167967210966305502301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313260778644807310870334867 469891167967210966305502301)
            ·
              refine ⟨176209187987704112364563363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469891167967210966305502301 176209187987704112364563363)
              ·
                refine ⟨264313781981556168546845045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176209187987704112364563363 264313781981556168546845045)
                ·
                  refine ⟨24779417060770890801266723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264313781981556168546845045 24779417060770890801266723)
                  ·
                    refine ⟨37169125591156336201900085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24779417060770890801266723 37169125591156336201900085)
                    ·
                      refine ⟨3484605524170906518928133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37169125591156336201900085 3484605524170906518928133)
                      ·
                        rfl

theorem cell23_6786245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_6786245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786245 prefixEnd_6786245 := by exact prefixLift 6786245
  have htrace : WordTrace (prefixWord ++ tailWord_6786245) baseStart_6786245 baseEnd_6786245 := by
    simpa [prefixWord, tailWord_6786245, baseEnd_6786245] using wordTrace_append hprefix tailTrace_6786245
  have hstable : (prefixWord ++ tailWord_6786245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786245).length < 2 ^ (prefixWord ++ tailWord_6786245).sum := by decide
  have hdescent : baseEnd_6786245 < baseStart_6786245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786276 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 3, 2, 2]
def baseStart_6786276 : Nat := 118140960795 + 6786276 * 2 ^ 59
def prefixEnd_6786276 : Nat := 4983230072969 + 3 ^ 40 * 6786276 * 2
def baseEnd_6786276 : Nat := 3484621442071195897640491

theorem tailTrace_6786276 : CollatzResearch.WordTrace tailWord_6786276 prefixEnd_6786276 3484621442071195897640491 := by
  unfold tailWord_6786276
  simp only [CollatzResearch.WordTrace]
  refine ⟨123757909981244265256457341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165010546641659020341943121 123757909981244265256457341)
  ·
    refine ⟨46409216242966599471171503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123757909981244265256457341 46409216242966599471171503)
    ·
      refine ⟨69613824364449899206757255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46409216242966599471171503 69613824364449899206757255)
      ·
        refine ⟨104420736546674848810135883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69613824364449899206757255 104420736546674848810135883)
        ·
          refine ⟨156631104820012273215203825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104420736546674848810135883 156631104820012273215203825)
          ·
            refine ⟨117473328615009204911402869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156631104820012273215203825 117473328615009204911402869)
            ·
              refine ⟨11013124557657112960444019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117473328615009204911402869 11013124557657112960444019)
              ·
                refine ⟨16519686836485669440666029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11013124557657112960444019 16519686836485669440666029)
                ·
                  refine ⟨6194882563682126040249761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16519686836485669440666029 6194882563682126040249761)
                  ·
                    refine ⟨4646161922761594530187321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6194882563682126040249761 4646161922761594530187321)
                    ·
                      refine ⟨3484621442071195897640491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4646161922761594530187321 3484621442071195897640491)
                      ·
                        rfl

theorem cell23_6786276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_6786276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786276 prefixEnd_6786276 := by exact prefixLift 6786276
  have htrace : WordTrace (prefixWord ++ tailWord_6786276) baseStart_6786276 baseEnd_6786276 := by
    simpa [prefixWord, tailWord_6786276, baseEnd_6786276] using wordTrace_append hprefix tailTrace_6786276
  have hstable : (prefixWord ++ tailWord_6786276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786276).length < 2 ^ (prefixWord ++ tailWord_6786276).sum := by decide
  have hdescent : baseEnd_6786276 < baseStart_6786276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786282 : List Nat := [3, 1, 3, 1, 1, 4, 2, 8]
def baseStart_6786282 : Nat := 118140960795 + 6786282 * 2 ^ 59
def prefixEnd_6786282 : Nat := 4983230072969 + 3 ^ 40 * 6786282 * 2
def baseEnd_6786282 : Nat := 129060167516856402746869

theorem tailTrace_6786282 : CollatzResearch.WordTrace tailWord_6786282 prefixEnd_6786282 129060167516856402746869 := by
  unfold tailWord_6786282
  simp only [CollatzResearch.WordTrace]
  refine ⟨61879009700116698384408275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165010692533644529025088733 61879009700116698384408275)
  ·
    refine ⟨92818514550175047576612413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61879009700116698384408275 92818514550175047576612413)
    ·
      refine ⟨34806942956315642841229655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92818514550175047576612413 34806942956315642841229655)
      ·
        refine ⟨52210414434473464261844483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34806942956315642841229655 52210414434473464261844483)
        ·
          refine ⟨78315621651710196392766725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52210414434473464261844483 78315621651710196392766725)
          ·
            refine ⟨14684179059695661823643761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78315621651710196392766725 14684179059695661823643761)
            ·
              refine ⟨11013134294771746367732821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14684179059695661823643761 11013134294771746367732821)
              ·
                refine ⟨129060167516856402746869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11013134294771746367732821 129060167516856402746869)
                ·
                  rfl

theorem cell23_6786282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 8].length) (baseStart_6786282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786282 prefixEnd_6786282 := by exact prefixLift 6786282
  have htrace : WordTrace (prefixWord ++ tailWord_6786282) baseStart_6786282 baseEnd_6786282 := by
    simpa [prefixWord, tailWord_6786282, baseEnd_6786282] using wordTrace_append hprefix tailTrace_6786282
  have hstable : (prefixWord ++ tailWord_6786282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786282).length < 2 ^ (prefixWord ++ tailWord_6786282).sum := by decide
  have hdescent : baseEnd_6786282 < baseStart_6786282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786286 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_6786286 : Nat := 118140960795 + 6786286 * 2 ^ 59
def prefixEnd_6786286 : Nat := 4983230072969 + 3 ^ 40 * 6786286 * 2
def baseEnd_6786286 : Nat := 1161542192292580286171815

theorem tailTrace_6786286 : CollatzResearch.WordTrace tailWord_6786286 prefixEnd_6786286 1161542192292580286171815 := by
  unfold tailWord_6786286
  simp only [CollatzResearch.WordTrace]
  refine ⟨30939523086556537777597339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165010789794968201480519141 30939523086556537777597339)
  ·
    refine ⟨46409284629834806666396009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30939523086556537777597339 46409284629834806666396009)
    ·
      refine ⟨34806963472376104999797007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46409284629834806666396009 34806963472376104999797007)
      ·
        refine ⟨52210445208564157499695511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34806963472376104999797007 52210445208564157499695511)
        ·
          refine ⟨78315667812846236249543267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52210445208564157499695511 78315667812846236249543267)
          ·
            refine ⟨117473501719269354374314901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78315667812846236249543267 117473501719269354374314901)
            ·
              refine ⟨5506570393090750986296011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117473501719269354374314901 5506570393090750986296011)
              ·
                refine ⟨8259855589636126479444017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5506570393090750986296011 8259855589636126479444017)
                ·
                  refine ⟨6194891692227094859583013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8259855589636126479444017 6194891692227094859583013)
                  ·
                    refine ⟨1161542192292580286171815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6194891692227094859583013 1161542192292580286171815)
                    ·
                      rfl

theorem cell23_6786286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_6786286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786286 prefixEnd_6786286 := by exact prefixLift 6786286
  have htrace : WordTrace (prefixWord ++ tailWord_6786286) baseStart_6786286 baseEnd_6786286 := by
    simpa [prefixWord, tailWord_6786286, baseEnd_6786286] using wordTrace_append hprefix tailTrace_6786286
  have hstable : (prefixWord ++ tailWord_6786286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786286).length < 2 ^ (prefixWord ++ tailWord_6786286).sum := by decide
  have hdescent : baseEnd_6786286 < baseStart_6786286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786295 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 2, 7]
def baseStart_6786295 : Nat := 118140960795 + 6786295 * 2 ^ 59
def prefixEnd_6786295 : Nat := 4983230072969 + 3 ^ 40 * 6786295 * 2
def baseEnd_6786295 : Nat := 1161543732734543774434301

theorem tailTrace_6786295 : CollatzResearch.WordTrace tailWord_6786295 prefixEnd_6786295 1161543732734543774434301 := by
  unfold tailWord_6786295
  simp only [CollatzResearch.WordTrace]
  refine ⟨247516512949419696757856339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165011008632946464505237559 247516512949419696757856339)
  ·
    refine ⟨371274769424129545136784509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247516512949419696757856339 371274769424129545136784509)
    ·
      refine ⟨139228038534048579426294191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371274769424129545136784509 139228038534048579426294191)
      ·
        refine ⟨208842057801072869139441287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139228038534048579426294191 208842057801072869139441287)
        ·
          refine ⟨313263086701609303709161931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208842057801072869139441287 313263086701609303709161931)
          ·
            refine ⟨469894630052413955563742897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313263086701609303709161931 469894630052413955563742897)
            ·
              refine ⟨352420972539310466672807173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469894630052413955563742897 352420972539310466672807173)
              ·
                refine ⟨66078932351120712501151345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352420972539310466672807173 66078932351120712501151345)
                ·
                  refine ⟨49559199263340534375863509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66078932351120712501151345 49559199263340534375863509)
                  ·
                    refine ⟨1161543732734543774434301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49559199263340534375863509 1161543732734543774434301)
                    ·
                      rfl

theorem cell23_6786295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_6786295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786295 prefixEnd_6786295 := by exact prefixLift 6786295
  have htrace : WordTrace (prefixWord ++ tailWord_6786295) baseStart_6786295 baseEnd_6786295 := by
    simpa [prefixWord, tailWord_6786295, baseEnd_6786295] using wordTrace_append hprefix tailTrace_6786295
  have hstable : (prefixWord ++ tailWord_6786295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786295).length < 2 ^ (prefixWord ++ tailWord_6786295).sum := by decide
  have hdescent : baseEnd_6786295 < baseStart_6786295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786306 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_6786306 : Nat := 118140960795 + 6786306 * 2 ^ 59
def prefixEnd_6786306 : Nat := 4983230072969 + 3 ^ 40 * 6786306 * 2
def baseEnd_6786306 : Nat := 3484636846490830780265353

theorem tailTrace_6786306 : CollatzResearch.WordTrace tailWord_6786306 prefixEnd_6786306 3484636846490830780265353 := by
  unfold tailWord_6786306
  simp only [CollatzResearch.WordTrace]
  refine ⟨61879228538094961409126693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165011276101586563757671181 61879228538094961409126693)
  ·
    refine ⟨11602355350892805264211255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61879228538094961409126693 11602355350892805264211255)
    ·
      refine ⟨17403533026339207896316883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11602355350892805264211255 17403533026339207896316883)
      ·
        refine ⟨26105299539508811844475325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17403533026339207896316883 26105299539508811844475325)
        ·
          refine ⟨9789487327315804441678247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26105299539508811844475325 9789487327315804441678247)
          ·
            refine ⟨14684230990973706662517371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9789487327315804441678247 14684230990973706662517371)
            ·
              refine ⟨22026346486460559993776057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14684230990973706662517371 22026346486460559993776057)
              ·
                refine ⟨16519759864845419995332043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22026346486460559993776057 16519759864845419995332043)
                ·
                  refine ⟨24779639797268129992998065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16519759864845419995332043 24779639797268129992998065)
                  ·
                    refine ⟨18584729847951097494748549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24779639797268129992998065 18584729847951097494748549)
                    ·
                      refine ⟨3484636846490830780265353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18584729847951097494748549 3484636846490830780265353)
                      ·
                        rfl

theorem cell23_6786306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_6786306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786306 prefixEnd_6786306 := by exact prefixLift 6786306
  have htrace : WordTrace (prefixWord ++ tailWord_6786306) baseStart_6786306 baseEnd_6786306 := by
    simpa [prefixWord, tailWord_6786306, baseEnd_6786306] using wordTrace_append hprefix tailTrace_6786306
  have hstable : (prefixWord ++ tailWord_6786306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786306).length < 2 ^ (prefixWord ++ tailWord_6786306).sum := by decide
  have hdescent : baseEnd_6786306 < baseStart_6786306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786332 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_6786332 : Nat := 118140960795 + 6786332 * 2 ^ 59
def prefixEnd_6786332 : Nat := 4983230072969 + 3 ^ 40 * 6786332 * 2
def baseEnd_6786332 : Nat := 3484650196987847678540233

theorem tailTrace_6786332 : CollatzResearch.WordTrace tailWord_6786332 prefixEnd_6786332 3484650196987847678540233 := by
  unfold tailWord_6786332
  simp only [CollatzResearch.WordTrace]
  refine ⟨123758931225142826038476625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165011908300190434717968833 123758931225142826038476625)
  ·
    refine ⟨92819198418857119528857469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123758931225142826038476625 92819198418857119528857469)
    ·
      refine ⟨34807199407071419823321551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92819198418857119528857469 34807199407071419823321551)
      ·
        refine ⟨52210799110607129734982327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34807199407071419823321551 52210799110607129734982327)
        ·
          refine ⟨78316198665910694602473491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52210799110607129734982327 78316198665910694602473491)
          ·
            refine ⟨117474297998866041903710237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78316198665910694602473491 117474297998866041903710237)
            ·
              refine ⟨44052861749574765713891339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117474297998866041903710237 44052861749574765713891339)
              ·
                refine ⟨66079292624362148570837009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44052861749574765713891339 66079292624362148570837009)
                ·
                  refine ⟨49559469468271611428127757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66079292624362148570837009 49559469468271611428127757)
                  ·
                    refine ⟨18584801050601854285547909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49559469468271611428127757 18584801050601854285547909)
                    ·
                      refine ⟨3484650196987847678540233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18584801050601854285547909 3484650196987847678540233)
                      ·
                        rfl

theorem cell23_6786332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_6786332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786332 prefixEnd_6786332 := by exact prefixLift 6786332
  have htrace : WordTrace (prefixWord ++ tailWord_6786332) baseStart_6786332 baseEnd_6786332 := by
    simpa [prefixWord, tailWord_6786332, baseEnd_6786332] using wordTrace_append hprefix tailTrace_6786332
  have hstable : (prefixWord ++ tailWord_6786332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786332).length < 2 ^ (prefixWord ++ tailWord_6786332).sum := by decide
  have hdescent : baseEnd_6786332 < baseStart_6786332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786352 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 3]
def baseStart_6786352 : Nat := 118140960795 + 6786352 * 2 ^ 59
def prefixEnd_6786352 : Nat := 4983230072969 + 3 ^ 40 * 6786352 * 2
def baseEnd_6786352 : Nat := 3484660466600937600290141

theorem tailTrace_6786352 : CollatzResearch.WordTrace tailWord_6786352 prefixEnd_6786352 3484660466600937600290141 := by
  unfold tailWord_6786352
  simp only [CollatzResearch.WordTrace]
  refine ⟨123759295955106597746340655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165012394606808796995120873 123759295955106597746340655)
  ·
    refine ⟨185638943932659896619510983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123759295955106597746340655 185638943932659896619510983)
    ·
      refine ⟨278458415898989844929266475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185638943932659896619510983 278458415898989844929266475)
      ·
        refine ⟨417687623848484767393899713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278458415898989844929266475 417687623848484767393899713)
        ·
          refine ⟨313265717886363575545424785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417687623848484767393899713 313265717886363575545424785)
          ·
            refine ⟨234949288414772681659068589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313265717886363575545424785 234949288414772681659068589)
            ·
              refine ⟨88105983155539755622150721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234949288414772681659068589 88105983155539755622150721)
              ·
                refine ⟨66079487366654816716613041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88105983155539755622150721 66079487366654816716613041)
                ·
                  refine ⟨49559615524991112537459781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66079487366654816716613041 49559615524991112537459781)
                  ·
                    refine ⟨9292427910935833600773709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49559615524991112537459781 9292427910935833600773709)
                    ·
                      refine ⟨3484660466600937600290141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9292427910935833600773709 3484660466600937600290141)
                      ·
                        rfl

theorem cell23_6786352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 3].length) (baseStart_6786352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786352 prefixEnd_6786352 := by exact prefixLift 6786352
  have htrace : WordTrace (prefixWord ++ tailWord_6786352) baseStart_6786352 baseEnd_6786352 := by
    simpa [prefixWord, tailWord_6786352, baseEnd_6786352] using wordTrace_append hprefix tailTrace_6786352
  have hstable : (prefixWord ++ tailWord_6786352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786352).length < 2 ^ (prefixWord ++ tailWord_6786352).sum := by decide
  have hdescent : baseEnd_6786352 < baseStart_6786352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786362 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_6786362 : Nat := 118140960795 + 6786362 * 2 ^ 59
def prefixEnd_6786362 : Nat := 4983230072969 + 3 ^ 40 * 6786362 * 2
def baseEnd_6786362 : Nat := 3484665601407482561165095

theorem tailTrace_6786362 : CollatzResearch.WordTrace tailWord_6786362 prefixEnd_6786362 3484665601407482561165095 := by
  unfold tailWord_6786362
  simp only [CollatzResearch.WordTrace]
  refine ⟨61879739160044241800136335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165012637760117978133696893 61879739160044241800136335)
  ·
    refine ⟨92819608740066362700204503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61879739160044241800136335 92819608740066362700204503)
    ·
      refine ⟨139229413110099544050306755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92819608740066362700204503 139229413110099544050306755)
      ·
        refine ⟨208844119665149316075460133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139229413110099544050306755 208844119665149316075460133)
        ·
          refine ⟨39158272437215496764148775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208844119665149316075460133 39158272437215496764148775)
          ·
            refine ⟨58737408655823245146223163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39158272437215496764148775 58737408655823245146223163)
            ·
              refine ⟨88106112983734867719334745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58737408655823245146223163 88106112983734867719334745)
              ·
                refine ⟨66079584737801150789501059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88106112983734867719334745 66079584737801150789501059)
                ·
                  refine ⟨99119377106701726184251589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66079584737801150789501059 99119377106701726184251589)
                  ·
                    refine ⟨18584883207506573659547173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99119377106701726184251589 18584883207506573659547173)
                    ·
                      refine ⟨3484665601407482561165095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18584883207506573659547173 3484665601407482561165095)
                      ·
                        rfl

theorem cell23_6786362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_6786362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786362 prefixEnd_6786362 := by exact prefixLift 6786362
  have htrace : WordTrace (prefixWord ++ tailWord_6786362) baseStart_6786362 baseEnd_6786362 := by
    simpa [prefixWord, tailWord_6786362, baseEnd_6786362] using wordTrace_append hprefix tailTrace_6786362
  have hstable : (prefixWord ++ tailWord_6786362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786362).length < 2 ^ (prefixWord ++ tailWord_6786362).sum := by decide
  have hdescent : baseEnd_6786362 < baseStart_6786362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786366 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_6786366 : Nat := 118140960795 + 6786366 * 2 ^ 59
def prefixEnd_6786366 : Nat := 4983230072969 + 3 ^ 40 * 6786366 * 2
def baseEnd_6786366 : Nat := 3484667655330100545515077

theorem tailTrace_6786366 : CollatzResearch.WordTrace tailWord_6786366 prefixEnd_6786366 3484667655330100545515077 := by
  unfold tailWord_6786366
  simp only [CollatzResearch.WordTrace]
  refine ⟨30939887816520309485461369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165012735021441650589127301 30939887816520309485461369)
  ·
    refine ⟨23204915862390232114096027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30939887816520309485461369 23204915862390232114096027)
    ·
      refine ⟨34807373793585348171144041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23204915862390232114096027 34807373793585348171144041)
      ·
        refine ⟨26105530345189011128358031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34807373793585348171144041 26105530345189011128358031)
        ·
          refine ⟨39158295517783516692537047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26105530345189011128358031 39158295517783516692537047)
          ·
            refine ⟨58737443276675275038805571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39158295517783516692537047 58737443276675275038805571)
            ·
              refine ⟨88106164915012912558208357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58737443276675275038805571 88106164915012912558208357)
              ·
                refine ⟨16519905921564921104664067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88106164915012912558208357 16519905921564921104664067)
                ·
                  refine ⟨24779858882347381656996101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16519905921564921104664067 24779858882347381656996101)
                  ·
                    refine ⟨4646223540440134060686769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24779858882347381656996101 4646223540440134060686769)
                    ·
                      refine ⟨3484667655330100545515077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4646223540440134060686769 3484667655330100545515077)
                      ·
                        rfl

theorem cell23_6786366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_6786366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786366 prefixEnd_6786366 := by exact prefixLift 6786366
  have htrace : WordTrace (prefixWord ++ tailWord_6786366) baseStart_6786366 baseEnd_6786366 := by
    simpa [prefixWord, tailWord_6786366, baseEnd_6786366] using wordTrace_append hprefix tailTrace_6786366
  have hstable : (prefixWord ++ tailWord_6786366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786366).length < 2 ^ (prefixWord ++ tailWord_6786366).sum := by decide
  have hdescent : baseEnd_6786366 < baseStart_6786366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786389 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 7]
def baseStart_6786389 : Nat := 118140960795 + 6786389 * 2 ^ 59
def prefixEnd_6786389 : Nat := 4983230072969 + 3 ^ 40 * 6786389 * 2
def baseEnd_6786389 : Nat := 387186607265017106169719

theorem tailTrace_6786389 : CollatzResearch.WordTrace tailWord_6786389 prefixEnd_6786389 387186607265017106169719 := by
  unfold tailWord_6786389
  simp only [CollatzResearch.WordTrace]
  refine ⟨247519941411079150811778221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165013294274052767207852147 247519941411079150811778221)
  ·
    refine ⟨92819978029154681554416833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247519941411079150811778221 92819978029154681554416833)
    ·
      refine ⟨69614983521866011165812625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92819978029154681554416833 69614983521866011165812625)
      ·
        refine ⟨52211237641399508374359469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69614983521866011165812625 52211237641399508374359469)
        ·
          refine ⟨19579214115524815640384801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52211237641399508374359469 19579214115524815640384801)
          ·
            refine ⟨14684410586643611730288601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19579214115524815640384801 14684410586643611730288601)
            ·
              refine ⟨11013307939982708797716451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14684410586643611730288601 11013307939982708797716451)
              ·
                refine ⟨16519961909974063196574677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11013307939982708797716451 16519961909974063196574677)
                ·
                  refine ⟨387186607265017106169719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16519961909974063196574677 387186607265017106169719)
                  ·
                    rfl

theorem cell23_6786389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_6786389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786389 prefixEnd_6786389 := by exact prefixLift 6786389
  have htrace : WordTrace (prefixWord ++ tailWord_6786389) baseStart_6786389 baseEnd_6786389 := by
    simpa [prefixWord, tailWord_6786389, baseEnd_6786389] using wordTrace_append hprefix tailTrace_6786389
  have hstable : (prefixWord ++ tailWord_6786389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786389).length < 2 ^ (prefixWord ++ tailWord_6786389).sum := by decide
  have hdescent : baseEnd_6786389 < baseStart_6786389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786400 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 2, 2, 2]
def baseStart_6786400 : Nat := 118140960795 + 6786400 * 2 ^ 59
def prefixEnd_6786400 : Nat := 4983230072969 + 3 ^ 40 * 6786400 * 2
def baseEnd_6786400 : Nat := 3484685113672353412489921

theorem tailTrace_6786400 : CollatzResearch.WordTrace tailWord_6786400 prefixEnd_6786400 3484685113672353412489921 := by
  unfold tailWord_6786400
  simp only [CollatzResearch.WordTrace]
  refine ⟨123760171307019649845214327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165013561742692866460285769 123760171307019649845214327)
  ·
    refine ⟨185640256960529474767821491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123760171307019649845214327 185640256960529474767821491)
    ·
      refine ⟨278460385440794212151732237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185640256960529474767821491 278460385440794212151732237)
      ·
        refine ⟨104422644540297829556899589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278460385440794212151732237 104422644540297829556899589)
        ·
          refine ⟨19579245851305843041918673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104422644540297829556899589 19579245851305843041918673)
          ·
            refine ⟨14684434388479382281439005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19579245851305843041918673 14684434388479382281439005)
            ·
              refine ⟨5506662895679768355539627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14684434388479382281439005 5506662895679768355539627)
              ·
                refine ⟨8259994343519652533309441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5506662895679768355539627 8259994343519652533309441)
                ·
                  refine ⟨6194995757639739399982081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8259994343519652533309441 6194995757639739399982081)
                  ·
                    refine ⟨4646246818229804549986561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6194995757639739399982081 4646246818229804549986561)
                    ·
                      refine ⟨3484685113672353412489921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4646246818229804549986561 3484685113672353412489921)
                      ·
                        rfl

theorem cell23_6786400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_6786400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786400 prefixEnd_6786400 := by exact prefixLift 6786400
  have htrace : WordTrace (prefixWord ++ tailWord_6786400) baseStart_6786400 baseEnd_6786400 := by
    simpa [prefixWord, tailWord_6786400, baseEnd_6786400] using wordTrace_append hprefix tailTrace_6786400
  have hstable : (prefixWord ++ tailWord_6786400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786400).length < 2 ^ (prefixWord ++ tailWord_6786400).sum := by decide
  have hdescent : baseEnd_6786400 < baseStart_6786400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786439 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_6786439 : Nat := 118140960795 + 6786439 * 2 ^ 59
def prefixEnd_6786439 : Nat := 4983230072969 + 3 ^ 40 * 6786439 * 2
def baseEnd_6786439 : Nat := 3484705139417878759902241

theorem tailTrace_6786439 : CollatzResearch.WordTrace tailWord_6786439 prefixEnd_6786439 3484705139417878759902241 := by
  unfold tailWord_6786439
  simp only [CollatzResearch.WordTrace]
  refine ⟨247521765060898009351098371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165014510040598672900732247 247521765060898009351098371)
  ·
    refine ⟨371282647591347014026647557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247521765060898009351098371 371282647591347014026647557)
    ·
      refine ⟨69615496423377565129996417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371282647591347014026647557 69615496423377565129996417)
      ·
        refine ⟨52211622317533173847497313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69615496423377565129996417 52211622317533173847497313)
        ·
          refine ⟨39158716738149880385622985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52211622317533173847497313 39158716738149880385622985)
          ·
            refine ⟨29369037553612410289217239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39158716738149880385622985 29369037553612410289217239)
            ·
              refine ⟨44053556330418615433825859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29369037553612410289217239 44053556330418615433825859)
              ·
                refine ⟨66080334495627923150738789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44053556330418615433825859 66080334495627923150738789)
                ·
                  refine ⟨12390062717930235590763523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66080334495627923150738789 12390062717930235590763523)
                  ·
                    refine ⟨18585094076895353386145285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12390062717930235590763523 18585094076895353386145285)
                    ·
                      refine ⟨3484705139417878759902241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18585094076895353386145285 3484705139417878759902241)
                      ·
                        rfl

theorem cell23_6786439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_6786439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786439 prefixEnd_6786439 := by exact prefixLift 6786439
  have htrace : WordTrace (prefixWord ++ tailWord_6786439) baseStart_6786439 baseEnd_6786439 := by
    simpa [prefixWord, tailWord_6786439, baseEnd_6786439] using wordTrace_append hprefix tailTrace_6786439
  have hstable : (prefixWord ++ tailWord_6786439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786439).length < 2 ^ (prefixWord ++ tailWord_6786439).sum := by decide
  have hdescent : baseEnd_6786439 < baseStart_6786439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786446 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_6786446 : Nat := 118140960795 + 6786446 * 2 ^ 59
def prefixEnd_6786446 : Nat := 4983230072969 + 3 ^ 40 * 6786446 * 2
def baseEnd_6786446 : Nat := 3484708733782460232514709

theorem tailTrace_6786446 : CollatzResearch.WordTrace tailWord_6786446 prefixEnd_6786446 3484708733782460232514709 := by
  unfold tailWord_6786446
  simp only [CollatzResearch.WordTrace]
  refine ⟨30940252546484081193325399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165014680247915099697735461 30940252546484081193325399)
  ·
    refine ⟨46410378819726121789988099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30940252546484081193325399 46410378819726121789988099)
    ·
      refine ⟨69615568229589182684982149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46410378819726121789988099 69615568229589182684982149)
      ·
        refine ⟨13052919043047971753434153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69615568229589182684982149 13052919043047971753434153)
        ·
          refine ⟨9789689282285978815075615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13052919043047971753434153 9789689282285978815075615)
          ·
            refine ⟨14684533923428968222613423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9789689282285978815075615 14684533923428968222613423)
            ·
              refine ⟨22026800885143452333920135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14684533923428968222613423 22026800885143452333920135)
              ·
                refine ⟨33040201327715178500880203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22026800885143452333920135 33040201327715178500880203)
                ·
                  refine ⟨49560301991572767751320305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33040201327715178500880203 49560301991572767751320305)
                  ·
                    refine ⟨37170226493679575813490229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49560301991572767751320305 37170226493679575813490229)
                    ·
                      refine ⟨3484708733782460232514709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37170226493679575813490229 3484708733782460232514709)
                      ·
                        rfl

theorem cell23_6786446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_6786446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786446 prefixEnd_6786446 := by exact prefixLift 6786446
  have htrace : WordTrace (prefixWord ++ tailWord_6786446) baseStart_6786446 baseEnd_6786446 := by
    simpa [prefixWord, tailWord_6786446, baseEnd_6786446] using wordTrace_append hprefix tailTrace_6786446
  have hstable : (prefixWord ++ tailWord_6786446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786446).length < 2 ^ (prefixWord ++ tailWord_6786446).sum := by decide
  have hdescent : baseEnd_6786446 < baseStart_6786446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786500 : List Nat := [2, 3, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_6786500 : Nat := 118140960795 + 6786500 * 2 ^ 59
def prefixEnd_6786500 : Nat := 4983230072969 + 3 ^ 40 * 6786500 * 2
def baseEnd_6786500 : Nat := 1161578820579267673746487

theorem tailTrace_6786500 : CollatzResearch.WordTrace tailWord_6786500 prefixEnd_6786500 1161578820579267673746487 := by
  unfold tailWord_6786500
  simp only [CollatzResearch.WordTrace]
  refine ⟨123761994956838508384534477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165015993275784677846045969 123761994956838508384534477)
  ·
    refine ⟨46410748108814440644200429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123761994956838508384534477 46410748108814440644200429)
    ·
      refine ⟨17404030540805415241575161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46410748108814440644200429 17404030540805415241575161)
      ·
        refine ⟨13053022905604061431181371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17404030540805415241575161 13053022905604061431181371)
        ·
          refine ⟨19579534358406092146772057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13053022905604061431181371 19579534358406092146772057)
          ·
            refine ⟨14684650768804569110079043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19579534358406092146772057 14684650768804569110079043)
            ·
              refine ⟨22026976153206853665118565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14684650768804569110079043 22026976153206853665118565)
              ·
                refine ⟨4130058028726285062209731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22026976153206853665118565 4130058028726285062209731)
                ·
                  refine ⟨6195087043089427593314597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130058028726285062209731 6195087043089427593314597)
                  ·
                    refine ⟨1161578820579267673746487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6195087043089427593314597 1161578820579267673746487)
                    ·
                      rfl

theorem cell23_6786500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_6786500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786500 prefixEnd_6786500 := by exact prefixLift 6786500
  have htrace : WordTrace (prefixWord ++ tailWord_6786500) baseStart_6786500 baseEnd_6786500 := by
    simpa [prefixWord, tailWord_6786500, baseEnd_6786500] using wordTrace_append hprefix tailTrace_6786500
  have hstable : (prefixWord ++ tailWord_6786500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786500).length < 2 ^ (prefixWord ++ tailWord_6786500).sum := by decide
  have hdescent : baseEnd_6786500 < baseStart_6786500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786533 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 1, 5, 2]
def baseStart_6786533 : Nat := 118140960795 + 6786533 * 2 ^ 59
def prefixEnd_6786533 : Nat := 4983230072969 + 3 ^ 40 * 6786533 * 2
def baseEnd_6786533 : Nat := 3484753406599401392126809

theorem tailTrace_6786533 : CollatzResearch.WordTrace tailWord_6786533 prefixEnd_6786533 3484753406599401392126809 := by
  unfold tailWord_6786533
  simp only [CollatzResearch.WordTrace]
  refine ⟨247525193522557463405020253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165016795681704975603346835 247525193522557463405020253)
  ·
    refine ⟨92821947570959048776882595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247525193522557463405020253 92821947570959048776882595)
    ·
      refine ⟨139232921356438573165323893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92821947570959048776882595 139232921356438573165323893)
      ·
        refine ⟨13053086377166116234249115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139232921356438573165323893 13053086377166116234249115)
        ·
          refine ⟨19579629565749174351373673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13053086377166116234249115 19579629565749174351373673)
          ·
            refine ⟨14684722174311880763530255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19579629565749174351373673 14684722174311880763530255)
            ·
              refine ⟨22027083261467821145295383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14684722174311880763530255 22027083261467821145295383)
              ·
                refine ⟨33040624892201731717943075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22027083261467821145295383 33040624892201731717943075)
                ·
                  refine ⟨49560937338302597576914613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33040624892201731717943075 49560937338302597576914613)
                  ·
                    refine ⟨4646337875465868522835745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49560937338302597576914613 4646337875465868522835745)
                    ·
                      refine ⟨3484753406599401392126809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4646337875465868522835745 3484753406599401392126809)
                      ·
                        rfl

theorem cell23_6786533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_6786533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786533 prefixEnd_6786533 := by exact prefixLift 6786533
  have htrace : WordTrace (prefixWord ++ tailWord_6786533) baseStart_6786533 baseEnd_6786533 := by
    simpa [prefixWord, tailWord_6786533, baseEnd_6786533] using wordTrace_append hprefix tailTrace_6786533
  have hstable : (prefixWord ++ tailWord_6786533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786533).length < 2 ^ (prefixWord ++ tailWord_6786533).sum := by decide
  have hdescent : baseEnd_6786533 < baseStart_6786533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786609 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_6786609 : Nat := 118140960795 + 6786609 * 2 ^ 59
def prefixEnd_6786609 : Nat := 4983230072969 + 3 ^ 40 * 6786609 * 2
def baseEnd_6786609 : Nat := 3484792431129143094776459

theorem tailTrace_6786609 : CollatzResearch.WordTrace tailWord_6786609 prefixEnd_6786609 3484792431129143094776459 := by
  unfold tailWord_6786609
  simp only [CollatzResearch.WordTrace]
  refine ⟨247527965470282128384786881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165018643646854752256524587 247527965470282128384786881)
  ·
    refine ⟨185645974102711596288590161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247527965470282128384786881 185645974102711596288590161)
    ·
      refine ⟨139234480577033697216442621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185645974102711596288590161 139234480577033697216442621)
      ·
        refine ⟨52212930216387636456165983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139234480577033697216442621 52212930216387636456165983)
        ·
          refine ⟨78319395324581454684248975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52212930216387636456165983 78319395324581454684248975)
          ·
            refine ⟨117479092986872182026373463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78319395324581454684248975 117479092986872182026373463)
            ·
              refine ⟨176218639480308273039560195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117479092986872182026373463 176218639480308273039560195)
              ·
                refine ⟨264327959220462409559340293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176218639480308273039560195 264327959220462409559340293)
                ·
                  refine ⟨49561492353836701792376305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264327959220462409559340293 49561492353836701792376305)
                  ·
                    refine ⟨37171119265377526344282229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49561492353836701792376305 37171119265377526344282229)
                    ·
                      refine ⟨3484792431129143094776459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37171119265377526344282229 3484792431129143094776459)
                      ·
                        rfl

theorem cell23_6786609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_6786609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786609 prefixEnd_6786609 := by exact prefixLift 6786609
  have htrace : WordTrace (prefixWord ++ tailWord_6786609) baseStart_6786609 baseEnd_6786609 := by
    simpa [prefixWord, tailWord_6786609, baseEnd_6786609] using wordTrace_append hprefix tailTrace_6786609
  have hstable : (prefixWord ++ tailWord_6786609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786609).length < 2 ^ (prefixWord ++ tailWord_6786609).sum := by decide
  have hdescent : baseEnd_6786609 < baseStart_6786609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786613 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_6786613 : Nat := 118140960795 + 6786613 * 2 ^ 59
def prefixEnd_6786613 : Nat := 4983230072969 + 3 ^ 40 * 6786613 * 2
def baseEnd_6786613 : Nat := 3484794485051761079126441

theorem tailTrace_6786613 : CollatzResearch.WordTrace tailWord_6786613 prefixEnd_6786613 3484794485051761079126441 := by
  unfold tailWord_6786613
  simp only [CollatzResearch.WordTrace]
  refine ⟨247528111362267637067932493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165018740908178424711954995 247528111362267637067932493)
  ·
    refine ⟨92823041760850363900474685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247528111362267637067932493 92823041760850363900474685)
    ·
      refine ⟨34808640660318886462678007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92823041760850363900474685 34808640660318886462678007)
      ·
        refine ⟨52212960990478329694017011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34808640660318886462678007 52212960990478329694017011)
        ·
          refine ⟨78319441485717494541025517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52212960990478329694017011 78319441485717494541025517)
          ·
            refine ⟨29369790557144060452884569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78319441485717494541025517 29369790557144060452884569)
            ·
              refine ⟨22027342917858045339663427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29369790557144060452884569 22027342917858045339663427)
              ·
                refine ⟨33041014376787068009495141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22027342917858045339663427 33041014376787068009495141)
                ·
                  refine ⟨6195190195647575251780339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33041014376787068009495141 6195190195647575251780339)
                  ·
                    refine ⟨9292785293471362877670509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6195190195647575251780339 9292785293471362877670509)
                    ·
                      refine ⟨3484794485051761079126441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9292785293471362877670509 3484794485051761079126441)
                      ·
                        rfl

theorem cell23_6786613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_6786613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786613 prefixEnd_6786613 := by exact prefixLift 6786613
  have htrace : WordTrace (prefixWord ++ tailWord_6786613) baseStart_6786613 baseEnd_6786613 := by
    simpa [prefixWord, tailWord_6786613, baseEnd_6786613] using wordTrace_append hprefix tailTrace_6786613
  have hstable : (prefixWord ++ tailWord_6786613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786613).length < 2 ^ (prefixWord ++ tailWord_6786613).sum := by decide
  have hdescent : baseEnd_6786613 < baseStart_6786613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786614 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_6786614 : Nat := 118140960795 + 6786614 * 2 ^ 59
def prefixEnd_6786614 : Nat := 4983230072969 + 3 ^ 40 * 6786614 * 2
def baseEnd_6786614 : Nat := 3484794998532415575213937

theorem tailTrace_6786614 : CollatzResearch.WordTrace tailWord_6786614 prefixEnd_6786614 3484794998532415575213937 := by
  unfold tailWord_6786614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15470509239704000889919931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165018765223509342825812597 15470509239704000889919931)
  ·
    refine ⟨23205763859556001334879897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15470509239704000889919931 23205763859556001334879897)
    ·
      refine ⟨17404322894667001001159923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23205763859556001334879897 17404322894667001001159923)
      ·
        refine ⟨26106484342000501501739885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17404322894667001001159923 26106484342000501501739885)
        ·
          refine ⟨9789931628250188063152457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26106484342000501501739885 9789931628250188063152457)
          ·
            refine ⟨7342448721187641047364343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9789931628250188063152457 7342448721187641047364343)
            ·
              refine ⟨11013673081781461571046515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7342448721187641047364343 11013673081781461571046515)
              ·
                refine ⟨16520509622672192356569773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11013673081781461571046515 16520509622672192356569773)
                ·
                  refine ⟨6195191108502072133713665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16520509622672192356569773 6195191108502072133713665)
                  ·
                    refine ⟨4646393331376554100285249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6195191108502072133713665 4646393331376554100285249)
                    ·
                      refine ⟨3484794998532415575213937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4646393331376554100285249 3484794998532415575213937)
                      ·
                        rfl

theorem cell23_6786614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_6786614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786614 prefixEnd_6786614 := by exact prefixLift 6786614
  have htrace : WordTrace (prefixWord ++ tailWord_6786614) baseStart_6786614 baseEnd_6786614 := by
    simpa [prefixWord, tailWord_6786614, baseEnd_6786614] using wordTrace_append hprefix tailTrace_6786614
  have hstable : (prefixWord ++ tailWord_6786614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786614).length < 2 ^ (prefixWord ++ tailWord_6786614).sum := by decide
  have hdescent : baseEnd_6786614 < baseStart_6786614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786629 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_6786629 : Nat := 118140960795 + 6786629 * 2 ^ 59
def prefixEnd_6786629 : Nat := 4983230072969 + 3 ^ 40 * 6786629 * 2
def baseEnd_6786629 : Nat := 1161600900247411005508789

theorem tailTrace_6786629 : CollatzResearch.WordTrace tailWord_6786629 prefixEnd_6786629 1161600900247411005508789 := by
  unfold tailWord_6786629
  simp only [CollatzResearch.WordTrace]
  refine ⟨247528694930209671800514941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165019129953473114533676627 247528694930209671800514941)
  ·
    refine ⟨92823260598828626925193103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247528694930209671800514941 92823260598828626925193103)
    ·
      refine ⟨139234890898242940387789655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92823260598828626925193103 139234890898242940387789655)
      ·
        refine ⟨208852336347364410581684483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139234890898242940387789655 208852336347364410581684483)
        ·
          refine ⟨313278504521046615872526725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208852336347364410581684483 313278504521046615872526725)
          ·
            refine ⟨58739719597696240476098761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313278504521046615872526725 58739719597696240476098761)
            ·
              refine ⟨44054789698272180357074071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58739719597696240476098761 44054789698272180357074071)
              ·
                refine ⟨66082184547408270535611107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44054789698272180357074071 66082184547408270535611107)
                ·
                  refine ⟨99123276821112405803416661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66082184547408270535611107 99123276821112405803416661)
                  ·
                    refine ⟨1161600900247411005508789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99123276821112405803416661 1161600900247411005508789)
                    ·
                      rfl

theorem cell23_6786629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_6786629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786629 prefixEnd_6786629 := by exact prefixLift 6786629
  have htrace : WordTrace (prefixWord ++ tailWord_6786629) baseStart_6786629 baseEnd_6786629 := by
    simpa [prefixWord, tailWord_6786629, baseEnd_6786629] using wordTrace_append hprefix tailTrace_6786629
  have hstable : (prefixWord ++ tailWord_6786629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786629).length < 2 ^ (prefixWord ++ tailWord_6786629).sum := by decide
  have hdescent : baseEnd_6786629 < baseStart_6786629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786679 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_6786679 : Nat := 118140960795 + 6786679 * 2 ^ 59
def prefixEnd_6786679 : Nat := 4983230072969 + 3 ^ 40 * 6786679 * 2
def baseEnd_6786679 : Nat := 3484828374774957820901137

theorem tailTrace_6786679 : CollatzResearch.WordTrace tailWord_6786679 prefixEnd_6786679 3484828374774957820901137 := by
  unfold tailWord_6786679
  simp only [CollatzResearch.WordTrace]
  refine ⟨247530518580028530339835091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165020345720019020226556727 247530518580028530339835091)
  ·
    refine ⟨371295777870042795509752637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247530518580028530339835091 371295777870042795509752637)
    ·
      refine ⟨139235916701266048316157239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371295777870042795509752637 139235916701266048316157239)
      ·
        refine ⟨208853875051899072474235859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139235916701266048316157239 208853875051899072474235859)
        ·
          refine ⟨313280812577848608711353789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208853875051899072474235859 313280812577848608711353789)
          ·
            refine ⟨117480304716693228266757671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313280812577848608711353789 117480304716693228266757671)
            ·
              refine ⟨176220457075039842400136507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117480304716693228266757671 176220457075039842400136507)
              ·
                refine ⟨264330685612559763600204761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176220457075039842400136507 264330685612559763600204761)
                ·
                  refine ⟨198248014209419822700153571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264330685612559763600204761 198248014209419822700153571)
                  ·
                    refine ⟨297372021314129734050230357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198248014209419822700153571 297372021314129734050230357)
                    ·
                      refine ⟨3484828374774957820901137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 297372021314129734050230357 3484828374774957820901137)
                      ·
                        rfl

theorem cell23_6786679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_6786679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786679 prefixEnd_6786679 := by exact prefixLift 6786679
  have htrace : WordTrace (prefixWord ++ tailWord_6786679) baseStart_6786679 baseEnd_6786679 := by
    simpa [prefixWord, tailWord_6786679, baseEnd_6786679] using wordTrace_append hprefix tailTrace_6786679
  have hstable : (prefixWord ++ tailWord_6786679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786679).length < 2 ^ (prefixWord ++ tailWord_6786679).sum := by decide
  have hdescent : baseEnd_6786679 < baseStart_6786679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786766 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_6786766 : Nat := 118140960795 + 6786766 * 2 ^ 59
def prefixEnd_6786766 : Nat := 4983230072969 + 3 ^ 40 * 6786766 * 2
def baseEnd_6786766 : Nat := 387208116399099886723693

theorem tailTrace_6786766 : CollatzResearch.WordTrace tailWord_6786766 prefixEnd_6786766 387208116399099886723693 := by
  unfold tailWord_6786766
  simp only [CollatzResearch.WordTrace]
  refine ⟨30941711466339168024781519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165022461153808896132168101 30941711466339168024781519)
  ·
    refine ⟨46412567199508752037172279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30941711466339168024781519 46412567199508752037172279)
    ·
      refine ⟨69618850799263128055758419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46412567199508752037172279 69618850799263128055758419)
      ·
        refine ⟨104428276198894692083637629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69618850799263128055758419 104428276198894692083637629)
        ·
          refine ⟨39160603574585509531364111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104428276198894692083637629 39160603574585509531364111)
          ·
            refine ⟨58740905361878264297046167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39160603574585509531364111 58740905361878264297046167)
            ·
              refine ⟨88111358042817396445569251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58740905361878264297046167 88111358042817396445569251)
              ·
                refine ⟨132167037064226094668353877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88111358042817396445569251 132167037064226094668353877)
                ·
                  refine ⟨387208116399099886723693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 132167037064226094668353877 387208116399099886723693)
                  ·
                    rfl

theorem cell23_6786766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_6786766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786766 prefixEnd_6786766 := by exact prefixLift 6786766
  have htrace : WordTrace (prefixWord ++ tailWord_6786766) baseStart_6786766 baseEnd_6786766 := by
    simpa [prefixWord, tailWord_6786766, baseEnd_6786766] using wordTrace_append hprefix tailTrace_6786766
  have hstable : (prefixWord ++ tailWord_6786766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786766).length < 2 ^ (prefixWord ++ tailWord_6786766).sum := by decide
  have hdescent : baseEnd_6786766 < baseStart_6786766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786787 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 3, 4]
def baseStart_6786787 : Nat := 118140960795 + 6786787 * 2 ^ 59
def prefixEnd_6786787 : Nat := 4983230072969 + 3 ^ 40 * 6786787 * 2
def baseEnd_6786787 : Nat := 1161627943561881132783547

theorem tailTrace_6786787 : CollatzResearch.WordTrace tailWord_6786787 prefixEnd_6786787 1161627943561881132783547 := by
  unfold tailWord_6786787
  simp only [CollatzResearch.WordTrace]
  refine ⟨247534457663637264784766615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165022971775758176523177743 247534457663637264784766615)
  ·
    refine ⟨371301686495455897177149923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247534457663637264784766615 371301686495455897177149923)
    ·
      refine ⟨556952529743183845765724885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371301686495455897177149923 556952529743183845765724885)
      ·
        refine ⟨13053574915855871385134177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 556952529743183845765724885 13053574915855871385134177)
        ·
          refine ⟨9790181186891903538850633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13053574915855871385134177 9790181186891903538850633)
          ·
            refine ⟨7342635890168927654137975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9790181186891903538850633 7342635890168927654137975)
            ·
              refine ⟨11013953835253391481206963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7342635890168927654137975 11013953835253391481206963)
              ·
                refine ⟨16520930752880087221810445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11013953835253391481206963 16520930752880087221810445)
                ·
                  refine ⟨6195349032330032708178917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16520930752880087221810445 6195349032330032708178917)
                  ·
                    refine ⟨1161627943561881132783547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6195349032330032708178917 1161627943561881132783547)
                    ·
                      rfl

theorem cell23_6786787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 4].length) (baseStart_6786787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786787 prefixEnd_6786787 := by exact prefixLift 6786787
  have htrace : WordTrace (prefixWord ++ tailWord_6786787) baseStart_6786787 baseEnd_6786787 := by
    simpa [prefixWord, tailWord_6786787, baseEnd_6786787] using wordTrace_append hprefix tailTrace_6786787
  have hstable : (prefixWord ++ tailWord_6786787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786787).length < 2 ^ (prefixWord ++ tailWord_6786787).sum := by decide
  have hdescent : baseEnd_6786787 < baseStart_6786787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786803 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 3, 5, 2]
def baseStart_6786803 : Nat := 118140960795 + 6786803 * 2 ^ 59
def prefixEnd_6786803 : Nat := 4983230072969 + 3 ^ 40 * 6786803 * 2
def baseEnd_6786803 : Nat := 3484892046376115335750567

theorem tailTrace_6786803 : CollatzResearch.WordTrace tailWord_6786803 prefixEnd_6786803 3484892046376115335750567 := by
  unfold tailWord_6786803
  simp only [CollatzResearch.WordTrace]
  refine ⟨247535041231579299517349063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165023360821052866344899375 247535041231579299517349063)
  ·
    refine ⟨371302561847368949276023595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247535041231579299517349063 371302561847368949276023595)
    ·
      refine ⟨556953842771053423914035393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371302561847368949276023595 556953842771053423914035393)
      ·
        refine ⟨417715382078290067935526545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556953842771053423914035393 417715382078290067935526545)
        ·
          refine ⟨313286536558717550951644909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417715382078290067935526545 313286536558717550951644909)
          ·
            refine ⟨117482451209519081606866841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313286536558717550951644909 117482451209519081606866841)
            ·
              refine ⟨88111838407139311205150131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117482451209519081606866841 88111838407139311205150131)
              ·
                refine ⟨132167757610708966807725197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88111838407139311205150131 132167757610708966807725197)
                ·
                  refine ⟨49562909104015862552896949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132167757610708966807725197 49562909104015862552896949)
                  ·
                    refine ⟨4646522728501487114334089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49562909104015862552896949 4646522728501487114334089)
                    ·
                      refine ⟨3484892046376115335750567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4646522728501487114334089 3484892046376115335750567)
                      ·
                        rfl

theorem cell23_6786803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 5, 2].length) (baseStart_6786803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786803 prefixEnd_6786803 := by exact prefixLift 6786803
  have htrace : WordTrace (prefixWord ++ tailWord_6786803) baseStart_6786803 baseEnd_6786803 := by
    simpa [prefixWord, tailWord_6786803, baseEnd_6786803] using wordTrace_append hprefix tailTrace_6786803
  have hstable : (prefixWord ++ tailWord_6786803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786803).length < 2 ^ (prefixWord ++ tailWord_6786803).sum := by decide
  have hdescent : baseEnd_6786803 < baseStart_6786803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786813 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_6786813 : Nat := 118140960795 + 6786813 * 2 ^ 59
def prefixEnd_6786813 : Nat := 4983230072969 + 3 ^ 40 * 6786813 * 2
def baseEnd_6786813 : Nat := 1161632393727553432208507

theorem tailTrace_6786813 : CollatzResearch.WordTrace tailWord_6786813 prefixEnd_6786813 1161632393727553432208507 := by
  unfold tailWord_6786813
  simp only [CollatzResearch.WordTrace]
  refine ⟨247535405961543071225213093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165023603974362047483475395 247535405961543071225213093)
  ·
    refine ⟨46412888617789325854727455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247535405961543071225213093 46412888617789325854727455)
    ·
      refine ⟨69619332926683988782091183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46412888617789325854727455 69619332926683988782091183)
      ·
        refine ⟨104428999390025983173136775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69619332926683988782091183 104428999390025983173136775)
        ·
          refine ⟨156643499085038974759705163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104428999390025983173136775 156643499085038974759705163)
          ·
            refine ⟨234965248627558462139557745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156643499085038974759705163 234965248627558462139557745)
            ·
              refine ⟨176223936470668846604668309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234965248627558462139557745 176223936470668846604668309)
              ·
                refine ⟨8260497022062602184593827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 176223936470668846604668309 8260497022062602184593827)
                ·
                  refine ⟨12390745533093903276890741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8260497022062602184593827 12390745533093903276890741)
                  ·
                    refine ⟨1161632393727553432208507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12390745533093903276890741 1161632393727553432208507)
                    ·
                      rfl

theorem cell23_6786813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_6786813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786813 prefixEnd_6786813 := by exact prefixLift 6786813
  have htrace : WordTrace (prefixWord ++ tailWord_6786813) baseStart_6786813 baseEnd_6786813 := by
    simpa [prefixWord, tailWord_6786813, baseEnd_6786813] using wordTrace_append hprefix tailTrace_6786813
  have hstable : (prefixWord ++ tailWord_6786813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786813).length < 2 ^ (prefixWord ++ tailWord_6786813).sum := by decide
  have hdescent : baseEnd_6786813 < baseStart_6786813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786816 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 4]
def baseStart_6786816 : Nat := 118140960795 + 6786816 * 2 ^ 59
def prefixEnd_6786816 : Nat := 4983230072969 + 3 ^ 40 * 6786816 * 2
def baseEnd_6786816 : Nat := 3484898721624623784888007

theorem tailTrace_6786816 : CollatzResearch.WordTrace tailWord_6786816 prefixEnd_6786816 3484898721624623784888007 := by
  unfold tailWord_6786816
  simp only [CollatzResearch.WordTrace]
  refine ⟨123767757690266101368786151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165023676920354801825048201 123767757690266101368786151)
  ·
    refine ⟨185651636535399152053179227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123767757690266101368786151 185651636535399152053179227)
    ·
      refine ⟨278477454803098728079768841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185651636535399152053179227 278477454803098728079768841)
      ·
        refine ⟨208858091102324046059826631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278477454803098728079768841 208858091102324046059826631)
        ·
          refine ⟨313287136653486069089739947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208858091102324046059826631 313287136653486069089739947)
          ·
            refine ⟨469930704980229103634609921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313287136653486069089739947 469930704980229103634609921)
            ·
              refine ⟨352448028735171827725957441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469930704980229103634609921 352448028735171827725957441)
              ·
                refine ⟨264336021551378870794468081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352448028735171827725957441 264336021551378870794468081)
                ·
                  refine ⟨198252016163534153095851061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264336021551378870794468081 198252016163534153095851061)
                  ·
                    refine ⟨18586126515331326852736037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 198252016163534153095851061 18586126515331326852736037)
                    ·
                      refine ⟨3484898721624623784888007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18586126515331326852736037 3484898721624623784888007)
                      ·
                        rfl

theorem cell23_6786816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_6786816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786816 prefixEnd_6786816 := by exact prefixLift 6786816
  have htrace : WordTrace (prefixWord ++ tailWord_6786816) baseStart_6786816 baseEnd_6786816 := by
    simpa [prefixWord, tailWord_6786816, baseEnd_6786816] using wordTrace_append hprefix tailTrace_6786816
  have hstable : (prefixWord ++ tailWord_6786816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786816).length < 2 ^ (prefixWord ++ tailWord_6786816).sum := by decide
  have hdescent : baseEnd_6786816 < baseStart_6786816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786860 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 2, 4]
def baseStart_6786860 : Nat := 118140960795 + 6786860 * 2 ^ 59
def prefixEnd_6786860 : Nat := 4983230072969 + 3 ^ 40 * 6786860 * 2
def baseEnd_6786860 : Nat := 1161640438257807204245935

theorem tailTrace_6786860 : CollatzResearch.WordTrace tailWord_6786860 prefixEnd_6786860 1161640438257807204245935 := by
  unfold tailWord_6786860
  simp only [CollatzResearch.WordTrace]
  refine ⟨123768560096186399126087017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165024746794915198834782689 123768560096186399126087017)
  ·
    refine ⟨92826420072139799344565263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123768560096186399126087017 92826420072139799344565263)
    ·
      refine ⟨139239630108209699016847895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92826420072139799344565263 139239630108209699016847895)
      ·
        refine ⟨208859445162314548525271843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139239630108209699016847895 208859445162314548525271843)
        ·
          refine ⟨313289167743471822787907765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208859445162314548525271843 313289167743471822787907765)
          ·
            refine ⟨29370859475950483386366353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 313289167743471822787907765 29370859475950483386366353)
            ·
              refine ⟨22028144606962862539774765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29370859475950483386366353 22028144606962862539774765)
              ·
                refine ⟨8260554227611073452415537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22028144606962862539774765 8260554227611073452415537)
                ·
                  refine ⟨6195415670708305089311653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8260554227611073452415537 6195415670708305089311653)
                  ·
                    refine ⟨1161640438257807204245935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6195415670708305089311653 1161640438257807204245935)
                    ·
                      rfl

theorem cell23_6786860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_6786860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786860 prefixEnd_6786860 := by exact prefixLift 6786860
  have htrace : WordTrace (prefixWord ++ tailWord_6786860) baseStart_6786860 baseEnd_6786860 := by
    simpa [prefixWord, tailWord_6786860, baseEnd_6786860] using wordTrace_append hprefix tailTrace_6786860
  have hstable : (prefixWord ++ tailWord_6786860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786860).length < 2 ^ (prefixWord ++ tailWord_6786860).sum := by decide
  have hdescent : baseEnd_6786860 < baseStart_6786860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786887 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 1, 2, 3]
def baseStart_6786887 : Nat := 118140960795 + 6786887 * 2 ^ 59
def prefixEnd_6786887 : Nat := 4983230072969 + 3 ^ 40 * 6786887 * 2
def baseEnd_6786887 : Nat := 3484935178751093007100181

theorem tailTrace_6786887 : CollatzResearch.WordTrace tailWord_6786887 prefixEnd_6786887 3484935178751093007100181 := by
  unfold tailWord_6786887
  simp only [CollatzResearch.WordTrace]
  refine ⟨247538104963274981863406915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165025403308849987908937943 247538104963274981863406915)
  ·
    refine ⟨371307157444912472795110373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247538104963274981863406915 371307157444912472795110373)
    ·
      refine ⟨69620092020921088649083195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371307157444912472795110373 69620092020921088649083195)
      ·
        refine ⟨104430138031381632973624793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69620092020921088649083195 104430138031381632973624793)
        ·
          refine ⟨78322603523536224730218595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104430138031381632973624793 78322603523536224730218595)
          ·
            refine ⟨117483905285304337095327893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78322603523536224730218595 117483905285304337095327893)
            ·
              refine ⟨5507058060248640801343495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117483905285304337095327893 5507058060248640801343495)
              ·
                refine ⟨8260587090372961202015243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5507058060248640801343495 8260587090372961202015243)
                ·
                  refine ⟨12390880635559441803022865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8260587090372961202015243 12390880635559441803022865)
                  ·
                    refine ⟨9293160476669581352267149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12390880635559441803022865 9293160476669581352267149)
                    ·
                      refine ⟨3484935178751093007100181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9293160476669581352267149 3484935178751093007100181)
                      ·
                        rfl

theorem cell23_6786887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_6786887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786887 prefixEnd_6786887 := by exact prefixLift 6786887
  have htrace : WordTrace (prefixWord ++ tailWord_6786887) baseStart_6786887 baseEnd_6786887 := by
    simpa [prefixWord, tailWord_6786887, baseEnd_6786887] using wordTrace_append hprefix tailTrace_6786887
  have hstable : (prefixWord ++ tailWord_6786887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786887).length < 2 ^ (prefixWord ++ tailWord_6786887).sum := by decide
  have hdescent : baseEnd_6786887 < baseStart_6786887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786943 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 3]
def baseStart_6786943 : Nat := 118140960795 + 6786943 * 2 ^ 59
def prefixEnd_6786943 : Nat := 4983230072969 + 3 ^ 40 * 6786943 * 2
def baseEnd_6786943 : Nat := 3484963933667744787999923

theorem tailTrace_6786943 : CollatzResearch.WordTrace tailWord_6786943 prefixEnd_6786943 3484963933667744787999923 := by
  unfold tailWord_6786943
  simp only [CollatzResearch.WordTrace]
  refine ⟨247540147451072103427445483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165026764967381402284963655 247540147451072103427445483)
  ·
    refine ⟨371310221176608155141168225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247540147451072103427445483 371310221176608155141168225)
    ·
      refine ⟨278482665882456116355876169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371310221176608155141168225 278482665882456116355876169)
      ·
        refine ⟨208861999411842087266907127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278482665882456116355876169 208861999411842087266907127)
        ·
          refine ⟨313292999117763130900360691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208861999411842087266907127 313292999117763130900360691)
          ·
            refine ⟨469939498676644696350541037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313292999117763130900360691 469939498676644696350541037)
            ·
              refine ⟨176227312003741761131452889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469939498676644696350541037 176227312003741761131452889)
              ·
                refine ⟨132170484002806320848589667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176227312003741761131452889 132170484002806320848589667)
                ·
                  refine ⟨198255726004209481272884501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132170484002806320848589667 198255726004209481272884501)
                  ·
                    refine ⟨9293237156447319434666461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 198255726004209481272884501 9293237156447319434666461)
                    ·
                      refine ⟨3484963933667744787999923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9293237156447319434666461 3484963933667744787999923)
                      ·
                        rfl

theorem cell23_6786943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_6786943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786943 prefixEnd_6786943 := by exact prefixLift 6786943
  have htrace : WordTrace (prefixWord ++ tailWord_6786943) baseStart_6786943 baseEnd_6786943 := by
    simpa [prefixWord, tailWord_6786943, baseEnd_6786943] using wordTrace_append hprefix tailTrace_6786943
  have hstable : (prefixWord ++ tailWord_6786943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786943).length < 2 ^ (prefixWord ++ tailWord_6786943).sum := by decide
  have hdescent : baseEnd_6786943 < baseStart_6786943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786968 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6786968 : Nat := 118140960795 + 6786968 * 2 ^ 59
def prefixEnd_6786968 : Nat := 4983230072969 + 3 ^ 40 * 6786968 * 2
def baseEnd_6786968 : Nat := 3484976770684107190187309

theorem tailTrace_6786968 : CollatzResearch.WordTrace tailWord_6786968 prefixEnd_6786968 3484976770684107190187309 := by
  unfold tailWord_6786968
  simp only [CollatzResearch.WordTrace]
  refine ⟨123770529637990766348552779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165027372850654355131403705 123770529637990766348552779)
  ·
    refine ⟨185655794456986149522829169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123770529637990766348552779 185655794456986149522829169)
    ·
      refine ⟨139241845842739612142121877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185655794456986149522829169 139241845842739612142121877)
      ·
        refine ⟨6526961523878419319161963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139241845842739612142121877 6526961523878419319161963)
        ·
          refine ⟨9790442285817628978742945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526961523878419319161963 9790442285817628978742945)
          ·
            refine ⟨7342831714363221734057209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9790442285817628978742945 7342831714363221734057209)
            ·
              refine ⟨5507123785772416300542907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7342831714363221734057209 5507123785772416300542907)
              ·
                refine ⟨8260685678658624450814361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5507123785772416300542907 8260685678658624450814361)
                ·
                  refine ⟨6195514258993968338110771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8260685678658624450814361 6195514258993968338110771)
                  ·
                    refine ⟨9293271388490952507166157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6195514258993968338110771 9293271388490952507166157)
                    ·
                      refine ⟨3484976770684107190187309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9293271388490952507166157 3484976770684107190187309)
                      ·
                        rfl

theorem cell23_6786968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6786968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786968 prefixEnd_6786968 := by exact prefixLift 6786968
  have htrace : WordTrace (prefixWord ++ tailWord_6786968) baseStart_6786968 baseEnd_6786968 := by
    simpa [prefixWord, tailWord_6786968, baseEnd_6786968] using wordTrace_append hprefix tailTrace_6786968
  have hstable : (prefixWord ++ tailWord_6786968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786968).length < 2 ^ (prefixWord ++ tailWord_6786968).sum := by decide
  have hdescent : baseEnd_6786968 < baseStart_6786968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6786978 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_6786978 : Nat := 118140960795 + 6786978 * 2 ^ 59
def prefixEnd_6786978 : Nat := 4983230072969 + 3 ^ 40 * 6786978 * 2
def baseEnd_6786978 : Nat := 3484981905490652151062263

theorem tailTrace_6786978 : CollatzResearch.WordTrace tailWord_6786978 prefixEnd_6786978 3484981905490652151062263 := by
  unfold tailWord_6786978
  simp only [CollatzResearch.WordTrace]
  refine ⟨61885356001486326101242397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165027616003963536269979725 61885356001486326101242397)
  ·
    refine ⟨23207008500557372287965899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61885356001486326101242397 23207008500557372287965899)
    ·
      refine ⟨34810512750836058431948849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23207008500557372287965899 34810512750836058431948849)
      ·
        refine ⟨26107884563127043823961637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34810512750836058431948849 26107884563127043823961637)
        ·
          refine ⟨4895228355586320716992807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26107884563127043823961637 4895228355586320716992807)
          ·
            refine ⟨7342842533379481075489211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895228355586320716992807 7342842533379481075489211)
            ·
              refine ⟨11014263800069221613233817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7342842533379481075489211 11014263800069221613233817)
              ·
                refine ⟨8260697850051916209925363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11014263800069221613233817 8260697850051916209925363)
                ·
                  refine ⟨12391046775077874314888045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8260697850051916209925363 12391046775077874314888045)
                  ·
                    refine ⟨4646642540654202868083017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12391046775077874314888045 4646642540654202868083017)
                    ·
                      refine ⟨3484981905490652151062263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4646642540654202868083017 3484981905490652151062263)
                      ·
                        rfl

theorem cell23_6786978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_6786978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6786978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6786978 prefixEnd_6786978 := by exact prefixLift 6786978
  have htrace : WordTrace (prefixWord ++ tailWord_6786978) baseStart_6786978 baseEnd_6786978 := by
    simpa [prefixWord, tailWord_6786978, baseEnd_6786978] using wordTrace_append hprefix tailTrace_6786978
  have hstable : (prefixWord ++ tailWord_6786978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6786978).length < 2 ^ (prefixWord ++ tailWord_6786978).sum := by decide
  have hdescent : baseEnd_6786978 < baseStart_6786978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6786978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787003 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 5]
def baseStart_6787003 : Nat := 118140960795 + 6787003 * 2 ^ 59
def prefixEnd_6787003 : Nat := 4983230072969 + 3 ^ 40 * 6787003 * 2
def baseEnd_6787003 : Nat := 3484994742507014553249647

theorem tailTrace_6787003 : CollatzResearch.WordTrace tailWord_6787003 prefixEnd_6787003 3484994742507014553249647 := by
  unfold tailWord_6787003
  simp only [CollatzResearch.WordTrace]
  refine ⟨247542335830854733674629663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165028223887236489116419775 247542335830854733674629663)
  ·
    refine ⟨371313503746282100511944495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247542335830854733674629663 371313503746282100511944495)
    ·
      refine ⟨556970255619423150767916743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371313503746282100511944495 556970255619423150767916743)
      ·
        refine ⟨835455383429134726151875115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556970255619423150767916743 835455383429134726151875115)
        ·
          refine ⟨1253183075143702089227812673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835455383429134726151875115 1253183075143702089227812673)
          ·
            refine ⟨939887306357776566920859505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253183075143702089227812673 939887306357776566920859505)
            ·
              refine ⟨704915479768332425190644629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939887306357776566920859505 704915479768332425190644629)
              ·
                refine ⟨33042913114140582430811467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 704915479768332425190644629 33042913114140582430811467)
                ·
                  refine ⟨49564369671210873646217201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33042913114140582430811467 49564369671210873646217201)
                  ·
                    refine ⟨37173277253408155234662901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49564369671210873646217201 37173277253408155234662901)
                    ·
                      refine ⟨3484994742507014553249647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37173277253408155234662901 3484994742507014553249647)
                      ·
                        rfl

theorem cell23_6787003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 5].length) (baseStart_6787003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787003 prefixEnd_6787003 := by exact prefixLift 6787003
  have htrace : WordTrace (prefixWord ++ tailWord_6787003) baseStart_6787003 baseEnd_6787003 := by
    simpa [prefixWord, tailWord_6787003, baseEnd_6787003] using wordTrace_append hprefix tailTrace_6787003
  have hstable : (prefixWord ++ tailWord_6787003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787003).length < 2 ^ (prefixWord ++ tailWord_6787003).sum := by decide
  have hdescent : baseEnd_6787003 < baseStart_6787003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787020 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6787020 : Nat := 118140960795 + 6787020 * 2 ^ 59
def prefixEnd_6787020 : Nat := 4983230072969 + 3 ^ 40 * 6787020 * 2
def baseEnd_6787020 : Nat := 3485003471678140986737069

theorem tailTrace_6787020 : CollatzResearch.WordTrace tailWord_6787020 prefixEnd_6787020 3485003471678140986737069 := by
  unfold tailWord_6787020
  simp only [CollatzResearch.WordTrace]
  refine ⟨123771477935896572788999257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165028637247862097051999009 123771477935896572788999257)
  ·
    refine ⟨92828608451922429591749443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123771477935896572788999257 92828608451922429591749443)
    ·
      refine ⟨139242912677883644387624165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92828608451922429591749443 139242912677883644387624165)
      ·
        refine ⟨26108046127103183322679531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139242912677883644387624165 26108046127103183322679531)
        ·
          refine ⟨39162069190654774984019297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26108046127103183322679531 39162069190654774984019297)
          ·
            refine ⟨29371551892991081238014473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39162069190654774984019297 29371551892991081238014473)
            ·
              refine ⟨22028663919743310928510855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29371551892991081238014473 22028663919743310928510855)
              ·
                refine ⟨33042995879614966392766283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22028663919743310928510855 33042995879614966392766283)
                ·
                  refine ⟨49564493819422449589149425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33042995879614966392766283 49564493819422449589149425)
                  ·
                    refine ⟨37173370364566837191862069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49564493819422449589149425 37173370364566837191862069)
                    ·
                      refine ⟨3485003471678140986737069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37173370364566837191862069 3485003471678140986737069)
                      ·
                        rfl

theorem cell23_6787020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6787020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787020 prefixEnd_6787020 := by exact prefixLift 6787020
  have htrace : WordTrace (prefixWord ++ tailWord_6787020) baseStart_6787020 baseEnd_6787020 := by
    simpa [prefixWord, tailWord_6787020, baseEnd_6787020] using wordTrace_append hprefix tailTrace_6787020
  have hstable : (prefixWord ++ tailWord_6787020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787020).length < 2 ^ (prefixWord ++ tailWord_6787020).sum := by decide
  have hdescent : baseEnd_6787020 < baseStart_6787020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787047 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_6787047 : Nat := 118140960795 + 6787047 * 2 ^ 59
def prefixEnd_6787047 : Nat := 4983230072969 + 3 ^ 40 * 6787047 * 2
def baseEnd_6787047 : Nat := 3485017335655812381099445

theorem tailTrace_6787047 : CollatzResearch.WordTrace tailWord_6787047 prefixEnd_6787047 3485017335655812381099445 := by
  unfold tailWord_6787047
  simp only [CollatzResearch.WordTrace]
  refine ⟨247543940642695329189231395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165029293761796886126154263 247543940642695329189231395)
  ·
    refine ⟨371315910964042993783847093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247543940642695329189231395 371315910964042993783847093)
    ·
      refine ⟨34810866652879030667235665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 371315910964042993783847093 34810866652879030667235665)
      ·
        refine ⟨26108149989659273000426749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34810866652879030667235665 26108149989659273000426749)
        ·
          refine ⟨9790556246122227375160031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26108149989659273000426749 9790556246122227375160031)
          ·
            refine ⟨14685834369183341062740047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9790556246122227375160031 14685834369183341062740047)
            ·
              refine ⟨22028751553775011594110071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14685834369183341062740047 22028751553775011594110071)
              ·
                refine ⟨33043127330662517391165107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22028751553775011594110071 33043127330662517391165107)
                ·
                  refine ⟨49564690995993776086747661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33043127330662517391165107 49564690995993776086747661)
                  ·
                    refine ⟨18586759123497666032530373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49564690995993776086747661 18586759123497666032530373)
                    ·
                      refine ⟨3485017335655812381099445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18586759123497666032530373 3485017335655812381099445)
                      ·
                        rfl

theorem cell23_6787047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_6787047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787047 prefixEnd_6787047 := by exact prefixLift 6787047
  have htrace : WordTrace (prefixWord ++ tailWord_6787047) baseStart_6787047 baseEnd_6787047 := by
    simpa [prefixWord, tailWord_6787047, baseEnd_6787047] using wordTrace_append hprefix tailTrace_6787047
  have hstable : (prefixWord ++ tailWord_6787047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787047).length < 2 ^ (prefixWord ++ tailWord_6787047).sum := by decide
  have hdescent : baseEnd_6787047 < baseStart_6787047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787063 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_6787063 : Nat := 118140960795 + 6787063 * 2 ^ 59
def prefixEnd_6787063 : Nat := 4983230072969 + 3 ^ 40 * 6787063 * 2
def baseEnd_6787063 : Nat := 3485025551346284318499371

theorem tailTrace_6787063 : CollatzResearch.WordTrace tailWord_6787063 prefixEnd_6787063 3485025551346284318499371 := by
  unfold tailWord_6787063
  simp only [CollatzResearch.WordTrace]
  refine ⟨247544524210637363921813843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165029682807091575947875895 247544524210637363921813843)
  ·
    refine ⟨371316786315956045882720765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247544524210637363921813843 371316786315956045882720765)
    ·
      refine ⟨139243794868483517206020287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371316786315956045882720765 139243794868483517206020287)
      ·
        refine ⟨208865692302725275809030431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139243794868483517206020287 208865692302725275809030431)
        ·
          refine ⟨313298538454087913713545647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208865692302725275809030431 313298538454087913713545647)
          ·
            refine ⟨469947807681131870570318471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313298538454087913713545647 469947807681131870570318471)
            ·
              refine ⟨704921711521697805855477707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469947807681131870570318471 704921711521697805855477707)
              ·
                refine ⟨1057382567282546708783216561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704921711521697805855477707 1057382567282546708783216561)
                ·
                  refine ⟨793036925461910031587412421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1057382567282546708783216561 793036925461910031587412421)
                  ·
                    refine ⟨148694423524108130922639829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 793036925461910031587412421 148694423524108130922639829)
                    ·
                      refine ⟨3485025551346284318499371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148694423524108130922639829 3485025551346284318499371)
                      ·
                        rfl

theorem cell23_6787063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_6787063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787063 prefixEnd_6787063 := by exact prefixLift 6787063
  have htrace : WordTrace (prefixWord ++ tailWord_6787063) baseStart_6787063 baseEnd_6787063 := by
    simpa [prefixWord, tailWord_6787063, baseEnd_6787063] using wordTrace_append hprefix tailTrace_6787063
  have hstable : (prefixWord ++ tailWord_6787063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787063).length < 2 ^ (prefixWord ++ tailWord_6787063).sum := by decide
  have hdescent : baseEnd_6787063 < baseStart_6787063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787107 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 1, 5, 2]
def baseStart_6787107 : Nat := 118140960795 + 6787107 * 2 ^ 59
def prefixEnd_6787107 : Nat := 4983230072969 + 3 ^ 40 * 6787107 * 2
def baseEnd_6787107 : Nat := 3485048144495082146349169

theorem tailTrace_6787107 : CollatzResearch.WordTrace tailWord_6787107 prefixEnd_6787107 3485048144495082146349169 := by
  unfold tailWord_6787107
  simp only [CollatzResearch.WordTrace]
  refine ⟨247546129022477959436415575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165030752681651972957610383 247546129022477959436415575)
  ·
    refine ⟨371319193533716939154623363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247546129022477959436415575 371319193533716939154623363)
    ·
      refine ⟨556978790300575408731935045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371319193533716939154623363 556978790300575408731935045)
      ·
        refine ⟨104433523181357889137237821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 556978790300575408731935045 104433523181357889137237821)
        ·
          refine ⟨39162571193009208426464183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104433523181357889137237821 39162571193009208426464183)
          ·
            refine ⟨58743856789513812639696275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39162571193009208426464183 58743856789513812639696275)
            ·
              refine ⟨88115785184270718959544413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58743856789513812639696275 88115785184270718959544413)
              ·
                refine ⟨33043419444101519609829155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88115785184270718959544413 33043419444101519609829155)
                ·
                  refine ⟨49565129166152279414743733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33043419444101519609829155 49565129166152279414743733)
                  ·
                    refine ⟨4646730859326776195132225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49565129166152279414743733 4646730859326776195132225)
                    ·
                      refine ⟨3485048144495082146349169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4646730859326776195132225 3485048144495082146349169)
                      ·
                        rfl

theorem cell23_6787107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_6787107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787107 prefixEnd_6787107 := by exact prefixLift 6787107
  have htrace : WordTrace (prefixWord ++ tailWord_6787107) baseStart_6787107 baseEnd_6787107 := by
    simpa [prefixWord, tailWord_6787107, baseEnd_6787107] using wordTrace_append hprefix tailTrace_6787107
  have hstable : (prefixWord ++ tailWord_6787107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787107).length < 2 ^ (prefixWord ++ tailWord_6787107).sum := by decide
  have hdescent : baseEnd_6787107 < baseStart_6787107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787108 : List Nat := [2, 3, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_6787108 : Nat := 118140960795 + 6787108 * 2 ^ 59
def prefixEnd_6787108 : Nat := 4983230072969 + 3 ^ 40 * 6787108 * 2
def baseEnd_6787108 : Nat := 1161682885991912214145555

theorem tailTrace_6787108 : CollatzResearch.WordTrace tailWord_6787108 prefixEnd_6787108 1161682885991912214145555 := by
  unfold tailWord_6787108
  simp only [CollatzResearch.WordTrace]
  refine ⟨123773082747737168303600989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165030776996982891071467985 123773082747737168303600989)
  ·
    refine ⟨46414906030401438113850371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123773082747737168303600989 46414906030401438113850371)
    ·
      refine ⟨69622359045602157170775557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46414906030401438113850371 69622359045602157170775557)
      ·
        refine ⟨13054192321050404469520417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69622359045602157170775557 13054192321050404469520417)
        ·
          refine ⟨9790644240787803352140313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13054192321050404469520417 9790644240787803352140313)
          ·
            refine ⟨7342983180590852514105235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9790644240787803352140313 7342983180590852514105235)
            ·
              refine ⟨11014474770886278771157853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7342983180590852514105235 11014474770886278771157853)
              ·
                refine ⟨4130428039082354539184195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11014474770886278771157853 4130428039082354539184195)
                ·
                  refine ⟨6195642058623531808776293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130428039082354539184195 6195642058623531808776293)
                  ·
                    refine ⟨1161682885991912214145555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6195642058623531808776293 1161682885991912214145555)
                    ·
                      rfl

theorem cell23_6787108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_6787108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787108 prefixEnd_6787108 := by exact prefixLift 6787108
  have htrace : WordTrace (prefixWord ++ tailWord_6787108) baseStart_6787108 baseEnd_6787108 := by
    simpa [prefixWord, tailWord_6787108, baseEnd_6787108] using wordTrace_append hprefix tailTrace_6787108
  have hstable : (prefixWord ++ tailWord_6787108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787108).length < 2 ^ (prefixWord ++ tailWord_6787108).sum := by decide
  have hdescent : baseEnd_6787108 < baseStart_6787108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787147 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 2, 4]
def baseStart_6787147 : Nat := 118140960795 + 6787147 * 2 ^ 59
def prefixEnd_6787147 : Nat := 4983230072969 + 3 ^ 40 * 6787147 * 2
def baseEnd_6787147 : Nat := 1161689561240420663282995

theorem tailTrace_6787147 : CollatzResearch.WordTrace tailWord_6787147 prefixEnd_6787147 1161689561240420663282995 := by
  unfold tailWord_6787147
  simp only [CollatzResearch.WordTrace]
  refine ⟨247547587942333046267871695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165031725294888697511914463 247547587942333046267871695)
  ·
    refine ⟨371321381913499569401807543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247547587942333046267871695 371321381913499569401807543)
    ·
      refine ⟨556982072870249354102711315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371321381913499569401807543 556982072870249354102711315)
      ·
        refine ⟨835473109305374031154066973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556982072870249354102711315 835473109305374031154066973)
        ·
          refine ⟨313302415989515261682775115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 835473109305374031154066973 313302415989515261682775115)
          ·
            refine ⟨469953623984272892524162673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313302415989515261682775115 469953623984272892524162673)
            ·
              refine ⟨352465217988204669393122005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469953623984272892524162673 352465217988204669393122005)
              ·
                refine ⟨8260903546598546938901297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 352465217988204669393122005 8260903546598546938901297)
                ·
                  refine ⟨6195677659948910204175973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8260903546598546938901297 6195677659948910204175973)
                  ·
                    refine ⟨1161689561240420663282995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6195677659948910204175973 1161689561240420663282995)
                    ·
                      rfl

theorem cell23_6787147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 4].length) (baseStart_6787147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787147 prefixEnd_6787147 := by exact prefixLift 6787147
  have htrace : WordTrace (prefixWord ++ tailWord_6787147) baseStart_6787147 baseEnd_6787147 := by
    simpa [prefixWord, tailWord_6787147, baseEnd_6787147] using wordTrace_append hprefix tailTrace_6787147
  have hstable : (prefixWord ++ tailWord_6787147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787147).length < 2 ^ (prefixWord ++ tailWord_6787147).sum := by decide
  have hdescent : baseEnd_6787147 < baseStart_6787147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787154 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_6787154 : Nat := 118140960795 + 6787154 * 2 ^ 59
def prefixEnd_6787154 : Nat := 4983230072969 + 3 ^ 40 * 6787154 * 2
def baseEnd_6787154 : Nat := 3485072278085843462461453

theorem tailTrace_6787154 : CollatzResearch.WordTrace tailWord_6787154 prefixEnd_6787154 3485072278085843462461453 := by
  unfold tailWord_6787154
  simp only [CollatzResearch.WordTrace]
  refine ⟨61886960813326921615844129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165031895502205124308917677 61886960813326921615844129)
  ·
    refine ⟨46415220609995191211883097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61886960813326921615844129 46415220609995191211883097)
    ·
      refine ⟨34811415457496393408912323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46415220609995191211883097 34811415457496393408912323)
      ·
        refine ⟨52217123186244590113368485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34811415457496393408912323 52217123186244590113368485)
        ·
          refine ⟨9790710597420860646256591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52217123186244590113368485 9790710597420860646256591)
          ·
            refine ⟨14686065896131290969384887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9790710597420860646256591 14686065896131290969384887)
            ·
              refine ⟨22029098844196936454077331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14686065896131290969384887 22029098844196936454077331)
              ·
                refine ⟨33043648266295404681115997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22029098844196936454077331 33043648266295404681115997)
                ·
                  refine ⟨12391368099860776755418499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33043648266295404681115997 12391368099860776755418499)
                  ·
                    refine ⟨18587052149791165133127749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12391368099860776755418499 18587052149791165133127749)
                    ·
                      refine ⟨3485072278085843462461453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18587052149791165133127749 3485072278085843462461453)
                      ·
                        rfl

theorem cell23_6787154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_6787154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787154 prefixEnd_6787154 := by exact prefixLift 6787154
  have htrace : WordTrace (prefixWord ++ tailWord_6787154) baseStart_6787154 baseEnd_6787154 := by
    simpa [prefixWord, tailWord_6787154, baseEnd_6787154] using wordTrace_append hprefix tailTrace_6787154
  have hstable : (prefixWord ++ tailWord_6787154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787154).length < 2 ^ (prefixWord ++ tailWord_6787154).sum := by decide
  have hdescent : baseEnd_6787154 < baseStart_6787154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787158 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_6787158 : Nat := 118140960795 + 6787158 * 2 ^ 59
def prefixEnd_6787158 : Nat := 4983230072969 + 3 ^ 40 * 6787158 * 2
def baseEnd_6787158 : Nat := 3485074332008461446811435

theorem tailTrace_6787158 : CollatzResearch.WordTrace tailWord_6787158 prefixEnd_6787158 3485074332008461446811435 := by
  unfold tailWord_6787158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15471749321580824696657633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165031992763528796764348085 15471749321580824696657633)
  ·
    refine ⟨11603811991185618522493225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15471749321580824696657633 11603811991185618522493225)
    ·
      refine ⟨8702858993389213891869919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11603811991185618522493225 8702858993389213891869919)
      ·
        refine ⟨13054288490083820837804879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8702858993389213891869919 13054288490083820837804879)
        ·
          refine ⟨19581432735125731256707319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13054288490083820837804879 19581432735125731256707319)
          ·
            refine ⟨29372149102688596885060979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19581432735125731256707319 29372149102688596885060979)
            ·
              refine ⟨44058223654032895327591469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29372149102688596885060979 44058223654032895327591469)
              ·
                refine ⟨16521833870262335747846801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44058223654032895327591469 16521833870262335747846801)
                ·
                  refine ⟨12391375402696751810885101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16521833870262335747846801 12391375402696751810885101)
                  ·
                    refine ⟨4646765776011281929081913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12391375402696751810885101 4646765776011281929081913)
                    ·
                      refine ⟨3485074332008461446811435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4646765776011281929081913 3485074332008461446811435)
                      ·
                        rfl

theorem cell23_6787158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_6787158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787158 prefixEnd_6787158 := by exact prefixLift 6787158
  have htrace : WordTrace (prefixWord ++ tailWord_6787158) baseStart_6787158 baseEnd_6787158 := by
    simpa [prefixWord, tailWord_6787158, baseEnd_6787158] using wordTrace_append hprefix tailTrace_6787158
  have hstable : (prefixWord ++ tailWord_6787158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787158).length < 2 ^ (prefixWord ++ tailWord_6787158).sum := by decide
  have hdescent : baseEnd_6787158 < baseStart_6787158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787160 : List Nat := [2, 1, 2, 2, 1, 4, 2, 9]
def baseStart_6787160 : Nat := 118140960795 + 6787160 * 2 ^ 59
def prefixEnd_6787160 : Nat := 4983230072969 + 3 ^ 40 * 6787160 * 2
def baseEnd_6787160 : Nat := 129076865147028534777275

theorem tailTrace_6787160 : CollatzResearch.WordTrace tailWord_6787160 prefixEnd_6787160 129076865147028534777275 := by
  unfold tailWord_6787160
  simp only [CollatzResearch.WordTrace]
  refine ⟨123774031045642974744047467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165032041394190632992063289 123774031045642974744047467)
  ·
    refine ⟨185661046568464462116071201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123774031045642974744047467 185661046568464462116071201)
    ·
      refine ⟨139245784926348346587053401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185661046568464462116071201 139245784926348346587053401)
      ·
        refine ⟨104434338694761259940290051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139245784926348346587053401 104434338694761259940290051)
        ·
          refine ⟨156651508042141889910435077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104434338694761259940290051 156651508042141889910435077)
          ·
            refine ⟨29372157757901604358206577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156651508042141889910435077 29372157757901604358206577)
            ·
              refine ⟨22029118318426203268654933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29372157757901604358206577 22029118318426203268654933)
              ·
                refine ⟨129076865147028534777275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22029118318426203268654933 129076865147028534777275)
                ·
                  rfl

theorem cell23_6787160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 9].length) (baseStart_6787160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787160 prefixEnd_6787160 := by exact prefixLift 6787160
  have htrace : WordTrace (prefixWord ++ tailWord_6787160) baseStart_6787160 baseEnd_6787160 := by
    simpa [prefixWord, tailWord_6787160, baseEnd_6787160] using wordTrace_append hprefix tailTrace_6787160
  have hstable : (prefixWord ++ tailWord_6787160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787160).length < 2 ^ (prefixWord ++ tailWord_6787160).sum := by decide
  have hdescent : baseEnd_6787160 < baseStart_6787160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787200 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_6787200 : Nat := 118140960795 + 6787200 * 2 ^ 59
def prefixEnd_6787200 : Nat := 4983230072969 + 3 ^ 40 * 6787200 * 2
def baseEnd_6787200 : Nat := 3485095898195950282486241

theorem tailTrace_6787200 : CollatzResearch.WordTrace tailWord_6787200 prefixEnd_6787200 3485095898195950282486241 := by
  unfold tailWord_6787200
  simp only [CollatzResearch.WordTrace]
  refine ⟨123774760505570518159775527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165033014007427357546367369 123774760505570518159775527)
  ·
    refine ⟨185662140758355777239663291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123774760505570518159775527 185662140758355777239663291)
    ·
      refine ⟨278493211137533665859494937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185662140758355777239663291 278493211137533665859494937)
      ·
        refine ⟨208869908353150249394621203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278493211137533665859494937 208869908353150249394621203)
        ·
          refine ⟨313304862529725374091931805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208869908353150249394621203 313304862529725374091931805)
          ·
            refine ⟨117489323448647015284474427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313304862529725374091931805 117489323448647015284474427)
            ·
              refine ⟨176233985172970522926711641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117489323448647015284474427 176233985172970522926711641)
              ·
                refine ⟨132175488879727892195033731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176233985172970522926711641 132175488879727892195033731)
                ·
                  refine ⟨198263233319591838292550597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132175488879727892195033731 198263233319591838292550597)
                  ·
                    refine ⟨37174356247423469679853237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198263233319591838292550597 37174356247423469679853237)
                    ·
                      refine ⟨3485095898195950282486241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37174356247423469679853237 3485095898195950282486241)
                      ·
                        rfl

theorem cell23_6787200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_6787200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787200 prefixEnd_6787200 := by exact prefixLift 6787200
  have htrace : WordTrace (prefixWord ++ tailWord_6787200) baseStart_6787200 baseEnd_6787200 := by
    simpa [prefixWord, tailWord_6787200, baseEnd_6787200] using wordTrace_append hprefix tailTrace_6787200
  have hstable : (prefixWord ++ tailWord_6787200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787200).length < 2 ^ (prefixWord ++ tailWord_6787200).sum := by decide
  have hdescent : baseEnd_6787200 < baseStart_6787200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787204 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_6787204 : Nat := 118140960795 + 6787204 * 2 ^ 59
def prefixEnd_6787204 : Nat := 4983230072969 + 3 ^ 40 * 6787204 * 2
def baseEnd_6787204 : Nat := 3485097952118568266836223

theorem tailTrace_6787204 : CollatzResearch.WordTrace tailWord_6787204 prefixEnd_6787204 3485097952118568266836223 := by
  unfold tailWord_6787204
  simp only [CollatzResearch.WordTrace]
  refine ⟨123774833451563272501348333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165033111268751030001797777 123774833451563272501348333)
  ·
    refine ⟨46415562544336227188005625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123774833451563272501348333 46415562544336227188005625)
    ·
      refine ⟨34811671908252170391004219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46415562544336227188005625 34811671908252170391004219)
      ·
        refine ⟨52217507862378255586506329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34811671908252170391004219 52217507862378255586506329)
        ·
          refine ⟨39163130896783691689879747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52217507862378255586506329 39163130896783691689879747)
          ·
            refine ⟨58744696345175537534819621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39163130896783691689879747 58744696345175537534819621)
            ·
              refine ⟨11014630564720413287778679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58744696345175537534819621 11014630564720413287778679)
              ·
                refine ⟨16521945847080619931668019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11014630564720413287778679 16521945847080619931668019)
                ·
                  refine ⟨24782918770620929897502029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16521945847080619931668019 24782918770620929897502029)
                  ·
                    refine ⟨9293594538982848711563261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24782918770620929897502029 9293594538982848711563261)
                    ·
                      refine ⟨3485097952118568266836223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9293594538982848711563261 3485097952118568266836223)
                      ·
                        rfl

theorem cell23_6787204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_6787204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787204 prefixEnd_6787204 := by exact prefixLift 6787204
  have htrace : WordTrace (prefixWord ++ tailWord_6787204) baseStart_6787204 baseEnd_6787204 := by
    simpa [prefixWord, tailWord_6787204, baseEnd_6787204] using wordTrace_append hprefix tailTrace_6787204
  have hstable : (prefixWord ++ tailWord_6787204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787204).length < 2 ^ (prefixWord ++ tailWord_6787204).sum := by decide
  have hdescent : baseEnd_6787204 < baseStart_6787204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787222 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_6787222 : Nat := 118140960795 + 6787222 * 2 ^ 59
def prefixEnd_6787222 : Nat := 4983230072969 + 3 ^ 40 * 6787222 * 2
def baseEnd_6787222 : Nat := 3485107194770349196411141

theorem tailTrace_6787222 : CollatzResearch.WordTrace tailWord_6787222 prefixEnd_6787222 3485107194770349196411141 := by
  unfold tailWord_6787222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15471895213566333379803245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165033548944707556051234613 15471895213566333379803245)
  ·
    refine ⟨5801960705087375017426217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15471895213566333379803245 5801960705087375017426217)
    ·
      refine ⟨4351470528815531263069663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5801960705087375017426217 4351470528815531263069663)
      ·
        refine ⟨6527205793223296894604495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4351470528815531263069663 6527205793223296894604495)
        ·
          refine ⟨9790808689834945341906743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6527205793223296894604495 9790808689834945341906743)
          ·
            refine ⟨14686213034752418012860115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9790808689834945341906743 14686213034752418012860115)
            ·
              refine ⟨22029319552128627019290173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14686213034752418012860115 22029319552128627019290173)
              ·
                refine ⟨8260994832048235132233815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22029319552128627019290173 8260994832048235132233815)
                ·
                  refine ⟨12391492248072352698350723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8260994832048235132233815 12391492248072352698350723)
                  ·
                    refine ⟨18587238372108529047526085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12391492248072352698350723 18587238372108529047526085)
                    ·
                      refine ⟨3485107194770349196411141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18587238372108529047526085 3485107194770349196411141)
                      ·
                        rfl

theorem cell23_6787222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_6787222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787222 prefixEnd_6787222 := by exact prefixLift 6787222
  have htrace : WordTrace (prefixWord ++ tailWord_6787222) baseStart_6787222 baseEnd_6787222 := by
    simpa [prefixWord, tailWord_6787222, baseEnd_6787222] using wordTrace_append hprefix tailTrace_6787222
  have hstable : (prefixWord ++ tailWord_6787222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787222).length < 2 ^ (prefixWord ++ tailWord_6787222).sum := by decide
  have hdescent : baseEnd_6787222 < baseStart_6787222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787252 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_6787252 : Nat := 118140960795 + 6787252 * 2 ^ 59
def prefixEnd_6787252 : Nat := 4983230072969 + 3 ^ 40 * 6787252 * 2
def baseEnd_6787252 : Nat := 3485122599189984079036003

theorem tailTrace_6787252 : CollatzResearch.WordTrace tailWord_6787252 prefixEnd_6787252 3485122599189984079036003 := by
  unfold tailWord_6787252
  simp only [CollatzResearch.WordTrace]
  refine ⟨123775708803476324600222005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165034278404635099466962673 123775708803476324600222005)
  ·
    refine ⟨11603972700325905431270813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123775708803476324600222005 11603972700325905431270813)
    ·
      refine ⟨4351489762622214536726555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11603972700325905431270813 4351489762622214536726555)
      ·
        refine ⟨6527234643933321805089833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4351489762622214536726555 6527234643933321805089833)
        ·
          refine ⟨4895425982949991353817375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6527234643933321805089833 4895425982949991353817375)
          ·
            refine ⟨7343138974424987030726063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895425982949991353817375 7343138974424987030726063)
            ·
              refine ⟨11014708461637480546089095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343138974424987030726063 11014708461637480546089095)
              ·
                refine ⟨16522062692456220819133643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11014708461637480546089095 16522062692456220819133643)
                ·
                  refine ⟨24783094038684331228700465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16522062692456220819133643 24783094038684331228700465)
                  ·
                    refine ⟨18587320529013248421525349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24783094038684331228700465 18587320529013248421525349)
                    ·
                      refine ⟨3485122599189984079036003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18587320529013248421525349 3485122599189984079036003)
                      ·
                        rfl

theorem cell23_6787252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_6787252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787252 prefixEnd_6787252 := by exact prefixLift 6787252
  have htrace : WordTrace (prefixWord ++ tailWord_6787252) baseStart_6787252 baseEnd_6787252 := by
    simpa [prefixWord, tailWord_6787252, baseEnd_6787252] using wordTrace_append hprefix tailTrace_6787252
  have hstable : (prefixWord ++ tailWord_6787252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787252).length < 2 ^ (prefixWord ++ tailWord_6787252).sum := by decide
  have hdescent : baseEnd_6787252 < baseStart_6787252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787257 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 4]
def baseStart_6787257 : Nat := 118140960795 + 6787257 * 2 ^ 59
def prefixEnd_6787257 : Nat := 4983230072969 + 3 ^ 40 * 6787257 * 2
def baseEnd_6787257 : Nat := 3485125166593256559473479

theorem tailTrace_6787257 : CollatzResearch.WordTrace tailWord_6787257 prefixEnd_6787257 3485125166593256559473479 := by
  unfold tailWord_6787257
  simp only [CollatzResearch.WordTrace]
  refine ⟨247551599971934535054376025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165034399981289690036250683 247551599971934535054376025)
  ·
    refine ⟨185663699978950901290782019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247551599971934535054376025 185663699978950901290782019)
    ·
      refine ⟨278495549968426351936173029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185663699978950901290782019 278495549968426351936173029)
      ·
        refine ⟨52217915619079940988032443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278495549968426351936173029 52217915619079940988032443)
        ·
          refine ⟨78326873428619911482048665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52217915619079940988032443 78326873428619911482048665)
          ·
            refine ⟨58745155071464933611536499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78326873428619911482048665 58745155071464933611536499)
            ·
              refine ⟨88117732607197400417304749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58745155071464933611536499 88117732607197400417304749)
              ·
                refine ⟨33044149727699025156489281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88117732607197400417304749 33044149727699025156489281)
                ·
                  refine ⟨24783112295774268867366961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33044149727699025156489281 24783112295774268867366961)
                  ·
                    refine ⟨18587334221830701650525221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24783112295774268867366961 18587334221830701650525221)
                    ·
                      refine ⟨3485125166593256559473479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18587334221830701650525221 3485125166593256559473479)
                      ·
                        rfl

theorem cell23_6787257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_6787257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787257 prefixEnd_6787257 := by exact prefixLift 6787257
  have htrace : WordTrace (prefixWord ++ tailWord_6787257) baseStart_6787257 baseEnd_6787257 := by
    simpa [prefixWord, tailWord_6787257, baseEnd_6787257] using wordTrace_append hprefix tailTrace_6787257
  have hstable : (prefixWord ++ tailWord_6787257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787257).length < 2 ^ (prefixWord ++ tailWord_6787257).sum := by decide
  have hdescent : baseEnd_6787257 < baseStart_6787257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787265 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_6787265 : Nat := 118140960795 + 6787265 * 2 ^ 59
def prefixEnd_6787265 : Nat := 4983230072969 + 3 ^ 40 * 6787265 * 2
def baseEnd_6787265 : Nat := 3485129274438492528173443

theorem tailTrace_6787265 : CollatzResearch.WordTrace tailWord_6787265 prefixEnd_6787265 3485129274438492528173443 := by
  unfold tailWord_6787265
  simp only [CollatzResearch.WordTrace]
  refine ⟨247551891755905552420667249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165034594503937034947111499 247551891755905552420667249)
  ·
    refine ⟨185663918816929164315500437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247551891755905552420667249 185663918816929164315500437)
    ·
      refine ⟨8702996194543554577289083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185663918816929164315500437 8702996194543554577289083)
      ·
        refine ⟨13054494291815331865933625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8702996194543554577289083 13054494291815331865933625)
        ·
          refine ⟨9790870718861498899450219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13054494291815331865933625 9790870718861498899450219)
          ·
            refine ⟨14686306078292248349175329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9790870718861498899450219 14686306078292248349175329)
            ·
              refine ⟨11014729558719186261881497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14686306078292248349175329 11014729558719186261881497)
              ·
                refine ⟨8261047169039389696411123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11014729558719186261881497 8261047169039389696411123)
                ·
                  refine ⟨12391570753559084544616685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8261047169039389696411123 12391570753559084544616685)
                  ·
                    refine ⟨4646839032584656704231257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12391570753559084544616685 4646839032584656704231257)
                    ·
                      refine ⟨3485129274438492528173443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4646839032584656704231257 3485129274438492528173443)
                      ·
                        rfl

theorem cell23_6787265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_6787265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787265 prefixEnd_6787265 := by exact prefixLift 6787265
  have htrace : WordTrace (prefixWord ++ tailWord_6787265) baseStart_6787265 baseEnd_6787265 := by
    simpa [prefixWord, tailWord_6787265, baseEnd_6787265] using wordTrace_append hprefix tailTrace_6787265
  have hstable : (prefixWord ++ tailWord_6787265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787265).length < 2 ^ (prefixWord ++ tailWord_6787265).sum := by decide
  have hdescent : baseEnd_6787265 < baseStart_6787265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787307 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 5]
def baseStart_6787307 : Nat := 118140960795 + 6787307 * 2 ^ 59
def prefixEnd_6787307 : Nat := 4983230072969 + 3 ^ 40 * 6787307 * 2
def baseEnd_6787307 : Nat := 3485150840625981363848249

theorem tailTrace_6787307 : CollatzResearch.WordTrace tailWord_6787307 prefixEnd_6787307 3485150840625981363848249 := by
  unfold tailWord_6787307
  simp only [CollatzResearch.WordTrace]
  refine ⟨247553423621753393593696175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165035615747835595729130783 247553423621753393593696175)
  ·
    refine ⟨371330135432630090390544263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247553423621753393593696175 371330135432630090390544263)
    ·
      refine ⟨556995203148945135585816395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371330135432630090390544263 556995203148945135585816395)
      ·
        refine ⟨835492804723417703378724593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556995203148945135585816395 835492804723417703378724593)
        ·
          refine ⟨626619603542563277534043445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835492804723417703378724593 626619603542563277534043445)
          ·
            refine ⟨58745587832115307268816573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 626619603542563277534043445 58745587832115307268816573)
            ·
              refine ⟨22029595437043240225806215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58745587832115307268816573 22029595437043240225806215)
              ·
                refine ⟨33044393155564860338709323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22029595437043240225806215 33044393155564860338709323)
                ·
                  refine ⟨49566589733347290508063985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33044393155564860338709323 49566589733347290508063985)
                  ·
                    refine ⟨37174942300010467881047989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49566589733347290508063985 37174942300010467881047989)
                    ·
                      refine ⟨3485150840625981363848249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37174942300010467881047989 3485150840625981363848249)
                      ·
                        rfl

theorem cell23_6787307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 5].length) (baseStart_6787307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787307 prefixEnd_6787307 := by exact prefixLift 6787307
  have htrace : WordTrace (prefixWord ++ tailWord_6787307) baseStart_6787307 baseEnd_6787307 := by
    simpa [prefixWord, tailWord_6787307, baseEnd_6787307] using wordTrace_append hprefix tailTrace_6787307
  have hstable : (prefixWord ++ tailWord_6787307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787307).length < 2 ^ (prefixWord ++ tailWord_6787307).sum := by decide
  have hdescent : baseEnd_6787307 < baseStart_6787307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787368 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_6787368 : Nat := 118140960795 + 6787368 * 2 ^ 59
def prefixEnd_6787368 : Nat := 4983230072969 + 3 ^ 40 * 6787368 * 2
def baseEnd_6787368 : Nat := 3485182162945905625185469

theorem tailTrace_6787368 : CollatzResearch.WordTrace tailWord_6787368 prefixEnd_6787368 3485182162945905625185469 := by
  unfold tailWord_6787368
  simp only [CollatzResearch.WordTrace]
  refine ⟨123777824237266200505833379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165037098983021600674444505 123777824237266200505833379)
  ·
    refine ⟨185666736355899300758750069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123777824237266200505833379 185666736355899300758750069)
    ·
      refine ⟨17406256533365559446132819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185666736355899300758750069 17406256533365559446132819)
      ·
        refine ⟨26109384800048339169199229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17406256533365559446132819 26109384800048339169199229)
        ·
          refine ⟨9791019300018127188449711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26109384800048339169199229 9791019300018127188449711)
          ·
            refine ⟨14686528950027190782674567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9791019300018127188449711 14686528950027190782674567)
            ·
              refine ⟨22029793425040786174011851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14686528950027190782674567 22029793425040786174011851)
              ·
                refine ⟨33044690137561179261017777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22029793425040786174011851 33044690137561179261017777)
                ·
                  refine ⟨24783517603170884445763333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33044690137561179261017777 24783517603170884445763333)
                  ·
                    refine ⟨4646909550594540833580625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24783517603170884445763333 4646909550594540833580625)
                    ·
                      refine ⟨3485182162945905625185469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4646909550594540833580625 3485182162945905625185469)
                      ·
                        rfl

theorem cell23_6787368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_6787368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787368 prefixEnd_6787368 := by exact prefixLift 6787368
  have htrace : WordTrace (prefixWord ++ tailWord_6787368) baseStart_6787368 baseEnd_6787368 := by
    simpa [prefixWord, tailWord_6787368, baseEnd_6787368] using wordTrace_append hprefix tailTrace_6787368
  have hstable : (prefixWord ++ tailWord_6787368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787368).length < 2 ^ (prefixWord ++ tailWord_6787368).sum := by decide
  have hdescent : baseEnd_6787368 < baseStart_6787368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787397 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_6787397 : Nat := 118140960795 + 6787397 * 2 ^ 59
def prefixEnd_6787397 : Nat := 4983230072969 + 3 ^ 40 * 6787397 * 2
def baseEnd_6787397 : Nat := 3485197053884886011722835

theorem tailTrace_6787397 : CollatzResearch.WordTrace tailWord_6787397 prefixEnd_6787397 3485197053884886011722835 := by
  unfold tailWord_6787397
  simp only [CollatzResearch.WordTrace]
  refine ⟨247556706191427338964472445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165037804127618225976314963 247556706191427338964472445)
  ·
    refine ⟨92833764821785252111677167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247556706191427338964472445 92833764821785252111677167)
    ·
      refine ⟨139250647232677878167515751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92833764821785252111677167 139250647232677878167515751)
      ·
        refine ⟨208875970849016817251273627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139250647232677878167515751 208875970849016817251273627)
        ·
          refine ⟨313313956273525225876910441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208875970849016817251273627 313313956273525225876910441)
          ·
            refine ⟨234985467205143919407682831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313313956273525225876910441 234985467205143919407682831)
            ·
              refine ⟨352478200807715879111524247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234985467205143919407682831 352478200807715879111524247)
              ·
                refine ⟨528717301211573818667286371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352478200807715879111524247 528717301211573818667286371)
                ·
                  refine ⟨793075951817360728000929557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528717301211573818667286371 793075951817360728000929557)
                  ·
                    refine ⟨37175435241438784125043573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 793075951817360728000929557 37175435241438784125043573)
                    ·
                      refine ⟨3485197053884886011722835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37175435241438784125043573 3485197053884886011722835)
                      ·
                        rfl

theorem cell23_6787397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_6787397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787397 prefixEnd_6787397 := by exact prefixLift 6787397
  have htrace : WordTrace (prefixWord ++ tailWord_6787397) baseStart_6787397 baseEnd_6787397 := by
    simpa [prefixWord, tailWord_6787397, baseEnd_6787397] using wordTrace_append hprefix tailTrace_6787397
  have hstable : (prefixWord ++ tailWord_6787397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787397).length < 2 ^ (prefixWord ++ tailWord_6787397).sum := by decide
  have hdescent : baseEnd_6787397 < baseStart_6787397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787495 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_6787495 : Nat := 118140960795 + 6787495 * 2 ^ 59
def prefixEnd_6787495 : Nat := 4983230072969 + 3 ^ 40 * 6787495 * 2
def baseEnd_6787495 : Nat := 3485247374989026628297385

theorem tailTrace_6787495 : CollatzResearch.WordTrace tailWord_6787495 prefixEnd_6787495 3485247374989026628297385 := by
  unfold tailWord_6787495
  simp only [CollatzResearch.WordTrace]
  refine ⟨247560280545072301701539939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165040187030048201134359959 247560280545072301701539939)
  ·
    refine ⟨371340420817608452552309909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247560280545072301701539939 371340420817608452552309909)
    ·
      refine ⟨17406582225825396213389527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 371340420817608452552309909 17406582225825396213389527)
      ·
        refine ⟨26109873338738094320084291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17406582225825396213389527 26109873338738094320084291)
        ·
          refine ⟨39164810008107141480126437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26109873338738094320084291 39164810008107141480126437)
          ·
            refine ⟨7343401876520089027523707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39164810008107141480126437 7343401876520089027523707)
            ·
              refine ⟨11015102814780133541285561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343401876520089027523707 11015102814780133541285561)
              ·
                refine ⟨8261327111085100155964171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11015102814780133541285561 8261327111085100155964171)
                ·
                  refine ⟨12391990666627650233946257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8261327111085100155964171 12391990666627650233946257)
                  ·
                    refine ⟨9293992999970737675459693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12391990666627650233946257 9293992999970737675459693)
                    ·
                      refine ⟨3485247374989026628297385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9293992999970737675459693 3485247374989026628297385)
                      ·
                        rfl

theorem cell23_6787495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_6787495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787495 prefixEnd_6787495 := by exact prefixLift 6787495
  have htrace : WordTrace (prefixWord ++ tailWord_6787495) baseStart_6787495 baseEnd_6787495 := by
    simpa [prefixWord, tailWord_6787495, baseEnd_6787495] using wordTrace_append hprefix tailTrace_6787495
  have hstable : (prefixWord ++ tailWord_6787495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787495).length < 2 ^ (prefixWord ++ tailWord_6787495).sum := by decide
  have hdescent : baseEnd_6787495 < baseStart_6787495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787514 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_6787514 : Nat := 118140960795 + 6787514 * 2 ^ 59
def prefixEnd_6787514 : Nat := 4983230072969 + 3 ^ 40 * 6787514 * 2
def baseEnd_6787514 : Nat := 3485257131121462053959797

theorem tailTrace_6787514 : CollatzResearch.WordTrace tailWord_6787514 prefixEnd_6787514 3485257131121462053959797 := by
  unfold tailWord_6787514
  simp only [CollatzResearch.WordTrace]
  refine ⟨61890243383000866986620399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165040649021335645297654397 61890243383000866986620399)
  ·
    refine ⟨92835365074501300479930599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61890243383000866986620399 92835365074501300479930599)
    ·
      refine ⟨139253047611751950719895899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92835365074501300479930599 139253047611751950719895899)
      ·
        refine ⟨208879571417627926079843849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139253047611751950719895899 208879571417627926079843849)
        ·
          refine ⟨156659678563220944559882887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208879571417627926079843849 156659678563220944559882887)
          ·
            refine ⟨234989517844831416839824331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156659678563220944559882887 234989517844831416839824331)
            ·
              refine ⟨352484276767247125259736497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234989517844831416839824331 352484276767247125259736497)
              ·
                refine ⟨264363207575435343944802373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352484276767247125259736497 264363207575435343944802373)
                ·
                  refine ⟨49568101420394126989650445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264363207575435343944802373 49568101420394126989650445)
                  ·
                    refine ⟨18588038032647797621118917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49568101420394126989650445 18588038032647797621118917)
                    ·
                      refine ⟨3485257131121462053959797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18588038032647797621118917 3485257131121462053959797)
                      ·
                        rfl

theorem cell23_6787514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_6787514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787514 prefixEnd_6787514 := by exact prefixLift 6787514
  have htrace : WordTrace (prefixWord ++ tailWord_6787514) baseStart_6787514 baseEnd_6787514 := by
    simpa [prefixWord, tailWord_6787514, baseEnd_6787514] using wordTrace_append hprefix tailTrace_6787514
  have hstable : (prefixWord ++ tailWord_6787514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787514).length < 2 ^ (prefixWord ++ tailWord_6787514).sum := by decide
  have hdescent : baseEnd_6787514 < baseStart_6787514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787531 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 5, 4, 2]
def baseStart_6787531 : Nat := 118140960795 + 6787531 * 2 ^ 59
def prefixEnd_6787531 : Nat := 4983230072969 + 3 ^ 40 * 6787531 * 2
def baseEnd_6787531 : Nat := 3485265860292588487447219

theorem tailTrace_6787531 : CollatzResearch.WordTrace tailWord_6787531 prefixEnd_6787531 3485265860292588487447219 := by
  unfold tailWord_6787531
  simp only [CollatzResearch.WordTrace]
  refine ⟨247561593572941879849850447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165041062381961253233233631 247561593572941879849850447)
  ·
    refine ⟨371342390359412819774775671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247561593572941879849850447 371342390359412819774775671)
    ·
      refine ⟨557013585539119229662163507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371342390359412819774775671 557013585539119229662163507)
      ·
        refine ⟨835520378308678844493245261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557013585539119229662163507 835520378308678844493245261)
        ·
          refine ⟨313320141865754566684966973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 835520378308678844493245261 313320141865754566684966973)
          ·
            refine ⟨117495053199657962506862615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313320141865754566684966973 117495053199657962506862615)
            ·
              refine ⟨176242579799486943760293923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117495053199657962506862615 176242579799486943760293923)
              ·
                refine ⟨264363869699230415640440885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176242579799486943760293923 264363869699230415640440885)
                ·
                  refine ⟨24784112784302851466291333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264363869699230415640440885 24784112784302851466291333)
                  ·
                    refine ⟨4647021147056784649929625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24784112784302851466291333 4647021147056784649929625)
                    ·
                      refine ⟨3485265860292588487447219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647021147056784649929625 3485265860292588487447219)
                      ·
                        rfl

theorem cell23_6787531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 4, 2].length) (baseStart_6787531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787531 prefixEnd_6787531 := by exact prefixLift 6787531
  have htrace : WordTrace (prefixWord ++ tailWord_6787531) baseStart_6787531 baseEnd_6787531 := by
    simpa [prefixWord, tailWord_6787531, baseEnd_6787531] using wordTrace_append hprefix tailTrace_6787531
  have hstable : (prefixWord ++ tailWord_6787531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787531).length < 2 ^ (prefixWord ++ tailWord_6787531).sum := by decide
  have hdescent : baseEnd_6787531 < baseStart_6787531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787541 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_6787541 : Nat := 118140960795 + 6787541 * 2 ^ 59
def prefixEnd_6787541 : Nat := 4983230072969 + 3 ^ 40 * 6787541 * 2
def baseEnd_6787541 : Nat := 1161756998366377816107391

theorem tailTrace_6787541 : CollatzResearch.WordTrace tailWord_6787541 prefixEnd_6787541 1161756998366377816107391 := by
  unfold tailWord_6787541
  simp only [CollatzResearch.WordTrace]
  refine ⟨247561958302905651557714477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165041305535270434371809651 247561958302905651557714477)
  ·
    refine ⟨92835734363589619334142929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247561958302905651557714477 92835734363589619334142929)
    ·
      refine ⟨69626800772692214500607197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92835734363589619334142929 69626800772692214500607197)
      ·
        refine ⟨26110050289759580437727699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69626800772692214500607197 26110050289759580437727699)
        ·
          refine ⟨39165075434639370656591549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26110050289759580437727699 39165075434639370656591549)
          ·
            refine ⟨14686903287989763996221831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39165075434639370656591549 14686903287989763996221831)
            ·
              refine ⟨22030354931984645994332747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14686903287989763996221831 22030354931984645994332747)
              ·
                refine ⟨33045532397976968991499121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22030354931984645994332747 33045532397976968991499121)
                ·
                  refine ⟨24784149298482726743624341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33045532397976968991499121 24784149298482726743624341)
                  ·
                    refine ⟨1161756998366377816107391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24784149298482726743624341 1161756998366377816107391)
                    ·
                      rfl

theorem cell23_6787541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_6787541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787541 prefixEnd_6787541 := by exact prefixLift 6787541
  have htrace : WordTrace (prefixWord ++ tailWord_6787541) baseStart_6787541 baseEnd_6787541 := by
    simpa [prefixWord, tailWord_6787541, baseEnd_6787541] using wordTrace_append hprefix tailTrace_6787541
  have hstable : (prefixWord ++ tailWord_6787541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787541).length < 2 ^ (prefixWord ++ tailWord_6787541).sum := by decide
  have hdescent : baseEnd_6787541 < baseStart_6787541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787565 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_6787565 : Nat := 118140960795 + 6787565 * 2 ^ 59
def prefixEnd_6787565 : Nat := 4983230072969 + 3 ^ 40 * 6787565 * 2
def baseEnd_6787565 : Nat := 3485283318634841354422063

theorem tailTrace_6787565 : CollatzResearch.WordTrace tailWord_6787565 prefixEnd_6787565 3485283318634841354422063 := by
  unfold tailWord_6787565
  simp only [CollatzResearch.WordTrace]
  refine ⟨247562833654818703656588149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165041889103212469104392099 247562833654818703656588149)
  ·
    refine ⟨23209015655139253467805139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247562833654818703656588149 23209015655139253467805139)
    ·
      refine ⟨34813523482708880201707709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23209015655139253467805139 34813523482708880201707709)
      ·
        refine ⟨13055071306015830075640391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34813523482708880201707709 13055071306015830075640391)
        ·
          refine ⟨19582606959023745113460587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055071306015830075640391 19582606959023745113460587)
          ·
            refine ⟨29373910438535617670190881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19582606959023745113460587 29373910438535617670190881)
            ·
              refine ⟨22030432828901713252643161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29373910438535617670190881 22030432828901713252643161)
              ·
                refine ⟨16522824621676284939482371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22030432828901713252643161 16522824621676284939482371)
                ·
                  refine ⟨24784236932514427409223557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16522824621676284939482371 24784236932514427409223557)
                  ·
                    refine ⟨4647044424846455139229417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24784236932514427409223557 4647044424846455139229417)
                    ·
                      refine ⟨3485283318634841354422063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647044424846455139229417 3485283318634841354422063)
                      ·
                        rfl

theorem cell23_6787565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_6787565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787565 prefixEnd_6787565 := by exact prefixLift 6787565
  have htrace : WordTrace (prefixWord ++ tailWord_6787565) baseStart_6787565 baseEnd_6787565 := by
    simpa [prefixWord, tailWord_6787565, baseEnd_6787565] using wordTrace_append hprefix tailTrace_6787565
  have hstable : (prefixWord ++ tailWord_6787565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787565).length < 2 ^ (prefixWord ++ tailWord_6787565).sum := by decide
  have hdescent : baseEnd_6787565 < baseStart_6787565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787581 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_6787581 : Nat := 118140960795 + 6787581 * 2 ^ 59
def prefixEnd_6787581 : Nat := 4983230072969 + 3 ^ 40 * 6787581 * 2
def baseEnd_6787581 : Nat := 3485291534325313291821989

theorem tailTrace_6787581 : CollatzResearch.WordTrace tailWord_6787581 prefixEnd_6787581 3485291534325313291821989 := by
  unfold tailWord_6787581
  simp only [CollatzResearch.WordTrace]
  refine ⟨247563417222760738389170597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165042278148507158926113731 247563417222760738389170597)
  ·
    refine ⟨46418140729267638447969487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247563417222760738389170597 46418140729267638447969487)
    ·
      refine ⟨69627211093901457671954231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46418140729267638447969487 69627211093901457671954231)
      ·
        refine ⟨104440816640852186507931347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69627211093901457671954231 104440816640852186507931347)
        ·
          refine ⟨156661224961278279761897021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104440816640852186507931347 156661224961278279761897021)
          ·
            refine ⟨58747959360479354910711383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156661224961278279761897021 58747959360479354910711383)
            ·
              refine ⟨88121939040719032366067075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58747959360479354910711383 88121939040719032366067075)
              ·
                refine ⟨132182908561078548549100613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88121939040719032366067075 132182908561078548549100613)
                ·
                  refine ⟨24784295355202227852956365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132182908561078548549100613 24784295355202227852956365)
                  ·
                    refine ⟨9294110758200835444858637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24784295355202227852956365 9294110758200835444858637)
                    ·
                      refine ⟨3485291534325313291821989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9294110758200835444858637 3485291534325313291821989)
                      ·
                        rfl

theorem cell23_6787581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_6787581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787581 prefixEnd_6787581 := by exact prefixLift 6787581
  have htrace : WordTrace (prefixWord ++ tailWord_6787581) baseStart_6787581 baseEnd_6787581 := by
    simpa [prefixWord, tailWord_6787581, baseEnd_6787581] using wordTrace_append hprefix tailTrace_6787581
  have hstable : (prefixWord ++ tailWord_6787581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787581).length < 2 ^ (prefixWord ++ tailWord_6787581).sum := by decide
  have hdescent : baseEnd_6787581 < baseStart_6787581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787588 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 7]
def baseStart_6787588 : Nat := 118140960795 + 6787588 * 2 ^ 59
def prefixEnd_6787588 : Nat := 4983230072969 + 3 ^ 40 * 6787588 * 2
def baseEnd_6787588 : Nat := 387255014298877196048273

theorem tailTrace_6787588 : CollatzResearch.WordTrace tailWord_6787588 prefixEnd_6787588 387255014298877196048273 := by
  unfold tailWord_6787588
  simp only [CollatzResearch.WordTrace]
  refine ⟨123781836266867689292337709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165042448355823585723116945 123781836266867689292337709)
  ·
    refine ⟨46418188600075383484626641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123781836266867689292337709 46418188600075383484626641)
    ·
      refine ⟨34813641450056537613469981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46418188600075383484626641 34813641450056537613469981)
      ·
        refine ⟨13055115543771201605051243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34813641450056537613469981 13055115543771201605051243)
        ·
          refine ⟨19582673315656802407576865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055115543771201605051243 19582673315656802407576865)
          ·
            refine ⟨14687004986742601805682649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19582673315656802407576865 14687004986742601805682649)
            ·
              refine ⟨11015253740056951354261987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14687004986742601805682649 11015253740056951354261987)
              ·
                refine ⟨16522880610085427031392981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11015253740056951354261987 16522880610085427031392981)
                ·
                  refine ⟨387255014298877196048273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16522880610085427031392981 387255014298877196048273)
                  ·
                    rfl

theorem cell23_6787588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_6787588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787588 prefixEnd_6787588 := by exact prefixLift 6787588
  have htrace : WordTrace (prefixWord ++ tailWord_6787588) baseStart_6787588 baseEnd_6787588 := by
    simpa [prefixWord, tailWord_6787588, baseEnd_6787588] using wordTrace_append hprefix tailTrace_6787588
  have hstable : (prefixWord ++ tailWord_6787588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787588).length < 2 ^ (prefixWord ++ tailWord_6787588).sum := by decide
  have hdescent : baseEnd_6787588 < baseStart_6787588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787598 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_6787598 : Nat := 118140960795 + 6787598 * 2 ^ 59
def prefixEnd_6787598 : Nat := 4983230072969 + 3 ^ 40 * 6787598 * 2
def baseEnd_6787598 : Nat := 3485300263496439725309411

theorem tailTrace_6787598 : CollatzResearch.WordTrace tailWord_6787598 prefixEnd_6787598 3485300263496439725309411 := by
  unfold tailWord_6787598
  simp only [CollatzResearch.WordTrace]
  refine ⟨30945504657962393786567431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165042691509132766861692965 30945504657962393786567431)
  ·
    refine ⟨46418256986943590679851147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30945504657962393786567431 46418256986943590679851147)
    ·
      refine ⟨69627385480415386019776721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46418256986943590679851147 69627385480415386019776721)
      ·
        refine ⟨52220539110311539514832541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69627385480415386019776721 52220539110311539514832541)
        ·
          refine ⟨19582702166366827318062203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52220539110311539514832541 19582702166366827318062203)
          ·
            refine ⟨29374053249550240977093305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19582702166366827318062203 29374053249550240977093305)
            ·
              refine ⟨22030539937162680732819979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29374053249550240977093305 22030539937162680732819979)
              ·
                refine ⟨33045809905744021099229969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22030539937162680732819979 33045809905744021099229969)
                ·
                  refine ⟨24784357429308015824422477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33045809905744021099229969 24784357429308015824422477)
                  ·
                    refine ⟨9294134035990505934158429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24784357429308015824422477 9294134035990505934158429)
                    ·
                      refine ⟨3485300263496439725309411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9294134035990505934158429 3485300263496439725309411)
                      ·
                        rfl

theorem cell23_6787598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_6787598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787598 prefixEnd_6787598 := by exact prefixLift 6787598
  have htrace : WordTrace (prefixWord ++ tailWord_6787598) baseStart_6787598 baseEnd_6787598 := by
    simpa [prefixWord, tailWord_6787598, baseEnd_6787598] using wordTrace_append hprefix tailTrace_6787598
  have hstable : (prefixWord ++ tailWord_6787598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787598).length < 2 ^ (prefixWord ++ tailWord_6787598).sum := by decide
  have hdescent : baseEnd_6787598 < baseStart_6787598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787621 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_6787621 : Nat := 118140960795 + 6787621 * 2 ^ 59
def prefixEnd_6787621 : Nat := 4983230072969 + 3 ^ 40 * 6787621 * 2
def baseEnd_6787621 : Nat := 3485312073551493135321805

theorem tailTrace_6787621 : CollatzResearch.WordTrace tailWord_6787621 prefixEnd_6787621 3485312073551493135321805 := by
  unfold tailWord_6787621
  simp only [CollatzResearch.WordTrace]
  refine ⟨247564876142615825220626717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165043250761743883480417811 247564876142615825220626717)
  ·
    refine ⟨92836828553480934457735019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247564876142615825220626717 92836828553480934457735019)
    ·
      refine ⟨139255242830221401686602529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92836828553480934457735019 139255242830221401686602529)
      ·
        refine ⟨104441432122666051264951897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139255242830221401686602529 104441432122666051264951897)
        ·
          refine ⟨78331074091999538448713923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104441432122666051264951897 78331074091999538448713923)
          ·
            refine ⟨117496611137999307673070885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78331074091999538448713923 117496611137999307673070885)
            ·
              refine ⟨22030614588374870188700791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117496611137999307673070885 22030614588374870188700791)
              ·
                refine ⟨33045921882562305283051187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22030614588374870188700791 33045921882562305283051187)
                ·
                  refine ⟨49568882823843457924576781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33045921882562305283051187 49568882823843457924576781)
                  ·
                    refine ⟨18588331058941296721716293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49568882823843457924576781 18588331058941296721716293)
                    ·
                      refine ⟨3485312073551493135321805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18588331058941296721716293 3485312073551493135321805)
                      ·
                        rfl

theorem cell23_6787621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_6787621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787621 prefixEnd_6787621 := by exact prefixLift 6787621
  have htrace : WordTrace (prefixWord ++ tailWord_6787621) baseStart_6787621 baseEnd_6787621 := by
    simpa [prefixWord, tailWord_6787621, baseEnd_6787621] using wordTrace_append hprefix tailTrace_6787621
  have hstable : (prefixWord ++ tailWord_6787621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787621).length < 2 ^ (prefixWord ++ tailWord_6787621).sum := by decide
  have hdescent : baseEnd_6787621 < baseStart_6787621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787648 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 3, 4]
def baseStart_6787648 : Nat := 118140960795 + 6787648 * 2 ^ 59
def prefixEnd_6787648 : Nat := 4983230072969 + 3 ^ 40 * 6787648 * 2
def baseEnd_6787648 : Nat := 1161775312509721509894727

theorem tailTrace_6787648 : CollatzResearch.WordTrace tailWord_6787648 prefixEnd_6787648 1161775312509721509894727 := by
  unfold tailWord_6787648
  simp only [CollatzResearch.WordTrace]
  refine ⟨123782930456759004415929799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165043907275678672554573065 123782930456759004415929799)
  ·
    refine ⟨185674395685138506623894699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123782930456759004415929799 185674395685138506623894699)
    ·
      refine ⟨278511593527707759935842049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185674395685138506623894699 278511593527707759935842049)
      ·
        refine ⟨208883695145780819951881537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278511593527707759935842049 208883695145780819951881537)
        ·
          refine ⟨156662771359335614963911153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208883695145780819951881537 156662771359335614963911153)
          ·
            refine ⟨117497078519501711222933365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156662771359335614963911153 117497078519501711222933365)
            ·
              refine ⟨11015351111203285427150003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117497078519501711222933365 11015351111203285427150003)
              ·
                refine ⟨16523026666804928140725005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11015351111203285427150003 16523026666804928140725005)
                ·
                  refine ⟨6196135000051848052771877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16523026666804928140725005 6196135000051848052771877)
                  ·
                    refine ⟨1161775312509721509894727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196135000051848052771877 1161775312509721509894727)
                    ·
                      rfl

theorem cell23_6787648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3, 4].length) (baseStart_6787648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787648 prefixEnd_6787648 := by exact prefixLift 6787648
  have htrace : WordTrace (prefixWord ++ tailWord_6787648) baseStart_6787648 baseEnd_6787648 := by
    simpa [prefixWord, tailWord_6787648, baseEnd_6787648] using wordTrace_append hprefix tailTrace_6787648
  have hstable : (prefixWord ++ tailWord_6787648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787648).length < 2 ^ (prefixWord ++ tailWord_6787648).sum := by decide
  have hdescent : baseEnd_6787648 < baseStart_6787648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787722 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_6787722 : Nat := 118140960795 + 6787722 * 2 ^ 59
def prefixEnd_6787722 : Nat := 4983230072969 + 3 ^ 40 * 6787722 * 2
def baseEnd_6787722 : Nat := 3485363935097597240158841

theorem tailTrace_6787722 : CollatzResearch.WordTrace tailWord_6787722 prefixEnd_6787722 3485363935097597240158841 := by
  unfold tailWord_6787722
  simp only [CollatzResearch.WordTrace]
  refine ⟨61892139978812479867513355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165045706610166612980035613 61892139978812479867513355)
  ·
    refine ⟨92838209968218719801270033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61892139978812479867513355 92838209968218719801270033)
    ·
      refine ⟨69628657476164039850952525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92838209968218719801270033 69628657476164039850952525)
      ·
        refine ⟨26110746553561514944107197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69628657476164039850952525 26110746553561514944107197)
        ·
          refine ⟨9791529957585568104040199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26110746553561514944107197 9791529957585568104040199)
          ·
            refine ⟨14687294936378352156060299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9791529957585568104040199 14687294936378352156060299)
            ·
              refine ⟨22030942404567528234090449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14687294936378352156060299 22030942404567528234090449)
              ·
                refine ⟨16523206803425646175567837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22030942404567528234090449 16523206803425646175567837)
                ·
                  refine ⟨6196202551284617315837939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16523206803425646175567837 6196202551284617315837939)
                  ·
                    refine ⟨9294303826926925973756909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6196202551284617315837939 9294303826926925973756909)
                    ·
                      refine ⟨3485363935097597240158841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9294303826926925973756909 3485363935097597240158841)
                      ·
                        rfl

theorem cell23_6787722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_6787722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787722 prefixEnd_6787722 := by exact prefixLift 6787722
  have htrace : WordTrace (prefixWord ++ tailWord_6787722) baseStart_6787722 baseEnd_6787722 := by
    simpa [prefixWord, tailWord_6787722, baseEnd_6787722] using wordTrace_append hprefix tailTrace_6787722
  have hstable : (prefixWord ++ tailWord_6787722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787722).length < 2 ^ (prefixWord ++ tailWord_6787722).sum := by decide
  have hdescent : baseEnd_6787722 < baseStart_6787722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787731 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 5]
def baseStart_6787731 : Nat := 118140960795 + 6787731 * 2 ^ 59
def prefixEnd_6787731 : Nat := 4983230072969 + 3 ^ 40 * 6787731 * 2
def baseEnd_6787731 : Nat := 3485368556423487704946299

theorem tailTrace_6787731 : CollatzResearch.WordTrace tailWord_6787731 prefixEnd_6787731 3485368556423487704946299 := by
  unfold tailWord_6787731
  simp only [CollatzResearch.WordTrace]
  refine ⟨247568888172217314007131047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165045925448144876004754031 247568888172217314007131047)
  ·
    refine ⟨371353332258325971010696571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247568888172217314007131047 371353332258325971010696571)
    ·
      refine ⟨557029998387488956516044857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371353332258325971010696571 557029998387488956516044857)
      ·
        refine ⟨417772498790616717387033643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557029998387488956516044857 417772498790616717387033643)
        ·
          refine ⟨626658748185925076080550465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417772498790616717387033643 626658748185925076080550465)
          ·
            refine ⟨469994061139443807060412849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626658748185925076080550465 469994061139443807060412849)
            ·
              refine ⟨352495545854582855295309637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469994061139443807060412849 352495545854582855295309637)
              ·
                refine ⟨66092914847734285367870557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352495545854582855295309637 66092914847734285367870557)
                ·
                  refine ⟨24784843067900357012951459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66092914847734285367870557 24784843067900357012951459)
                  ·
                    refine ⟨37177264601850535519427189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24784843067900357012951459 37177264601850535519427189)
                    ·
                      refine ⟨3485368556423487704946299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37177264601850535519427189 3485368556423487704946299)
                      ·
                        rfl

theorem cell23_6787731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_6787731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787731 prefixEnd_6787731 := by exact prefixLift 6787731
  have htrace : WordTrace (prefixWord ++ tailWord_6787731) baseStart_6787731 baseEnd_6787731 := by
    simpa [prefixWord, tailWord_6787731, baseEnd_6787731] using wordTrace_append hprefix tailTrace_6787731
  have hstable : (prefixWord ++ tailWord_6787731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787731).length < 2 ^ (prefixWord ++ tailWord_6787731).sum := by decide
  have hdescent : baseEnd_6787731 < baseStart_6787731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787732 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_6787732 : Nat := 118140960795 + 6787732 * 2 ^ 59
def prefixEnd_6787732 : Nat := 4983230072969 + 3 ^ 40 * 6787732 * 2
def baseEnd_6787732 : Nat := 3485369069904142201033795

theorem tailTrace_6787732 : CollatzResearch.WordTrace tailWord_6787732 prefixEnd_6787732 3485369069904142201033795 := by
  unfold tailWord_6787732
  simp only [CollatzResearch.WordTrace]
  refine ⟨123784462322606845588958725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165045949763475794118611633 123784462322606845588958725)
  ·
    refine ⟨23209586685488783547929761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123784462322606845588958725 23209586685488783547929761)
    ·
      refine ⟨17407190014116587660947321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23209586685488783547929761 17407190014116587660947321)
      ·
        refine ⟨13055392510587440745710491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17407190014116587660947321 13055392510587440745710491)
        ·
          refine ⟨19583088765881161118565737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055392510587440745710491 19583088765881161118565737)
          ·
            refine ⟨14687316574410870838924303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19583088765881161118565737 14687316574410870838924303)
            ·
              refine ⟨22030974861616306258386455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14687316574410870838924303 22030974861616306258386455)
              ·
                refine ⟨33046462292424459387579683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22030974861616306258386455 33046462292424459387579683)
                ·
                  refine ⟨49569693438636689081369525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33046462292424459387579683 49569693438636689081369525)
                  ·
                    refine ⟨4647158759872189601378393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49569693438636689081369525 4647158759872189601378393)
                    ·
                      refine ⟨3485369069904142201033795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647158759872189601378393 3485369069904142201033795)
                      ·
                        rfl

theorem cell23_6787732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_6787732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787732 prefixEnd_6787732 := by exact prefixLift 6787732
  have htrace : WordTrace (prefixWord ++ tailWord_6787732) baseStart_6787732 baseEnd_6787732 := by
    simpa [prefixWord, tailWord_6787732, baseEnd_6787732] using wordTrace_append hprefix tailTrace_6787732
  have hstable : (prefixWord ++ tailWord_6787732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787732).length < 2 ^ (prefixWord ++ tailWord_6787732).sum := by decide
  have hdescent : baseEnd_6787732 < baseStart_6787732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787748 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_6787748 : Nat := 118140960795 + 6787748 * 2 ^ 59
def prefixEnd_6787748 : Nat := 4983230072969 + 3 ^ 40 * 6787748 * 2
def baseEnd_6787748 : Nat := 3485377285594614138433721

theorem tailTrace_6787748 : CollatzResearch.WordTrace tailWord_6787748 prefixEnd_6787748 3485377285594614138433721 := by
  unfold tailWord_6787748
  simp only [CollatzResearch.WordTrace]
  refine ⟨123784754106577862955249949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165046338808770483940333265 123784754106577862955249949)
  ·
    refine ⟨46419282789966698608218731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123784754106577862955249949 46419282789966698608218731)
    ·
      refine ⟨69628924184950047912328097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46419282789966698608218731 69628924184950047912328097)
      ·
        refine ⟨52221693138712535934246073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69628924184950047912328097 52221693138712535934246073)
        ·
          refine ⟨39166269854034401950684555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52221693138712535934246073 39166269854034401950684555)
          ·
            refine ⟨58749404781051602926026833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39166269854034401950684555 58749404781051602926026833)
            ·
              refine ⟨44062053585788702194520125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58749404781051602926026833 44062053585788702194520125)
              ·
                refine ⟨16523270094670763322945047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44062053585788702194520125 16523270094670763322945047)
                ·
                  refine ⟨24784905142006144984417571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16523270094670763322945047 24784905142006144984417571)
                  ·
                    refine ⟨37177357713009217476626357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24784905142006144984417571 37177357713009217476626357)
                    ·
                      refine ⟨3485377285594614138433721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37177357713009217476626357 3485377285594614138433721)
                      ·
                        rfl

theorem cell23_6787748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_6787748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787748 prefixEnd_6787748 := by exact prefixLift 6787748
  have htrace : WordTrace (prefixWord ++ tailWord_6787748) baseStart_6787748 baseEnd_6787748 := by
    simpa [prefixWord, tailWord_6787748, baseEnd_6787748] using wordTrace_append hprefix tailTrace_6787748
  have hstable : (prefixWord ++ tailWord_6787748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787748).length < 2 ^ (prefixWord ++ tailWord_6787748).sum := by decide
  have hdescent : baseEnd_6787748 < baseStart_6787748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787765 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_6787765 : Nat := 118140960795 + 6787765 * 2 ^ 59
def prefixEnd_6787765 : Nat := 4983230072969 + 3 ^ 40 * 6787765 * 2
def baseEnd_6787765 : Nat := 3485386014765740571921143

theorem tailTrace_6787765 : CollatzResearch.WordTrace tailWord_6787765 prefixEnd_6787765 3485386014765740571921143 := by
  unfold tailWord_6787765
  simp only [CollatzResearch.WordTrace]
  refine ⟨247570128254094137813868749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165046752169396091875912499 247570128254094137813868749)
  ·
    refine ⟨92838798095285301680200781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247570128254094137813868749 92838798095285301680200781)
    ·
      refine ⟨34814549285731988130075293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92838798095285301680200781 34814549285731988130075293)
      ·
        refine ⟨13055455982149495548778235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34814549285731988130075293 13055455982149495548778235)
        ·
          refine ⟨19583183973224243323167353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055455982149495548778235 19583183973224243323167353)
          ·
            refine ⟨14687387979918182492375515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19583183973224243323167353 14687387979918182492375515)
            ·
              refine ⟨22031081969877273738563273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14687387979918182492375515 22031081969877273738563273)
              ·
                refine ⟨16523311477407955303922455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22031081969877273738563273 16523311477407955303922455)
                ·
                  refine ⟨24784967216111932955883683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16523311477407955303922455 24784967216111932955883683)
                  ·
                    refine ⟨37177450824167899433825525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24784967216111932955883683 37177450824167899433825525)
                    ·
                      refine ⟨3485386014765740571921143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37177450824167899433825525 3485386014765740571921143)
                      ·
                        rfl

theorem cell23_6787765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_6787765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787765 prefixEnd_6787765 := by exact prefixLift 6787765
  have htrace : WordTrace (prefixWord ++ tailWord_6787765) baseStart_6787765 baseEnd_6787765 := by
    simpa [prefixWord, tailWord_6787765, baseEnd_6787765] using wordTrace_append hprefix tailTrace_6787765
  have hstable : (prefixWord ++ tailWord_6787765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787765).length < 2 ^ (prefixWord ++ tailWord_6787765).sum := by decide
  have hdescent : baseEnd_6787765 < baseStart_6787765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787772 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 2, 4]
def baseStart_6787772 : Nat := 118140960795 + 6787772 * 2 ^ 59
def prefixEnd_6787772 : Nat := 4983230072969 + 3 ^ 40 * 6787772 * 2
def baseEnd_6787772 : Nat := 1161796536376774014844537

theorem tailTrace_6787772 : CollatzResearch.WordTrace tailWord_6787772 prefixEnd_6787772 1161796536376774014844537 := by
  unfold tailWord_6787772
  simp only [CollatzResearch.WordTrace]
  refine ⟨123785191782534389004686785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165046922376712518672915713 123785191782534389004686785)
  ·
    refine ⟨92838893836900791753515089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123785191782534389004686785 92838893836900791753515089)
    ·
      refine ⟨69629170377675593815136317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92838893836900791753515089 69629170377675593815136317)
      ·
        refine ⟨26110938891628347680676119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69629170377675593815136317 26110938891628347680676119)
        ·
          refine ⟨39166408337442521521014179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26110938891628347680676119 39166408337442521521014179)
          ·
            refine ⟨58749612506163782281521269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39166408337442521521014179 58749612506163782281521269)
            ·
              refine ⟨5507776172452854588892619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58749612506163782281521269 5507776172452854588892619)
              ·
                refine ⟨8261664258679281883338929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5507776172452854588892619 8261664258679281883338929)
                ·
                  refine ⟨6196248194009461412504197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8261664258679281883338929 6196248194009461412504197)
                  ·
                    refine ⟨1161796536376774014844537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196248194009461412504197 1161796536376774014844537)
                    ·
                      rfl

theorem cell23_6787772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_6787772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787772 prefixEnd_6787772 := by exact prefixLift 6787772
  have htrace : WordTrace (prefixWord ++ tailWord_6787772) baseStart_6787772 baseEnd_6787772 := by
    simpa [prefixWord, tailWord_6787772, baseEnd_6787772] using wordTrace_append hprefix tailTrace_6787772
  have hstable : (prefixWord ++ tailWord_6787772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787772).length < 2 ^ (prefixWord ++ tailWord_6787772).sum := by decide
  have hdescent : baseEnd_6787772 < baseStart_6787772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787775 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 4]
def baseStart_6787775 : Nat := 118140960795 + 6787775 * 2 ^ 59
def prefixEnd_6787775 : Nat := 4983230072969 + 3 ^ 40 * 6787775 * 2
def baseEnd_6787775 : Nat := 3485391149572285532796097

theorem tailTrace_6787775 : CollatzResearch.WordTrace tailWord_6787775 prefixEnd_6787775 3485391149572285532796097 := by
  unfold tailWord_6787775
  simp only [CollatzResearch.WordTrace]
  refine ⟨247570492984057909521732779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165046995322705273014488519 247570492984057909521732779)
  ·
    refine ⟨371355739476086864282599169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247570492984057909521732779 371355739476086864282599169)
    ·
      refine ⟨278516804607065148211949377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371355739476086864282599169 278516804607065148211949377)
      ·
        refine ⟨208887603455298861158962033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278516804607065148211949377 208887603455298861158962033)
        ·
          refine ⟨156665702591474145869221525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208887603455298861158962033 156665702591474145869221525)
          ·
            refine ⟨7343704808975350587619759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156665702591474145869221525 7343704808975350587619759)
            ·
              refine ⟨11015557213463025881429639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343704808975350587619759 11015557213463025881429639)
              ·
                refine ⟨16523335820194538822144459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11015557213463025881429639 16523335820194538822144459)
                ·
                  refine ⟨24785003730291808233216689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16523335820194538822144459 24785003730291808233216689)
                  ·
                    refine ⟨18588752797718856174912517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24785003730291808233216689 18588752797718856174912517)
                    ·
                      refine ⟨3485391149572285532796097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18588752797718856174912517 3485391149572285532796097)
                      ·
                        rfl

theorem cell23_6787775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_6787775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787775 prefixEnd_6787775 := by exact prefixLift 6787775
  have htrace : WordTrace (prefixWord ++ tailWord_6787775) baseStart_6787775 baseEnd_6787775 := by
    simpa [prefixWord, tailWord_6787775, baseEnd_6787775] using wordTrace_append hprefix tailTrace_6787775
  have hstable : (prefixWord ++ tailWord_6787775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787775).length < 2 ^ (prefixWord ++ tailWord_6787775).sum := by decide
  have hdescent : baseEnd_6787775 < baseStart_6787775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787818 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_6787818 : Nat := 118140960795 + 6787818 * 2 ^ 59
def prefixEnd_6787818 : Nat := 4983230072969 + 3 ^ 40 * 6787818 * 2
def baseEnd_6787818 : Nat := 3485413229240428864558399

theorem tailTrace_6787818 : CollatzResearch.WordTrace tailWord_6787818 prefixEnd_6787818 3485413229240428864558399 := by
  unfold tailWord_6787818
  simp only [CollatzResearch.WordTrace]
  refine ⟨61893015330725531966387027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165048040881934751910365405 61893015330725531966387027)
  ·
    refine ⟨92839522996088297949580541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61893015330725531966387027 92839522996088297949580541)
    ·
      refine ⟨34814821123533111731092703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92839522996088297949580541 34814821123533111731092703)
      ·
        refine ⟨52222231685299667596639055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34814821123533111731092703 52222231685299667596639055)
        ·
          refine ⟨78333347527949501394958583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52222231685299667596639055 78333347527949501394958583)
          ·
            refine ⟨117500021291924252092437875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78333347527949501394958583 117500021291924252092437875)
            ·
              refine ⟨176250031937886378138656813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117500021291924252092437875 176250031937886378138656813)
              ·
                refine ⟨66093761976707391801996305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176250031937886378138656813 66093761976707391801996305)
                ·
                  refine ⟨49570321482530543851497229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66093761976707391801996305 49570321482530543851497229)
                  ·
                    refine ⟨18588870555948953944311461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49570321482530543851497229 18588870555948953944311461)
                    ·
                      refine ⟨3485413229240428864558399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18588870555948953944311461 3485413229240428864558399)
                      ·
                        rfl

theorem cell23_6787818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_6787818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787818 prefixEnd_6787818 := by exact prefixLift 6787818
  have htrace : WordTrace (prefixWord ++ tailWord_6787818) baseStart_6787818 baseEnd_6787818 := by
    simpa [prefixWord, tailWord_6787818, baseEnd_6787818] using wordTrace_append hprefix tailTrace_6787818
  have hstable : (prefixWord ++ tailWord_6787818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787818).length < 2 ^ (prefixWord ++ tailWord_6787818).sum := by decide
  have hdescent : baseEnd_6787818 < baseStart_6787818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787886 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_6787886 : Nat := 118140960795 + 6787886 * 2 ^ 59
def prefixEnd_6787886 : Nat := 4983230072969 + 3 ^ 40 * 6787886 * 2
def baseEnd_6787886 : Nat := 3485448145924934598508087

theorem tailTrace_6787886 : CollatzResearch.WordTrace tailWord_6787886 prefixEnd_6787886 3485448145924934598508087 := by
  unfold tailWord_6787886
  simp only [CollatzResearch.WordTrace]
  refine ⟨30946817685831971934877939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165049694324437183652682341 30946817685831971934877939)
  ·
    refine ⟨46420226528747957902316909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30946817685831971934877939 46420226528747957902316909)
    ·
      refine ⟨17407584948280484213368841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46420226528747957902316909 17407584948280484213368841)
      ·
        refine ⟨13055688711210363160026631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17407584948280484213368841 13055688711210363160026631)
        ·
          refine ⟨19583533066815544740039947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055688711210363160026631 19583533066815544740039947)
          ·
            refine ⟨29375299600223317110059921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19583533066815544740039947 29375299600223317110059921)
            ·
              refine ⟨22031474700167487832544941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29375299600223317110059921 22031474700167487832544941)
              ·
                refine ⟨8261803012562807937204353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22031474700167487832544941 8261803012562807937204353)
                ·
                  refine ⟨6196352259422105952903265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8261803012562807937204353 6196352259422105952903265)
                  ·
                    refine ⟨4647264194566579464677449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6196352259422105952903265 4647264194566579464677449)
                    ·
                      refine ⟨3485448145924934598508087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647264194566579464677449 3485448145924934598508087)
                      ·
                        rfl

theorem cell23_6787886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_6787886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787886 prefixEnd_6787886 := by exact prefixLift 6787886
  have htrace : WordTrace (prefixWord ++ tailWord_6787886) baseStart_6787886 baseEnd_6787886 := by
    simpa [prefixWord, tailWord_6787886, baseEnd_6787886] using wordTrace_append hprefix tailTrace_6787886
  have hstable : (prefixWord ++ tailWord_6787886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787886).length < 2 ^ (prefixWord ++ tailWord_6787886).sum := by decide
  have hdescent : baseEnd_6787886 < baseStart_6787886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787888 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 4, 5]
def baseStart_6787888 : Nat := 118140960795 + 6787888 * 2 ^ 59
def prefixEnd_6787888 : Nat := 4983230072969 + 3 ^ 40 * 6787888 * 2
def baseEnd_6787888 : Nat := 1161816390962081196894359

theorem tailTrace_6787888 : CollatzResearch.WordTrace tailWord_6787888 prefixEnd_6787888 1161816390962081196894359 := by
  unfold tailWord_6787888
  simp only [CollatzResearch.WordTrace]
  refine ⟨123787307216324264910298159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165049742955099019880397545 123787307216324264910298159)
  ·
    refine ⟨185680960824486397365447239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123787307216324264910298159 185680960824486397365447239)
    ·
      refine ⟨278521441236729596048170859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185680960824486397365447239 278521441236729596048170859)
      ·
        refine ⟨417782161855094394072256289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278521441236729596048170859 417782161855094394072256289)
        ·
          refine ⟨313336621391320795554192217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417782161855094394072256289 313336621391320795554192217)
          ·
            refine ⟨235002466043490596665644163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313336621391320795554192217 235002466043490596665644163)
            ·
              refine ⟨352503699065235894998466245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235002466043490596665644163 352503699065235894998466245)
              ·
                refine ⟨66094443574731730312212421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352503699065235894998466245 66094443574731730312212421)
                ·
                  refine ⟨12392708170262199433539829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66094443574731730312212421 12392708170262199433539829)
                  ·
                    refine ⟨1161816390962081196894359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12392708170262199433539829 1161816390962081196894359)
                    ·
                      rfl

theorem cell23_6787888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_6787888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787888 prefixEnd_6787888 := by exact prefixLift 6787888
  have htrace : WordTrace (prefixWord ++ tailWord_6787888) baseStart_6787888 baseEnd_6787888 := by
    simpa [prefixWord, tailWord_6787888, baseEnd_6787888] using wordTrace_append hprefix tailTrace_6787888
  have hstable : (prefixWord ++ tailWord_6787888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787888).length < 2 ^ (prefixWord ++ tailWord_6787888).sum := by decide
  have hdescent : baseEnd_6787888 < baseStart_6787888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787892 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 7]
def baseStart_6787892 : Nat := 118140960795 + 6787892 * 2 ^ 59
def prefixEnd_6787892 : Nat := 4983230072969 + 3 ^ 40 * 6787892 * 2
def baseEnd_6787892 : Nat := 387272358534317952781451

theorem tailTrace_6787892 : CollatzResearch.WordTrace tailWord_6787892 prefixEnd_6787892 387272358534317952781451 := by
  unfold tailWord_6787892
  simp only [CollatzResearch.WordTrace]
  refine ⟨123787380162317019251870965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165049840216422692335827953 123787380162317019251870965)
  ·
    refine ⟨11605066890217220554862903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123787380162317019251870965 11605066890217220554862903)
    ·
      refine ⟨17407600335325830832294355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11605066890217220554862903 17407600335325830832294355)
      ·
        refine ⟨26111400502988746248441533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17407600335325830832294355 26111400502988746248441533)
        ·
          refine ⟨9791775188620779843165575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26111400502988746248441533 9791775188620779843165575)
          ·
            refine ⟨14687662782931169764748363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9791775188620779843165575 14687662782931169764748363)
            ·
              refine ⟨22031494174396754647122545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14687662782931169764748363 22031494174396754647122545)
              ·
                refine ⟨16523620630797565985341909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22031494174396754647122545 16523620630797565985341909)
                ·
                  refine ⟨387272358534317952781451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16523620630797565985341909 387272358534317952781451)
                  ·
                    rfl

theorem cell23_6787892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_6787892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787892 prefixEnd_6787892 := by exact prefixLift 6787892
  have htrace : WordTrace (prefixWord ++ tailWord_6787892) baseStart_6787892 baseEnd_6787892 := by
    simpa [prefixWord, tailWord_6787892, baseEnd_6787892] using wordTrace_append hprefix tailTrace_6787892
  have hstable : (prefixWord ++ tailWord_6787892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787892).length < 2 ^ (prefixWord ++ tailWord_6787892).sum := by decide
  have hdescent : baseEnd_6787892 < baseStart_6787892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787895 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 2, 5, 2]
def baseStart_6787895 : Nat := 118140960795 + 6787895 * 2 ^ 59
def prefixEnd_6787895 : Nat := 4983230072969 + 3 ^ 40 * 6787895 * 2
def baseEnd_6787895 : Nat := 3485452767250825063295545

theorem tailTrace_6787895 : CollatzResearch.WordTrace tailWord_6787895 prefixEnd_6787895 3485452767250825063295545 := by
  unfold tailWord_6787895
  simp only [CollatzResearch.WordTrace]
  refine ⟨247574869743623170016101139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165049913162415446677400759 247574869743623170016101139)
  ·
    refine ⟨371362304615434755024151709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247574869743623170016101139 371362304615434755024151709)
    ·
      refine ⟨139260864230788033134056891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371362304615434755024151709 139260864230788033134056891)
      ·
        refine ⟨208891296346182049701085337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139260864230788033134056891 208891296346182049701085337)
        ·
          refine ⟨156668472259636537275814003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208891296346182049701085337 156668472259636537275814003)
          ·
            refine ⟨235002708389454805913721005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156668472259636537275814003 235002708389454805913721005)
            ·
              refine ⟨88126015646045552217645377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235002708389454805913721005 88126015646045552217645377)
              ·
                refine ⟨66094511734534164163234033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88126015646045552217645377 66094511734534164163234033)
                ·
                  refine ⟨49570883800900623122425525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66094511734534164163234033 49570883800900623122425525)
                  ·
                    refine ⟨4647270356334433417727393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49570883800900623122425525 4647270356334433417727393)
                    ·
                      refine ⟨3485452767250825063295545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647270356334433417727393 3485452767250825063295545)
                      ·
                        rfl

theorem cell23_6787895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 5, 2].length) (baseStart_6787895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787895 prefixEnd_6787895 := by exact prefixLift 6787895
  have htrace : WordTrace (prefixWord ++ tailWord_6787895) baseStart_6787895 baseEnd_6787895 := by
    simpa [prefixWord, tailWord_6787895, baseEnd_6787895] using wordTrace_append hprefix tailTrace_6787895
  have hstable : (prefixWord ++ tailWord_6787895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787895).length < 2 ^ (prefixWord ++ tailWord_6787895).sum := by decide
  have hdescent : baseEnd_6787895 < baseStart_6787895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787918 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_6787918 : Nat := 118140960795 + 6787918 * 2 ^ 59
def prefixEnd_6787918 : Nat := 4983230072969 + 3 ^ 40 * 6787918 * 2
def baseEnd_6787918 : Nat := 1161821525768626157769313

theorem tailTrace_6787918 : CollatzResearch.WordTrace tailWord_6787918 prefixEnd_6787918 1161821525768626157769313 := by
  unfold tailWord_6787918
  simp only [CollatzResearch.WordTrace]
  refine ⟨30946963577817480618023551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165050472415026563296125605 30946963577817480618023551)
  ·
    refine ⟨46420445366726220927035327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30946963577817480618023551 46420445366726220927035327)
    ·
      refine ⟨69630668050089331390552991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46420445366726220927035327 69630668050089331390552991)
      ·
        refine ⟨104446002075133997085829487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69630668050089331390552991 104446002075133997085829487)
        ·
          refine ⟨156669003112700995628744231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104446002075133997085829487 156669003112700995628744231)
          ·
            refine ⟨235003504669051493443116347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156669003112700995628744231 235003504669051493443116347)
            ·
              refine ⟨352505257003577240164674521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235003504669051493443116347 352505257003577240164674521)
              ·
                refine ⟨264378942752682930123505891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352505257003577240164674521 264378942752682930123505891)
                ·
                  refine ⟨396568414129024395185258837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264378942752682930123505891 396568414129024395185258837)
                  ·
                    refine ⟨1161821525768626157769313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 396568414129024395185258837 1161821525768626157769313)
                    ·
                      rfl

theorem cell23_6787918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_6787918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787918 prefixEnd_6787918 := by exact prefixLift 6787918
  have htrace : WordTrace (prefixWord ++ tailWord_6787918) baseStart_6787918 baseEnd_6787918 := by
    simpa [prefixWord, tailWord_6787918, baseEnd_6787918] using wordTrace_append hprefix tailTrace_6787918
  have hstable : (prefixWord ++ tailWord_6787918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787918).length < 2 ^ (prefixWord ++ tailWord_6787918).sum := by decide
  have hdescent : baseEnd_6787918 < baseStart_6787918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787925 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_6787925 : Nat := 118140960795 + 6787925 * 2 ^ 59
def prefixEnd_6787925 : Nat := 4983230072969 + 3 ^ 40 * 6787925 * 2
def baseEnd_6787925 : Nat := 3485468171670459945920407

theorem tailTrace_6787925 : CollatzResearch.WordTrace tailWord_6787925 prefixEnd_6787925 3485468171670459945920407 := by
  unfold tailWord_6787925
  simp only [CollatzResearch.WordTrace]
  refine ⟨247575963933514485139693229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165050642622342990093128819 247575963933514485139693229)
  ·
    refine ⟨92840986475067931927384961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247575963933514485139693229 92840986475067931927384961)
    ·
      refine ⟨69630739856300948945538721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92840986475067931927384961 69630739856300948945538721)
      ·
        refine ⟨52223054892225711709154041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69630739856300948945538721 52223054892225711709154041)
        ·
          refine ⟨39167291169169283781865531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52223054892225711709154041 39167291169169283781865531)
          ·
            refine ⟨58750936753753925672798297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39167291169169283781865531 58750936753753925672798297)
            ·
              refine ⟨44063202565315444254598723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58750936753753925672798297 44063202565315444254598723)
              ·
                refine ⟨66094803847973166381898085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44063202565315444254598723 66094803847973166381898085)
                ·
                  refine ⟨12392775721494968696605891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66094803847973166381898085 12392775721494968696605891)
                  ·
                    refine ⟨18589163582242453044908837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12392775721494968696605891 18589163582242453044908837)
                    ·
                      refine ⟨3485468171670459945920407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18589163582242453044908837 3485468171670459945920407)
                      ·
                        rfl

theorem cell23_6787925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_6787925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787925 prefixEnd_6787925 := by exact prefixLift 6787925
  have htrace : WordTrace (prefixWord ++ tailWord_6787925) baseStart_6787925 baseEnd_6787925 := by
    simpa [prefixWord, tailWord_6787925, baseEnd_6787925] using wordTrace_append hprefix tailTrace_6787925
  have hstable : (prefixWord ++ tailWord_6787925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787925).length < 2 ^ (prefixWord ++ tailWord_6787925).sum := by decide
  have hdescent : baseEnd_6787925 < baseStart_6787925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787928 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_6787928 : Nat := 118140960795 + 6787928 * 2 ^ 59
def prefixEnd_6787928 : Nat := 4983230072969 + 3 ^ 40 * 6787928 * 2
def baseEnd_6787928 : Nat := 3485469712112423434182893

theorem tailTrace_6787928 : CollatzResearch.WordTrace tailWord_6787928 prefixEnd_6787928 3485469712112423434182893 := by
  unfold tailWord_6787928
  simp only [CollatzResearch.WordTrace]
  refine ⟨123788036676251808326026219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165050715568335744434701625 123788036676251808326026219)
  ·
    refine ⟨185682055014377712489039329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123788036676251808326026219 185682055014377712489039329)
    ·
      refine ⟨139261541260783284366779497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185682055014377712489039329 139261541260783284366779497)
      ·
        refine ⟨104446155945587463275084623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139261541260783284366779497 104446155945587463275084623)
        ·
          refine ⟨156669233918381194912626935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104446155945587463275084623 156669233918381194912626935)
          ·
            refine ⟨235003850877571792368940403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156669233918381194912626935 235003850877571792368940403)
            ·
              refine ⟨352505776316357688553410605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235003850877571792368940403 352505776316357688553410605)
              ·
                refine ⟨132189666118634133207528977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352505776316357688553410605 132189666118634133207528977)
                ·
                  refine ⟨99142249588975599905646733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132189666118634133207528977 99142249588975599905646733)
                  ·
                    refine ⟨37178343595865849964617525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99142249588975599905646733 37178343595865849964617525)
                    ·
                      refine ⟨3485469712112423434182893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37178343595865849964617525 3485469712112423434182893)
                      ·
                        rfl

theorem cell23_6787928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_6787928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787928 prefixEnd_6787928 := by exact prefixLift 6787928
  have htrace : WordTrace (prefixWord ++ tailWord_6787928) baseStart_6787928 baseEnd_6787928 := by
    simpa [prefixWord, tailWord_6787928, baseEnd_6787928] using wordTrace_append hprefix tailTrace_6787928
  have hstable : (prefixWord ++ tailWord_6787928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787928).length < 2 ^ (prefixWord ++ tailWord_6787928).sum := by decide
  have hdescent : baseEnd_6787928 < baseStart_6787928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787968 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_6787968 : Nat := 118140960795 + 6787968 * 2 ^ 59
def prefixEnd_6787968 : Nat := 4983230072969 + 3 ^ 40 * 6787968 * 2
def baseEnd_6787968 : Nat := 3485490251338603277682709

theorem tailTrace_6787968 : CollatzResearch.WordTrace tailWord_6787968 prefixEnd_6787968 3485490251338603277682709 := by
  unfold tailWord_6787968
  simp only [CollatzResearch.WordTrace]
  refine ⟨123788766136179351741754279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165051688181572468989005705 123788766136179351741754279)
  ·
    refine ⟨185683149204269027612631419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123788766136179351741754279 185683149204269027612631419)
    ·
      refine ⟨278524723806403541418947129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185683149204269027612631419 278524723806403541418947129)
      ·
        refine ⟨208893542854802656064210347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278524723806403541418947129 208893542854802656064210347)
        ·
          refine ⟨313340314282203984096315521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208893542854802656064210347 313340314282203984096315521)
          ·
            refine ⟨235005235711652988072236641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313340314282203984096315521 235005235711652988072236641)
            ·
              refine ⟨176253926783739741054177481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235005235711652988072236641 176253926783739741054177481)
              ·
                refine ⟨132190445087804805790633111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176253926783739741054177481 132190445087804805790633111)
                ·
                  refine ⟨198285667631707208685949667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132190445087804805790633111 198285667631707208685949667)
                  ·
                    refine ⟨297428501447560813028924501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198285667631707208685949667 297428501447560813028924501)
                    ·
                      refine ⟨3485490251338603277682709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 297428501447560813028924501 3485490251338603277682709)
                      ·
                        rfl

theorem cell23_6787968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_6787968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787968 prefixEnd_6787968 := by exact prefixLift 6787968
  have htrace : WordTrace (prefixWord ++ tailWord_6787968) baseStart_6787968 baseEnd_6787968 := by
    simpa [prefixWord, tailWord_6787968, baseEnd_6787968] using wordTrace_append hprefix tailTrace_6787968
  have hstable : (prefixWord ++ tailWord_6787968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787968).length < 2 ^ (prefixWord ++ tailWord_6787968).sum := by decide
  have hdescent : baseEnd_6787968 < baseStart_6787968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787986 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_6787986 : Nat := 118140960795 + 6787986 * 2 ^ 59
def prefixEnd_6787986 : Nat := 4983230072969 + 3 ^ 40 * 6787986 * 2
def baseEnd_6787986 : Nat := 1161833164663461402419209

theorem tailTrace_6787986 : CollatzResearch.WordTrace tailWord_6787986 prefixEnd_6787986 1161833164663461402419209 := by
  unfold tailWord_6787986
  simp only [CollatzResearch.WordTrace]
  refine ⟨61894547196573373139415953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165052125857528995038442541 61894547196573373139415953)
  ·
    refine ⟨46420910397430029854561965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61894547196573373139415953 46420910397430029854561965)
    ·
      refine ⟨17407841399036261195460737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46420910397430029854561965 17407841399036261195460737)
      ·
        refine ⟨13055881049277195896595553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17407841399036261195460737 13055881049277195896595553)
        ·
          refine ⟨9791910786957896922446665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13055881049277195896595553 9791910786957896922446665)
          ·
            refine ⟨7343933090218422691834999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9791910786957896922446665 7343933090218422691834999)
            ·
              refine ⟨11015899635327634037752499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343933090218422691834999 11015899635327634037752499)
              ·
                refine ⟨16523849452991451056628749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11015899635327634037752499 16523849452991451056628749)
                ·
                  refine ⟨6196443544871794146235781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16523849452991451056628749 6196443544871794146235781)
                  ·
                    refine ⟨1161833164663461402419209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196443544871794146235781 1161833164663461402419209)
                    ·
                      rfl

theorem cell23_6787986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_6787986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787986 prefixEnd_6787986 := by exact prefixLift 6787986
  have htrace : WordTrace (prefixWord ++ tailWord_6787986) baseStart_6787986 baseEnd_6787986 := by
    simpa [prefixWord, tailWord_6787986, baseEnd_6787986] using wordTrace_append hprefix tailTrace_6787986
  have hstable : (prefixWord ++ tailWord_6787986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787986).length < 2 ^ (prefixWord ++ tailWord_6787986).sum := by decide
  have hdescent : baseEnd_6787986 < baseStart_6787986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6787999 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 6]
def baseStart_6787999 : Nat := 118140960795 + 6787999 * 2 ^ 59
def prefixEnd_6787999 : Nat := 4983230072969 + 3 ^ 40 * 6787999 * 2
def baseEnd_6787999 : Nat := 387278463248765850710563

theorem tailTrace_6787999 : CollatzResearch.WordTrace tailWord_6787999 prefixEnd_6787999 387278463248765850710563 := by
  unfold tailWord_6787999
  simp only [CollatzResearch.WordTrace]
  refine ⟨247578662935246395777887051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165052441956830930518591367 247578662935246395777887051)
  ·
    refine ⟨371367994402869593666830577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247578662935246395777887051 371367994402869593666830577)
    ·
      refine ⟨278525995802152195250122933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371367994402869593666830577 278525995802152195250122933)
      ·
        refine ⟨26111812106451768304699025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 278525995802152195250122933 26111812106451768304699025)
        ·
          refine ⟨19583859079838826228524269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26111812106451768304699025 19583859079838826228524269)
          ·
            refine ⟨7343947154939559835696601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19583859079838826228524269 7343947154939559835696601)
            ·
              refine ⟨5507960366204669876772451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7343947154939559835696601 5507960366204669876772451)
              ·
                refine ⟨8261940549307004815158677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5507960366204669876772451 8261940549307004815158677)
                ·
                  refine ⟨387278463248765850710563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8261940549307004815158677 387278463248765850710563)
                  ·
                    rfl

theorem cell23_6787999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 6].length) (baseStart_6787999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6787999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6787999 prefixEnd_6787999 := by exact prefixLift 6787999
  have htrace : WordTrace (prefixWord ++ tailWord_6787999) baseStart_6787999 baseEnd_6787999 := by
    simpa [prefixWord, tailWord_6787999, baseEnd_6787999] using wordTrace_append hprefix tailTrace_6787999
  have hstable : (prefixWord ++ tailWord_6787999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6787999).length < 2 ^ (prefixWord ++ tailWord_6787999).sum := by decide
  have hdescent : baseEnd_6787999 < baseStart_6787999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6787999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788025 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 3, 6]
def baseStart_6788025 : Nat := 118140960795 + 6788025 * 2 ^ 59
def prefixEnd_6788025 : Nat := 4983230072969 + 3 ^ 40 * 6788025 * 2
def baseEnd_6788025 : Nat := 1161839839911969851556649

theorem tailTrace_6788025 : CollatzResearch.WordTrace tailWord_6788025 prefixEnd_6788025 1161839839911969851556649 := by
  unfold tailWord_6788025
  simp only [CollatzResearch.WordTrace]
  refine ⟨247579611233152202218333529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165053074155434801478889019 247579611233152202218333529)
  ·
    refine ⟨185684708424864151663750147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247579611233152202218333529 185684708424864151663750147)
    ·
      refine ⟨278527062637296227495625221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185684708424864151663750147 278527062637296227495625221)
      ·
        refine ⟨52223824244493042655429729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278527062637296227495625221 52223824244493042655429729)
        ·
          refine ⟨39167868183369781991572297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52223824244493042655429729 39167868183369781991572297)
          ·
            refine ⟨29375901137527336493679223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39167868183369781991572297 29375901137527336493679223)
            ·
              refine ⟨44063851706291004740518835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29375901137527336493679223 44063851706291004740518835)
              ·
                refine ⟨66095777559436507110778253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44063851706291004740518835 66095777559436507110778253)
                ·
                  refine ⟨24785916584788690166541845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66095777559436507110778253 24785916584788690166541845)
                  ·
                    refine ⟨1161839839911969851556649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24785916584788690166541845 1161839839911969851556649)
                    ·
                      rfl

theorem cell23_6788025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_6788025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788025 prefixEnd_6788025 := by exact prefixLift 6788025
  have htrace : WordTrace (prefixWord ++ tailWord_6788025) baseStart_6788025 baseEnd_6788025 := by
    simpa [prefixWord, tailWord_6788025, baseEnd_6788025] using wordTrace_append hprefix tailTrace_6788025
  have hstable : (prefixWord ++ tailWord_6788025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788025).length < 2 ^ (prefixWord ++ tailWord_6788025).sum := by decide
  have hdescent : baseEnd_6788025 < baseStart_6788025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788043 : List Nat := [1, 1, 1, 1, 3, 7, 2, 2, 1, 1, 3]
def baseStart_6788043 : Nat := 118140960795 + 6788043 * 2 ^ 59
def prefixEnd_6788043 : Nat := 4983230072969 + 3 ^ 40 * 6788043 * 2
def baseEnd_6788043 : Nat := 3485528762387690484244865

theorem tailTrace_6788043 : CollatzResearch.WordTrace tailWord_6788043 prefixEnd_6788043 3485528762387690484244865 := by
  unfold tailWord_6788043
  simp only [CollatzResearch.WordTrace]
  refine ⟨247580267747086991292488783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165053511831391327528325855 247580267747086991292488783)
  ·
    refine ⟨371370401620630486938733175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247580267747086991292488783 371370401620630486938733175)
    ·
      refine ⟨557055602430945730408099763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371370401620630486938733175 557055602430945730408099763)
      ·
        refine ⟨835583403646418595612149645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557055602430945730408099763 835583403646418595612149645)
        ·
          refine ⟨313343776367406973354556117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 835583403646418595612149645 313343776367406973354556117)
          ·
            refine ⟨7343994758611100937997409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 313343776367406973354556117 7343994758611100937997409)
            ·
              refine ⟨5507996068958325703498057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7343994758611100937997409 5507996068958325703498057)
              ·
                refine ⟨4130997051718744277623543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5507996068958325703498057 4130997051718744277623543)
                ·
                  refine ⟨6196495577578116416435315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130997051718744277623543 6196495577578116416435315)
                  ·
                    refine ⟨9294743366367174624652973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6196495577578116416435315 9294743366367174624652973)
                    ·
                      refine ⟨3485528762387690484244865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9294743366367174624652973 3485528762387690484244865)
                      ·
                        rfl

theorem cell23_6788043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 1, 1, 3].length) (baseStart_6788043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788043 prefixEnd_6788043 := by exact prefixLift 6788043
  have htrace : WordTrace (prefixWord ++ tailWord_6788043) baseStart_6788043 baseEnd_6788043 := by
    simpa [prefixWord, tailWord_6788043, baseEnd_6788043] using wordTrace_append hprefix tailTrace_6788043
  have hstable : (prefixWord ++ tailWord_6788043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788043).length < 2 ^ (prefixWord ++ tailWord_6788043).sum := by decide
  have hdescent : baseEnd_6788043 < baseStart_6788043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788049 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 3, 2, 2]
def baseStart_6788049 : Nat := 118140960795 + 6788049 * 2 ^ 59
def prefixEnd_6788049 : Nat := 4983230072969 + 3 ^ 40 * 6788049 * 2
def baseEnd_6788049 : Nat := 3485531843271617460769837

theorem tailTrace_6788049 : CollatzResearch.WordTrace tailWord_6788049 prefixEnd_6788049 3485531843271617460769837 := by
  unfold tailWord_6788049
  simp only [CollatzResearch.WordTrace]
  refine ⟨247580486585065254317207201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165053657723376836211471467 247580486585065254317207201)
  ·
    refine ⟨185685364938798940737905401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247580486585065254317207201 185685364938798940737905401)
    ·
      refine ⟨139264023704099205553429051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185685364938798940737905401 139264023704099205553429051)
      ·
        refine ⟨208896035556148808330143577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139264023704099205553429051 208896035556148808330143577)
        ·
          refine ⟨156672026667111606247607683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208896035556148808330143577 156672026667111606247607683)
          ·
            refine ⟨235008040000667409371411525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156672026667111606247607683 235008040000667409371411525)
            ·
              refine ⟨44064007500125139257139661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235008040000667409371411525 44064007500125139257139661)
              ·
                refine ⟨16524002812546927221427373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44064007500125139257139661 16524002812546927221427373)
                ·
                  refine ⟨6196501054705097708035265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16524002812546927221427373 6196501054705097708035265)
                  ·
                    refine ⟨4647375791028823281026449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6196501054705097708035265 4647375791028823281026449)
                    ·
                      refine ⟨3485531843271617460769837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647375791028823281026449 3485531843271617460769837)
                      ·
                        rfl

theorem cell23_6788049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 2, 2].length) (baseStart_6788049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788049 prefixEnd_6788049 := by exact prefixLift 6788049
  have htrace : WordTrace (prefixWord ++ tailWord_6788049) baseStart_6788049 baseEnd_6788049 := by
    simpa [prefixWord, tailWord_6788049, baseEnd_6788049] using wordTrace_append hprefix tailTrace_6788049
  have hstable : (prefixWord ++ tailWord_6788049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788049).length < 2 ^ (prefixWord ++ tailWord_6788049).sum := by decide
  have hdescent : baseEnd_6788049 < baseStart_6788049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788086 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_6788086 : Nat := 118140960795 + 6788086 * 2 ^ 59
def prefixEnd_6788086 : Nat := 4983230072969 + 3 ^ 40 * 6788086 * 2
def baseEnd_6788086 : Nat := 3485550842055833816007167

theorem tailTrace_6788086 : CollatzResearch.WordTrace tailWord_6788086 prefixEnd_6788086 3485550842055833816007167 := by
  unfold tailWord_6788086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15473864755370700602269007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165054557390620806424202741 15473864755370700602269007)
  ·
    refine ⟨23210797133056050903403511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15473864755370700602269007 23210797133056050903403511)
    ·
      refine ⟨34816195699584076355105267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23210797133056050903403511 34816195699584076355105267)
      ·
        refine ⟨52224293549376114532657901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34816195699584076355105267 52224293549376114532657901)
        ·
          refine ⟨19584110081016042949746713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52224293549376114532657901 19584110081016042949746713)
          ·
            refine ⟨14688082560762032212310035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19584110081016042949746713 14688082560762032212310035)
            ·
              refine ⟨22032123841143048318465053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14688082560762032212310035 22032123841143048318465053)
              ·
                refine ⟨8262046440428643119424395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22032123841143048318465053 8262046440428643119424395)
                ·
                  refine ⟨12393069660642964679136593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8262046440428643119424395 12393069660642964679136593)
                  ·
                    refine ⟨9294802245482223509352445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12393069660642964679136593 9294802245482223509352445)
                    ·
                      refine ⟨3485550842055833816007167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9294802245482223509352445 3485550842055833816007167)
                      ·
                        rfl

theorem cell23_6788086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_6788086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788086 prefixEnd_6788086 := by exact prefixLift 6788086
  have htrace : WordTrace (prefixWord ++ tailWord_6788086) baseStart_6788086 baseEnd_6788086 := by
    simpa [prefixWord, tailWord_6788086, baseEnd_6788086] using wordTrace_append hprefix tailTrace_6788086
  have hstable : (prefixWord ++ tailWord_6788086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788086).length < 2 ^ (prefixWord ++ tailWord_6788086).sum := by decide
  have hdescent : baseEnd_6788086 < baseStart_6788086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788105 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 4]
def baseStart_6788105 : Nat := 118140960795 + 6788105 * 2 ^ 59
def prefixEnd_6788105 : Nat := 4983230072969 + 3 ^ 40 * 6788105 * 2
def baseEnd_6788105 : Nat := 3485560598188269241669579

theorem tailTrace_6788105 : CollatzResearch.WordTrace tailWord_6788105 prefixEnd_6788105 3485560598188269241669579 := by
  unfold tailWord_6788105
  simp only [CollatzResearch.WordTrace]
  refine ⟨247582529072862375881245769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165055019381908250587497179 247582529072862375881245769)
  ·
    refine ⟨185686896804646781910934327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247582529072862375881245769 185686896804646781910934327)
    ·
      refine ⟨278530345206970172866401491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185686896804646781910934327 278530345206970172866401491)
      ·
        refine ⟨417795517810455259299602237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278530345206970172866401491 417795517810455259299602237)
        ·
          refine ⟨156673319178920722237350839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 417795517810455259299602237 156673319178920722237350839)
          ·
            refine ⟨235009978768381083356026259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156673319178920722237350839 235009978768381083356026259)
            ·
              refine ⟨352514968152571625034039389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235009978768381083356026259 352514968152571625034039389)
              ·
                refine ⟨132193113057214359387764771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352514968152571625034039389 132193113057214359387764771)
                ·
                  refine ⟨198289669585821539081647157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132193113057214359387764771 198289669585821539081647157)
                  ·
                    refine ⟨18589656523670769288904421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 198289669585821539081647157 18589656523670769288904421)
                    ·
                      refine ⟨3485560598188269241669579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18589656523670769288904421 3485560598188269241669579)
                      ·
                        rfl

theorem cell23_6788105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_6788105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788105 prefixEnd_6788105 := by exact prefixLift 6788105
  have htrace : WordTrace (prefixWord ++ tailWord_6788105) baseStart_6788105 baseEnd_6788105 := by
    simpa [prefixWord, tailWord_6788105, baseEnd_6788105] using wordTrace_append hprefix tailTrace_6788105
  have hstable : (prefixWord ++ tailWord_6788105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788105).length < 2 ^ (prefixWord ++ tailWord_6788105).sum := by decide
  have hdescent : baseEnd_6788105 < baseStart_6788105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788139 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 6, 2, 2]
def baseStart_6788139 : Nat := 118140960795 + 6788139 * 2 ^ 59
def prefixEnd_6788139 : Nat := 4983230072969 + 3 ^ 40 * 6788139 * 2
def baseEnd_6788139 : Nat := 3485578056530522108644423

theorem tailTrace_6788139 : CollatzResearch.WordTrace tailWord_6788139 prefixEnd_6788139 3485578056530522108644423 := by
  unfold tailWord_6788139
  simp only [CollatzResearch.WordTrace]
  refine ⟨247583769154739199687983471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165055846103159466458655647 247583769154739199687983471)
  ·
    refine ⟨371375653732108799531975207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247583769154739199687983471 371375653732108799531975207)
    ·
      refine ⟨557063480598163199297962811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371375653732108799531975207 557063480598163199297962811)
      ·
        refine ⟨835595220897244798946944217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557063480598163199297962811 835595220897244798946944217)
        ·
          refine ⟨626696415672933599210208163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835595220897244798946944217 626696415672933599210208163)
          ·
            refine ⟨940044623509400398815312245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626696415672933599210208163 940044623509400398815312245)
            ·
              refine ⟨88129183454006287388935523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 940044623509400398815312245 88129183454006287388935523)
              ·
                refine ⟨132193775181009431083403285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88129183454006287388935523 132193775181009431083403285)
                ·
                  refine ⟨6196583211609817082034529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132193775181009431083403285 6196583211609817082034529)
                  ·
                    refine ⟨4647437408707362811525897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6196583211609817082034529 4647437408707362811525897)
                    ·
                      refine ⟨3485578056530522108644423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647437408707362811525897 3485578056530522108644423)
                      ·
                        rfl

theorem cell23_6788139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 2, 2].length) (baseStart_6788139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788139 prefixEnd_6788139 := by exact prefixLift 6788139
  have htrace : WordTrace (prefixWord ++ tailWord_6788139) baseStart_6788139 baseEnd_6788139 := by
    simpa [prefixWord, tailWord_6788139, baseEnd_6788139] using wordTrace_append hprefix tailTrace_6788139
  have hstable : (prefixWord ++ tailWord_6788139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788139).length < 2 ^ (prefixWord ++ tailWord_6788139).sum := by decide
  have hdescent : baseEnd_6788139 < baseStart_6788139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788156 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 4, 2, 2]
def baseStart_6788156 : Nat := 118140960795 + 6788156 * 2 ^ 59
def prefixEnd_6788156 : Nat := 4983230072969 + 3 ^ 40 * 6788156 * 2
def baseEnd_6788156 : Nat := 3485586785701648542131845

theorem tailTrace_6788156 : CollatzResearch.WordTrace tailWord_6788156 prefixEnd_6788156 3485586785701648542131845 := by
  unfold tailWord_6788156
  simp only [CollatzResearch.WordTrace]
  refine ⟨123792194597838805795676161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165056259463785074394234881 123792194597838805795676161)
  ·
    refine ⟨92844145948379104346757121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123792194597838805795676161 92844145948379104346757121)
    ·
      refine ⟨69633109461284328260067841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92844145948379104346757121 69633109461284328260067841)
      ·
        refine ⟨52224832095963246195050881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69633109461284328260067841 52224832095963246195050881)
        ·
          refine ⟨39168624071972434646288161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52224832095963246195050881 39168624071972434646288161)
          ·
            refine ⟨29376468053979325984716121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39168624071972434646288161 29376468053979325984716121)
            ·
              refine ⟨22032351040484494488537091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29376468053979325984716121 22032351040484494488537091)
              ·
                refine ⟨33048526560726741732805637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22032351040484494488537091 33048526560726741732805637)
                ·
                  refine ⟨6196598730136264074901057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33048526560726741732805637 6196598730136264074901057)
                  ·
                    refine ⟨4647449047602198056175793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6196598730136264074901057 4647449047602198056175793)
                    ·
                      refine ⟨3485586785701648542131845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647449047602198056175793 3485586785701648542131845)
                      ·
                        rfl

theorem cell23_6788156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_6788156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788156 prefixEnd_6788156 := by exact prefixLift 6788156
  have htrace : WordTrace (prefixWord ++ tailWord_6788156) baseStart_6788156 baseEnd_6788156 := by
    simpa [prefixWord, tailWord_6788156, baseEnd_6788156] using wordTrace_append hprefix tailTrace_6788156
  have hstable : (prefixWord ++ tailWord_6788156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788156).length < 2 ^ (prefixWord ++ tailWord_6788156).sum := by decide
  have hdescent : baseEnd_6788156 < baseStart_6788156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788172 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 1, 5, 3]
def baseStart_6788172 : Nat := 118140960795 + 6788172 * 2 ^ 59
def prefixEnd_6788172 : Nat := 4983230072969 + 3 ^ 40 * 6788172 * 2
def baseEnd_6788172 : Nat := 3485595001392120479531771

theorem tailTrace_6788172 : CollatzResearch.WordTrace tailWord_6788172 prefixEnd_6788172 3485595001392120479531771 := by
  unfold tailWord_6788172
  simp only [CollatzResearch.WordTrace]
  refine ⟨123792486381809823161967385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165056648509079764215956513 123792486381809823161967385)
  ·
    refine ⟨92844364786357367371475539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123792486381809823161967385 92844364786357367371475539)
    ·
      refine ⟨139266547179536051057213309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92844364786357367371475539 139266547179536051057213309)
      ·
        refine ⟨52224955192326019146454991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139266547179536051057213309 52224955192326019146454991)
        ·
          refine ⟨78337432788489028719682487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52224955192326019146454991 78337432788489028719682487)
          ·
            refine ⟨117506149182733543079523731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78337432788489028719682487 117506149182733543079523731)
            ·
              refine ⟨176259223774100314619285597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117506149182733543079523731 176259223774100314619285597)
              ·
                refine ⟨66097208915287617982232099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176259223774100314619285597 66097208915287617982232099)
                ·
                  refine ⟨99145813372931426973348149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66097208915287617982232099 99145813372931426973348149)
                  ·
                    refine ⟨9294920003712321278751389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99145813372931426973348149 9294920003712321278751389)
                    ·
                      refine ⟨3485595001392120479531771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9294920003712321278751389 3485595001392120479531771)
                      ·
                        rfl

theorem cell23_6788172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_6788172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788172 prefixEnd_6788172 := by exact prefixLift 6788172
  have htrace : WordTrace (prefixWord ++ tailWord_6788172) baseStart_6788172 baseEnd_6788172 := by
    simpa [prefixWord, tailWord_6788172, baseEnd_6788172] using wordTrace_append hprefix tailTrace_6788172
  have hstable : (prefixWord ++ tailWord_6788172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788172).length < 2 ^ (prefixWord ++ tailWord_6788172).sum := by decide
  have hdescent : baseEnd_6788172 < baseStart_6788172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788190 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_6788190 : Nat := 118140960795 + 6788190 * 2 ^ 59
def prefixEnd_6788190 : Nat := 4983230072969 + 3 ^ 40 * 6788190 * 2
def baseEnd_6788190 : Nat := 3485604244043901409106689

theorem tailTrace_6788190 : CollatzResearch.WordTrace tailWord_6788190 prefixEnd_6788190 3485604244043901409106689 := by
  unfold tailWord_6788190
  simp only [CollatzResearch.WordTrace]
  refine ⟨30948203659694304424761253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165057086185036290265393349 30948203659694304424761253)
  ·
    refine ⟨5802788186192682079642735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30948203659694304424761253 5802788186192682079642735)
    ·
      refine ⟨8704182279289023119464103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5802788186192682079642735 8704182279289023119464103)
      ·
        refine ⟨13056273418933534679196155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8704182279289023119464103 13056273418933534679196155)
        ·
          refine ⟨19584410128400302018794233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13056273418933534679196155 19584410128400302018794233)
          ·
            refine ⟨14688307596300226514095675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19584410128400302018794233 14688307596300226514095675)
            ·
              refine ⟨22032461394450339771143513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14688307596300226514095675 22032461394450339771143513)
              ·
                refine ⟨16524346045837754828357635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22032461394450339771143513 16524346045837754828357635)
                ·
                  refine ⟨24786519068756632242536453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16524346045837754828357635 24786519068756632242536453)
                  ·
                    refine ⟨4647472325391868545475585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24786519068756632242536453 4647472325391868545475585)
                    ·
                      refine ⟨3485604244043901409106689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647472325391868545475585 3485604244043901409106689)
                      ·
                        rfl

theorem cell23_6788190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_6788190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788190 prefixEnd_6788190 := by exact prefixLift 6788190
  have htrace : WordTrace (prefixWord ++ tailWord_6788190) baseStart_6788190 baseEnd_6788190 := by
    simpa [prefixWord, tailWord_6788190, baseEnd_6788190] using wordTrace_append hprefix tailTrace_6788190
  have hstable : (prefixWord ++ tailWord_6788190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788190).length < 2 ^ (prefixWord ++ tailWord_6788190).sum := by decide
  have hdescent : baseEnd_6788190 < baseStart_6788190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788213 : List Nat := [1, 3, 4, 3, 1, 1, 1, 4, 5]
def baseStart_6788213 : Nat := 118140960795 + 6788213 * 2 ^ 59
def prefixEnd_6788213 : Nat := 4983230072969 + 3 ^ 40 * 6788213 * 2
def baseEnd_6788213 : Nat := 387290672677661646568787

theorem tailTrace_6788213 : CollatzResearch.WordTrace tailWord_6788213 prefixEnd_6788213 387290672677661646568787 := by
  unfold tailWord_6788213
  simp only [CollatzResearch.WordTrace]
  refine ⟨247586468156471110326177293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165057645437647406884118195 247586468156471110326177293)
  ·
    refine ⟨92844925558676666372316485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247586468156471110326177293 92844925558676666372316485)
    ·
      refine ⟨17408423542251874944809341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92844925558676666372316485 17408423542251874944809341)
      ·
        refine ⟨6528158828344453104303503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17408423542251874944809341 6528158828344453104303503)
        ·
          refine ⟨9792238242516679656455255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528158828344453104303503 9792238242516679656455255)
          ·
            refine ⟨14688357363775019484682883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9792238242516679656455255 14688357363775019484682883)
            ·
              refine ⟨22032536045662529227024325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14688357363775019484682883 22032536045662529227024325)
              ·
                refine ⟨4131100508561724230067061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22032536045662529227024325 4131100508561724230067061)
                ·
                  refine ⟨387290672677661646568787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4131100508561724230067061 387290672677661646568787)
                  ·
                    rfl

theorem cell23_6788213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_6788213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788213 prefixEnd_6788213 := by exact prefixLift 6788213
  have htrace : WordTrace (prefixWord ++ tailWord_6788213) baseStart_6788213 baseEnd_6788213 := by
    simpa [prefixWord, tailWord_6788213, baseEnd_6788213] using wordTrace_append hprefix tailTrace_6788213
  have hstable : (prefixWord ++ tailWord_6788213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788213).length < 2 ^ (prefixWord ++ tailWord_6788213).sum := by decide
  have hdescent : baseEnd_6788213 < baseStart_6788213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788273 : List Nat := [1, 2, 2, 5, 1, 1, 2, 4, 1, 4]
def baseStart_6788273 : Nat := 118140960795 + 6788273 * 2 ^ 59
def prefixEnd_6788273 : Nat := 4983230072969 + 3 ^ 40 * 6788273 * 2
def baseEnd_6788273 : Nat := 1161882287646074861456269

theorem tailTrace_6788273 : CollatzResearch.WordTrace tailWord_6788273 prefixEnd_6788273 1161882287646074861456269 := by
  unfold tailWord_6788273
  simp only [CollatzResearch.WordTrace]
  refine ⟨247588656536253740573361473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165059104357502493715574315 247588656536253740573361473)
  ·
    refine ⟨185691492402190305430021105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247588656536253740573361473 185691492402190305430021105)
    ·
      refine ⟨139268619301642729072515829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185691492402190305430021105 139268619301642729072515829)
      ·
        refine ⟨13056433059529005850548359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139268619301642729072515829 13056433059529005850548359)
        ·
          refine ⟨19584649589293508775822539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13056433059529005850548359 19584649589293508775822539)
          ·
            refine ⟨29376974383940263163733809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19584649589293508775822539 29376974383940263163733809)
            ·
              refine ⟨22032730787955197372800357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29376974383940263163733809 22032730787955197372800357)
              ·
                refine ⟨4131137022741599507400067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22032730787955197372800357 4131137022741599507400067)
                ·
                  refine ⟨6196705534112399261100101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131137022741599507400067 6196705534112399261100101)
                  ·
                    refine ⟨1161882287646074861456269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196705534112399261100101 1161882287646074861456269)
                    ·
                      rfl

theorem cell23_6788273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_6788273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788273 prefixEnd_6788273 := by exact prefixLift 6788273
  have htrace : WordTrace (prefixWord ++ tailWord_6788273) baseStart_6788273 baseEnd_6788273 := by
    simpa [prefixWord, tailWord_6788273, baseEnd_6788273] using wordTrace_append hprefix tailTrace_6788273
  have hstable : (prefixWord ++ tailWord_6788273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788273).length < 2 ^ (prefixWord ++ tailWord_6788273).sum := by decide
  have hdescent : baseEnd_6788273 < baseStart_6788273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788296 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_6788296 : Nat := 118140960795 + 6788296 * 2 ^ 59
def prefixEnd_6788296 : Nat := 4983230072969 + 3 ^ 40 * 6788296 * 2
def baseEnd_6788296 : Nat := 3485658672993277994381201

theorem tailTrace_6788296 : CollatzResearch.WordTrace tailWord_6788296 prefixEnd_6788296 3485658672993277994381201 := by
  unfold tailWord_6788296
  simp only [CollatzResearch.WordTrace]
  refine ⟨123794747707585207750724371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165059663610113610334299161 123794747707585207750724371)
  ·
    refine ⟨185692121561377811626086557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123794747707585207750724371 185692121561377811626086557)
    ·
      refine ⟨69634545585516679359782459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185692121561377811626086557 69634545585516679359782459)
      ·
        refine ⟨104451818378275019039673689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69634545585516679359782459 104451818378275019039673689)
        ·
          refine ⟨78338863783706264279755267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104451818378275019039673689 78338863783706264279755267)
          ·
            refine ⟨117508295675559396419632901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78338863783706264279755267 117508295675559396419632901)
            ·
              refine ⟨22032805439167386828681169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117508295675559396419632901 22032805439167386828681169)
              ·
                refine ⟨16524604079375540121510877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22032805439167386828681169 16524604079375540121510877)
                ·
                  refine ⟨6196726529765827545566579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16524604079375540121510877 6196726529765827545566579)
                  ·
                    refine ⟨9295089794648741318349869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6196726529765827545566579 9295089794648741318349869)
                    ·
                      refine ⟨3485658672993277994381201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9295089794648741318349869 3485658672993277994381201)
                      ·
                        rfl

theorem cell23_6788296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_6788296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788296 prefixEnd_6788296 := by exact prefixLift 6788296
  have htrace : WordTrace (prefixWord ++ tailWord_6788296) baseStart_6788296 baseEnd_6788296 := by
    simpa [prefixWord, tailWord_6788296, baseEnd_6788296] using wordTrace_append hprefix tailTrace_6788296
  have hstable : (prefixWord ++ tailWord_6788296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788296).length < 2 ^ (prefixWord ++ tailWord_6788296).sum := by decide
  have hdescent : baseEnd_6788296 < baseStart_6788296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788306 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_6788306 : Nat := 118140960795 + 6788306 * 2 ^ 59
def prefixEnd_6788306 : Nat := 4983230072969 + 3 ^ 40 * 6788306 * 2
def baseEnd_6788306 : Nat := 3485663807799822955256155

theorem tailTrace_6788306 : CollatzResearch.WordTrace tailWord_6788306 prefixEnd_6788306 3485663807799822955256155 := by
  unfold tailWord_6788306
  simp only [CollatzResearch.WordTrace]
  refine ⟨61897465036283546802328193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165059906763422791472875181 61897465036283546802328193)
  ·
    refine ⟨46423098777212660101746145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61897465036283546802328193 46423098777212660101746145)
    ·
      refine ⟨34817324082909495076309609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46423098777212660101746145 34817324082909495076309609)
      ·
        refine ⟨26112993062182121307232207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34817324082909495076309609 26112993062182121307232207)
        ·
          refine ⟨39169489593273181960848311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26112993062182121307232207 39169489593273181960848311)
          ·
            refine ⟨58754234389909772941272467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39169489593273181960848311 58754234389909772941272467)
            ·
              refine ⟨88131351584864659411908701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58754234389909772941272467 88131351584864659411908701)
              ·
                refine ⟨33049256844324247279465763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88131351584864659411908701 33049256844324247279465763)
                ·
                  refine ⟨49573885266486370919198645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33049256844324247279465763 49573885266486370919198645)
                  ·
                    refine ⟨4647551743733097273674873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49573885266486370919198645 4647551743733097273674873)
                    ·
                      refine ⟨3485663807799822955256155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647551743733097273674873 3485663807799822955256155)
                      ·
                        rfl

theorem cell23_6788306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_6788306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788306 prefixEnd_6788306 := by exact prefixLift 6788306
  have htrace : WordTrace (prefixWord ++ tailWord_6788306) baseStart_6788306 baseEnd_6788306 := by
    simpa [prefixWord, tailWord_6788306, baseEnd_6788306] using wordTrace_append hprefix tailTrace_6788306
  have hstable : (prefixWord ++ tailWord_6788306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788306).length < 2 ^ (prefixWord ++ tailWord_6788306).sum := by decide
  have hdescent : baseEnd_6788306 < baseStart_6788306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788339 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 5]
def baseStart_6788339 : Nat := 118140960795 + 6788339 * 2 ^ 59
def prefixEnd_6788339 : Nat := 4983230072969 + 3 ^ 40 * 6788339 * 2
def baseEnd_6788339 : Nat := 3485680752661421326143503

theorem tailTrace_6788339 : CollatzResearch.WordTrace tailWord_6788339 prefixEnd_6788339 3485680752661421326143503 := by
  unfold tailWord_6788339
  simp only [CollatzResearch.WordTrace]
  refine ⟨247591063754014633845264071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165060709169343089230176047 247591063754014633845264071)
  ·
    refine ⟨371386595631021950767896107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247591063754014633845264071 371386595631021950767896107)
    ·
      refine ⟨557079893446532926151844161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371386595631021950767896107 557079893446532926151844161)
      ·
        refine ⟨417809920084899694613883121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557079893446532926151844161 417809920084899694613883121)
        ·
          refine ⟨313357440063674770960412341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417809920084899694613883121 313357440063674770960412341)
          ·
            refine ⟨29377260005969509777538657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 313357440063674770960412341 29377260005969509777538657)
            ·
              refine ⟨22032945004477132333153993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29377260005969509777538657 22032945004477132333153993)
              ·
                refine ⟨16524708753357849249865495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22032945004477132333153993 16524708753357849249865495)
                ·
                  refine ⟨24787063130036773874798243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16524708753357849249865495 24787063130036773874798243)
                  ·
                    refine ⟨37180594695055160812197365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24787063130036773874798243 37180594695055160812197365)
                    ·
                      refine ⟨3485680752661421326143503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37180594695055160812197365 3485680752661421326143503)
                      ·
                        rfl

theorem cell23_6788339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_6788339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788339 prefixEnd_6788339 := by exact prefixLift 6788339
  have htrace : WordTrace (prefixWord ++ tailWord_6788339) baseStart_6788339 baseEnd_6788339 := by
    simpa [prefixWord, tailWord_6788339, baseEnd_6788339] using wordTrace_append hprefix tailTrace_6788339
  have hstable : (prefixWord ++ tailWord_6788339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788339).length < 2 ^ (prefixWord ++ tailWord_6788339).sum := by decide
  have hdescent : baseEnd_6788339 < baseStart_6788339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788346 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 2, 4]
def baseStart_6788346 : Nat := 118140960795 + 6788346 * 2 ^ 59
def prefixEnd_6788346 : Nat := 4983230072969 + 3 ^ 40 * 6788346 * 2
def baseEnd_6788346 : Nat := 1161894782342000932918657

theorem tailTrace_6788346 : CollatzResearch.WordTrace tailWord_6788346 prefixEnd_6788346 1161894782342000932918657 := by
  unfold tailWord_6788346
  simp only [CollatzResearch.WordTrace]
  refine ⟨61897829766247318510192223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165060879376659516027179261 61897829766247318510192223)
  ·
    refine ⟨92846744649370977765288335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61897829766247318510192223 92846744649370977765288335)
    ·
      refine ⟨139270116974056466647932503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92846744649370977765288335 139270116974056466647932503)
      ·
        refine ⟨208905175461084699971898755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139270116974056466647932503 208905175461084699971898755)
        ·
          refine ⟨313357763191627049957848133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208905175461084699971898755 313357763191627049957848133)
          ·
            refine ⟨58754580598430071867096525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313357763191627049957848133 58754580598430071867096525)
            ·
              refine ⟨22032967724411276950161197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58754580598430071867096525 22032967724411276950161197)
              ·
                refine ⟨8262362896654228856310449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22032967724411276950161197 8262362896654228856310449)
                ·
                  refine ⟨6196772172490671642232837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8262362896654228856310449 6196772172490671642232837)
                  ·
                    refine ⟨1161894782342000932918657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196772172490671642232837 1161894782342000932918657)
                    ·
                      rfl

theorem cell23_6788346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_6788346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788346 prefixEnd_6788346 := by exact prefixLift 6788346
  have htrace : WordTrace (prefixWord ++ tailWord_6788346) baseStart_6788346 baseEnd_6788346 := by
    simpa [prefixWord, tailWord_6788346, baseEnd_6788346] using wordTrace_append hprefix tailTrace_6788346
  have hstable : (prefixWord ++ tailWord_6788346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788346).length < 2 ^ (prefixWord ++ tailWord_6788346).sum := by decide
  have hdescent : baseEnd_6788346 < baseStart_6788346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788353 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_6788353 : Nat := 118140960795 + 6788353 * 2 ^ 59
def prefixEnd_6788353 : Nat := 4983230072969 + 3 ^ 40 * 6788353 * 2
def baseEnd_6788353 : Nat := 3485687941390584271368439

theorem tailTrace_6788353 : CollatzResearch.WordTrace tailWord_6788353 prefixEnd_6788353 3485687941390584271368439 := by
  unfold tailWord_6788353
  simp only [CollatzResearch.WordTrace]
  refine ⟨247591574375963914236273713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165061049583975942824182475 247591574375963914236273713)
  ·
    refine ⟨185693680781972935677205285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247591574375963914236273713 185693680781972935677205285)
    ·
      refine ⟨34817565146619925439475991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185693680781972935677205285 34817565146619925439475991)
      ·
        refine ⟨52226347719929888159213987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34817565146619925439475991 52226347719929888159213987)
        ·
          refine ⟨78339521579894832238820981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52226347719929888159213987 78339521579894832238820981)
          ·
            refine ⟨7344330148115140522389467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78339521579894832238820981 7344330148115140522389467)
            ·
              refine ⟨11016495222172710783584201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7344330148115140522389467 11016495222172710783584201)
              ·
                refine ⟨8262371416629533087688151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11016495222172710783584201 8262371416629533087688151)
                ·
                  refine ⟨12393557124944299631532227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8262371416629533087688151 12393557124944299631532227)
                  ·
                    refine ⟨18590335687416449447298341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12393557124944299631532227 18590335687416449447298341)
                    ·
                      refine ⟨3485687941390584271368439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18590335687416449447298341 3485687941390584271368439)
                      ·
                        rfl

theorem cell23_6788353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_6788353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788353 prefixEnd_6788353 := by exact prefixLift 6788353
  have htrace : WordTrace (prefixWord ++ tailWord_6788353) baseStart_6788353 baseEnd_6788353 := by
    simpa [prefixWord, tailWord_6788353, baseEnd_6788353] using wordTrace_append hprefix tailTrace_6788353
  have hstable : (prefixWord ++ tailWord_6788353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788353).length < 2 ^ (prefixWord ++ tailWord_6788353).sum := by decide
  have hdescent : baseEnd_6788353 < baseStart_6788353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788366 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_6788366 : Nat := 118140960795 + 6788366 * 2 ^ 59
def prefixEnd_6788366 : Nat := 4983230072969 + 3 ^ 40 * 6788366 * 2
def baseEnd_6788366 : Nat := 3485694616639092720505879

theorem tailTrace_6788366 : CollatzResearch.WordTrace tailWord_6788366 prefixEnd_6788366 3485694616639092720505879 := by
  unfold tailWord_6788366
  simp only [CollatzResearch.WordTrace]
  refine ⟨30949006065614602182062119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165061365683277878304331301 30949006065614602182062119)
  ·
    refine ⟨46423509098421903273093179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30949006065614602182062119 46423509098421903273093179)
    ·
      refine ⟨69635263647632854909639769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46423509098421903273093179 69635263647632854909639769)
      ·
        refine ⟨52226447735724641182229827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69635263647632854909639769 52226447735724641182229827)
        ·
          refine ⟨78339671603586961773344741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52226447735724641182229827 78339671603586961773344741)
          ·
            refine ⟨14688688425672555332502139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78339671603586961773344741 14688688425672555332502139)
            ·
              refine ⟨22033032638508832998753209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14688688425672555332502139 22033032638508832998753209)
              ·
                refine ⟨16524774478881624749064907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22033032638508832998753209 16524774478881624749064907)
                ·
                  refine ⟨24787161718322437123597361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16524774478881624749064907 24787161718322437123597361)
                  ·
                    refine ⟨18590371288741827842698021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24787161718322437123597361 18590371288741827842698021)
                    ·
                      refine ⟨3485694616639092720505879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18590371288741827842698021 3485694616639092720505879)
                      ·
                        rfl

theorem cell23_6788366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_6788366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788366 prefixEnd_6788366 := by exact prefixLift 6788366
  have htrace : WordTrace (prefixWord ++ tailWord_6788366) baseStart_6788366 baseEnd_6788366 := by
    simpa [prefixWord, tailWord_6788366, baseEnd_6788366] using wordTrace_append hprefix tailTrace_6788366
  have hstable : (prefixWord ++ tailWord_6788366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788366).length < 2 ^ (prefixWord ++ tailWord_6788366).sum := by decide
  have hdescent : baseEnd_6788366 < baseStart_6788366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788387 : List Nat := [1, 1, 1, 4, 2, 3, 4, 2, 1, 2, 2]
def baseStart_6788387 : Nat := 118140960795 + 6788387 * 2 ^ 59
def prefixEnd_6788387 : Nat := 4983230072969 + 3 ^ 40 * 6788387 * 2
def baseEnd_6788387 : Nat := 3485705399732837138343283

theorem tailTrace_6788387 : CollatzResearch.WordTrace tailWord_6788387 prefixEnd_6788387 3485705399732837138343283 := by
  unfold tailWord_6788387
  simp only [CollatzResearch.WordTrace]
  refine ⟨247592814457840738043011415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165061876305227158695340943 247592814457840738043011415)
  ·
    refine ⟨371389221686761107064517123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247592814457840738043011415 371389221686761107064517123)
    ·
      refine ⟨557083832530141660596775685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371389221686761107064517123 557083832530141660596775685)
      ·
        refine ⟨104453218599401561361895441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 557083832530141660596775685 104453218599401561361895441)
        ·
          refine ⟨78339913949551171021421581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104453218599401561361895441 78339913949551171021421581)
          ·
            refine ⟨29377467731081689133033093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78339913949551171021421581 29377467731081689133033093)
            ·
              refine ⟨5508275199577816712443705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29377467731081689133033093 5508275199577816712443705)
              ·
                refine ⟨4131206399683362534332779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5508275199577816712443705 4131206399683362534332779)
                ·
                  refine ⟨6196809599525043801499169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131206399683362534332779 6196809599525043801499169)
                  ·
                    refine ⟨4647607199643782851124377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6196809599525043801499169 4647607199643782851124377)
                    ·
                      refine ⟨3485705399732837138343283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647607199643782851124377 3485705399732837138343283)
                      ·
                        rfl

theorem cell23_6788387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_6788387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788387 prefixEnd_6788387 := by exact prefixLift 6788387
  have htrace : WordTrace (prefixWord ++ tailWord_6788387) baseStart_6788387 baseEnd_6788387 := by
    simpa [prefixWord, tailWord_6788387, baseEnd_6788387] using wordTrace_append hprefix tailTrace_6788387
  have hstable : (prefixWord ++ tailWord_6788387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788387).length < 2 ^ (prefixWord ++ tailWord_6788387).sum := by decide
  have hdescent : baseEnd_6788387 < baseStart_6788387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788389 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_6788389 : Nat := 118140960795 + 6788389 * 2 ^ 59
def prefixEnd_6788389 : Nat := 4983230072969 + 3 ^ 40 * 6788389 * 2
def baseEnd_6788389 : Nat := 1161902142231382043506091

theorem tailTrace_6788389 : CollatzResearch.WordTrace tailWord_6788389 prefixEnd_6788389 1161902142231382043506091 := by
  unfold tailWord_6788389
  simp only [CollatzResearch.WordTrace]
  refine ⟨247592887403833492384584221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165061924935888994923056147 247592887403833492384584221)
  ·
    refine ⟨92847332776437559644219083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247592887403833492384584221 92847332776437559644219083)
    ·
      refine ⟨139270999164656339466328625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92847332776437559644219083 139270999164656339466328625)
      ·
        refine ⟨104453249373492254599746469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139270999164656339466328625 104453249373492254599746469)
        ·
          refine ⟨19584984257529797737452463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104453249373492254599746469 19584984257529797737452463)
          ·
            refine ⟨29377476386294696606178695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19584984257529797737452463 29377476386294696606178695)
            ·
              refine ⟨44066214579442044909268043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29377476386294696606178695 44066214579442044909268043)
              ·
                refine ⟨66099321869163067363902065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44066214579442044909268043 66099321869163067363902065)
                ·
                  refine ⟨49574491401872300522926549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66099321869163067363902065 49574491401872300522926549)
                  ·
                    refine ⟨1161902142231382043506091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49574491401872300522926549 1161902142231382043506091)
                    ·
                      rfl

theorem cell23_6788389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_6788389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788389 prefixEnd_6788389 := by exact prefixLift 6788389
  have htrace : WordTrace (prefixWord ++ tailWord_6788389) baseStart_6788389 baseEnd_6788389 := by
    simpa [prefixWord, tailWord_6788389, baseEnd_6788389] using wordTrace_append hprefix tailTrace_6788389
  have hstable : (prefixWord ++ tailWord_6788389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788389).length < 2 ^ (prefixWord ++ tailWord_6788389).sum := by decide
  have hdescent : baseEnd_6788389 < baseStart_6788389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788403 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 2, 1, 3]
def baseStart_6788403 : Nat := 118140960795 + 6788403 * 2 ^ 59
def prefixEnd_6788403 : Nat := 4983230072969 + 3 ^ 40 * 6788403 * 2
def baseEnd_6788403 : Nat := 3485713615423309075743209

theorem tailTrace_6788403 : CollatzResearch.WordTrace tailWord_6788403 prefixEnd_6788403 3485713615423309075743209 := by
  unfold tailWord_6788403
  simp only [CollatzResearch.WordTrace]
  refine ⟨247593398025782772775593863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165062265350521848517062575 247593398025782772775593863)
  ·
    refine ⟨371390097038674159163390795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247593398025782772775593863 371390097038674159163390795)
    ·
      refine ⟨557085145558011238745086193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371390097038674159163390795 557085145558011238745086193)
      ·
        refine ⟨417813859168508429058814645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557085145558011238745086193 417813859168508429058814645)
        ·
          refine ⟨39170049297047665224263873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 417813859168508429058814645 39170049297047665224263873)
          ·
            refine ⟨29377536972785748918197905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39170049297047665224263873 29377536972785748918197905)
            ·
              refine ⟨22033152729589311688648429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29377536972785748918197905 22033152729589311688648429)
              ·
                refine ⟨8262432273595991883243161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22033152729589311688648429 8262432273595991883243161)
                ·
                  refine ⟨6196824205196993912432371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8262432273595991883243161 6196824205196993912432371)
                  ·
                    refine ⟨9295236307795490868648557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6196824205196993912432371 9295236307795490868648557)
                    ·
                      refine ⟨3485713615423309075743209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9295236307795490868648557 3485713615423309075743209)
                      ·
                        rfl

theorem cell23_6788403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 1, 3].length) (baseStart_6788403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788403 prefixEnd_6788403 := by exact prefixLift 6788403
  have htrace : WordTrace (prefixWord ++ tailWord_6788403) baseStart_6788403 baseEnd_6788403 := by
    simpa [prefixWord, tailWord_6788403, baseEnd_6788403] using wordTrace_append hprefix tailTrace_6788403
  have hstable : (prefixWord ++ tailWord_6788403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788403).length < 2 ^ (prefixWord ++ tailWord_6788403).sum := by decide
  have hdescent : baseEnd_6788403 < baseStart_6788403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788460 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 1, 4, 2]
def baseStart_6788460 : Nat := 118140960795 + 6788460 * 2 ^ 59
def prefixEnd_6788460 : Nat := 4983230072969 + 3 ^ 40 * 6788460 * 2
def baseEnd_6788460 : Nat := 3485742883820615352730447

theorem tailTrace_6788460 : CollatzResearch.WordTrace tailWord_6788460 prefixEnd_6788460 3485742883820615352730447 := by
  unfold tailWord_6788460
  simp only [CollatzResearch.WordTrace]
  refine ⟨123797738493288135755209417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165063651324384181006945889 123797738493288135755209417)
  ·
    refine ⟨92848303869966101816407063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123797738493288135755209417 92848303869966101816407063)
    ·
      refine ⟨139272455804949152724610595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92848303869966101816407063 139272455804949152724610595)
      ·
        refine ⟨208908683707423729086915893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139272455804949152724610595 208908683707423729086915893)
        ·
          refine ⟨19585189097570974601898365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208908683707423729086915893 19585189097570974601898365)
          ·
            refine ⟨7344445911589115475711887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19585189097570974601898365 7344445911589115475711887)
            ·
              refine ⟨11016668867383673213567831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7344445911589115475711887 11016668867383673213567831)
              ·
                refine ⟨16525003301075509820351747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11016668867383673213567831 16525003301075509820351747)
                ·
                  refine ⟨24787504951613264730527621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16525003301075509820351747 24787504951613264730527621)
                  ·
                    refine ⟨4647657178427487136973929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24787504951613264730527621 4647657178427487136973929)
                    ·
                      refine ⟨3485742883820615352730447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647657178427487136973929 3485742883820615352730447)
                      ·
                        rfl

theorem cell23_6788460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 4, 2].length) (baseStart_6788460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788460 prefixEnd_6788460 := by exact prefixLift 6788460
  have htrace : WordTrace (prefixWord ++ tailWord_6788460) baseStart_6788460 baseEnd_6788460 := by
    simpa [prefixWord, tailWord_6788460, baseEnd_6788460] using wordTrace_append hprefix tailTrace_6788460
  have hstable : (prefixWord ++ tailWord_6788460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788460).length < 2 ^ (prefixWord ++ tailWord_6788460).sum := by decide
  have hdescent : baseEnd_6788460 < baseStart_6788460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788483 : List Nat := [1, 1, 1, 3, 5, 1, 3, 3, 5]
def baseStart_6788483 : Nat := 118140960795 + 6788483 * 2 ^ 59
def prefixEnd_6788483 : Nat := 4983230072969 + 3 ^ 40 * 6788483 * 2
def baseEnd_6788483 : Nat := 387306077097296529193649

theorem tailTrace_6788483 : CollatzResearch.WordTrace tailWord_6788483 prefixEnd_6788483 387306077097296529193649 := by
  unfold tailWord_6788483
  simp only [CollatzResearch.WordTrace]
  refine ⟨247596315865492946438506103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165064210576995297625670735 247596315865492946438506103)
  ·
    refine ⟨371394473798239419657759155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247596315865492946438506103 371394473798239419657759155)
    ·
      refine ⟨557091710697359129486638733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371394473798239419657759155 557091710697359129486638733)
      ·
        refine ⟨208909391511509673557489525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 557091710697359129486638733 208909391511509673557489525)
        ·
          refine ⟨19585255454204031896014643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208909391511509673557489525 19585255454204031896014643)
          ·
            refine ⟨29377883181306047844021965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19585255454204031896014643 29377883181306047844021965)
            ·
              refine ⟨11016706192989767941508237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29377883181306047844021965 11016706192989767941508237)
              ·
                refine ⟨4131264822371162978065589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11016706192989767941508237 4131264822371162978065589)
                ·
                  refine ⟨387306077097296529193649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4131264822371162978065589 387306077097296529193649)
                  ·
                    rfl

theorem cell23_6788483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 5].length) (baseStart_6788483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788483 prefixEnd_6788483 := by exact prefixLift 6788483
  have htrace : WordTrace (prefixWord ++ tailWord_6788483) baseStart_6788483 baseEnd_6788483 := by
    simpa [prefixWord, tailWord_6788483, baseEnd_6788483] using wordTrace_append hprefix tailTrace_6788483
  have hstable : (prefixWord ++ tailWord_6788483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788483).length < 2 ^ (prefixWord ++ tailWord_6788483).sum := by decide
  have hdescent : baseEnd_6788483 < baseStart_6788483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788499 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 4]
def baseStart_6788499 : Nat := 118140960795 + 6788499 * 2 ^ 59
def prefixEnd_6788499 : Nat := 4983230072969 + 3 ^ 40 * 6788499 * 2
def baseEnd_6788499 : Nat := 3485762909566140700142767

theorem tailTrace_6788499 : CollatzResearch.WordTrace tailWord_6788499 prefixEnd_6788499 3485762909566140700142767 := by
  unfold tailWord_6788499
  simp only [CollatzResearch.WordTrace]
  refine ⟨247596899433434981171088551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165064599622289987447392367 247596899433434981171088551)
  ·
    refine ⟨371395349150152471756632827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247596899433434981171088551 371395349150152471756632827)
    ·
      refine ⟨557093023725228707634949241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371395349150152471756632827 557093023725228707634949241)
      ·
        refine ⟨417819767793921530726211931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557093023725228707634949241 417819767793921530726211931)
        ·
          refine ⟨626729651690882296089317897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417819767793921530726211931 626729651690882296089317897)
          ·
            refine ⟨470047238768161722066988423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626729651690882296089317897 470047238768161722066988423)
            ·
              refine ⟨705070858152242583100482635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470047238768161722066988423 705070858152242583100482635)
              ·
                refine ⟨1057606287228363874650723953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705070858152242583100482635 1057606287228363874650723953)
                ·
                  refine ⟨793204715421272905988042965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1057606287228363874650723953 793204715421272905988042965)
                  ·
                    refine ⟨18590735517686083734094757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 793204715421272905988042965 18590735517686083734094757)
                    ·
                      refine ⟨3485762909566140700142767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18590735517686083734094757 3485762909566140700142767)
                      ·
                        rfl

theorem cell23_6788499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_6788499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788499 prefixEnd_6788499 := by exact prefixLift 6788499
  have htrace : WordTrace (prefixWord ++ tailWord_6788499) baseStart_6788499 baseEnd_6788499 := by
    simpa [prefixWord, tailWord_6788499, baseEnd_6788499] using wordTrace_append hprefix tailTrace_6788499
  have hstable : (prefixWord ++ tailWord_6788499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788499).length < 2 ^ (prefixWord ++ tailWord_6788499).sum := by decide
  have hdescent : baseEnd_6788499 < baseStart_6788499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788506 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_6788506 : Nat := 118140960795 + 6788506 * 2 ^ 59
def prefixEnd_6788506 : Nat := 4983230072969 + 3 ^ 40 * 6788506 * 2
def baseEnd_6788506 : Nat := 3485766503930722172755235

theorem tailTrace_6788506 : CollatzResearch.WordTrace tailWord_6788506 prefixEnd_6788506 3485766503930722172755235 := by
  unfold tailWord_6788506
  simp only [CollatzResearch.WordTrace]
  refine ⟨61899288686102405341648343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165064769829606414244395581 61899288686102405341648343)
  ·
    refine ⟨92848933029153608012472515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61899288686102405341648343 92848933029153608012472515)
    ·
      refine ⟨139273399543730412018708773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92848933029153608012472515 139273399543730412018708773)
      ·
        refine ⟨26113762414449452253507895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139273399543730412018708773 26113762414449452253507895)
        ·
          refine ⟨39170643621674178380261843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26113762414449452253507895 39170643621674178380261843)
          ·
            refine ⟨58755965432511267570392765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39170643621674178380261843 58755965432511267570392765)
            ·
              refine ⟨22033487037191725338897287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58755965432511267570392765 22033487037191725338897287)
              ·
                refine ⟨33050230555787588008345931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22033487037191725338897287 33050230555787588008345931)
                ·
                  refine ⟨49575345833681382012518897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33050230555787588008345931 49575345833681382012518897)
                  ·
                    refine ⟨37181509375261036509389173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49575345833681382012518897 37181509375261036509389173)
                    ·
                      refine ⟨3485766503930722172755235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37181509375261036509389173 3485766503930722172755235)
                      ·
                        rfl

theorem cell23_6788506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_6788506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788506 prefixEnd_6788506 := by exact prefixLift 6788506
  have htrace : WordTrace (prefixWord ++ tailWord_6788506) baseStart_6788506 baseEnd_6788506 := by
    simpa [prefixWord, tailWord_6788506, baseEnd_6788506] using wordTrace_append hprefix tailTrace_6788506
  have hstable : (prefixWord ++ tailWord_6788506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788506).length < 2 ^ (prefixWord ++ tailWord_6788506).sum := by decide
  have hdescent : baseEnd_6788506 < baseStart_6788506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788516 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_6788516 : Nat := 118140960795 + 6788516 * 2 ^ 59
def prefixEnd_6788516 : Nat := 4983230072969 + 3 ^ 40 * 6788516 * 2
def baseEnd_6788516 : Nat := 3485771638737267133630189

theorem tailTrace_6788516 : CollatzResearch.WordTrace tailWord_6788516 prefixEnd_6788516 3485771638737267133630189 := by
  unfold tailWord_6788516
  simp only [CollatzResearch.WordTrace]
  refine ⟨123798759737186696537228701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165065012982915595382971601 123798759737186696537228701)
  ·
    refine ⟨46424534901445011201460763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123798759737186696537228701 46424534901445011201460763)
    ·
      refine ⟨69636802352167516802191145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46424534901445011201460763 69636802352167516802191145)
      ·
        refine ⟨52227601764125637601643359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69636802352167516802191145 52227601764125637601643359)
        ·
          refine ⟨78341402646188456402465039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52227601764125637601643359 78341402646188456402465039)
          ·
            refine ⟨117512103969282684603697559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78341402646188456402465039 117512103969282684603697559)
            ·
              refine ⟨176268155953924026905546339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117512103969282684603697559 176268155953924026905546339)
              ·
                refine ⟨264402233930886040358319509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176268155953924026905546339 264402233930886040358319509)
                ·
                  refine ⟨12393854715510283141796227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 264402233930886040358319509 12393854715510283141796227)
                  ·
                    refine ⟨18590782073265424712694341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12393854715510283141796227 18590782073265424712694341)
                    ·
                      refine ⟨3485771638737267133630189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18590782073265424712694341 3485771638737267133630189)
                      ·
                        rfl

theorem cell23_6788516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_6788516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788516 prefixEnd_6788516 := by exact prefixLift 6788516
  have htrace : WordTrace (prefixWord ++ tailWord_6788516) baseStart_6788516 baseEnd_6788516 := by
    simpa [prefixWord, tailWord_6788516, baseEnd_6788516] using wordTrace_append hprefix tailTrace_6788516
  have hstable : (prefixWord ++ tailWord_6788516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788516).length < 2 ^ (prefixWord ++ tailWord_6788516).sum := by decide
  have hdescent : baseEnd_6788516 < baseStart_6788516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788533 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_6788533 : Nat := 118140960795 + 6788533 * 2 ^ 59
def prefixEnd_6788533 : Nat := 4983230072969 + 3 ^ 40 * 6788533 * 2
def baseEnd_6788533 : Nat := 3485780367908393567117611

theorem tailTrace_6788533 : CollatzResearch.WordTrace tailWord_6788533 prefixEnd_6788533 3485780367908393567117611 := by
  unfold tailWord_6788533
  simp only [CollatzResearch.WordTrace]
  refine ⟨247598139515311804977826253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165065426343541203318550835 247598139515311804977826253)
  ·
    refine ⟨92849302318241926866684845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247598139515311804977826253 92849302318241926866684845)
    ·
      refine ⟨34818488369340722575006817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92849302318241926866684845 34818488369340722575006817)
      ·
        refine ⟨26113866277005541931255113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34818488369340722575006817 26113866277005541931255113)
        ·
          refine ⟨19585399707754156448441335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26113866277005541931255113 19585399707754156448441335)
          ·
            refine ⟨29378099561631234672662003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19585399707754156448441335 29378099561631234672662003)
            ·
              refine ⟨44067149342446852008993005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29378099561631234672662003 44067149342446852008993005)
              ·
                refine ⟨16525181003417569503372377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44067149342446852008993005 16525181003417569503372377)
                ·
                  refine ⟨12393885752563177127529283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16525181003417569503372377 12393885752563177127529283)
                  ·
                    refine ⟨18590828628844765691293925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12393885752563177127529283 18590828628844765691293925)
                    ·
                      refine ⟨3485780367908393567117611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18590828628844765691293925 3485780367908393567117611)
                      ·
                        rfl

theorem cell23_6788533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_6788533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788533 prefixEnd_6788533 := by exact prefixLift 6788533
  have htrace : WordTrace (prefixWord ++ tailWord_6788533) baseStart_6788533 baseEnd_6788533 := by
    simpa [prefixWord, tailWord_6788533, baseEnd_6788533] using wordTrace_append hprefix tailTrace_6788533
  have hstable : (prefixWord ++ tailWord_6788533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788533).length < 2 ^ (prefixWord ++ tailWord_6788533).sum := by decide
  have hdescent : baseEnd_6788533 < baseStart_6788533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788536 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 1, 4, 3]
def baseStart_6788536 : Nat := 118140960795 + 6788536 * 2 ^ 59
def prefixEnd_6788536 : Nat := 4983230072969 + 3 ^ 40 * 6788536 * 2
def baseEnd_6788536 : Nat := 3485781908350357055380097

theorem tailTrace_6788536 : CollatzResearch.WordTrace tailWord_6788536 prefixEnd_6788536 3485781908350357055380097 := by
  unfold tailWord_6788536
  simp only [CollatzResearch.WordTrace]
  refine ⟨123799124467150468245092731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165065499289533957660123641 123799124467150468245092731)
  ·
    refine ⟨185698686700725702367639097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123799124467150468245092731 185698686700725702367639097)
    ·
      refine ⟨139274015025544276775729323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185698686700725702367639097 139274015025544276775729323)
      ·
        refine ⟨208911022538316415163593985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139274015025544276775729323 208911022538316415163593985)
        ·
          refine ⟨156683266903737311372695489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208911022538316415163593985 156683266903737311372695489)
          ·
            refine ⟨117512450177802983529521617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156683266903737311372695489 117512450177802983529521617)
            ·
              refine ⟨88134337633352237647141213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117512450177802983529521617 88134337633352237647141213)
              ·
                refine ⟨33050376612507089117677955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88134337633352237647141213 33050376612507089117677955)
                ·
                  refine ⟨49575564918760633676516933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33050376612507089117677955 49575564918760633676516933)
                  ·
                    refine ⟨9295418422267618814346925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49575564918760633676516933 9295418422267618814346925)
                    ·
                      refine ⟨3485781908350357055380097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9295418422267618814346925 3485781908350357055380097)
                      ·
                        rfl

theorem cell23_6788536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_6788536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788536 prefixEnd_6788536 := by exact prefixLift 6788536
  have htrace : WordTrace (prefixWord ++ tailWord_6788536) baseStart_6788536 baseEnd_6788536 := by
    simpa [prefixWord, tailWord_6788536, baseEnd_6788536] using wordTrace_append hprefix tailTrace_6788536
  have hstable : (prefixWord ++ tailWord_6788536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788536).length < 2 ^ (prefixWord ++ tailWord_6788536).sum := by decide
  have hdescent : baseEnd_6788536 < baseStart_6788536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788573 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 6]
def baseStart_6788573 : Nat := 118140960795 + 6788573 * 2 ^ 59
def prefixEnd_6788573 : Nat := 4983230072969 + 3 ^ 40 * 6788573 * 2
def baseEnd_6788573 : Nat := 387311211903841490068603

theorem tailTrace_6788573 : CollatzResearch.WordTrace tailWord_6788573 prefixEnd_6788573 387311211903841490068603 := by
  unfold tailWord_6788573
  simp only [CollatzResearch.WordTrace]
  refine ⟨247599598435166891809282373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165066398956777927872854915 247599598435166891809282373)
  ·
    refine ⟨46424924706593792214240445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247599598435166891809282373 46424924706593792214240445)
    ·
      refine ⟨17409346764972672080340167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46424924706593792214240445 17409346764972672080340167)
      ·
        refine ⟨26114020147459008120510251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17409346764972672080340167 26114020147459008120510251)
        ·
          refine ⟨39171030221188512180765377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26114020147459008120510251 39171030221188512180765377)
          ·
            refine ⟨29378272665891384135574033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39171030221188512180765377 29378272665891384135574033)
            ·
              refine ⟨22033704499418538101680525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29378272665891384135574033 22033704499418538101680525)
              ·
                refine ⟨8262639187281951788130197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22033704499418538101680525 8262639187281951788130197)
                ·
                  refine ⟨387311211903841490068603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8262639187281951788130197 387311211903841490068603)
                  ·
                    rfl

theorem cell23_6788573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_6788573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788573 prefixEnd_6788573 := by exact prefixLift 6788573
  have htrace : WordTrace (prefixWord ++ tailWord_6788573) baseStart_6788573 baseEnd_6788573 := by
    simpa [prefixWord, tailWord_6788573, baseEnd_6788573] using wordTrace_append hprefix tailTrace_6788573
  have hstable : (prefixWord ++ tailWord_6788573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788573).length < 2 ^ (prefixWord ++ tailWord_6788573).sum := by decide
  have hdescent : baseEnd_6788573 < baseStart_6788573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788616 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 3, 6]
def baseStart_6788616 : Nat := 118140960795 + 6788616 * 2 ^ 59
def prefixEnd_6788616 : Nat := 4983230072969 + 3 ^ 40 * 6788616 * 2
def baseEnd_6788616 : Nat := 1161940995600905580793243

theorem tailTrace_6788616 : CollatzResearch.WordTrace tailWord_6788616 prefixEnd_6788616 1161940995600905580793243 := by
  unfold tailWord_6788616
  simp only [CollatzResearch.WordTrace]
  refine ⟨123800583387005555076548851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165067444516007406768731801 123800583387005555076548851)
  ·
    refine ⟨185700875080508332614823277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123800583387005555076548851 185700875080508332614823277)
    ·
      refine ⟨69637828155190624730558729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185700875080508332614823277 69637828155190624730558729)
      ·
        refine ⟨52228371116392968547919047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69637828155190624730558729 52228371116392968547919047)
        ·
          refine ⟨78342556674589452821878571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52228371116392968547919047 78342556674589452821878571)
          ·
            refine ⟨117513835011884179232817857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78342556674589452821878571 117513835011884179232817857)
            ·
              refine ⟨88135376258913134424613393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117513835011884179232817857 88135376258913134424613393)
              ·
                refine ⟨66101532194184850818460045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88135376258913134424613393 66101532194184850818460045)
                ·
                  refine ⟨24788074572819319056922517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66101532194184850818460045 24788074572819319056922517)
                  ·
                    refine ⟨1161940995600905580793243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24788074572819319056922517 1161940995600905580793243)
                    ·
                      rfl

theorem cell23_6788616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_6788616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788616 prefixEnd_6788616 := by exact prefixLift 6788616
  have htrace : WordTrace (prefixWord ++ tailWord_6788616) baseStart_6788616 baseEnd_6788616 := by
    simpa [prefixWord, tailWord_6788616, baseEnd_6788616] using wordTrace_append hprefix tailTrace_6788616
  have hstable : (prefixWord ++ tailWord_6788616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788616).length < 2 ^ (prefixWord ++ tailWord_6788616).sum := by decide
  have hdescent : baseEnd_6788616 < baseStart_6788616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788640 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6788640 : Nat := 118140960795 + 6788640 * 2 ^ 59
def prefixEnd_6788640 : Nat := 4983230072969 + 3 ^ 40 * 6788640 * 2
def baseEnd_6788640 : Nat := 3485835310338424648479619

theorem tailTrace_6788640 : CollatzResearch.WordTrace tailWord_6788640 prefixEnd_6788640 3485835310338424648479619 := by
  unfold tailWord_6788640
  simp only [CollatzResearch.WordTrace]
  refine ⟨123801021062962081125985687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165068028083949441501314249 123801021062962081125985687)
  ·
    refine ⟨185701531594443121688978531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123801021062962081125985687 185701531594443121688978531)
    ·
      refine ⟨278552297391664682533467797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185701531594443121688978531 278552297391664682533467797)
      ·
        refine ⟨13057138940234281993756303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 278552297391664682533467797 13057138940234281993756303)
        ·
          refine ⟨19585708410351422990634455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13057138940234281993756303 19585708410351422990634455)
          ·
            refine ⟨29378562615527134485951683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19585708410351422990634455 29378562615527134485951683)
            ·
              refine ⟨44067843923290701728927525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29378562615527134485951683 44067843923290701728927525)
              ·
                refine ⟨8262720735617006574173911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44067843923290701728927525 8262720735617006574173911)
                ·
                  refine ⟨12394081103425509861260867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8262720735617006574173911 12394081103425509861260867)
                  ·
                    refine ⟨18591121655138264791891301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12394081103425509861260867 18591121655138264791891301)
                    ·
                      refine ⟨3485835310338424648479619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18591121655138264791891301 3485835310338424648479619)
                      ·
                        rfl

theorem cell23_6788640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6788640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788640 prefixEnd_6788640 := by exact prefixLift 6788640
  have htrace : WordTrace (prefixWord ++ tailWord_6788640) baseStart_6788640 baseEnd_6788640 := by
    simpa [prefixWord, tailWord_6788640, baseEnd_6788640] using wordTrace_append hprefix tailTrace_6788640
  have hstable : (prefixWord ++ tailWord_6788640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788640).length < 2 ^ (prefixWord ++ tailWord_6788640).sum := by decide
  have hdescent : baseEnd_6788640 < baseStart_6788640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788683 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 2, 7, 2]
def baseStart_6788683 : Nat := 118140960795 + 6788683 * 2 ^ 59
def prefixEnd_6788683 : Nat := 4983230072969 + 3 ^ 40 * 6788683 * 2
def baseEnd_6788683 : Nat := 3485857390006567980241921

theorem tailTrace_6788683 : CollatzResearch.WordTrace tailWord_6788683 prefixEnd_6788683 3485857390006567980241921 := by
  unfold tailWord_6788683
  simp only [CollatzResearch.WordTrace]
  refine ⟨247603610464768380595786703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165069073643178920397191135 247603610464768380595786703)
  ·
    refine ⟨371405415697152570893680055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247603610464768380595786703 371405415697152570893680055)
    ·
      refine ⟨557108123545728856340520083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371405415697152570893680055 557108123545728856340520083)
      ·
        refine ⟨835662185318593284510780125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557108123545728856340520083 835662185318593284510780125)
        ·
          refine ⟨313373319494472481691542547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 835662185318593284510780125 313373319494472481691542547)
          ·
            refine ⟨470059979241708722537313821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313373319494472481691542547 470059979241708722537313821)
            ·
              refine ⟨176272492215640770951492683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470059979241708722537313821 176272492215640770951492683)
              ·
                refine ⟨264408738323461156427239025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176272492215640770951492683 264408738323461156427239025)
                ·
                  refine ⟨198306553742595867320429269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264408738323461156427239025 198306553742595867320429269)
                  ·
                    refine ⟨4647809853342090640322561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 198306553742595867320429269 4647809853342090640322561)
                    ·
                      refine ⟨3485857390006567980241921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4647809853342090640322561 3485857390006567980241921)
                      ·
                        rfl

theorem cell23_6788683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 7, 2].length) (baseStart_6788683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788683 prefixEnd_6788683 := by exact prefixLift 6788683
  have htrace : WordTrace (prefixWord ++ tailWord_6788683) baseStart_6788683 baseEnd_6788683 := by
    simpa [prefixWord, tailWord_6788683, baseEnd_6788683] using wordTrace_append hprefix tailTrace_6788683
  have hstable : (prefixWord ++ tailWord_6788683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788683).length < 2 ^ (prefixWord ++ tailWord_6788683).sum := by decide
  have hdescent : baseEnd_6788683 < baseStart_6788683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788696 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_6788696 : Nat := 118140960795 + 6788696 * 2 ^ 59
def prefixEnd_6788696 : Nat := 4983230072969 + 3 ^ 40 * 6788696 * 2
def baseEnd_6788696 : Nat := 3485864065255076429379361

theorem tailTrace_6788696 : CollatzResearch.WordTrace tailWord_6788696 prefixEnd_6788696 3485864065255076429379361 := by
  unfold tailWord_6788696
  simp only [CollatzResearch.WordTrace]
  refine ⟨123802042306860641908004971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165069389742480855877339961 123802042306860641908004971)
  ·
    refine ⟨185703063460290962862007457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123802042306860641908004971 185703063460290962862007457)
    ·
      refine ⟨139277297595218222146505593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185703063460290962862007457 139277297595218222146505593)
      ·
        refine ⟨104457973196413666609879195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139277297595218222146505593 104457973196413666609879195)
        ·
          refine ⟨156686959794620499914818793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104457973196413666609879195 156686959794620499914818793)
          ·
            refine ⟨117515219845965374936114095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156686959794620499914818793 117515219845965374936114095)
            ·
              refine ⟨176272829768948062404171143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117515219845965374936114095 176272829768948062404171143)
              ·
                refine ⟨264409244653422093606256715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176272829768948062404171143 264409244653422093606256715)
                ·
                  refine ⟨396613866980133140409385073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264409244653422093606256715 396613866980133140409385073)
                  ·
                    refine ⟨297460400235099855307038805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 396613866980133140409385073 297460400235099855307038805)
                    ·
                      refine ⟨3485864065255076429379361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 297460400235099855307038805 3485864065255076429379361)
                      ·
                        rfl

theorem cell23_6788696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_6788696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788696 prefixEnd_6788696 := by exact prefixLift 6788696
  have htrace : WordTrace (prefixWord ++ tailWord_6788696) baseStart_6788696 baseEnd_6788696 := by
    simpa [prefixWord, tailWord_6788696, baseEnd_6788696] using wordTrace_append hprefix tailTrace_6788696
  have hstable : (prefixWord ++ tailWord_6788696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788696).length < 2 ^ (prefixWord ++ tailWord_6788696).sum := by decide
  have hdescent : baseEnd_6788696 < baseStart_6788696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788740 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_6788740 : Nat := 118140960795 + 6788740 * 2 ^ 59
def prefixEnd_6788740 : Nat := 4983230072969 + 3 ^ 40 * 6788740 * 2
def baseEnd_6788740 : Nat := 1161962219467958085743053

theorem tailTrace_6788740 : CollatzResearch.WordTrace tailWord_6788740 prefixEnd_6788740 1161962219467958085743053 := by
  unfold tailWord_6788740
  simp only [CollatzResearch.WordTrace]
  refine ⟨123802844712780939665305837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165070459617041252887074449 123802844712780939665305837)
  ·
    refine ⟨46426066767292852374489689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123802844712780939665305837 46426066767292852374489689)
    ·
      refine ⟨34819550075469639280867267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46426066767292852374489689 34819550075469639280867267)
      ·
        refine ⟨52229325113204458921300901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34819550075469639280867267 52229325113204458921300901)
        ·
          refine ⟨9792998458725836047743919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52229325113204458921300901 9792998458725836047743919)
          ·
            refine ⟨14689497688088754071615879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9792998458725836047743919 14689497688088754071615879)
            ·
              refine ⟨22034246532133131107423819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14689497688088754071615879 22034246532133131107423819)
              ·
                refine ⟨33051369798199696661135729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22034246532133131107423819 33051369798199696661135729)
                ·
                  refine ⟨24788527348649772495851797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33051369798199696661135729 24788527348649772495851797)
                  ·
                    refine ⟨1161962219467958085743053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24788527348649772495851797 1161962219467958085743053)
                    ·
                      rfl

theorem cell23_6788740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_6788740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6788740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6788740 prefixEnd_6788740 := by exact prefixLift 6788740
  have htrace : WordTrace (prefixWord ++ tailWord_6788740) baseStart_6788740 baseEnd_6788740 := by
    simpa [prefixWord, tailWord_6788740, baseEnd_6788740] using wordTrace_append hprefix tailTrace_6788740
  have hstable : (prefixWord ++ tailWord_6788740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788740).length < 2 ^ (prefixWord ++ tailWord_6788740).sum := by decide
  have hdescent : baseEnd_6788740 < baseStart_6788740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
