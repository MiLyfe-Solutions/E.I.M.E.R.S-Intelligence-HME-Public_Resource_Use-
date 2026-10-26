import V185TrunkScan21Chunk165

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_2024581 : List Nat := [1, 3, 1, 1, 6, 1, 8]
def baseStart_2024581 : Nat := 118140960795 + 2024581 * 2 ^ 59
def prefixEnd_2024581 : Nat := 4983230072969 + 3 ^ 40 * 2024581 * 2
def baseEnd_2024581 : Nat := 51337440837553014875389

theorem tailTrace_2024581 : CollatzResearch.WordTrace tailWord_2024581 prefixEnd_2024581 51337440837553014875389 := by
  unfold tailWord_2024581
  simp only [CollatzResearch.WordTrace]
  refine ⟨73842535478296282751681597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49228356985530855167787731 73842535478296282751681597)
  ·
    refine ⟨27690950804361106031880599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73842535478296282751681597 27690950804361106031880599)
    ·
      refine ⟨41536426206541659047820899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27690950804361106031880599 41536426206541659047820899)
      ·
        refine ⟨62304639309812488571731349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41536426206541659047820899 62304639309812488571731349)
        ·
          refine ⟨2920529967647460401799907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62304639309812488571731349 2920529967647460401799907)
          ·
            refine ⟨4380794951471190602699861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920529967647460401799907 4380794951471190602699861)
            ·
              refine ⟨51337440837553014875389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4380794951471190602699861 51337440837553014875389)
              ·
                rfl

theorem cell21_2024581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 8].length) (baseStart_2024581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024581 prefixEnd_2024581 := by exact prefixLift 2024581
  have htrace : WordTrace (prefixWord ++ tailWord_2024581) baseStart_2024581 baseEnd_2024581 := by
    simpa [prefixWord, tailWord_2024581, baseEnd_2024581] using wordTrace_append hprefix tailTrace_2024581
  have hstable : (prefixWord ++ tailWord_2024581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024581).length < 2 ^ (prefixWord ++ tailWord_2024581).sum := by decide
  have hdescent : baseEnd_2024581 < baseStart_2024581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024595 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 5]
def baseStart_2024595 : Nat := 118140960795 + 2024595 * 2 ^ 59
def prefixEnd_2024595 : Nat := 4983230072969 + 3 ^ 40 * 2024595 * 2
def baseEnd_2024595 : Nat := 462040162528716220645139

theorem tailTrace_2024595 : CollatzResearch.WordTrace tailWord_2024595 prefixEnd_2024595 462040162528716220645139 := by
  unfold tailWord_2024595
  simp only [CollatzResearch.WordTrace]
  refine ⟨73843046100245563142691239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49228697400163708761794159 73843046100245563142691239)
  ·
    refine ⟨110764569150368344714036859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73843046100245563142691239 110764569150368344714036859)
    ·
      refine ⟨166146853725552517071055289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110764569150368344714036859 166146853725552517071055289)
      ·
        refine ⟨124610140294164387803291467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166146853725552517071055289 124610140294164387803291467)
        ·
          refine ⟨186915210441246581704937201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124610140294164387803291467 186915210441246581704937201)
          ·
            refine ⟨140186407830934936278702901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186915210441246581704937201 140186407830934936278702901)
            ·
              refine ⟨13142475734150150276128397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140186407830934936278702901 13142475734150150276128397)
              ·
                refine ⟨4928428400306306353548149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13142475734150150276128397 4928428400306306353548149)
                ·
                  refine ⟨462040162528716220645139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4928428400306306353548149 462040162528716220645139)
                  ·
                    rfl

theorem cell21_2024595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_2024595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024595 prefixEnd_2024595 := by exact prefixLift 2024595
  have htrace : WordTrace (prefixWord ++ tailWord_2024595) baseStart_2024595 baseEnd_2024595 := by
    simpa [prefixWord, tailWord_2024595, baseEnd_2024595] using wordTrace_append hprefix tailTrace_2024595
  have hstable : (prefixWord ++ tailWord_2024595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024595).length < 2 ^ (prefixWord ++ tailWord_2024595).sum := by decide
  have hdescent : baseEnd_2024595 < baseStart_2024595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024612 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_2024612 : Nat := 118140960795 + 2024612 * 2 ^ 59
def prefixEnd_2024612 : Nat := 4983230072969 + 3 ^ 40 * 2024612 * 2
def baseEnd_2024612 : Nat := 462044042160327968861771

theorem tailTrace_2024612 : CollatzResearch.WordTrace tailWord_2024612 prefixEnd_2024612 462044042160327968861771 := by
  unfold tailWord_2024612
  simp only [CollatzResearch.WordTrace]
  refine ⟨36921833070591987523030045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49229110760789316697373393 36921833070591987523030045)
  ·
    refine ⟨13845687401471995321136267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36921833070591987523030045 13845687401471995321136267)
    ·
      refine ⟨20768531102207992981704401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13845687401471995321136267 20768531102207992981704401)
      ·
        refine ⟨15576398326655994736278301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20768531102207992981704401 15576398326655994736278301)
        ·
          refine ⟨5841149372495998026104363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15576398326655994736278301 5841149372495998026104363)
          ·
            refine ⟨8761724058743997039156545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841149372495998026104363 8761724058743997039156545)
            ·
              refine ⟨6571293044057997779367409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8761724058743997039156545 6571293044057997779367409)
              ·
                refine ⟨4928469783043498334525557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6571293044057997779367409 4928469783043498334525557)
                ·
                  refine ⟨462044042160327968861771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4928469783043498334525557 462044042160327968861771)
                  ·
                    rfl

theorem cell21_2024612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_2024612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024612 prefixEnd_2024612 := by exact prefixLift 2024612
  have htrace : WordTrace (prefixWord ++ tailWord_2024612) baseStart_2024612 baseEnd_2024612 := by
    simpa [prefixWord, tailWord_2024612, baseEnd_2024612] using wordTrace_append hprefix tailTrace_2024612
  have hstable : (prefixWord ++ tailWord_2024612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024612).length < 2 ^ (prefixWord ++ tailWord_2024612).sum := by decide
  have hdescent : baseEnd_2024612 < baseStart_2024612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024615 : List Nat := [1, 1, 6, 2, 1, 3, 2, 5]
def baseStart_2024615 : Nat := 118140960795 + 2024615 * 2 ^ 59
def prefixEnd_2024615 : Nat := 4983230072969 + 3 ^ 40 * 2024615 * 2
def baseEnd_2024615 : Nat := 154014908933733543437255

theorem tailTrace_2024615 : CollatzResearch.WordTrace tailWord_2024615 prefixEnd_2024615 154014908933733543437255 := by
  unfold tailWord_2024615
  simp only [CollatzResearch.WordTrace]
  refine ⟨73843775560173106558419299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49229183706782071038946199 73843775560173106558419299)
  ·
    refine ⟨110765663340259659837628949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73843775560173106558419299 110765663340259659837628949)
    ·
      refine ⟨5192140469074671554888857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110765663340259659837628949 5192140469074671554888857)
      ·
        refine ⟨3894105351806003666166643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5192140469074671554888857 3894105351806003666166643)
        ·
          refine ⟨5841158027709005499249965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894105351806003666166643 5841158027709005499249965)
          ·
            refine ⟨2190434260390877062218737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5841158027709005499249965 2190434260390877062218737)
            ·
              refine ⟨1642825695293157796664053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2190434260390877062218737 1642825695293157796664053)
              ·
                refine ⟨154014908933733543437255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1642825695293157796664053 154014908933733543437255)
                ·
                  rfl

theorem cell21_2024615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 5].length) (baseStart_2024615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024615 prefixEnd_2024615 := by exact prefixLift 2024615
  have htrace : WordTrace (prefixWord ++ tailWord_2024615) baseStart_2024615 baseEnd_2024615 := by
    simpa [prefixWord, tailWord_2024615, baseEnd_2024615] using wordTrace_append hprefix tailTrace_2024615
  have hstable : (prefixWord ++ tailWord_2024615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024615).length < 2 ^ (prefixWord ++ tailWord_2024615).sum := by decide
  have hdescent : baseEnd_2024615 < baseStart_2024615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024626 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_2024626 : Nat := 118140960795 + 2024626 * 2 ^ 59
def prefixEnd_2024626 : Nat := 4983230072969 + 3 ^ 40 * 2024626 * 2
def baseEnd_2024626 : Nat := 462047237151067055628409

theorem tailTrace_2024626 : CollatzResearch.WordTrace tailWord_2024626 prefixEnd_2024626 462047237151067055628409 := by
  unfold tailWord_2024626
  simp only [CollatzResearch.WordTrace]
  refine ⟨18461044190783313859267433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49229451175422170291379821 18461044190783313859267433)
  ·
    refine ⟨13845783143087485394450575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18461044190783313859267433 13845783143087485394450575)
    ·
      refine ⟨20768674714631228091675863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13845783143087485394450575 20768674714631228091675863)
      ·
        refine ⟨31153012071946842137513795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20768674714631228091675863 31153012071946842137513795)
        ·
          refine ⟨46729518107920263206270693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31153012071946842137513795 46729518107920263206270693)
          ·
            refine ⟨8761784645235049351175755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46729518107920263206270693 8761784645235049351175755)
            ·
              refine ⟨13142676967852574026763633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761784645235049351175755 13142676967852574026763633)
              ·
                refine ⟨9857007725889430520072725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13142676967852574026763633 9857007725889430520072725)
                ·
                  refine ⟨462047237151067055628409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9857007725889430520072725 462047237151067055628409)
                  ·
                    rfl

theorem cell21_2024626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_2024626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024626 prefixEnd_2024626 := by exact prefixLift 2024626
  have htrace : WordTrace (prefixWord ++ tailWord_2024626) baseStart_2024626 baseEnd_2024626 := by
    simpa [prefixWord, tailWord_2024626, baseEnd_2024626] using wordTrace_append hprefix tailTrace_2024626
  have hstable : (prefixWord ++ tailWord_2024626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024626).length < 2 ^ (prefixWord ++ tailWord_2024626).sum := by decide
  have hdescent : baseEnd_2024626 < baseStart_2024626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024671 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 5]
def baseStart_2024671 : Nat := 118140960795 + 2024671 * 2 ^ 59
def prefixEnd_2024671 : Nat := 4983230072969 + 3 ^ 40 * 2024671 * 2
def baseEnd_2024671 : Nat := 462057506764156977378317

theorem tailTrace_2024671 : CollatzResearch.WordTrace tailWord_2024671 prefixEnd_2024671 462057506764156977378317 := by
  unfold tailWord_2024671
  simp only [CollatzResearch.WordTrace]
  refine ⟨73845818047970228122457867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49230545365313485414971911 73845818047970228122457867)
  ·
    refine ⟨110768727071955342183686801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73845818047970228122457867 110768727071955342183686801)
    ·
      refine ⟨83076545303966506637765101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110768727071955342183686801 83076545303966506637765101)
      ·
        refine ⟨31153704488987439989161913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83076545303966506637765101 31153704488987439989161913)
        ·
          refine ⟨23365278366740579991871435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31153704488987439989161913 23365278366740579991871435)
          ·
            refine ⟨35047917550110869987807153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23365278366740579991871435 35047917550110869987807153)
            ·
              refine ⟨26285938162583152490855365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35047917550110869987807153 26285938162583152490855365)
              ·
                refine ⟨4928613405484341092035381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26285938162583152490855365 4928613405484341092035381)
                ·
                  refine ⟨462057506764156977378317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4928613405484341092035381 462057506764156977378317)
                  ·
                    rfl

theorem cell21_2024671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_2024671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024671 prefixEnd_2024671 := by exact prefixLift 2024671
  have htrace : WordTrace (prefixWord ++ tailWord_2024671) baseStart_2024671 baseEnd_2024671 := by
    simpa [prefixWord, tailWord_2024671, baseEnd_2024671] using wordTrace_append hprefix tailTrace_2024671
  have hstable : (prefixWord ++ tailWord_2024671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024671).length < 2 ^ (prefixWord ++ tailWord_2024671).sum := by decide
  have hdescent : baseEnd_2024671 < baseStart_2024671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024705 : List Nat := [1, 2, 4, 1, 1, 4, 1, 4, 3]
def baseStart_2024705 : Nat := 118140960795 + 2024705 * 2 ^ 59
def prefixEnd_2024705 : Nat := 4983230072969 + 3 ^ 40 * 2024705 * 2
def baseEnd_2024705 : Nat := 462065266027380473811581

theorem tailTrace_2024705 : CollatzResearch.WordTrace tailWord_2024705 prefixEnd_2024705 462065266027380473811581 := by
  unfold tailWord_2024705
  simp only [CollatzResearch.WordTrace]
  refine ⟨73847058129847051929195569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49231372086564701286130379 73847058129847051929195569)
  ·
    refine ⟨55385293597385288946896677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73847058129847051929195569 55385293597385288946896677)
    ·
      refine ⟨10384742549509741677543127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55385293597385288946896677 10384742549509741677543127)
      ·
        refine ⟨15577113824264612516314691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10384742549509741677543127 15577113824264612516314691)
        ·
          refine ⟨23365670736396918774472037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15577113824264612516314691 23365670736396918774472037)
          ·
            refine ⟨4381063263074422270213507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23365670736396918774472037 4381063263074422270213507)
            ·
              refine ⟨6571594894611633405320261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381063263074422270213507 6571594894611633405320261)
              ·
                refine ⟨1232174042739681263497549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6571594894611633405320261 1232174042739681263497549)
                ·
                  refine ⟨462065266027380473811581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232174042739681263497549 462065266027380473811581)
                  ·
                    rfl

theorem cell21_2024705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 3].length) (baseStart_2024705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024705 prefixEnd_2024705 := by exact prefixLift 2024705
  have htrace : WordTrace (prefixWord ++ tailWord_2024705) baseStart_2024705 baseEnd_2024705 := by
    simpa [prefixWord, tailWord_2024705, baseEnd_2024705] using wordTrace_append hprefix tailTrace_2024705
  have hstable : (prefixWord ++ tailWord_2024705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024705).length < 2 ^ (prefixWord ++ tailWord_2024705).sum := by decide
  have hdescent : baseEnd_2024705 < baseStart_2024705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024722 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_2024722 : Nat := 118140960795 + 2024722 * 2 ^ 59
def prefixEnd_2024722 : Nat := 4983230072969 + 3 ^ 40 * 2024722 * 2
def baseEnd_2024722 : Nat := 462069145658992222028213

theorem tailTrace_2024722 : CollatzResearch.WordTrace tailWord_2024722 prefixEnd_2024722 462069145658992222028213 := by
  unfold tailWord_2024722
  simp only [CollatzResearch.WordTrace]
  refine ⟨18461919542696365958141105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49231785447190309221709613 18461919542696365958141105)
  ·
    refine ⟨13846439657022274468605829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18461919542696365958141105 13846439657022274468605829)
    ·
      refine ⟨2596207435691676462863593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13846439657022274468605829 2596207435691676462863593)
      ·
        refine ⟨1947155576768757347147695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2596207435691676462863593 1947155576768757347147695)
        ·
          refine ⟨2920733365153136020721543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947155576768757347147695 2920733365153136020721543)
          ·
            refine ⟨4381100047729704031082315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920733365153136020721543 4381100047729704031082315)
            ·
              refine ⟨6571650071594556046623473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381100047729704031082315 6571650071594556046623473)
              ·
                refine ⟨4928737553695917034967605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6571650071594556046623473 4928737553695917034967605)
                ·
                  refine ⟨462069145658992222028213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4928737553695917034967605 462069145658992222028213)
                  ·
                    rfl

theorem cell21_2024722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_2024722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024722 prefixEnd_2024722 := by exact prefixLift 2024722
  have htrace : WordTrace (prefixWord ++ tailWord_2024722) baseStart_2024722 baseEnd_2024722 := by
    simpa [prefixWord, tailWord_2024722, baseEnd_2024722] using wordTrace_append hprefix tailTrace_2024722
  have hstable : (prefixWord ++ tailWord_2024722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024722).length < 2 ^ (prefixWord ++ tailWord_2024722).sum := by decide
  have hdescent : baseEnd_2024722 < baseStart_2024722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024764 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 5]
def baseStart_2024764 : Nat := 118140960795 + 2024764 * 2 ^ 59
def prefixEnd_2024764 : Nat := 4983230072969 + 3 ^ 40 * 2024764 * 2
def baseEnd_2024764 : Nat := 462078730631209482328127

theorem tailTrace_2024764 : CollatzResearch.WordTrace tailWord_2024764 prefixEnd_2024764 462078730631209482328127 := by
  unfold tailWord_2024764
  simp only [CollatzResearch.WordTrace]
  refine ⟨36924605018316652502796673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49232806691088870003728897 36924605018316652502796673)
  ·
    refine ⟨27693453763737489377097505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36924605018316652502796673 27693453763737489377097505)
    ·
      refine ⟨20770090322803117032823129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27693453763737489377097505 20770090322803117032823129)
      ·
        refine ⟨15577567742102337774617347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20770090322803117032823129 15577567742102337774617347)
        ·
          refine ⟨23366351613153506661926021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15577567742102337774617347 23366351613153506661926021)
          ·
            refine ⟨4381190927466282499111129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23366351613153506661926021 4381190927466282499111129)
            ·
              refine ⟨3285893195599711874333347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4381190927466282499111129 3285893195599711874333347)
              ·
                refine ⟨4928839793399567811500021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3285893195599711874333347 4928839793399567811500021)
                ·
                  refine ⟨462078730631209482328127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4928839793399567811500021 462078730631209482328127)
                  ·
                    rfl

theorem cell21_2024764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_2024764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024764 prefixEnd_2024764 := by exact prefixLift 2024764
  have htrace : WordTrace (prefixWord ++ tailWord_2024764) baseStart_2024764 baseEnd_2024764 := by
    simpa [prefixWord, tailWord_2024764, baseEnd_2024764] using wordTrace_append hprefix tailTrace_2024764
  have hstable : (prefixWord ++ tailWord_2024764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024764).length < 2 ^ (prefixWord ++ tailWord_2024764).sum := by decide
  have hdescent : baseEnd_2024764 < baseStart_2024764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024778 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_2024778 : Nat := 118140960795 + 2024778 * 2 ^ 59
def prefixEnd_2024778 : Nat := 4983230072969 + 3 ^ 40 * 2024778 * 2
def baseEnd_2024778 : Nat := 462081925621948569094765

theorem tailTrace_2024778 : CollatzResearch.WordTrace tailWord_2024778 prefixEnd_2024778 462081925621948569094765 := by
  unfold tailWord_2024778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18462430164645646349150747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49233147105721723597735325 18462430164645646349150747)
  ·
    refine ⟨27693645246968469523726121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18462430164645646349150747 27693645246968469523726121)
    ·
      refine ⟨20770233935226352142794591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27693645246968469523726121 20770233935226352142794591)
      ·
        refine ⟨31155350902839528214191887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20770233935226352142794591 31155350902839528214191887)
        ·
          refine ⟨46733026354259292321287831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31155350902839528214191887 46733026354259292321287831)
          ·
            refine ⟨70099539531388938481931747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46733026354259292321287831 70099539531388938481931747)
            ·
              refine ⟨105149309297083407722897621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70099539531388938481931747 105149309297083407722897621)
              ·
                refine ⟨2464436936650392368505413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105149309297083407722897621 2464436936650392368505413)
                ·
                  refine ⟨462081925621948569094765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464436936650392368505413 462081925621948569094765)
                  ·
                    rfl

theorem cell21_2024778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_2024778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024778 prefixEnd_2024778 := by exact prefixLift 2024778
  have htrace : WordTrace (prefixWord ++ tailWord_2024778) baseStart_2024778 baseEnd_2024778 := by
    simpa [prefixWord, tailWord_2024778, baseEnd_2024778] using wordTrace_append hprefix tailTrace_2024778
  have hstable : (prefixWord ++ tailWord_2024778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024778).length < 2 ^ (prefixWord ++ tailWord_2024778).sum := by decide
  have hdescent : baseEnd_2024778 < baseStart_2024778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024790 : List Nat := [5, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2024790 : Nat := 118140960795 + 2024790 * 2 ^ 59
def prefixEnd_2024790 : Nat := 4983230072969 + 3 ^ 40 * 2024790 * 2
def baseEnd_2024790 : Nat := 462084664185439214894741

theorem tailTrace_2024790 : CollatzResearch.WordTrace tailWord_2024790 prefixEnd_2024790 462084664185439214894741 := by
  unfold tailWord_2024790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615634895908694465377489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49233438889692740964026549 4615634895908694465377489)
  ·
    refine ⟨3461726171931520849033117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4615634895908694465377489 3461726171931520849033117)
    ·
      refine ⟨1298147314474320318387419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3461726171931520849033117 1298147314474320318387419)
      ·
        refine ⟨1947220971711480477581129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298147314474320318387419 1947220971711480477581129)
        ·
          refine ⟨1460415728783610358185847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1947220971711480477581129 1460415728783610358185847)
          ·
            refine ⟨2190623593175415537278771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460415728783610358185847 2190623593175415537278771)
            ·
              refine ⟨3285935389763123305918157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190623593175415537278771 3285935389763123305918157)
              ·
                refine ⟨1232225771161171239719309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3285935389763123305918157 1232225771161171239719309)
                ·
                  refine ⟨462084664185439214894741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232225771161171239719309 462084664185439214894741)
                  ·
                    rfl

theorem cell21_2024790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2024790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024790 prefixEnd_2024790 := by exact prefixLift 2024790
  have htrace : WordTrace (prefixWord ++ tailWord_2024790) baseStart_2024790 baseEnd_2024790 := by
    simpa [prefixWord, tailWord_2024790, baseEnd_2024790] using wordTrace_append hprefix tailTrace_2024790
  have hstable : (prefixWord ++ tailWord_2024790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024790).length < 2 ^ (prefixWord ++ tailWord_2024790).sum := by decide
  have hdescent : baseEnd_2024790 < baseStart_2024790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024792 : List Nat := [2, 1, 2, 2, 1, 1, 5, 7]
def baseStart_2024792 : Nat := 118140960795 + 2024792 * 2 ^ 59
def prefixEnd_2024792 : Nat := 4983230072969 + 3 ^ 40 * 2024792 * 2
def baseEnd_2024792 : Nat := 154028373537562551953801

theorem tailTrace_2024792 : CollatzResearch.WordTrace tailWord_2024792 prefixEnd_2024792 154028373537562551953801 := by
  unfold tailWord_2024792
  simp only [CollatzResearch.WordTrace]
  refine ⟨36925115640265932893806315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49233487520354577191741753 36925115640265932893806315)
  ·
    refine ⟨55387673460398899340709473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36925115640265932893806315 55387673460398899340709473)
    ·
      refine ⟨41540755095299174505532105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55387673460398899340709473 41540755095299174505532105)
      ·
        refine ⟨31155566321474380879149079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41540755095299174505532105 31155566321474380879149079)
        ·
          refine ⟨46733349482211571318723619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31155566321474380879149079 46733349482211571318723619)
          ·
            refine ⟨70100024223317356978085429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46733349482211571318723619 70100024223317356978085429)
            ·
              refine ⟨6571877270936002216695509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70100024223317356978085429 6571877270936002216695509)
              ·
                refine ⟨154028373537562551953801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6571877270936002216695509 154028373537562551953801)
                ·
                  rfl

theorem cell21_2024792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_2024792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024792 prefixEnd_2024792 := by exact prefixLift 2024792
  have htrace : WordTrace (prefixWord ++ tailWord_2024792) baseStart_2024792 baseEnd_2024792 := by
    simpa [prefixWord, tailWord_2024792, baseEnd_2024792] using wordTrace_append hprefix tailTrace_2024792
  have hstable : (prefixWord ++ tailWord_2024792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024792).length < 2 ^ (prefixWord ++ tailWord_2024792).sum := by decide
  have hdescent : baseEnd_2024792 < baseStart_2024792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024871 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 4]
def baseStart_2024871 : Nat := 118140960795 + 2024871 * 2 ^ 59
def prefixEnd_2024871 : Nat := 4983230072969 + 3 ^ 40 * 2024871 * 2
def baseEnd_2024871 : Nat := 462103149489001074044575

theorem tailTrace_2024871 : CollatzResearch.WordTrace tailWord_2024871 prefixEnd_2024871 462103149489001074044575 := by
  unfold tailWord_2024871
  simp only [CollatzResearch.WordTrace]
  refine ⟨73853112647245662279738467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49235408431497108186492311 73853112647245662279738467)
  ·
    refine ⟨110779668970868493419607701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73853112647245662279738467 110779668970868493419607701)
    ·
      refine ⟨5192796983009460629044111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110779668970868493419607701 5192796983009460629044111)
      ·
        refine ⟨7789195474514190943566167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5192796983009460629044111 7789195474514190943566167)
        ·
          refine ⟨11683793211771286415349251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7789195474514190943566167 11683793211771286415349251)
          ·
            refine ⟨17525689817656929623023877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11683793211771286415349251 17525689817656929623023877)
            ·
              refine ⟨3286066840810674304316977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17525689817656929623023877 3286066840810674304316977)
              ·
                refine ⟨2464550130608005728237733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286066840810674304316977 2464550130608005728237733)
                ·
                  refine ⟨462103149489001074044575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464550130608005728237733 462103149489001074044575)
                  ·
                    rfl

theorem cell21_2024871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 4].length) (baseStart_2024871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024871 prefixEnd_2024871 := by exact prefixLift 2024871
  have htrace : WordTrace (prefixWord ++ tailWord_2024871) baseStart_2024871 baseEnd_2024871 := by
    simpa [prefixWord, tailWord_2024871, baseEnd_2024871] using wordTrace_append hprefix tailTrace_2024871
  have hstable : (prefixWord ++ tailWord_2024871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024871).length < 2 ^ (prefixWord ++ tailWord_2024871).sum := by decide
  have hdescent : baseEnd_2024871 < baseStart_2024871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024885 : List Nat := [1, 3, 3, 2, 2, 1, 3, 6]
def baseStart_2024885 : Nat := 118140960795 + 2024885 * 2 ^ 59
def prefixEnd_2024885 : Nat := 4983230072969 + 3 ^ 40 * 2024885 * 2
def baseEnd_2024885 : Nat := 154035448159913386937071

theorem tailTrace_2024885 : CollatzResearch.WordTrace tailWord_2024885 prefixEnd_2024885 154035448159913386937071 := by
  unfold tailWord_2024885
  simp only [CollatzResearch.WordTrace]
  refine ⟨73853623269194942670748109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49235748846129961780498739 73853623269194942670748109)
  ·
    refine ⟨27695108725948103501530541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73853623269194942670748109 27695108725948103501530541)
    ·
      refine ⟨10385665772230538813073953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27695108725948103501530541 10385665772230538813073953)
      ·
        refine ⟨7789249329172904109805465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10385665772230538813073953 7789249329172904109805465)
        ·
          refine ⟨5841936996879678082354099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7789249329172904109805465 5841936996879678082354099)
          ·
            refine ⟨8762905495319517123531149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841936996879678082354099 8762905495319517123531149)
            ·
              refine ⟨3286089560744818921324181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8762905495319517123531149 3286089560744818921324181)
              ·
                refine ⟨154035448159913386937071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3286089560744818921324181 154035448159913386937071)
                ·
                  rfl

theorem cell21_2024885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 6].length) (baseStart_2024885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024885 prefixEnd_2024885 := by exact prefixLift 2024885
  have htrace : WordTrace (prefixWord ++ tailWord_2024885) baseStart_2024885 baseEnd_2024885 := by
    simpa [prefixWord, tailWord_2024885, baseEnd_2024885] using wordTrace_append hprefix tailTrace_2024885
  have hstable : (prefixWord ++ tailWord_2024885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024885).length < 2 ^ (prefixWord ++ tailWord_2024885).sum := by decide
  have hdescent : baseEnd_2024885 < baseStart_2024885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024933 : List Nat := [1, 3, 1, 5, 1, 1, 2, 4, 3]
def baseStart_2024933 : Nat := 118140960795 + 2024933 * 2 ^ 59
def prefixEnd_2024933 : Nat := 4983230072969 + 3 ^ 40 * 2024933 * 2
def baseEnd_2024933 : Nat := 462117298733702744011115

theorem tailTrace_2024933 : CollatzResearch.WordTrace tailWord_2024933 prefixEnd_2024933 462117298733702744011115 := by
  unfold tailWord_2024933
  simp only [CollatzResearch.WordTrace]
  refine ⟨73855373973021046868495453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49236915982014031245663635 73855373973021046868495453)
  ·
    refine ⟨27695765239882892575685795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73855373973021046868495453 27695765239882892575685795)
    ·
      refine ⟨41543647859824338863528693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27695765239882892575685795 41543647859824338863528693)
      ·
        refine ⟨3894716986858531768455815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41543647859824338863528693 3894716986858531768455815)
        ·
          refine ⟨5842075480287797652683723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894716986858531768455815 5842075480287797652683723)
          ·
            refine ⟨8763113220431696479025585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5842075480287797652683723 8763113220431696479025585)
            ·
              refine ⟨6572334915323772359269189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8763113220431696479025585 6572334915323772359269189)
              ·
                refine ⟨1232312796623207317362973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6572334915323772359269189 1232312796623207317362973)
                ·
                  refine ⟨462117298733702744011115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232312796623207317362973 462117298733702744011115)
                  ·
                    rfl

theorem cell21_2024933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_2024933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024933 prefixEnd_2024933 := by exact prefixLift 2024933
  have htrace : WordTrace (prefixWord ++ tailWord_2024933) baseStart_2024933 baseEnd_2024933 := by
    simpa [prefixWord, tailWord_2024933, baseEnd_2024933] using wordTrace_append hprefix tailTrace_2024933
  have hstable : (prefixWord ++ tailWord_2024933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024933).length < 2 ^ (prefixWord ++ tailWord_2024933).sum := by decide
  have hdescent : baseEnd_2024933 < baseStart_2024933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024961 : List Nat := [1, 2, 4, 1, 4, 1, 1, 7]
def baseStart_2024961 : Nat := 118140960795 + 2024961 * 2 ^ 59
def prefixEnd_2024961 : Nat := 4983230072969 + 3 ^ 40 * 2024961 * 2
def baseEnd_2024961 : Nat := 154041229571726972514797

theorem tailTrace_2024961 : CollatzResearch.WordTrace tailWord_2024961 prefixEnd_2024961 154041229571726972514797 := by
  unfold tailWord_2024961
  simp only [CollatzResearch.WordTrace]
  refine ⟨73856395216919607650514737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49237596811279738433676491 73856395216919607650514737)
  ·
    refine ⟨55392296412689705737886053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73856395216919607650514737 55392296412689705737886053)
    ·
      refine ⟨10386055577379319825853635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55392296412689705737886053 10386055577379319825853635)
      ·
        refine ⟨15579083366068979738780453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10386055577379319825853635 15579083366068979738780453)
        ·
          refine ⟨2921078131137933701021335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15579083366068979738780453 2921078131137933701021335)
          ·
            refine ⟨4381617196706900551532003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921078131137933701021335 4381617196706900551532003)
            ·
              refine ⟨6572425795060350827298005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381617196706900551532003 6572425795060350827298005)
              ·
                refine ⟨154041229571726972514797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6572425795060350827298005 154041229571726972514797)
                ·
                  rfl

theorem cell21_2024961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 7].length) (baseStart_2024961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024961 prefixEnd_2024961 := by exact prefixLift 2024961
  have htrace : WordTrace (prefixWord ++ tailWord_2024961) baseStart_2024961 baseEnd_2024961 := by
    simpa [prefixWord, tailWord_2024961, baseEnd_2024961] using wordTrace_append hprefix tailTrace_2024961
  have hstable : (prefixWord ++ tailWord_2024961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024961).length < 2 ^ (prefixWord ++ tailWord_2024961).sum := by decide
  have hdescent : baseEnd_2024961 < baseStart_2024961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024992 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 5]
def baseStart_2024992 : Nat := 118140960795 + 2024992 * 2 ^ 59
def prefixEnd_2024992 : Nat := 4983230072969 + 3 ^ 40 * 2024992 * 2
def baseEnd_2024992 : Nat := 462130763337531752527661

theorem tailTrace_2024992 : CollatzResearch.WordTrace tailWord_2024992 prefixEnd_2024992 462130763337531752527661 := by
  unfold tailWord_2024992
  simp only [CollatzResearch.WordTrace]
  refine ⟨36928762939903649972446615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49238350586538199963262153 36928762939903649972446615)
  ·
    refine ⟨55393144409855474958669923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36928762939903649972446615 55393144409855474958669923)
    ·
      refine ⟨83089716614783212438004885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55393144409855474958669923 83089716614783212438004885)
      ·
        refine ⟨3894830466317963083031479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83089716614783212438004885 3894830466317963083031479)
        ·
          refine ⟨5842245699476944624547219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894830466317963083031479 5842245699476944624547219)
          ·
            refine ⟨8763368549215416936820829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5842245699476944624547219 8763368549215416936820829)
            ·
              refine ⟨3286263205955781351307811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8763368549215416936820829 3286263205955781351307811)
              ·
                refine ⟨4929394808933672026961717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286263205955781351307811 4929394808933672026961717)
                ·
                  refine ⟨462130763337531752527661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4929394808933672026961717 462130763337531752527661)
                  ·
                    rfl

theorem cell21_2024992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_2024992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024992 prefixEnd_2024992 := by exact prefixLift 2024992
  have htrace : WordTrace (prefixWord ++ tailWord_2024992) baseStart_2024992 baseEnd_2024992 := by
    simpa [prefixWord, tailWord_2024992, baseEnd_2024992] using wordTrace_append hprefix tailTrace_2024992
  have hstable : (prefixWord ++ tailWord_2024992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024992).length < 2 ^ (prefixWord ++ tailWord_2024992).sum := by decide
  have hdescent : baseEnd_2024992 < baseStart_2024992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025037 : List Nat := [1, 6, 1, 1, 3, 9]
def baseStart_2025037 : Nat := 118140960795 + 2025037 * 2 ^ 59
def prefixEnd_2025037 : Nat := 4983230072969 + 3 ^ 40 * 2025037 * 2
def baseEnd_2025037 : Nat := 17116334553726728676947

theorem tailTrace_2025037 : CollatzResearch.WordTrace tailWord_2025037 prefixEnd_2025037 17116334553726728676947 := by
  unfold tailWord_2025037
  simp only [CollatzResearch.WordTrace]
  refine ⟨73859167164644272630281365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49239444776429515086854243 73859167164644272630281365)
  ·
    refine ⟨3462148460842700279544439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73859167164644272630281365 3462148460842700279544439)
    ·
      refine ⟨5193222691264050419316659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3462148460842700279544439 5193222691264050419316659)
      ·
        refine ⟨7789834036896075628974989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5193222691264050419316659 7789834036896075628974989)
        ·
          refine ⟨2921187763836028360865621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7789834036896075628974989 2921187763836028360865621)
          ·
            refine ⟨17116334553726728676947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2921187763836028360865621 17116334553726728676947)
            ·
              rfl

theorem cell21_2025037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 9].length) (baseStart_2025037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025037 prefixEnd_2025037 := by exact prefixLift 2025037
  have htrace : WordTrace (prefixWord ++ tailWord_2025037) baseStart_2025037 baseEnd_2025037 := by
    simpa [prefixWord, tailWord_2025037, baseEnd_2025037] using wordTrace_append hprefix tailTrace_2025037
  have hstable : (prefixWord ++ tailWord_2025037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025037).length < 2 ^ (prefixWord ++ tailWord_2025037).sum := by decide
  have hdescent : baseEnd_2025037 < baseStart_2025037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025085 : List Nat := [1, 4, 1, 1, 4, 2, 2, 3, 3]
def baseStart_2025085 : Nat := 118140960795 + 2025085 * 2 ^ 59
def prefixEnd_2025085 : Nat := 4983230072969 + 3 ^ 40 * 2025085 * 2
def baseEnd_2025085 : Nat := 462151987204584257477471

theorem tailTrace_2025085 : CollatzResearch.WordTrace tailWord_2025085 prefixEnd_2025085 462151987204584257477471 := by
  unfold tailWord_2025085
  simp only [CollatzResearch.WordTrace]
  refine ⟨73860917868470376828028709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49240611912313584552019139 73860917868470376828028709)
  ·
    refine ⟨13848922100338195655255383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73860917868470376828028709 13848922100338195655255383)
    ·
      refine ⟨20773383150507293482883075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13848922100338195655255383 20773383150507293482883075)
      ·
        refine ⟨31160074725760940224324613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20773383150507293482883075 31160074725760940224324613)
        ·
          refine ⟨5842514011080176292060865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31160074725760940224324613 5842514011080176292060865)
          ·
            refine ⟨4381885508310132219045649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5842514011080176292060865 4381885508310132219045649)
            ·
              refine ⟨3286414131232599164284237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4381885508310132219045649 3286414131232599164284237)
              ·
                refine ⟨1232405299212224686606589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3286414131232599164284237 1232405299212224686606589)
                ·
                  refine ⟨462151987204584257477471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232405299212224686606589 462151987204584257477471)
                  ·
                    rfl

theorem cell21_2025085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_2025085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025085 prefixEnd_2025085 := by exact prefixLift 2025085
  have htrace : WordTrace (prefixWord ++ tailWord_2025085) baseStart_2025085 baseEnd_2025085 := by
    simpa [prefixWord, tailWord_2025085, baseEnd_2025085] using wordTrace_append hprefix tailTrace_2025085
  have hstable : (prefixWord ++ tailWord_2025085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025085).length < 2 ^ (prefixWord ++ tailWord_2025085).sum := by decide
  have hdescent : baseEnd_2025085 < baseStart_2025085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025116 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 4]
def baseStart_2025116 : Nat := 118140960795 + 2025116 * 2 ^ 59
def prefixEnd_2025116 : Nat := 4983230072969 + 3 ^ 40 * 2025116 * 2
def baseEnd_2025116 : Nat := 462159061826935092460741

theorem tailTrace_2025116 : CollatzResearch.WordTrace tailWord_2025116 prefixEnd_2025116 462159061826935092460741 := by
  unfold tailWord_2025116
  simp only [CollatzResearch.WordTrace]
  refine ⟨36931024265679034561203601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49241365687572046081604801 36931024265679034561203601)
  ·
    refine ⟨27698268199259275920902701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36931024265679034561203601 27698268199259275920902701)
    ·
      refine ⟨10386850574722228470338513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27698268199259275920902701 10386850574722228470338513)
      ·
        refine ⟨7790137931041671352753885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10386850574722228470338513 7790137931041671352753885)
        ·
          refine ⟨2921301724140626757282707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7790137931041671352753885 2921301724140626757282707)
          ·
            refine ⟨4381952586210940135924061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921301724140626757282707 4381952586210940135924061)
            ·
              refine ⟨1643232219829102550971523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4381952586210940135924061 1643232219829102550971523)
              ·
                refine ⟨2464848329743653826457285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643232219829102550971523 2464848329743653826457285)
                ·
                  refine ⟨462159061826935092460741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464848329743653826457285 462159061826935092460741)
                  ·
                    rfl

theorem cell21_2025116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_2025116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025116 prefixEnd_2025116 := by exact prefixLift 2025116
  have htrace : WordTrace (prefixWord ++ tailWord_2025116) baseStart_2025116 baseEnd_2025116 := by
    simpa [prefixWord, tailWord_2025116, baseEnd_2025116] using wordTrace_append hprefix tailTrace_2025116
  have hstable : (prefixWord ++ tailWord_2025116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025116).length < 2 ^ (prefixWord ++ tailWord_2025116).sum := by decide
  have hdescent : baseEnd_2025116 < baseStart_2025116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025217 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 6]
def baseStart_2025217 : Nat := 118140960795 + 2025217 * 2 ^ 59
def prefixEnd_2025217 : Nat := 4983230072969 + 3 ^ 40 * 2025217 * 2
def baseEnd_2025217 : Nat := 462182111402981361277201

theorem tailTrace_2025217 : CollatzResearch.WordTrace tailWord_2025217 prefixEnd_2025217 462182111402981361277201 := by
  unfold tailWord_2025217
  simp only [CollatzResearch.WordTrace]
  refine ⟨73865732303992163371833905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49243821535994775581222603 73865732303992163371833905)
  ·
    refine ⟨55399299227994122528875429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73865732303992163371833905 55399299227994122528875429)
    ·
      refine ⟨10387368605248897974164143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55399299227994122528875429 10387368605248897974164143)
      ·
        refine ⟨15581052907873346961246215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10387368605248897974164143 15581052907873346961246215)
        ·
          refine ⟨23371579361810020441869323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581052907873346961246215 23371579361810020441869323)
          ·
            refine ⟨35057369042715030662803985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23371579361810020441869323 35057369042715030662803985)
            ·
              refine ⟨26293026782036272997102989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35057369042715030662803985 26293026782036272997102989)
              ·
                refine ⟨9859885043263602373913621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26293026782036272997102989 9859885043263602373913621)
                ·
                  refine ⟨462182111402981361277201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9859885043263602373913621 462182111402981361277201)
                  ·
                    rfl

theorem cell21_2025217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_2025217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025217 prefixEnd_2025217 := by exact prefixLift 2025217
  have htrace : WordTrace (prefixWord ++ tailWord_2025217) baseStart_2025217 baseEnd_2025217 := by
    simpa [prefixWord, tailWord_2025217, baseEnd_2025217] using wordTrace_append hprefix tailTrace_2025217
  have hstable : (prefixWord ++ tailWord_2025217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025217).length < 2 ^ (prefixWord ++ tailWord_2025217).sum := by decide
  have hdescent : baseEnd_2025217 < baseStart_2025217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025231 : List Nat := [1, 1, 2, 1, 1, 1, 4, 10]
def baseStart_2025231 : Nat := 118140960795 + 2025231 * 2 ^ 59
def prefixEnd_2025231 : Nat := 4983230072969 + 3 ^ 40 * 2025231 * 2
def baseEnd_2025231 : Nat := 154061768797906816014613

theorem tailTrace_2025231 : CollatzResearch.WordTrace tailWord_2025231 prefixEnd_2025231 154061768797906816014613 := by
  unfold tailWord_2025231
  simp only [CollatzResearch.WordTrace]
  refine ⟨73866242925941443762843547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49244161950627629175229031 73866242925941443762843547)
  ·
    refine ⟨110799364388912165644265321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73866242925941443762843547 110799364388912165644265321)
    ·
      refine ⟨83099523291684124233198991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110799364388912165644265321 83099523291684124233198991)
      ·
        refine ⟨124649284937526186349798487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83099523291684124233198991 124649284937526186349798487)
        ·
          refine ⟨186973927406289279524697731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124649284937526186349798487 186973927406289279524697731)
          ·
            refine ⟨280460891109433919287046597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186973927406289279524697731 280460891109433919287046597)
            ·
              refine ⟨52586417083018859866321237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280460891109433919287046597 52586417083018859866321237)
              ·
                refine ⟨154061768797906816014613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52586417083018859866321237 154061768797906816014613)
                ·
                  rfl

theorem cell21_2025231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 10].length) (baseStart_2025231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025231 prefixEnd_2025231 := by exact prefixLift 2025231
  have htrace : WordTrace (prefixWord ++ tailWord_2025231) baseStart_2025231 baseEnd_2025231 := by
    simpa [prefixWord, tailWord_2025231, baseEnd_2025231] using wordTrace_append hprefix tailTrace_2025231
  have hstable : (prefixWord ++ tailWord_2025231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025231).length < 2 ^ (prefixWord ++ tailWord_2025231).sum := by decide
  have hdescent : baseEnd_2025231 < baseStart_2025231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025268 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2025268 : Nat := 118140960795 + 2025268 * 2 ^ 59
def prefixEnd_2025268 : Nat := 4983230072969 + 3 ^ 40 * 2025268 * 2
def baseEnd_2025268 : Nat := 462193750297816605927097

theorem tailTrace_2025268 : CollatzResearch.WordTrace tailWord_2025268 prefixEnd_2025268 462193750297816605927097 := by
  unfold tailWord_2025268
  simp only [CollatzResearch.WordTrace]
  refine ⟨36933796213403699540970229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49245061617871599387960305 36933796213403699540970229)
  ·
    refine ⟨3462543395006596831965959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36933796213403699540970229 3462543395006596831965959)
    ·
      refine ⟨5193815092509895247948939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3462543395006596831965959 5193815092509895247948939)
      ·
        refine ⟨7790722638764842871923409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5193815092509895247948939 7790722638764842871923409)
        ·
          refine ⟨5843041979073632153942557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7790722638764842871923409 5843041979073632153942557)
          ·
            refine ⟨2191140742152612057728459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5843041979073632153942557 2191140742152612057728459)
            ·
              refine ⟨3286711113228918086592689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2191140742152612057728459 3286711113228918086592689)
              ·
                refine ⟨2465033334921688564944517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286711113228918086592689 2465033334921688564944517)
                ·
                  refine ⟨462193750297816605927097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2465033334921688564944517 462193750297816605927097)
                  ·
                    rfl

theorem cell21_2025268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2025268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025268 prefixEnd_2025268 := by exact prefixLift 2025268
  have htrace : WordTrace (prefixWord ++ tailWord_2025268) baseStart_2025268 baseEnd_2025268 := by
    simpa [prefixWord, tailWord_2025268, baseEnd_2025268] using wordTrace_append hprefix tailTrace_2025268
  have hstable : (prefixWord ++ tailWord_2025268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025268).length < 2 ^ (prefixWord ++ tailWord_2025268).sum := by decide
  have hdescent : baseEnd_2025268 < baseStart_2025268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025324 : List Nat := [2, 2, 1, 1, 4, 4, 7]
def baseStart_2025324 : Nat := 118140960795 + 2025324 * 2 ^ 59
def prefixEnd_2025324 : Nat := 4983230072969 + 3 ^ 40 * 2025324 * 2
def baseEnd_2025324 : Nat := 51356281140085883665961

theorem tailTrace_2025324 : CollatzResearch.WordTrace tailWord_2025324 prefixEnd_2025324 51356281140085883665961 := by
  unfold tailWord_2025324
  simp only [CollatzResearch.WordTrace]
  refine ⟨36934817457302260322989513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49246423276403013763986017 36934817457302260322989513)
  ·
    refine ⟨27701113092976695242242135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36934817457302260322989513 27701113092976695242242135)
    ·
      refine ⟨41551669639465042863363203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27701113092976695242242135 41551669639465042863363203)
      ·
        refine ⟨62327504459197564295044805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41551669639465042863363203 62327504459197564295044805)
        ·
          refine ⟨11686407086099543305320901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62327504459197564295044805 11686407086099543305320901)
          ·
            refine ⟨2191201328643664369747669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11686407086099543305320901 2191201328643664369747669)
            ·
              refine ⟨51356281140085883665961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2191201328643664369747669 51356281140085883665961)
              ·
                rfl

theorem cell21_2025324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 7].length) (baseStart_2025324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025324 prefixEnd_2025324 := by exact prefixLift 2025324
  have htrace : WordTrace (prefixWord ++ tailWord_2025324) baseStart_2025324 baseEnd_2025324 := by
    simpa [prefixWord, tailWord_2025324, baseEnd_2025324] using wordTrace_append hprefix tailTrace_2025324
  have hstable : (prefixWord ++ tailWord_2025324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025324).length < 2 ^ (prefixWord ++ tailWord_2025324).sum := by decide
  have hdescent : baseEnd_2025324 < baseStart_2025324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025482 : List Nat := [3, 1, 2, 2, 5, 1, 1, 3, 3]
def baseStart_2025482 : Nat := 118140960795 + 2025482 * 2 ^ 59
def prefixEnd_2025482 : Nat := 4983230072969 + 3 ^ 40 * 2025482 * 2
def baseEnd_2025482 : Nat := 462242588013399789359993

theorem tailTrace_2025482 : CollatzResearch.WordTrace tailWord_2025482 prefixEnd_2025482 462242588013399789359993 := by
  unfold tailWord_2025482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18468849412008028407557675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49250265098688075753487133 18468849412008028407557675)
  ·
    refine ⟨27703274118012042611336513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18468849412008028407557675 27703274118012042611336513)
    ·
      refine ⟨20777455588509031958502385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27703274118012042611336513 20777455588509031958502385)
      ·
        refine ⟨15583091691381773968876789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20777455588509031958502385 15583091691381773968876789)
        ·
          refine ⟨1460914846067041309582199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15583091691381773968876789 1460914846067041309582199)
          ·
            refine ⟨2191372269100561964373299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460914846067041309582199 2191372269100561964373299)
            ·
              refine ⟨3287058403650842946559949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2191372269100561964373299 3287058403650842946559949)
              ·
                refine ⟨1232646901369066104959981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3287058403650842946559949 1232646901369066104959981)
                ·
                  refine ⟨462242588013399789359993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232646901369066104959981 462242588013399789359993)
                  ·
                    rfl

theorem cell21_2025482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_2025482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025482 prefixEnd_2025482 := by exact prefixLift 2025482
  have htrace : WordTrace (prefixWord ++ tailWord_2025482) baseStart_2025482 baseEnd_2025482 := by
    simpa [prefixWord, tailWord_2025482, baseEnd_2025482] using wordTrace_append hprefix tailTrace_2025482
  have hstable : (prefixWord ++ tailWord_2025482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025482).length < 2 ^ (prefixWord ++ tailWord_2025482).sum := by decide
  have hdescent : baseEnd_2025482 < baseStart_2025482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025493 : List Nat := [1, 3, 2, 1, 6, 1, 7]
def baseStart_2025493 : Nat := 118140960795 + 2025493 * 2 ^ 59
def prefixEnd_2025493 : Nat := 4983230072969 + 3 ^ 40 * 2025493 * 2
def baseEnd_2025493 : Nat := 51360566484807357186293

theorem tailTrace_2025493 : CollatzResearch.WordTrace tailWord_2025493 prefixEnd_2025493 51360566484807357186293 := by
  unfold tailWord_2025493
  simp only [CollatzResearch.WordTrace]
  refine ⟨73875798850992262508881133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49250532567328175005920755 73875798850992262508881133)
  ·
    refine ⟨27703424569122098440830425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73875798850992262508881133 27703424569122098440830425)
    ·
      refine ⟨20777568426841573830622819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27703424569122098440830425 20777568426841573830622819)
      ·
        refine ⟨31166352640262360745934229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20777568426841573830622819 31166352640262360745934229)
        ·
          refine ⟨1460922780012298159965667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31166352640262360745934229 1460922780012298159965667)
          ·
            refine ⟨2191384170018447239948501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460922780012298159965667 2191384170018447239948501)
            ·
              refine ⟨51360566484807357186293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2191384170018447239948501 51360566484807357186293)
              ·
                rfl

theorem cell21_2025493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 7].length) (baseStart_2025493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025493 prefixEnd_2025493 := by exact prefixLift 2025493
  have htrace : WordTrace (prefixWord ++ tailWord_2025493) baseStart_2025493 baseEnd_2025493 := by
    simpa [prefixWord, tailWord_2025493, baseEnd_2025493] using wordTrace_append hprefix tailTrace_2025493
  have hstable : (prefixWord ++ tailWord_2025493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025493).length < 2 ^ (prefixWord ++ tailWord_2025493).sum := by decide
  have hdescent : baseEnd_2025493 < baseStart_2025493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025535 : List Nat := [1, 1, 2, 2, 3, 1, 4, 7]
def baseStart_2025535 : Nat := 118140960795 + 2025535 * 2 ^ 59
def prefixEnd_2025535 : Nat := 4983230072969 + 3 ^ 40 * 2025535 * 2
def baseEnd_2025535 : Nat := 154084894445161158325517

theorem tailTrace_2025535 : CollatzResearch.WordTrace tailWord_2025535 prefixEnd_2025535 154084894445161158325517 := by
  unfold tailWord_2025535
  simp only [CollatzResearch.WordTrace]
  refine ⟨73877330716840103681910059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49251553811226735787940039 73877330716840103681910059)
  ·
    refine ⟨110815996075260155522865089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73877330716840103681910059 110815996075260155522865089)
    ·
      refine ⟨83111997056445116642148817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110815996075260155522865089 83111997056445116642148817)
      ·
        refine ⟨62333997792333837481611613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83111997056445116642148817 62333997792333837481611613)
        ·
          refine ⟨23375249172125189055604355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62333997792333837481611613 23375249172125189055604355)
          ·
            refine ⟨35062873758187783583406533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23375249172125189055604355 35062873758187783583406533)
            ·
              refine ⟨6574288829660209421888725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35062873758187783583406533 6574288829660209421888725)
              ·
                refine ⟨154084894445161158325517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6574288829660209421888725 154084894445161158325517)
                ·
                  rfl

theorem cell21_2025535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 7].length) (baseStart_2025535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025535 prefixEnd_2025535 := by exact prefixLift 2025535
  have htrace : WordTrace (prefixWord ++ tailWord_2025535) baseStart_2025535 baseEnd_2025535 := by
    simpa [prefixWord, tailWord_2025535, baseEnd_2025535] using wordTrace_append hprefix tailTrace_2025535
  have hstable : (prefixWord ++ tailWord_2025535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025535).length < 2 ^ (prefixWord ++ tailWord_2025535).sum := by decide
  have hdescent : baseEnd_2025535 < baseStart_2025535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025558 : List Nat := [5, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2025558 : Nat := 118140960795 + 2025558 * 2 ^ 59
def prefixEnd_2025558 : Nat := 4983230072969 + 3 ^ 40 * 2025558 * 2
def baseEnd_2025558 : Nat := 462259932248840546093171

theorem tailTrace_2025558 : CollatzResearch.WordTrace tailWord_2025558 prefixEnd_2025558 462259932248840546093171 := by
  unfold tailWord_2025558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617385599734798663124833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49252113063837852406664885 4617385599734798663124833)
  ·
    refine ⟨3463039199801098997343625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4617385599734798663124833 3463039199801098997343625)
    ·
      refine ⟨2597279399850824248007719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3463039199801098997343625 2597279399850824248007719)
      ·
        refine ⟨3895919099776236372011579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597279399850824248007719 3895919099776236372011579)
        ·
          refine ⟨5843878649664354558017369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3895919099776236372011579 5843878649664354558017369)
          ·
            refine ⟨4382908987248265918513027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5843878649664354558017369 4382908987248265918513027)
            ·
              refine ⟨6574363480872398877769541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382908987248265918513027 6574363480872398877769541)
              ·
                refine ⟨1232693152663574789581789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6574363480872398877769541 1232693152663574789581789)
                ·
                  refine ⟨462259932248840546093171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232693152663574789581789 462259932248840546093171)
                  ·
                    rfl

theorem cell21_2025558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2025558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025558 prefixEnd_2025558 := by exact prefixLift 2025558
  have htrace : WordTrace (prefixWord ++ tailWord_2025558) baseStart_2025558 baseEnd_2025558 := by
    simpa [prefixWord, tailWord_2025558, baseEnd_2025558] using wordTrace_append hprefix tailTrace_2025558
  have hstable : (prefixWord ++ tailWord_2025558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025558).length < 2 ^ (prefixWord ++ tailWord_2025558).sum := by decide
  have hdescent : baseEnd_2025558 < baseStart_2025558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025614 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_2025614 : Nat := 118140960795 + 2025614 * 2 ^ 59
def prefixEnd_2025614 : Nat := 4983230072969 + 3 ^ 40 * 2025614 * 2
def baseEnd_2025614 : Nat := 462272712211796893159723

theorem tailTrace_2025614 : CollatzResearch.WordTrace tailWord_2025614 prefixEnd_2025614 462272712211796893159723 := by
  unfold tailWord_2025614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9235026510444237521754487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49253474722369266782690597 9235026510444237521754487)
  ·
    refine ⟨13852539765666356282631731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9235026510444237521754487 13852539765666356282631731)
    ·
      refine ⟨20778809648499534423947597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13852539765666356282631731 20778809648499534423947597)
      ·
        refine ⟨7792053618187325408980349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20778809648499534423947597 7792053618187325408980349)
        ·
          refine ⟨2922020106820247028367631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7792053618187325408980349 2922020106820247028367631)
          ·
            refine ⟨4383030160230370542551447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922020106820247028367631 4383030160230370542551447)
            ·
              refine ⟨6574545240345555813827171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383030160230370542551447 6574545240345555813827171)
              ·
                refine ⟨9861817860518333720740757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6574545240345555813827171 9861817860518333720740757)
                ·
                  refine ⟨462272712211796893159723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9861817860518333720740757 462272712211796893159723)
                  ·
                    rfl

theorem cell21_2025614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_2025614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025614 prefixEnd_2025614 := by exact prefixLift 2025614
  have htrace : WordTrace (prefixWord ++ tailWord_2025614) baseStart_2025614 baseEnd_2025614 := by
    simpa [prefixWord, tailWord_2025614, baseEnd_2025614] using wordTrace_append hprefix tailTrace_2025614
  have hstable : (prefixWord ++ tailWord_2025614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025614).length < 2 ^ (prefixWord ++ tailWord_2025614).sum := by decide
  have hdescent : baseEnd_2025614 < baseStart_2025614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025631 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 4]
def baseStart_2025631 : Nat := 118140960795 + 2025631 * 2 ^ 59
def prefixEnd_2025631 : Nat := 4983230072969 + 3 ^ 40 * 2025631 * 2
def baseEnd_2025631 : Nat := 462276591843408641376355

theorem tailTrace_2025631 : CollatzResearch.WordTrace tailWord_2025631 prefixEnd_2025631 462276591843408641376355 := by
  unfold tailWord_2025631
  simp only [CollatzResearch.WordTrace]
  refine ⟨73880832124492312077404747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49253888082994874718269831 73880832124492312077404747)
  ·
    refine ⟨110821248186738468116107121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73880832124492312077404747 110821248186738468116107121)
    ·
      refine ⟨83115936140053851087080341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110821248186738468116107121 83115936140053851087080341)
      ·
        refine ⟨3896059506565024269706891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83115936140053851087080341 3896059506565024269706891)
        ·
          refine ⟨5844089259847536404560337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3896059506565024269706891 5844089259847536404560337)
          ·
            refine ⟨4383066944885652303420253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5844089259847536404560337 4383066944885652303420253)
            ·
              refine ⟨1643650104332119613782595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4383066944885652303420253 1643650104332119613782595)
              ·
                refine ⟨2465475156498179420673893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643650104332119613782595 2465475156498179420673893)
                ·
                  refine ⟨462276591843408641376355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2465475156498179420673893 462276591843408641376355)
                  ·
                    rfl

theorem cell21_2025631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 4].length) (baseStart_2025631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025631 prefixEnd_2025631 := by exact prefixLift 2025631
  have htrace : WordTrace (prefixWord ++ tailWord_2025631) baseStart_2025631 baseEnd_2025631 := by
    simpa [prefixWord, tailWord_2025631, baseEnd_2025631] using wordTrace_append hprefix tailTrace_2025631
  have hstable : (prefixWord ++ tailWord_2025631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025631).length < 2 ^ (prefixWord ++ tailWord_2025631).sum := by decide
  have hdescent : baseEnd_2025631 < baseStart_2025631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025645 : List Nat := [1, 5, 2, 1, 2, 1, 4, 5]
def baseStart_2025645 : Nat := 118140960795 + 2025645 * 2 ^ 59
def prefixEnd_2025645 : Nat := 4983230072969 + 3 ^ 40 * 2025645 * 2
def baseEnd_2025645 : Nat := 154093262278049242714331

theorem tailTrace_2025645 : CollatzResearch.WordTrace tailWord_2025645 prefixEnd_2025645 154093262278049242714331 := by
  unfold tailWord_2025645
  simp only [CollatzResearch.WordTrace]
  refine ⟨73881342746441592468414389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49254228497627728312276259 73881342746441592468414389)
  ·
    refine ⟨6926375882478899293913849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73881342746441592468414389 6926375882478899293913849)
    ·
      refine ⟨5194781911859174470435387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6926375882478899293913849 5194781911859174470435387)
      ·
        refine ⟨7792172867788761705653081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194781911859174470435387 7792172867788761705653081)
        ·
          refine ⟨5844129650841571279239811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7792172867788761705653081 5844129650841571279239811)
          ·
            refine ⟨8766194476262356918859717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5844129650841571279239811 8766194476262356918859717)
            ·
              refine ⟨1643661464299191922286197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8766194476262356918859717 1643661464299191922286197)
              ·
                refine ⟨154093262278049242714331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1643661464299191922286197 154093262278049242714331)
                ·
                  rfl

theorem cell21_2025645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 5].length) (baseStart_2025645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025645 prefixEnd_2025645 := by exact prefixLift 2025645
  have htrace : WordTrace (prefixWord ++ tailWord_2025645) baseStart_2025645 baseEnd_2025645 := by
    simpa [prefixWord, tailWord_2025645, baseEnd_2025645] using wordTrace_append hprefix tailTrace_2025645
  have hstable : (prefixWord ++ tailWord_2025645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025645).length < 2 ^ (prefixWord ++ tailWord_2025645).sum := by decide
  have hdescent : baseEnd_2025645 < baseStart_2025645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025656 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_2025656 : Nat := 118140960795 + 2025656 * 2 ^ 59
def prefixEnd_2025656 : Nat := 4983230072969 + 3 ^ 40 * 2025656 * 2
def baseEnd_2025656 : Nat := 462282297184014153459637

theorem tailTrace_2025656 : CollatzResearch.WordTrace tailWord_2025656 prefixEnd_2025656 462282297184014153459637 := by
  unfold tailWord_2025656
  simp only [CollatzResearch.WordTrace]
  refine ⟨36940871974700870673532411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49254495966267827564709881 36940871974700870673532411)
  ·
    refine ⟨55411307962051306010298617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36940871974700870673532411 55411307962051306010298617)
    ·
      refine ⟨41558480971538479507723963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55411307962051306010298617 41558480971538479507723963)
      ·
        refine ⟨62337721457307719261585945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41558480971538479507723963 62337721457307719261585945)
        ·
          refine ⟨46753291092980789446189459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62337721457307719261585945 46753291092980789446189459)
          ·
            refine ⟨70129936639471184169284189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46753291092980789446189459 70129936639471184169284189)
            ·
              refine ⟨26298726239801694063481571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70129936639471184169284189 26298726239801694063481571)
              ·
                refine ⟨39448089359702541095222357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26298726239801694063481571 39448089359702541095222357)
                ·
                  refine ⟨462282297184014153459637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39448089359702541095222357 462282297184014153459637)
                  ·
                    rfl

theorem cell21_2025656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_2025656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025656 prefixEnd_2025656 := by exact prefixLift 2025656
  have htrace : WordTrace (prefixWord ++ tailWord_2025656) baseStart_2025656 baseEnd_2025656 := by
    simpa [prefixWord, tailWord_2025656, baseEnd_2025656] using wordTrace_append hprefix tailTrace_2025656
  have hstable : (prefixWord ++ tailWord_2025656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025656).length < 2 ^ (prefixWord ++ tailWord_2025656).sum := by decide
  have hdescent : baseEnd_2025656 < baseStart_2025656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025690 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_2025690 : Nat := 118140960795 + 2025690 * 2 ^ 59
def prefixEnd_2025690 : Nat := 4983230072969 + 3 ^ 40 * 2025690 * 2
def baseEnd_2025690 : Nat := 462290056447237649892901

theorem tailTrace_2025690 : CollatzResearch.WordTrace tailWord_2025690 prefixEnd_2025690 462290056447237649892901 := by
  unfold tailWord_2025690
  simp only [CollatzResearch.WordTrace]
  refine ⟨18470746007819641288450631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49255322687519043435868349 18470746007819641288450631)
  ·
    refine ⟨27706119011729461932675947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18470746007819641288450631 27706119011729461932675947)
    ·
      refine ⟨41559178517594192899013921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27706119011729461932675947 41559178517594192899013921)
      ·
        refine ⟨31169383888195644674260441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41559178517594192899013921 31169383888195644674260441)
        ·
          refine ⟨23377037916146733505695331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31169383888195644674260441 23377037916146733505695331)
          ·
            refine ⟨35065556874220100258542997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23377037916146733505695331 35065556874220100258542997)
            ·
              refine ⟨1643697978479067199619203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35065556874220100258542997 1643697978479067199619203)
              ·
                refine ⟨2465546967718600799428805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643697978479067199619203 2465546967718600799428805)
                ·
                  refine ⟨462290056447237649892901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2465546967718600799428805 462290056447237649892901)
                  ·
                    rfl

theorem cell21_2025690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_2025690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025690 prefixEnd_2025690 := by exact prefixLift 2025690
  have htrace : WordTrace (prefixWord ++ tailWord_2025690) baseStart_2025690 baseEnd_2025690 := by
    simpa [prefixWord, tailWord_2025690, baseEnd_2025690] using wordTrace_append hprefix tailTrace_2025690
  have hstable : (prefixWord ++ tailWord_2025690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025690).length < 2 ^ (prefixWord ++ tailWord_2025690).sum := by decide
  have hdescent : baseEnd_2025690 < baseStart_2025690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025749 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 4]
def baseStart_2025749 : Nat := 118140960795 + 2025749 * 2 ^ 59
def prefixEnd_2025749 : Nat := 4983230072969 + 3 ^ 40 * 2025749 * 2
def baseEnd_2025749 : Nat := 462303521051066658409447

theorem tailTrace_2025749 : CollatzResearch.WordTrace tailWord_2025749 prefixEnd_2025749 462303521051066658409447 := by
  unfold tailWord_2025749
  simp only [CollatzResearch.WordTrace]
  refine ⟨73885135938064818230200301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49256757292043212153466867 73885135938064818230200301)
  ·
    refine ⟨27706925976774306836325113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73885135938064818230200301 27706925976774306836325113)
    ·
      refine ⟨20780194482580730127243835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27706925976774306836325113 20780194482580730127243835)
      ·
        refine ⟨31170291723871095190865753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20780194482580730127243835 31170291723871095190865753)
        ·
          refine ⟨23377718792903321393149315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31170291723871095190865753 23377718792903321393149315)
          ·
            refine ⟨35066578189354982089723973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23377718792903321393149315 35066578189354982089723973)
            ·
              refine ⟨6574983410504059141823245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35066578189354982089723973 6574983410504059141823245)
              ·
                refine ⟨2465618778939022178183717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6574983410504059141823245 2465618778939022178183717)
                ·
                  refine ⟨462303521051066658409447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2465618778939022178183717 462303521051066658409447)
                  ·
                    rfl

theorem cell21_2025749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_2025749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025749 prefixEnd_2025749 := by exact prefixLift 2025749
  have htrace : WordTrace (prefixWord ++ tailWord_2025749) baseStart_2025749 baseEnd_2025749 := by
    simpa [prefixWord, tailWord_2025749, baseEnd_2025749] using wordTrace_append hprefix tailTrace_2025749
  have hstable : (prefixWord ++ tailWord_2025749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025749).length < 2 ^ (prefixWord ++ tailWord_2025749).sum := by decide
  have hdescent : baseEnd_2025749 < baseStart_2025749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025780 : List Nat := [2, 5, 1, 1, 1, 3, 8]
def baseStart_2025780 : Nat := 118140960795 + 2025780 * 2 ^ 59
def prefixEnd_2025780 : Nat := 4983230072969 + 3 ^ 40 * 2025780 * 2
def baseEnd_2025780 : Nat := 51367843963713054821413

theorem tailTrace_2025780 : CollatzResearch.WordTrace tailWord_2025780 prefixEnd_2025780 51367843963713054821413 := by
  unfold tailWord_2025780
  simp only [CollatzResearch.WordTrace]
  refine ⟨36943133300476255262289397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49257511067301673683052529 36943133300476255262289397)
  ·
    refine ⟨3463418746919648930839631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36943133300476255262289397 3463418746919648930839631)
    ·
      refine ⟨5195128120379473396259447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3463418746919648930839631 5195128120379473396259447)
      ·
        refine ⟨7792692180569210094389171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5195128120379473396259447 7792692180569210094389171)
        ·
          refine ⟨11689038270853815141583757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7792692180569210094389171 11689038270853815141583757)
          ·
            refine ⟨4383389351570180678093909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11689038270853815141583757 4383389351570180678093909)
            ·
              refine ⟨51367843963713054821413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4383389351570180678093909 51367843963713054821413)
              ·
                rfl

theorem cell21_2025780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 8].length) (baseStart_2025780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025780 prefixEnd_2025780 := by exact prefixLift 2025780
  have htrace : WordTrace (prefixWord ++ tailWord_2025780) baseStart_2025780 baseEnd_2025780 := by
    simpa [prefixWord, tailWord_2025780, baseEnd_2025780] using wordTrace_append hprefix tailTrace_2025780
  have hstable : (prefixWord ++ tailWord_2025780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025780).length < 2 ^ (prefixWord ++ tailWord_2025780).sum := by decide
  have hdescent : baseEnd_2025780 < baseStart_2025780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025845 : List Nat := [1, 3, 4, 1, 2, 2, 3, 2, 3]
def baseStart_2025845 : Nat := 118140960795 + 2025845 * 2 ^ 59
def prefixEnd_2025845 : Nat := 4983230072969 + 3 ^ 40 * 2025845 * 2
def baseEnd_2025845 : Nat := 462325429558991824809251

theorem tailTrace_2025845 : CollatzResearch.WordTrace tailWord_2025845 prefixEnd_2025845 462325429558991824809251 := by
  unfold tailWord_2025845
  simp only [CollatzResearch.WordTrace]
  refine ⟨73888637345717026625694989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49259091563811351083796659 73888637345717026625694989)
  ·
    refine ⟨27708239004643884984635621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73888637345717026625694989 27708239004643884984635621)
    ·
      refine ⟨5195294813370728434619179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27708239004643884984635621 5195294813370728434619179)
      ·
        refine ⟨7792942220056092651928769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5195294813370728434619179 7792942220056092651928769)
        ·
          refine ⟨5844706665042069488946577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7792942220056092651928769 5844706665042069488946577)
          ·
            refine ⟨4383529998781552116709933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5844706665042069488946577 4383529998781552116709933)
            ·
              refine ⟨1643823749543082043766225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4383529998781552116709933 1643823749543082043766225)
              ·
                refine ⟨1232867812157311532824669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643823749543082043766225 1232867812157311532824669)
                ·
                  refine ⟨462325429558991824809251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232867812157311532824669 462325429558991824809251)
                  ·
                    rfl

theorem cell21_2025845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_2025845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025845 prefixEnd_2025845 := by exact prefixLift 2025845
  have htrace : WordTrace (prefixWord ++ tailWord_2025845) baseStart_2025845 baseEnd_2025845 := by
    simpa [prefixWord, tailWord_2025845, baseEnd_2025845] using wordTrace_append hprefix tailTrace_2025845
  have hstable : (prefixWord ++ tailWord_2025845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025845).length < 2 ^ (prefixWord ++ tailWord_2025845).sum := by decide
  have hdescent : baseEnd_2025845 < baseStart_2025845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025859 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 4]
def baseStart_2025859 : Nat := 118140960795 + 2025859 * 2 ^ 59
def prefixEnd_2025859 : Nat := 4983230072969 + 3 ^ 40 * 2025859 * 2
def baseEnd_2025859 : Nat := 462328624549730911575889

theorem tailTrace_2025859 : CollatzResearch.WordTrace tailWord_2025859 prefixEnd_2025859 462328624549730911575889 := by
  unfold tailWord_2025859
  simp only [CollatzResearch.WordTrace]
  refine ⟨73889147967666307016704631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49259431978444204677803087 73889147967666307016704631)
  ·
    refine ⟨110833721951499460525056947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73889147967666307016704631 110833721951499460525056947)
    ·
      refine ⟨166250582927249190787585421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110833721951499460525056947 166250582927249190787585421)
      ·
        refine ⟨62343968597718446545344533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166250582927249190787585421 62343968597718446545344533)
        ·
          refine ⟨2922373528018052181813025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62343968597718446545344533 2922373528018052181813025)
          ·
            refine ⟨2191780146013539136359769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2922373528018052181813025 2191780146013539136359769)
            ·
              refine ⟨1643835109510154352269827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191780146013539136359769 1643835109510154352269827)
              ·
                refine ⟨2465752664265231528404741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643835109510154352269827 2465752664265231528404741)
                ·
                  refine ⟨462328624549730911575889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2465752664265231528404741 462328624549730911575889)
                  ·
                    rfl

theorem cell21_2025859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 4].length) (baseStart_2025859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025859 prefixEnd_2025859 := by exact prefixLift 2025859
  have htrace : WordTrace (prefixWord ++ tailWord_2025859) baseStart_2025859 baseEnd_2025859 := by
    simpa [prefixWord, tailWord_2025859, baseEnd_2025859] using wordTrace_append hprefix tailTrace_2025859
  have hstable : (prefixWord ++ tailWord_2025859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025859).length < 2 ^ (prefixWord ++ tailWord_2025859).sum := by decide
  have hdescent : baseEnd_2025859 < baseStart_2025859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025887 : List Nat := [1, 1, 2, 5, 1, 1, 2, 5, 3]
def baseStart_2025887 : Nat := 118140960795 + 2025887 * 2 ^ 59
def prefixEnd_2025887 : Nat := 4983230072969 + 3 ^ 40 * 2025887 * 2
def baseEnd_2025887 : Nat := 462335014531209085109165

theorem tailTrace_2025887 : CollatzResearch.WordTrace tailWord_2025887 prefixEnd_2025887 462335014531209085109165 := by
  unfold tailWord_2025887
  simp only [CollatzResearch.WordTrace]
  refine ⟨73890169211564867798723915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49260112807709911865815943 73890169211564867798723915)
  ·
    refine ⟨110835253817347301698085873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73890169211564867798723915 110835253817347301698085873)
    ·
      refine ⟨83126440363010476273564405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110835253817347301698085873 83126440363010476273564405)
      ·
        refine ⟨7793103784032232150646663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83126440363010476273564405 7793103784032232150646663)
        ·
          refine ⟨11689655676048348225969995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7793103784032232150646663 11689655676048348225969995)
          ·
            refine ⟨17534483514072522338954993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11689655676048348225969995 17534483514072522338954993)
            ·
              refine ⟨13150862635554391754216245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17534483514072522338954993 13150862635554391754216245)
              ·
                refine ⟨1232893372083224226957773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13150862635554391754216245 1232893372083224226957773)
                ·
                  refine ⟨462335014531209085109165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232893372083224226957773 462335014531209085109165)
                  ·
                    rfl

theorem cell21_2025887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 3].length) (baseStart_2025887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025887 prefixEnd_2025887 := by exact prefixLift 2025887
  have htrace : WordTrace (prefixWord ++ tailWord_2025887) baseStart_2025887 baseEnd_2025887 := by
    simpa [prefixWord, tailWord_2025887, baseEnd_2025887] using wordTrace_append hprefix tailTrace_2025887
  have hstable : (prefixWord ++ tailWord_2025887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025887).length < 2 ^ (prefixWord ++ tailWord_2025887).sum := by decide
  have hdescent : baseEnd_2025887 < baseStart_2025887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025921 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 5]
def baseStart_2025921 : Nat := 118140960795 + 2025921 * 2 ^ 59
def prefixEnd_2025921 : Nat := 4983230072969 + 3 ^ 40 * 2025921 * 2
def baseEnd_2025921 : Nat := 462342773794432581542429

theorem tailTrace_2025921 : CollatzResearch.WordTrace tailWord_2025921 prefixEnd_2025921 462342773794432581542429 := by
  unfold tailWord_2025921
  simp only [CollatzResearch.WordTrace]
  refine ⟨73891409293441691605461617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49260939528961127736974411 73891409293441691605461617)
  ·
    refine ⟨55418556970081268704096213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73891409293441691605461617 55418556970081268704096213)
    ·
      refine ⟨1298872428986279735252255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 55418556970081268704096213 1298872428986279735252255)
      ·
        refine ⟨1948308643479419602878383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298872428986279735252255 1948308643479419602878383)
        ·
          refine ⟨2922462965219129404317575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948308643479419602878383 2922462965219129404317575)
          ·
            refine ⟨4383694447828694106476363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922462965219129404317575 4383694447828694106476363)
            ·
              refine ⟨6575541671743041159714545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383694447828694106476363 6575541671743041159714545)
              ·
                refine ⟨4931656253807280869785909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6575541671743041159714545 4931656253807280869785909)
                ·
                  refine ⟨462342773794432581542429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4931656253807280869785909 462342773794432581542429)
                  ·
                    rfl

theorem cell21_2025921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 5].length) (baseStart_2025921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025921 prefixEnd_2025921 := by exact prefixLift 2025921
  have htrace : WordTrace (prefixWord ++ tailWord_2025921) baseStart_2025921 baseEnd_2025921 := by
    simpa [prefixWord, tailWord_2025921, baseEnd_2025921] using wordTrace_append hprefix tailTrace_2025921
  have hstable : (prefixWord ++ tailWord_2025921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025921).length < 2 ^ (prefixWord ++ tailWord_2025921).sum := by decide
  have hdescent : baseEnd_2025921 < baseStart_2025921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025929 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 7]
def baseStart_2025929 : Nat := 118140960795 + 2025929 * 2 ^ 59
def prefixEnd_2025929 : Nat := 4983230072969 + 3 ^ 40 * 2025929 * 2
def baseEnd_2025929 : Nat := 462344599503426345409079

theorem tailTrace_2025929 : CollatzResearch.WordTrace tailWord_2025929 prefixEnd_2025929 462344599503426345409079 := by
  unfold tailWord_2025929
  simp only [CollatzResearch.WordTrace]
  refine ⟨73891701077412708971752841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49261134051608472647835227 73891701077412708971752841)
  ·
    refine ⟨55418775808059531728814631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73891701077412708971752841 55418775808059531728814631)
    ·
      refine ⟨83128163712089297593221947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55418775808059531728814631 83128163712089297593221947)
      ·
        refine ⟨124692245568133946389832921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83128163712089297593221947 124692245568133946389832921)
        ·
          refine ⟨93519184176100459792374691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124692245568133946389832921 93519184176100459792374691)
          ·
            refine ⟨140278776264150689688562037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93519184176100459792374691 140278776264150689688562037)
            ·
              refine ⟨13151135274764127158302691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140278776264150689688562037 13151135274764127158302691)
              ·
                refine ⟨19726702912146190737454037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13151135274764127158302691 19726702912146190737454037)
                ·
                  refine ⟨462344599503426345409079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19726702912146190737454037 462344599503426345409079)
                  ·
                    rfl

theorem cell21_2025929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_2025929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2025929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2025929 prefixEnd_2025929 := by exact prefixLift 2025929
  have htrace : WordTrace (prefixWord ++ tailWord_2025929) baseStart_2025929 baseEnd_2025929 := by
    simpa [prefixWord, tailWord_2025929, baseEnd_2025929] using wordTrace_append hprefix tailTrace_2025929
  have hstable : (prefixWord ++ tailWord_2025929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025929).length < 2 ^ (prefixWord ++ tailWord_2025929).sum := by decide
  have hdescent : baseEnd_2025929 < baseStart_2025929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026101 : List Nat := [1, 3, 4, 2, 2, 1, 3, 5]
def baseStart_2026101 : Nat := 118140960795 + 2026101 * 2 ^ 59
def prefixEnd_2026101 : Nat := 4983230072969 + 3 ^ 40 * 2026101 * 2
def baseEnd_2026101 : Nat := 154127950748930756180687

theorem tailTrace_2026101 : CollatzResearch.WordTrace tailWord_2026101 prefixEnd_2026101 154127950748930756180687 := by
  unfold tailWord_2026101
  simp only [CollatzResearch.WordTrace]
  refine ⟨73897974432789582347014157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49265316288526388231342771 73897974432789582347014157)
  ·
    refine ⟨27711740412296093380130309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73897974432789582347014157 27711740412296093380130309)
    ·
      refine ⟨5195951327305517508774433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27711740412296093380130309 5195951327305517508774433)
      ·
        refine ⟨3896963495479138131580825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5195951327305517508774433 3896963495479138131580825)
        ·
          refine ⟨2922722621609353598685619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3896963495479138131580825 2922722621609353598685619)
          ·
            refine ⟨4384083932414030398028429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922722621609353598685619 4384083932414030398028429)
            ·
              refine ⟨1644031474655261399260661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4384083932414030398028429 1644031474655261399260661)
              ·
                refine ⟨154127950748930756180687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1644031474655261399260661 154127950748930756180687)
                ·
                  rfl

theorem cell21_2026101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 5].length) (baseStart_2026101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026101 prefixEnd_2026101 := by exact prefixLift 2026101
  have htrace : WordTrace (prefixWord ++ tailWord_2026101) baseStart_2026101 baseEnd_2026101 := by
    simpa [prefixWord, tailWord_2026101, baseEnd_2026101] using wordTrace_append hprefix tailTrace_2026101
  have hstable : (prefixWord ++ tailWord_2026101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026101).length < 2 ^ (prefixWord ++ tailWord_2026101).sum := by decide
  have hdescent : baseEnd_2026101 < baseStart_2026101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026132 : List Nat := [2, 4, 2, 2, 1, 1, 2, 4, 3]
def baseStart_2026132 : Nat := 118140960795 + 2026132 * 2 ^ 59
def prefixEnd_2026132 : Nat := 4983230072969 + 3 ^ 40 * 2026132 * 2
def baseEnd_2026132 : Nat := 462390926869143103525331

theorem tailTrace_2026132 : CollatzResearch.WordTrace tailWord_2026132 prefixEnd_2026132 462390926869143103525331 := by
  unfold tailWord_2026132
  simp only [CollatzResearch.WordTrace]
  refine ⟨36949552547838637320696325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49266070063784849760928433 36949552547838637320696325)
  ·
    refine ⟨6928041102719744497630561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36949552547838637320696325 6928041102719744497630561)
    ·
      refine ⟨5196030827039808373222921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6928041102719744497630561 5196030827039808373222921)
      ·
        refine ⟨3897023120279856279917191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5196030827039808373222921 3897023120279856279917191)
        ·
          refine ⟨5845534680419784419875787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3897023120279856279917191 5845534680419784419875787)
          ·
            refine ⟨8768302020629676629813681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5845534680419784419875787 8768302020629676629813681)
            ·
              refine ⟨6576226515472257472360261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8768302020629676629813681 6576226515472257472360261)
              ·
                refine ⟨1233042471651048276067549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6576226515472257472360261 1233042471651048276067549)
                ·
                  refine ⟨462390926869143103525331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233042471651048276067549 462390926869143103525331)
                  ·
                    rfl

theorem cell21_2026132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_2026132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026132 prefixEnd_2026132 := by exact prefixLift 2026132
  have htrace : WordTrace (prefixWord ++ tailWord_2026132) baseStart_2026132 baseEnd_2026132 := by
    simpa [prefixWord, tailWord_2026132, baseEnd_2026132] using wordTrace_append hprefix tailTrace_2026132
  have hstable : (prefixWord ++ tailWord_2026132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026132).length < 2 ^ (prefixWord ++ tailWord_2026132).sum := by decide
  have hdescent : baseEnd_2026132 < baseStart_2026132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026166 : List Nat := [5, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_2026166 : Nat := 118140960795 + 2026166 * 2 ^ 59
def prefixEnd_2026166 : Nat := 4983230072969 + 3 ^ 40 * 2026166 * 2
def baseEnd_2026166 : Nat := 462398686132366599958595

theorem tailTrace_2026166 : CollatzResearch.WordTrace tailWord_2026166 prefixEnd_2026166 462398686132366599958595 := by
  unfold tailWord_2026166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618771573597131153008147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49266896785036065632086901 4618771573597131153008147)
  ·
    refine ⟨6928157360395696729512221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4618771573597131153008147 6928157360395696729512221)
    ·
      refine ⟨2598059010148386273567083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6928157360395696729512221 2598059010148386273567083)
      ·
        refine ⟨3897088515222579410350625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2598059010148386273567083 3897088515222579410350625)
        ·
          refine ⟨2922816386416934557762969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3897088515222579410350625 2922816386416934557762969)
          ·
            refine ⟨2192112289812700918322227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2922816386416934557762969 2192112289812700918322227)
            ·
              refine ⟨3288168434719051377483341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192112289812700918322227 3288168434719051377483341)
              ·
                refine ⟨1233063163019644266556253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3288168434719051377483341 1233063163019644266556253)
                ·
                  refine ⟨462398686132366599958595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233063163019644266556253 462398686132366599958595)
                  ·
                    rfl

theorem cell21_2026166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_2026166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026166 prefixEnd_2026166 := by exact prefixLift 2026166
  have htrace : WordTrace (prefixWord ++ tailWord_2026166) baseStart_2026166 baseEnd_2026166 := by
    simpa [prefixWord, tailWord_2026166, baseEnd_2026166] using wordTrace_append hprefix tailTrace_2026166
  have hstable : (prefixWord ++ tailWord_2026166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026166).length < 2 ^ (prefixWord ++ tailWord_2026166).sum := by decide
  have hdescent : baseEnd_2026166 < baseStart_2026166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026177 : List Nat := [1, 2, 6, 2, 1, 2, 7]
def baseStart_2026177 : Nat := 118140960795 + 2026177 * 2 ^ 59
def prefixEnd_2026177 : Nat := 4983230072969 + 3 ^ 40 * 2026177 * 2
def baseEnd_2026177 : Nat := 51377910720248113919471

theorem tailTrace_2026177 : CollatzResearch.WordTrace tailWord_2026177 prefixEnd_2026177 51377910720248113919471 := by
  unfold tailWord_2026177
  simp only [CollatzResearch.WordTrace]
  refine ⟨73900746380514247326780785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49267164253676164884520523 73900746380514247326780785)
  ·
    refine ⟨55425559785385685495085589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73900746380514247326780785 55425559785385685495085589)
    ·
      refine ⟨2598073114939954007582137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55425559785385685495085589 2598073114939954007582137)
      ·
        refine ⟨1948554836204965505686603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2598073114939954007582137 1948554836204965505686603)
        ·
          refine ⟨2922832254307448258529905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948554836204965505686603 2922832254307448258529905)
          ·
            refine ⟨2192124190730586193897429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2922832254307448258529905 2192124190730586193897429)
            ·
              refine ⟨51377910720248113919471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2192124190730586193897429 51377910720248113919471)
              ·
                rfl

theorem cell21_2026177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 7].length) (baseStart_2026177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026177 prefixEnd_2026177 := by exact prefixLift 2026177
  have htrace : WordTrace (prefixWord ++ tailWord_2026177) baseStart_2026177 baseEnd_2026177 := by
    simpa [prefixWord, tailWord_2026177, baseEnd_2026177] using wordTrace_append hprefix tailTrace_2026177
  have hstable : (prefixWord ++ tailWord_2026177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026177).length < 2 ^ (prefixWord ++ tailWord_2026177).sum := by decide
  have hdescent : baseEnd_2026177 < baseStart_2026177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026298 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_2026298 : Nat := 118140960795 + 2026298 * 2 ^ 59
def prefixEnd_2026298 : Nat := 4983230072969 + 3 ^ 40 * 2026298 * 2
def baseEnd_2026298 : Nat := 462428810330763703758325

theorem tailTrace_2026298 : CollatzResearch.WordTrace tailWord_2026298 prefixEnd_2026298 462428810330763703758325 := by
  unfold tailWord_2026298
  simp only [CollatzResearch.WordTrace]
  refine ⟨18476289903268971247983887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49270106408717256661290365 18476289903268971247983887)
  ·
    refine ⟨27714434854903456871975831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18476289903268971247983887 27714434854903456871975831)
    ·
      refine ⟨41571652282355185307963747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27714434854903456871975831 41571652282355185307963747)
      ·
        refine ⟨62357478423532777961945621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41571652282355185307963747 62357478423532777961945621)
        ·
          refine ⟨2923006801103098966966201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62357478423532777961945621 2923006801103098966966201)
          ·
            refine ⟨2192255100827324225224651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2923006801103098966966201 2192255100827324225224651)
            ·
              refine ⟨3288382651240986337836977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192255100827324225224651 3288382651240986337836977)
              ·
                refine ⟨2466286988430739753377733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3288382651240986337836977 2466286988430739753377733)
                ·
                  refine ⟨462428810330763703758325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2466286988430739753377733 462428810330763703758325)
                  ·
                    rfl

theorem cell21_2026298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_2026298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026298 prefixEnd_2026298 := by exact prefixLift 2026298
  have htrace : WordTrace (prefixWord ++ tailWord_2026298) baseStart_2026298 baseEnd_2026298 := by
    simpa [prefixWord, tailWord_2026298, baseEnd_2026298] using wordTrace_append hprefix tailTrace_2026298
  have hstable : (prefixWord ++ tailWord_2026298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026298).length < 2 ^ (prefixWord ++ tailWord_2026298).sum := by decide
  have hdescent : baseEnd_2026298 < baseStart_2026298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026340 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_2026340 : Nat := 118140960795 + 2026340 * 2 ^ 59
def prefixEnd_2026340 : Nat := 4983230072969 + 3 ^ 40 * 2026340 * 2
def baseEnd_2026340 : Nat := 462438395302980964058239

theorem tailTrace_2026340 : CollatzResearch.WordTrace tailWord_2026340 prefixEnd_2026340 462438395302980964058239 := by
  unfold tailWord_2026340
  simp only [CollatzResearch.WordTrace]
  refine ⟨36953345739461863082482237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49271127652615817443309649 36953345739461863082482237)
  ·
    refine ⟨13857504652298198655930839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36953345739461863082482237 13857504652298198655930839)
    ·
      refine ⟨20786256978447297983896259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13857504652298198655930839 20786256978447297983896259)
      ·
        refine ⟨31179385467670946975844389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20786256978447297983896259 31179385467670946975844389)
        ·
          refine ⟨5846134775188302557970823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31179385467670946975844389 5846134775188302557970823)
          ·
            refine ⟨8769202162782453836956235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846134775188302557970823 8769202162782453836956235)
            ·
              refine ⟨13153803244173680755434353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8769202162782453836956235 13153803244173680755434353)
              ·
                refine ⟨9865352433130260566575765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13153803244173680755434353 9865352433130260566575765)
                ·
                  refine ⟨462438395302980964058239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9865352433130260566575765 462438395302980964058239)
                  ·
                    rfl

theorem cell21_2026340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_2026340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026340 prefixEnd_2026340 := by exact prefixLift 2026340
  have htrace : WordTrace (prefixWord ++ tailWord_2026340) baseStart_2026340 baseEnd_2026340 := by
    simpa [prefixWord, tailWord_2026340, baseEnd_2026340] using wordTrace_append hprefix tailTrace_2026340
  have hstable : (prefixWord ++ tailWord_2026340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026340).length < 2 ^ (prefixWord ++ tailWord_2026340).sum := by decide
  have hdescent : baseEnd_2026340 < baseStart_2026340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026343 : List Nat := [1, 1, 5, 1, 2, 2, 3, 3, 3]
def baseStart_2026343 : Nat := 118140960795 + 2026343 * 2 ^ 59
def prefixEnd_2026343 : Nat := 4983230072969 + 3 ^ 40 * 2026343 * 2
def baseEnd_2026343 : Nat := 462439079943853625508233

theorem tailTrace_2026343 : CollatzResearch.WordTrace tailWord_2026343 prefixEnd_2026343 462439079943853625508233 := by
  unfold tailWord_2026343
  simp only [CollatzResearch.WordTrace]
  refine ⟨73906800897912857677323683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49271200598608571784882455 73906800897912857677323683)
  ·
    refine ⟨110860201346869286515985525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73906800897912857677323683 110860201346869286515985525)
    ·
      refine ⟨10393143876268995610873643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110860201346869286515985525 10393143876268995610873643)
      ·
        refine ⟨15589715814403493416310465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10393143876268995610873643 15589715814403493416310465)
        ·
          refine ⟨11692286860802620062232849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15589715814403493416310465 11692286860802620062232849)
          ·
            refine ⟨8769215145601965046674637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11692286860802620062232849 8769215145601965046674637)
            ·
              refine ⟨3288455679600736892502989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8769215145601965046674637 3288455679600736892502989)
              ·
                refine ⟨1233170879850276334688621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3288455679600736892502989 1233170879850276334688621)
                ·
                  refine ⟨462439079943853625508233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233170879850276334688621 462439079943853625508233)
                  ·
                    rfl

theorem cell21_2026343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 3].length) (baseStart_2026343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026343 prefixEnd_2026343 := by exact prefixLift 2026343
  have htrace : WordTrace (prefixWord ++ tailWord_2026343) baseStart_2026343 baseEnd_2026343 := by
    simpa [prefixWord, tailWord_2026343, baseEnd_2026343] using wordTrace_append hprefix tailTrace_2026343
  have hstable : (prefixWord ++ tailWord_2026343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026343).length < 2 ^ (prefixWord ++ tailWord_2026343).sum := by decide
  have hdescent : baseEnd_2026343 < baseStart_2026343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026354 : List Nat := [3, 2, 1, 2, 1, 1, 11]
def baseStart_2026354 : Nat := 118140960795 + 2026354 * 2 ^ 59
def prefixEnd_2026354 : Nat := 4983230072969 + 3 ^ 40 * 2026354 * 2
def baseEnd_2026354 : Nat := 51382398921524450091653

theorem tailTrace_2026354 : CollatzResearch.WordTrace tailWord_2026354 prefixEnd_2026354 51382398921524450091653 := by
  unfold tailWord_2026354
  simp only [CollatzResearch.WordTrace]
  refine ⟨18476800525218251638993529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49271468067248671037316077 18476800525218251638993529)
  ·
    refine ⟨13857600393913688729245147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18476800525218251638993529 13857600393913688729245147)
    ·
      refine ⟨20786400590870533093867721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13857600393913688729245147 20786400590870533093867721)
      ·
        refine ⟨15589800443152899820400791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20786400590870533093867721 15589800443152899820400791)
        ·
          refine ⟨23384700664729349730601187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15589800443152899820400791 23384700664729349730601187)
          ·
            refine ⟨35077050997094024595901781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23384700664729349730601187 35077050997094024595901781)
            ·
              refine ⟨51382398921524450091653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35077050997094024595901781 51382398921524450091653)
              ·
                rfl

theorem cell21_2026354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 11].length) (baseStart_2026354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026354 prefixEnd_2026354 := by exact prefixLift 2026354
  have htrace : WordTrace (prefixWord ++ tailWord_2026354) baseStart_2026354 baseEnd_2026354 := by
    simpa [prefixWord, tailWord_2026354, baseEnd_2026354] using wordTrace_append hprefix tailTrace_2026354
  have hstable : (prefixWord ++ tailWord_2026354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026354).length < 2 ^ (prefixWord ++ tailWord_2026354).sum := by decide
  have hdescent : baseEnd_2026354 < baseStart_2026354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026447 : List Nat := [1, 1, 2, 1, 1, 7, 3, 5]
def baseStart_2026447 : Nat := 118140960795 + 2026447 * 2 ^ 59
def prefixEnd_2026447 : Nat := 4983230072969 + 3 ^ 40 * 2026447 * 2
def baseEnd_2026447 : Nat := 154154271386924185258229

theorem tailTrace_2026447 : CollatzResearch.WordTrace tailWord_2026447 prefixEnd_2026447 154154271386924185258229 := by
  unfold tailWord_2026447
  simp only [CollatzResearch.WordTrace]
  refine ⟨73910594089536083439109595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49273729393024055626073063 73910594089536083439109595)
  ·
    refine ⟨110865891134304125158664393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73910594089536083439109595 110865891134304125158664393)
    ·
      refine ⟨83149418350728093868998295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110865891134304125158664393 83149418350728093868998295)
      ·
        refine ⟨124724127526092140803497443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83149418350728093868998295 124724127526092140803497443)
        ·
          refine ⟨187086191289138211205246165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124724127526092140803497443 187086191289138211205246165)
          ·
            refine ⟨4384832608339176825122957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 187086191289138211205246165 4384832608339176825122957)
            ·
              refine ⟨1644312228127191309421109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4384832608339176825122957 1644312228127191309421109)
              ·
                refine ⟨154154271386924185258229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1644312228127191309421109 154154271386924185258229)
                ·
                  rfl

theorem cell21_2026447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 5].length) (baseStart_2026447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026447 prefixEnd_2026447 := by exact prefixLift 2026447
  have htrace : WordTrace (prefixWord ++ tailWord_2026447) baseStart_2026447 baseEnd_2026447 := by
    simpa [prefixWord, tailWord_2026447, baseEnd_2026447] using wordTrace_append hprefix tailTrace_2026447
  have hstable : (prefixWord ++ tailWord_2026447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026447).length < 2 ^ (prefixWord ++ tailWord_2026447).sum := by decide
  have hdescent : baseEnd_2026447 < baseStart_2026447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026498 : List Nat := [3, 4, 1, 3, 1, 2, 2, 5]
def baseStart_2026498 : Nat := 118140960795 + 2026498 * 2 ^ 59
def prefixEnd_2026498 : Nat := 4983230072969 + 3 ^ 40 * 2026498 * 2
def baseEnd_2026498 : Nat := 154158151018535933474861

theorem tailTrace_2026498 : CollatzResearch.WordTrace tailWord_2026498 prefixEnd_2026498 154158151018535933474861 := by
  unfold tailWord_2026498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18478113553087829787304037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49274969474900879432810765 18478113553087829787304037)
  ·
    refine ⟨3464646291203968085119507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18478113553087829787304037 3464646291203968085119507)
    ·
      refine ⟨5196969436805952127679261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3464646291203968085119507 5196969436805952127679261)
      ·
        refine ⟨1948863538802232047879723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5196969436805952127679261 1948863538802232047879723)
        ·
          refine ⟨2923295308203348071819585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948863538802232047879723 2923295308203348071819585)
          ·
            refine ⟨2192471481152511053864689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2923295308203348071819585 2192471481152511053864689)
            ·
              refine ⟨1644353610864383290398517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2192471481152511053864689 1644353610864383290398517)
              ·
                refine ⟨154158151018535933474861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1644353610864383290398517 154158151018535933474861)
                ·
                  rfl

theorem cell21_2026498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_2026498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026498 prefixEnd_2026498 := by exact prefixLift 2026498
  have htrace : WordTrace (prefixWord ++ tailWord_2026498) baseStart_2026498 baseEnd_2026498 := by
    simpa [prefixWord, tailWord_2026498, baseEnd_2026498] using wordTrace_append hprefix tailTrace_2026498
  have hstable : (prefixWord ++ tailWord_2026498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026498).length < 2 ^ (prefixWord ++ tailWord_2026498).sum := by decide
  have hdescent : baseEnd_2026498 < baseStart_2026498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026599 : List Nat := [1, 1, 5, 1, 1, 5, 1, 6]
def baseStart_2026599 : Nat := 118140960795 + 2026599 * 2 ^ 59
def prefixEnd_2026599 : Nat := 4983230072969 + 3 ^ 40 * 2026599 * 2
def baseEnd_2026599 : Nat := 154165834210551356413681

theorem tailTrace_2026599 : CollatzResearch.WordTrace tailWord_2026599 prefixEnd_2026599 154165834210551356413681 := by
  unfold tailWord_2026599
  simp only [CollatzResearch.WordTrace]
  refine ⟨73916137984985413398642851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49277425323323608932428567 73916137984985413398642851)
  ·
    refine ⟨110874206977478120097964277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73916137984985413398642851 110874206977478120097964277)
    ·
      refine ⟨10394456904138573759184151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110874206977478120097964277 10394456904138573759184151)
      ·
        refine ⟨15591685356207860638776227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10394456904138573759184151 15591685356207860638776227)
        ·
          refine ⟨23387528034311790958164341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15591685356207860638776227 23387528034311790958164341)
          ·
            refine ⟨2192580753216730402327907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23387528034311790958164341 2192580753216730402327907)
            ·
              refine ⟨3288871129825095603491861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192580753216730402327907 3288871129825095603491861)
              ·
                refine ⟨154165834210551356413681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3288871129825095603491861 154165834210551356413681)
                ·
                  rfl

theorem cell21_2026599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 6].length) (baseStart_2026599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026599 prefixEnd_2026599 := by exact prefixLift 2026599
  have htrace : WordTrace (prefixWord ++ tailWord_2026599) baseStart_2026599 baseEnd_2026599 := by
    simpa [prefixWord, tailWord_2026599, baseEnd_2026599] using wordTrace_append hprefix tailTrace_2026599
  have hstable : (prefixWord ++ tailWord_2026599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026599).length < 2 ^ (prefixWord ++ tailWord_2026599).sum := by decide
  have hdescent : baseEnd_2026599 < baseStart_2026599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026622 : List Nat := [4, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_2026622 : Nat := 118140960795 + 2026622 * 2 ^ 59
def prefixEnd_2026622 : Nat := 4983230072969 + 3 ^ 40 * 2026622 * 2
def baseEnd_2026622 : Nat := 462502751545011140357663

theorem tailTrace_2026622 : CollatzResearch.WordTrace tailWord_2026622 prefixEnd_2026622 462502751545011140357663 := by
  unfold tailWord_2026622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9239622107987761040841265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49277984575934725551153413 9239622107987761040841265)
  ·
    refine ⟨6929716580990820780630949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9239622107987761040841265 6929716580990820780630949)
    ·
      refine ⟨1299321858935778896368303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6929716580990820780630949 1299321858935778896368303)
      ·
        refine ⟨1948982788403668344552455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299321858935778896368303 1948982788403668344552455)
        ·
          refine ⟨2923474182605502516828683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948982788403668344552455 2923474182605502516828683)
          ·
            refine ⟨4385211273908253775243025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923474182605502516828683 4385211273908253775243025)
            ·
              refine ⟨3288908455431190331432269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4385211273908253775243025 3288908455431190331432269)
              ·
                refine ⟨1233340670786696374287101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3288908455431190331432269 1233340670786696374287101)
                ·
                  refine ⟨462502751545011140357663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233340670786696374287101 462502751545011140357663)
                  ·
                    rfl

theorem cell21_2026622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_2026622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026622 prefixEnd_2026622 := by exact prefixLift 2026622
  have htrace : WordTrace (prefixWord ++ tailWord_2026622) baseStart_2026622 baseEnd_2026622 := by
    simpa [prefixWord, tailWord_2026622, baseEnd_2026622] using wordTrace_append hprefix tailTrace_2026622
  have hstable : (prefixWord ++ tailWord_2026622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026622).length < 2 ^ (prefixWord ++ tailWord_2026622).sum := by decide
  have hdescent : baseEnd_2026622 < baseStart_2026622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026627 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 6]
def baseStart_2026627 : Nat := 118140960795 + 2026627 * 2 ^ 59
def prefixEnd_2026627 : Nat := 4983230072969 + 3 ^ 40 * 2026627 * 2
def baseEnd_2026627 : Nat := 462503892613132242774319

theorem tailTrace_2026627 : CollatzResearch.WordTrace tailWord_2026627 prefixEnd_2026627 462503892613132242774319 := by
  unfold tailWord_2026627
  simp only [CollatzResearch.WordTrace]
  refine ⟨73917159228883974180662135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49278106152589316120441423 73917159228883974180662135)
  ·
    refine ⟨110875738843325961270993203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73917159228883974180662135 110875738843325961270993203)
    ·
      refine ⟨166313608264988941906489805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110875738843325961270993203 166313608264988941906489805)
      ·
        refine ⟨62367603099370853214933677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166313608264988941906489805 62367603099370853214933677)
        ·
          refine ⟨23387851162264069955600129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62367603099370853214933677 23387851162264069955600129)
          ·
            refine ⟨17540888371698052466700097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23387851162264069955600129 17540888371698052466700097)
            ·
              refine ⟨13155666278773539350025073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17540888371698052466700097 13155666278773539350025073)
              ·
                refine ⟨9866749709080154512518805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13155666278773539350025073 9866749709080154512518805)
                ·
                  refine ⟨462503892613132242774319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9866749709080154512518805 462503892613132242774319)
                  ·
                    rfl

theorem cell21_2026627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_2026627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026627 prefixEnd_2026627 := by exact prefixLift 2026627
  have htrace : WordTrace (prefixWord ++ tailWord_2026627) baseStart_2026627 baseEnd_2026627 := by
    simpa [prefixWord, tailWord_2026627, baseEnd_2026627] using wordTrace_append hprefix tailTrace_2026627
  have hstable : (prefixWord ++ tailWord_2026627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026627).length < 2 ^ (prefixWord ++ tailWord_2026627).sum := by decide
  have hdescent : baseEnd_2026627 < baseStart_2026627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026661 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 4]
def baseStart_2026661 : Nat := 118140960795 + 2026661 * 2 ^ 59
def prefixEnd_2026661 : Nat := 4983230072969 + 3 ^ 40 * 2026661 * 2
def baseEnd_2026661 : Nat := 462511651876355739207583

theorem tailTrace_2026661 : CollatzResearch.WordTrace tailWord_2026661 prefixEnd_2026661 462511651876355739207583 := by
  unfold tailWord_2026661
  simp only [CollatzResearch.WordTrace]
  refine ⟨73918399310760797987399837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49278932873840531991599891 73918399310760797987399837)
  ·
    refine ⟨27719399741535299245274939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73918399310760797987399837 27719399741535299245274939)
    ·
      refine ⟨41579099612302948867912409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27719399741535299245274939 41579099612302948867912409)
      ·
        refine ⟨31184324709227211650934307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41579099612302948867912409 31184324709227211650934307)
        ·
          refine ⟨46776487063840817476401461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31184324709227211650934307 46776487063840817476401461)
          ·
            refine ⟨4385295662235076638412637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46776487063840817476401461 4385295662235076638412637)
            ·
              refine ⟨1644485873338153739404739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4385295662235076638412637 1644485873338153739404739)
              ·
                refine ⟨2466728810007230609107109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644485873338153739404739 2466728810007230609107109)
                ·
                  refine ⟨462511651876355739207583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2466728810007230609107109 462511651876355739207583)
                  ·
                    rfl

theorem cell21_2026661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_2026661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026661 prefixEnd_2026661 := by exact prefixLift 2026661
  have htrace : WordTrace (prefixWord ++ tailWord_2026661) baseStart_2026661 baseEnd_2026661 := by
    simpa [prefixWord, tailWord_2026661, baseEnd_2026661] using wordTrace_append hprefix tailTrace_2026661
  have hstable : (prefixWord ++ tailWord_2026661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026661).length < 2 ^ (prefixWord ++ tailWord_2026661).sum := by decide
  have hdescent : baseEnd_2026661 < baseStart_2026661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026692 : List Nat := [2, 3, 3, 1, 4, 1, 7]
def baseStart_2026692 : Nat := 118140960795 + 2026692 * 2 ^ 59
def prefixEnd_2026692 : Nat := 4983230072969 + 3 ^ 40 * 2026692 * 2
def baseEnd_2026692 : Nat := 51390969610967397132317

theorem tailTrace_2026692 : CollatzResearch.WordTrace tailWord_2026692 prefixEnd_2026692 51390969610967397132317 := by
  unfold tailWord_2026692
  simp only [CollatzResearch.WordTrace]
  refine ⟨36959764986824245140889165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49279686649098993521185553 36959764986824245140889165)
  ·
    refine ⟨13859911870059091927833437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36959764986824245140889165 13859911870059091927833437)
    ·
      refine ⟨5197466951272159472937539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13859911870059091927833437 5197466951272159472937539)
      ·
        refine ⟨7796200426908239209406309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5197466951272159472937539 7796200426908239209406309)
        ·
          refine ⟨1461787580045294851763683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7796200426908239209406309 1461787580045294851763683)
          ·
            refine ⟨2192681370067942277645525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461787580045294851763683 2192681370067942277645525)
            ·
              refine ⟨51390969610967397132317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2192681370067942277645525 51390969610967397132317)
              ·
                rfl

theorem cell21_2026692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 7].length) (baseStart_2026692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026692 prefixEnd_2026692 := by exact prefixLift 2026692
  have htrace : WordTrace (prefixWord ++ tailWord_2026692) baseStart_2026692 baseEnd_2026692 := by
    simpa [prefixWord, tailWord_2026692, baseEnd_2026692] using wordTrace_append hprefix tailTrace_2026692
  have hstable : (prefixWord ++ tailWord_2026692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026692).length < 2 ^ (prefixWord ++ tailWord_2026692).sum := by decide
  have hdescent : baseEnd_2026692 < baseStart_2026692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026720 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 4]
def baseStart_2026720 : Nat := 118140960795 + 2026720 * 2 ^ 59
def prefixEnd_2026720 : Nat := 4983230072969 + 3 ^ 40 * 2026720 * 2
def baseEnd_2026720 : Nat := 462525116480184747724129

theorem tailTrace_2026720 : CollatzResearch.WordTrace tailWord_2026720 prefixEnd_2026720 462525116480184747724129 := by
  unfold tailWord_2026720
  simp only [CollatzResearch.WordTrace]
  refine ⟨36960275608773525531898807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49280367478364700709198409 36960275608773525531898807)
  ·
    refine ⟨55440413413160288297848211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36960275608773525531898807 55440413413160288297848211)
    ·
      refine ⟨83160620119740432446772317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55440413413160288297848211 83160620119740432446772317)
      ·
        refine ⟨31185232544902662167539619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83160620119740432446772317 31185232544902662167539619)
        ·
          refine ⟨46777848817353993251309429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31185232544902662167539619 46777848817353993251309429)
          ·
            refine ⟨4385423326626936867310259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46777848817353993251309429 4385423326626936867310259)
            ·
              refine ⟨6578134989940405300965389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385423326626936867310259 6578134989940405300965389)
              ·
                refine ⟨2466800621227651987862021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6578134989940405300965389 2466800621227651987862021)
                ·
                  refine ⟨462525116480184747724129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2466800621227651987862021 462525116480184747724129)
                  ·
                    rfl

theorem cell21_2026720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_2026720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026720 prefixEnd_2026720 := by exact prefixLift 2026720
  have htrace : WordTrace (prefixWord ++ tailWord_2026720) baseStart_2026720 baseEnd_2026720 := by
    simpa [prefixWord, tailWord_2026720, baseEnd_2026720] using wordTrace_append hprefix tailTrace_2026720
  have hstable : (prefixWord ++ tailWord_2026720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026720).length < 2 ^ (prefixWord ++ tailWord_2026720).sum := by decide
  have hdescent : baseEnd_2026720 < baseStart_2026720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026734 : List Nat := [4, 1, 2, 1, 1, 1, 4, 7]
def baseStart_2026734 : Nat := 118140960795 + 2026734 * 2 ^ 59
def prefixEnd_2026734 : Nat := 4983230072969 + 3 ^ 40 * 2026734 * 2
def baseEnd_2026734 : Nat := 154176103823641278163589

theorem tailTrace_2026734 : CollatzResearch.WordTrace tailWord_2026734 prefixEnd_2026734 154176103823641278163589 := by
  unfold tailWord_2026734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9240132729937041431850907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49280707892997554303204837 9240132729937041431850907)
  ·
    refine ⟨13860199094905562147776361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9240132729937041431850907 13860199094905562147776361)
    ·
      refine ⟨10395149321179171610832271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13860199094905562147776361 10395149321179171610832271)
      ·
        refine ⟨15592723981768757416248407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10395149321179171610832271 15592723981768757416248407)
        ·
          refine ⟨23389085972653136124372611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15592723981768757416248407 23389085972653136124372611)
          ·
            refine ⟨35083628958979704186558917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23389085972653136124372611 35083628958979704186558917)
            ·
              refine ⟨6578180429808694534979797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35083628958979704186558917 6578180429808694534979797)
              ·
                refine ⟨154176103823641278163589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6578180429808694534979797 154176103823641278163589)
                ·
                  rfl

theorem cell21_2026734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_2026734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026734 prefixEnd_2026734 := by exact prefixLift 2026734
  have htrace : WordTrace (prefixWord ++ tailWord_2026734) baseStart_2026734 baseEnd_2026734 := by
    simpa [prefixWord, tailWord_2026734, baseEnd_2026734] using wordTrace_append hprefix tailTrace_2026734
  have hstable : (prefixWord ++ tailWord_2026734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026734).length < 2 ^ (prefixWord ++ tailWord_2026734).sum := by decide
  have hdescent : baseEnd_2026734 < baseStart_2026734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026754 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2026754 : Nat := 118140960795 + 2026754 * 2 ^ 59
def prefixEnd_2026754 : Nat := 4983230072969 + 3 ^ 40 * 2026754 * 2
def baseEnd_2026754 : Nat := 462532875743408244157393

theorem tailTrace_2026754 : CollatzResearch.WordTrace tailWord_2026754 prefixEnd_2026754 462532875743408244157393 := by
  unfold tailWord_2026754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18480447824855968717633829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49281194199615916580356877 18480447824855968717633829)
  ·
    refine ⟨3465083967160494134556343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18480447824855968717633829 3465083967160494134556343)
    ·
      refine ⟨5197625950740741201834515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3465083967160494134556343 5197625950740741201834515)
      ·
        refine ⟨7796438926111111802751773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5197625950740741201834515 7796438926111111802751773)
        ·
          refine ⟨2923664597291666926031915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7796438926111111802751773 2923664597291666926031915)
          ·
            refine ⟨4385496895937500389047873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923664597291666926031915 4385496895937500389047873)
            ·
              refine ⟨3289122671953125291785905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4385496895937500389047873 3289122671953125291785905)
              ·
                refine ⟨2466842003964843968839429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3289122671953125291785905 2466842003964843968839429)
                ·
                  refine ⟨462532875743408244157393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2466842003964843968839429 462532875743408244157393)
                  ·
                    rfl

theorem cell21_2026754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2026754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026754 prefixEnd_2026754 := by exact prefixLift 2026754
  have htrace : WordTrace (prefixWord ++ tailWord_2026754) baseStart_2026754 baseEnd_2026754 := by
    simpa [prefixWord, tailWord_2026754, baseEnd_2026754] using wordTrace_append hprefix tailTrace_2026754
  have hstable : (prefixWord ++ tailWord_2026754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026754).length < 2 ^ (prefixWord ++ tailWord_2026754).sum := by decide
  have hdescent : baseEnd_2026754 < baseStart_2026754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026813 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 6]
def baseStart_2026813 : Nat := 118140960795 + 2026813 * 2 ^ 59
def prefixEnd_2026813 : Nat := 4983230072969 + 3 ^ 40 * 2026813 * 2
def baseEnd_2026813 : Nat := 462546340347237252673939

theorem tailTrace_2026813 : CollatzResearch.WordTrace tailWord_2026813 prefixEnd_2026813 462546340347237252673939 := by
  unfold tailWord_2026813
  simp only [CollatzResearch.WordTrace]
  refine ⟨73923943206210127946933093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49282628804140085297955395 73923943206210127946933093)
  ·
    refine ⟨13860739351164398990049955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73923943206210127946933093 13860739351164398990049955)
    ·
      refine ⟨20791109026746598485074933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13860739351164398990049955 20791109026746598485074933)
      ·
        refine ⟨1949166471257493607975775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20791109026746598485074933 1949166471257493607975775)
        ·
          refine ⟨2923749706886240411963663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1949166471257493607975775 2923749706886240411963663)
          ·
            refine ⟨4385624560329360617945495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923749706886240411963663 4385624560329360617945495)
            ·
              refine ⟨6578436840494040926918243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385624560329360617945495 6578436840494040926918243)
              ·
                refine ⟨9867655260741061390377365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6578436840494040926918243 9867655260741061390377365)
                ·
                  refine ⟨462546340347237252673939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9867655260741061390377365 462546340347237252673939)
                  ·
                    rfl

theorem cell21_2026813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_2026813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026813 prefixEnd_2026813 := by exact prefixLift 2026813
  have htrace : WordTrace (prefixWord ++ tailWord_2026813) baseStart_2026813 baseEnd_2026813 := by
    simpa [prefixWord, tailWord_2026813, baseEnd_2026813] using wordTrace_append hprefix tailTrace_2026813
  have hstable : (prefixWord ++ tailWord_2026813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026813).length < 2 ^ (prefixWord ++ tailWord_2026813).sum := by decide
  have hdescent : baseEnd_2026813 < baseStart_2026813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026993 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 5]
def baseStart_2026993 : Nat := 118140960795 + 2026993 * 2 ^ 59
def prefixEnd_2026993 : Nat := 4983230072969 + 3 ^ 40 * 2026993 * 2
def baseEnd_2026993 : Nat := 462587418799596939673571

theorem tailTrace_2026993 : CollatzResearch.WordTrace tailWord_2026993 prefixEnd_2026993 462587418799596939673571 := by
  unfold tailWord_2026993
  simp only [CollatzResearch.WordTrace]
  refine ⟨73930508345558018688485633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49287005563705345792323755 73930508345558018688485633)
  ·
    refine ⟨55447881259168514016364225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73930508345558018688485633 55447881259168514016364225)
    ·
      refine ⟨41585910944376385512273169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55447881259168514016364225 41585910944376385512273169)
      ·
        refine ⟨31189433208282289134204877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41585910944376385512273169 31189433208282289134204877)
        ·
          refine ⟨11696037453105858425326829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31189433208282289134204877 11696037453105858425326829)
          ·
            refine ⟨4386014044914696909497561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11696037453105858425326829 4386014044914696909497561)
            ·
              refine ⟨3289510533686022682123171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4386014044914696909497561 3289510533686022682123171)
              ·
                refine ⟨4934265800529034023184757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289510533686022682123171 4934265800529034023184757)
                ·
                  refine ⟨462587418799596939673571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4934265800529034023184757 462587418799596939673571)
                  ·
                    rfl

theorem cell21_2026993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_2026993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2026993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2026993 prefixEnd_2026993 := by exact prefixLift 2026993
  have htrace : WordTrace (prefixWord ++ tailWord_2026993) baseStart_2026993 baseEnd_2026993 := by
    simpa [prefixWord, tailWord_2026993, baseEnd_2026993] using wordTrace_append hprefix tailTrace_2026993
  have hstable : (prefixWord ++ tailWord_2026993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026993).length < 2 ^ (prefixWord ++ tailWord_2026993).sum := by decide
  have hdescent : baseEnd_2026993 < baseStart_2026993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027010 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2027010 : Nat := 118140960795 + 2027010 * 2 ^ 59
def prefixEnd_2027010 : Nat := 4983230072969 + 3 ^ 40 * 2027010 * 2
def baseEnd_2027010 : Nat := 462591298431208687890203

theorem tailTrace_2027010 : CollatzResearch.WordTrace tailWord_2027010 prefixEnd_2027010 462591298431208687890203 := by
  unfold tailWord_2027010
  simp only [CollatzResearch.WordTrace]
  refine ⟨18482782096624107647963621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49287418924330953727902989 18482782096624107647963621)
  ·
    refine ⟨3465521643117020183993179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18482782096624107647963621 3465521643117020183993179)
    ·
      refine ⟨5198282464675530275989769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3465521643117020183993179 5198282464675530275989769)
      ·
        refine ⟨3898711848506647706992327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5198282464675530275989769 3898711848506647706992327)
        ·
          refine ⟨5848067772759971560488491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898711848506647706992327 5848067772759971560488491)
          ·
            refine ⟨8772101659139957340732737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848067772759971560488491 8772101659139957340732737)
            ·
              refine ⟨6579076244354968005549553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8772101659139957340732737 6579076244354968005549553)
              ·
                refine ⟨4934307183266226004162165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6579076244354968005549553 4934307183266226004162165)
                ·
                  refine ⟨462591298431208687890203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4934307183266226004162165 462591298431208687890203)
                  ·
                    rfl

theorem cell21_2027010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2027010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027010 prefixEnd_2027010 := by exact prefixLift 2027010
  have htrace : WordTrace (prefixWord ++ tailWord_2027010) baseStart_2027010 baseEnd_2027010 := by
    simpa [prefixWord, tailWord_2027010, baseEnd_2027010] using wordTrace_append hprefix tailTrace_2027010
  have hstable : (prefixWord ++ tailWord_2027010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027010).length < 2 ^ (prefixWord ++ tailWord_2027010).sum := by decide
  have hdescent : baseEnd_2027010 < baseStart_2027010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027100 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 4]
def baseStart_2027100 : Nat := 118140960795 + 2027100 * 2 ^ 59
def prefixEnd_2027100 : Nat := 4983230072969 + 3 ^ 40 * 2027100 * 2
def baseEnd_2027100 : Nat := 462611837657388531390019

theorem tailTrace_2027100 : CollatzResearch.WordTrace tailWord_2027100 prefixEnd_2027100 462611837657388531390019 := by
  unfold tailWord_2027100
  simp only [CollatzResearch.WordTrace]
  refine ⟨36967205478085187981315377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49289607304113583975087169 36967205478085187981315377)
  ·
    refine ⟨27725404108563890985986533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36967205478085187981315377 27725404108563890985986533)
    ·
      refine ⟨5198513270355729559872475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27725404108563890985986533 5198513270355729559872475)
      ·
        refine ⟨7797769905533594339808713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5198513270355729559872475 7797769905533594339808713)
        ·
          refine ⟨5848327429150195754856535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7797769905533594339808713 5848327429150195754856535)
          ·
            refine ⟨8772491143725293632284803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848327429150195754856535 8772491143725293632284803)
            ·
              refine ⟨13158736715587940448427205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772491143725293632284803 13158736715587940448427205)
              ·
                refine ⟨2467263134172738834080101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13158736715587940448427205 2467263134172738834080101)
                ·
                  refine ⟨462611837657388531390019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2467263134172738834080101 462611837657388531390019)
                  ·
                    rfl

theorem cell21_2027100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_2027100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027100 prefixEnd_2027100 := by exact prefixLift 2027100
  have htrace : WordTrace (prefixWord ++ tailWord_2027100) baseStart_2027100 baseEnd_2027100 := by
    simpa [prefixWord, tailWord_2027100, baseEnd_2027100] using wordTrace_append hprefix tailTrace_2027100
  have hstable : (prefixWord ++ tailWord_2027100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027100).length < 2 ^ (prefixWord ++ tailWord_2027100).sum := by decide
  have hdescent : baseEnd_2027100 < baseStart_2027100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027114 : List Nat := [3, 1, 3, 2, 1, 2, 3, 6]
def baseStart_2027114 : Nat := 118140960795 + 2027114 * 2 ^ 59
def prefixEnd_2027114 : Nat := 4983230072969 + 3 ^ 40 * 2027114 * 2
def baseEnd_2027114 : Nat := 154205010882709206052219

theorem tailTrace_2027114 : CollatzResearch.WordTrace tailWord_2027114 prefixEnd_2027114 154205010882709206052219 := by
  unfold tailWord_2027114
  simp only [CollatzResearch.WordTrace]
  refine ⟨18483730394529914088410099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49289947718746437569093597 18483730394529914088410099)
  ·
    refine ⟨27725595591794871132615149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18483730394529914088410099 27725595591794871132615149)
    ·
      refine ⟨10397098346923076674730681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27725595591794871132615149 10397098346923076674730681)
      ·
        refine ⟨7797823760192307506048011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10397098346923076674730681 7797823760192307506048011)
        ·
          refine ⟨11696735640288461259072017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797823760192307506048011 11696735640288461259072017)
          ·
            refine ⟨8772551730216345944304013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11696735640288461259072017 8772551730216345944304013)
            ·
              refine ⟨3289706898831129729114005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8772551730216345944304013 3289706898831129729114005)
              ·
                refine ⟨154205010882709206052219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3289706898831129729114005 154205010882709206052219)
                ·
                  rfl

theorem cell21_2027114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_2027114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027114 prefixEnd_2027114 := by exact prefixLift 2027114
  have htrace : WordTrace (prefixWord ++ tailWord_2027114) baseStart_2027114 baseEnd_2027114 := by
    simpa [prefixWord, tailWord_2027114, baseEnd_2027114] using wordTrace_append hprefix tailTrace_2027114
  have hstable : (prefixWord ++ tailWord_2027114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027114).length < 2 ^ (prefixWord ++ tailWord_2027114).sum := by decide
  have hdescent : baseEnd_2027114 < baseStart_2027114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027145 : List Nat := [1, 2, 1, 1, 4, 1, 3, 5, 3]
def baseStart_2027145 : Nat := 118140960795 + 2027145 * 2 ^ 59
def prefixEnd_2027145 : Nat := 4983230072969 + 3 ^ 40 * 2027145 * 2
def baseEnd_2027145 : Nat := 462622107270478453139927

theorem tailTrace_2027145 : CollatzResearch.WordTrace tailWord_2027145 prefixEnd_2027145 462622107270478453139927 := by
  unfold tailWord_2027145
  simp only [CollatzResearch.WordTrace]
  refine ⟨73936052241007348648018889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49290701494004899098679259 73936052241007348648018889)
  ·
    refine ⟨55452039180755511486014167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73936052241007348648018889 55452039180755511486014167)
    ·
      refine ⟨83178058771133267229021251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55452039180755511486014167 83178058771133267229021251)
      ·
        refine ⟨124767088156699900843531877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83178058771133267229021251 124767088156699900843531877)
        ·
          refine ⟨23393829029381231408162227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124767088156699900843531877 23393829029381231408162227)
          ·
            refine ⟨35090743544071847112243341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23393829029381231408162227 35090743544071847112243341)
            ·
              refine ⟨13159028829026942667091253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35090743544071847112243341 13159028829026942667091253)
              ·
                refine ⟨1233658952721275875039805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13159028829026942667091253 1233658952721275875039805)
                ·
                  refine ⟨462622107270478453139927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233658952721275875039805 462622107270478453139927)
                  ·
                    rfl

theorem cell21_2027145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 3].length) (baseStart_2027145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027145 prefixEnd_2027145 := by exact prefixLift 2027145
  have htrace : WordTrace (prefixWord ++ tailWord_2027145) baseStart_2027145 baseEnd_2027145 := by
    simpa [prefixWord, tailWord_2027145, baseEnd_2027145] using wordTrace_append hprefix tailTrace_2027145
  have hstable : (prefixWord ++ tailWord_2027145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027145).length < 2 ^ (prefixWord ++ tailWord_2027145).sum := by decide
  have hdescent : baseEnd_2027145 < baseStart_2027145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027159 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 6]
def baseStart_2027159 : Nat := 118140960795 + 2027159 * 2 ^ 59
def prefixEnd_2027159 : Nat := 4983230072969 + 3 ^ 40 * 2027159 * 2
def baseEnd_2027159 : Nat := 462625302261217539906565

theorem tailTrace_2027159 : CollatzResearch.WordTrace tailWord_2027159 prefixEnd_2027159 462625302261217539906565 := by
  unfold tailWord_2027159
  simp only [CollatzResearch.WordTrace]
  refine ⟨73936562862956629039028531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49291041908637752692685687 73936562862956629039028531)
  ·
    refine ⟨110904844294434943558542797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73936562862956629039028531 110904844294434943558542797)
    ·
      refine ⟨41589316610413103834453549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110904844294434943558542797 41589316610413103834453549)
      ·
        refine ⟨15595993728904913937920081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41589316610413103834453549 15595993728904913937920081)
        ·
          refine ⟨11696995296678685453440061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15595993728904913937920081 11696995296678685453440061)
          ·
            refine ⟨4386373236254507045040023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11696995296678685453440061 4386373236254507045040023)
            ·
              refine ⟨6579559854381760567560035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4386373236254507045040023 6579559854381760567560035)
              ·
                refine ⟨9869339781572640851340053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579559854381760567560035 9869339781572640851340053)
                ·
                  refine ⟨462625302261217539906565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9869339781572640851340053 462625302261217539906565)
                  ·
                    rfl

theorem cell21_2027159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 6].length) (baseStart_2027159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027159 prefixEnd_2027159 := by exact prefixLift 2027159
  have htrace : WordTrace (prefixWord ++ tailWord_2027159) baseStart_2027159 baseEnd_2027159 := by
    simpa [prefixWord, tailWord_2027159, baseEnd_2027159] using wordTrace_append hprefix tailTrace_2027159
  have hstable : (prefixWord ++ tailWord_2027159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027159).length < 2 ^ (prefixWord ++ tailWord_2027159).sum := by decide
  have hdescent : baseEnd_2027159 < baseStart_2027159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027249 : List Nat := [1, 2, 2, 2, 2, 3, 2, 7]
def baseStart_2027249 : Nat := 118140960795 + 2027249 * 2 ^ 59
def prefixEnd_2027249 : Nat := 4983230072969 + 3 ^ 40 * 2027249 * 2
def baseEnd_2027249 : Nat := 154215280495799127802127

theorem tailTrace_2027249 : CollatzResearch.WordTrace tailWord_2027249 prefixEnd_2027249 154215280495799127802127 := by
  unfold tailWord_2027249
  simp only [CollatzResearch.WordTrace]
  refine ⟨73939845432630574409804801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49293230288420382939869867 73939845432630574409804801)
  ·
    refine ⟨55454884074472930807353601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73939845432630574409804801 55454884074472930807353601)
    ·
      refine ⟨41591163055854698105515201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55454884074472930807353601 41591163055854698105515201)
      ·
        refine ⟨31193372291891023579136401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41591163055854698105515201 31193372291891023579136401)
        ·
          refine ⟨23395029218918267684352301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31193372291891023579136401 23395029218918267684352301)
          ·
            refine ⟨8773135957094350381632113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23395029218918267684352301 8773135957094350381632113)
            ·
              refine ⟨6579851967820762786224085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8773135957094350381632113 6579851967820762786224085)
              ·
                refine ⟨154215280495799127802127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6579851967820762786224085 154215280495799127802127)
                ·
                  rfl

theorem cell21_2027249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 7].length) (baseStart_2027249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027249 prefixEnd_2027249 := by exact prefixLift 2027249
  have htrace : WordTrace (prefixWord ++ tailWord_2027249) baseStart_2027249 baseEnd_2027249 := by
    simpa [prefixWord, tailWord_2027249, baseEnd_2027249] using wordTrace_append hprefix tailTrace_2027249
  have hstable : (prefixWord ++ tailWord_2027249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027249).length < 2 ^ (prefixWord ++ tailWord_2027249).sum := by decide
  have hdescent : baseEnd_2027249 < baseStart_2027249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027314 : List Nat := [3, 2, 1, 1, 3, 3, 2, 3, 3]
def baseStart_2027314 : Nat := 118140960795 + 2027314 * 2 ^ 59
def prefixEnd_2027314 : Nat := 4983230072969 + 3 ^ 40 * 2027314 * 2
def baseEnd_2027314 : Nat := 462660675372971714822915

theorem tailTrace_2027314 : CollatzResearch.WordTrace tailWord_2027314 prefixEnd_2027314 462660675372971714822915 := by
  unfold tailWord_2027314
  simp only [CollatzResearch.WordTrace]
  refine ⟨18485554044348772627730249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49294810784930060340613997 18485554044348772627730249)
  ·
    refine ⟨13864165533261579470797687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18485554044348772627730249 13864165533261579470797687)
    ·
      refine ⟨20796248299892369206196531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13864165533261579470797687 20796248299892369206196531)
      ·
        refine ⟨31194372449838553809294797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20796248299892369206196531 31194372449838553809294797)
        ·
          refine ⟨11697889668689457678485549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31194372449838553809294797 11697889668689457678485549)
          ·
            refine ⟨4386708625758546629432081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11697889668689457678485549 4386708625758546629432081)
            ·
              refine ⟨3290031469318909972074061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4386708625758546629432081 3290031469318909972074061)
              ·
                refine ⟨1233761800994591239527773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3290031469318909972074061 1233761800994591239527773)
                ·
                  refine ⟨462660675372971714822915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233761800994591239527773 462660675372971714822915)
                  ·
                    rfl

theorem cell21_2027314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_2027314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027314 prefixEnd_2027314 := by exact prefixLift 2027314
  have htrace : WordTrace (prefixWord ++ tailWord_2027314) baseStart_2027314 baseEnd_2027314 := by
    simpa [prefixWord, tailWord_2027314, baseEnd_2027314] using wordTrace_append hprefix tailTrace_2027314
  have hstable : (prefixWord ++ tailWord_2027314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027314).length < 2 ^ (prefixWord ++ tailWord_2027314).sum := by decide
  have hdescent : baseEnd_2027314 < baseStart_2027314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027390 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_2027390 : Nat := 118140960795 + 2027390 * 2 ^ 59
def prefixEnd_2027390 : Nat := 4983230072969 + 3 ^ 40 * 2027390 * 2
def baseEnd_2027390 : Nat := 462678019608412471556093

theorem tailTrace_2027390 : CollatzResearch.WordTrace tailWord_2027390 prefixEnd_2027390 462678019608412471556093 := by
  unfold tailWord_2027390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9243123515639969436335953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49296658750079836993791749 9243123515639969436335953)
  ·
    refine ⟨6932342636729977077251965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9243123515639969436335953 6932342636729977077251965)
    ·
      refine ⟨2599628488773741403969487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6932342636729977077251965 2599628488773741403969487)
      ·
        refine ⟨3899442733160612105954231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599628488773741403969487 3899442733160612105954231)
        ·
          refine ⟨5849164099740918158931347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3899442733160612105954231 5849164099740918158931347)
          ·
            refine ⟨8773746149611377238397021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849164099740918158931347 8773746149611377238397021)
            ·
              refine ⟨3290154806104266464398883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8773746149611377238397021 3290154806104266464398883)
              ·
                refine ⟨4935232209156399696598325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290154806104266464398883 4935232209156399696598325)
                ·
                  refine ⟨462678019608412471556093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4935232209156399696598325 462678019608412471556093)
                  ·
                    rfl

theorem cell21_2027390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_2027390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027390 prefixEnd_2027390 := by exact prefixLift 2027390
  have htrace : WordTrace (prefixWord ++ tailWord_2027390) baseStart_2027390 baseEnd_2027390 := by
    simpa [prefixWord, tailWord_2027390, baseEnd_2027390] using wordTrace_append hprefix tailTrace_2027390
  have hstable : (prefixWord ++ tailWord_2027390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027390).length < 2 ^ (prefixWord ++ tailWord_2027390).sum := by decide
  have hdescent : baseEnd_2027390 < baseStart_2027390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027401 : List Nat := [1, 2, 1, 1, 5, 1, 4, 6]
def baseStart_2027401 : Nat := 118140960795 + 2027401 * 2 ^ 59
def prefixEnd_2027401 : Nat := 4983230072969 + 3 ^ 40 * 2027401 * 2
def baseEnd_2027401 : Nat := 154226843319426298957579

theorem tailTrace_2027401 : CollatzResearch.WordTrace tailWord_2027401 prefixEnd_2027401 154226843319426298957579 := by
  unfold tailWord_2027401
  simp only [CollatzResearch.WordTrace]
  refine ⟨73945389328079904369338057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49296926218719936246225371 73945389328079904369338057)
  ·
    refine ⟨55459041996059928277003543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73945389328079904369338057 55459041996059928277003543)
    ·
      refine ⟨83188562994089892415505315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55459041996059928277003543 83188562994089892415505315)
      ·
        refine ⟨124782844491134838623257973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83188562994089892415505315 124782844491134838623257973)
        ·
          refine ⟨11698391671043891120930435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124782844491134838623257973 11698391671043891120930435)
          ·
            refine ⟨17547587506565836681395653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11698391671043891120930435 17547587506565836681395653)
            ·
              refine ⟨3290172657481094377761685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17547587506565836681395653 3290172657481094377761685)
              ·
                refine ⟨154226843319426298957579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3290172657481094377761685 154226843319426298957579)
                ·
                  rfl

theorem cell21_2027401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 6].length) (baseStart_2027401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027401 prefixEnd_2027401 := by exact prefixLift 2027401
  have htrace : WordTrace (prefixWord ++ tailWord_2027401) baseStart_2027401 baseEnd_2027401 := by
    simpa [prefixWord, tailWord_2027401, baseEnd_2027401] using wordTrace_append hprefix tailTrace_2027401
  have hstable : (prefixWord ++ tailWord_2027401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027401).length < 2 ^ (prefixWord ++ tailWord_2027401).sum := by decide
  have hdescent : baseEnd_2027401 < baseStart_2027401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027449 : List Nat := [1, 2, 1, 4, 2, 1, 3, 4, 3]
def baseStart_2027449 : Nat := 118140960795 + 2027449 * 2 ^ 59
def prefixEnd_2027449 : Nat := 4983230072969 + 3 ^ 40 * 2027449 * 2
def baseEnd_2027449 : Nat := 462691484212241480072639

theorem tailTrace_2027449 : CollatzResearch.WordTrace tailWord_2027449 prefixEnd_2027449 462691484212241480072639 := by
  unfold tailWord_2027449
  simp only [CollatzResearch.WordTrace]
  refine ⟨73947140031906008567085401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49298093354604005711390267 73947140031906008567085401)
  ·
    refine ⟨55460355023929506425314051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73947140031906008567085401 55460355023929506425314051)
    ·
      refine ⟨83190532535894259637971077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55460355023929506425314051 83190532535894259637971077)
      ·
        refine ⟨15598224850480173682119577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83190532535894259637971077 15598224850480173682119577)
        ·
          refine ⟨11698668637860130261589683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15598224850480173682119577 11698668637860130261589683)
          ·
            refine ⟨17548002956790195392384525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11698668637860130261589683 17548002956790195392384525)
            ·
              refine ⟨6580501108796323272144197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17548002956790195392384525 6580501108796323272144197)
              ·
                refine ⟨1233843957899310613527037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6580501108796323272144197 1233843957899310613527037)
                ·
                  refine ⟨462691484212241480072639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233843957899310613527037 462691484212241480072639)
                  ·
                    rfl

theorem cell21_2027449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 3].length) (baseStart_2027449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027449 prefixEnd_2027449 := by exact prefixLift 2027449
  have htrace : WordTrace (prefixWord ++ tailWord_2027449) baseStart_2027449 baseEnd_2027449 := by
    simpa [prefixWord, tailWord_2027449, baseEnd_2027449] using wordTrace_append hprefix tailTrace_2027449
  have hstable : (prefixWord ++ tailWord_2027449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027449).length < 2 ^ (prefixWord ++ tailWord_2027449).sum := by decide
  have hdescent : baseEnd_2027449 < baseStart_2027449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027452 : List Nat := [2, 2, 2, 5, 2, 1, 1, 6]
def baseStart_2027452 : Nat := 118140960795 + 2027452 * 2 ^ 59
def prefixEnd_2027452 : Nat := 4983230072969 + 3 ^ 40 * 2027452 * 2
def baseEnd_2027452 : Nat := 154230722951038047174211

theorem tailTrace_2027452 : CollatzResearch.WordTrace tailWord_2027452 prefixEnd_2027452 154230722951038047174211 := by
  unfold tailWord_2027452
  simp only [CollatzResearch.WordTrace]
  refine ⟨36973624725447570039722305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49298166300596760052963073 36973624725447570039722305)
  ·
    refine ⟨27730218544085677529791729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36973624725447570039722305 27730218544085677529791729)
    ·
      refine ⟨20797663908064258147343797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27730218544085677529791729 20797663908064258147343797)
      ·
        refine ⟨1949780991381024201313481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20797663908064258147343797 1949780991381024201313481)
        ·
          refine ⟨1462335743535768150985111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1949780991381024201313481 1462335743535768150985111)
          ·
            refine ⟨2193503615303652226477667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462335743535768150985111 2193503615303652226477667)
            ·
              refine ⟨3290255422955478339716501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193503615303652226477667 3290255422955478339716501)
              ·
                refine ⟨154230722951038047174211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3290255422955478339716501 154230722951038047174211)
                ·
                  rfl

theorem cell21_2027452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 6].length) (baseStart_2027452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027452 prefixEnd_2027452 := by exact prefixLift 2027452
  have htrace : WordTrace (prefixWord ++ tailWord_2027452) baseStart_2027452 baseEnd_2027452 := by
    simpa [prefixWord, tailWord_2027452, baseEnd_2027452] using wordTrace_append hprefix tailTrace_2027452
  have hstable : (prefixWord ++ tailWord_2027452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027452).length < 2 ^ (prefixWord ++ tailWord_2027452).sum := by decide
  have hdescent : baseEnd_2027452 < baseStart_2027452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027536 : List Nat := [2, 1, 1, 1, 1, 1, 1, 13]
def baseStart_2027536 : Nat := 118140960795 + 2027536 * 2 ^ 59
def prefixEnd_2027536 : Nat := 4983230072969 + 3 ^ 40 * 2027536 * 2
def baseEnd_2027536 : Nat := 154237112932516220707487

theorem tailTrace_2027536 : CollatzResearch.WordTrace tailWord_2027536 prefixEnd_2027536 154237112932516220707487 := by
  unfold tailWord_2027536
  simp only [CollatzResearch.WordTrace]
  refine ⟨36975156591295411212751231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49300208788393881617001641 36975156591295411212751231)
  ·
    refine ⟨55462734886943116819126847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36975156591295411212751231 55462734886943116819126847)
    ·
      refine ⟨83194102330414675228690271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55462734886943116819126847 83194102330414675228690271)
      ·
        refine ⟨124791153495622012843035407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83194102330414675228690271 124791153495622012843035407)
        ·
          refine ⟨187186730243433019264553111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124791153495622012843035407 187186730243433019264553111)
          ·
            refine ⟨280780095365149528896829667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187186730243433019264553111 280780095365149528896829667)
            ·
              refine ⟨421170143047724293345244501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280780095365149528896829667 421170143047724293345244501)
              ·
                refine ⟨154237112932516220707487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 421170143047724293345244501 154237112932516220707487)
                ·
                  rfl

theorem cell21_2027536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_2027536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027536 prefixEnd_2027536 := by exact prefixLift 2027536
  have htrace : WordTrace (prefixWord ++ tailWord_2027536) baseStart_2027536 baseEnd_2027536 := by
    simpa [prefixWord, tailWord_2027536, baseEnd_2027536] using wordTrace_append hprefix tailTrace_2027536
  have hstable : (prefixWord ++ tailWord_2027536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027536).length < 2 ^ (prefixWord ++ tailWord_2027536).sum := by decide
  have hdescent : baseEnd_2027536 < baseStart_2027536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027559 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 5]
def baseStart_2027559 : Nat := 118140960795 + 2027559 * 2 ^ 59
def prefixEnd_2027559 : Nat := 4983230072969 + 3 ^ 40 * 2027559 * 2
def baseEnd_2027559 : Nat := 462716587710905733239081

theorem tailTrace_2027559 : CollatzResearch.WordTrace tailWord_2027559 prefixEnd_2027559 462716587710905733239081 := by
  unfold tailWord_2027559
  simp only [CollatzResearch.WordTrace]
  refine ⟨73951152061507497353589731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49300768041004998235726487 73951152061507497353589731)
  ·
    refine ⟨110926728092261246030384597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73951152061507497353589731 110926728092261246030384597)
    ·
      refine ⟨2599845189662372953837139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 110926728092261246030384597 2599845189662372953837139)
      ·
        refine ⟨3899767784493559430755709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599845189662372953837139 3899767784493559430755709)
        ·
          refine ⟨1462412919185084786533391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3899767784493559430755709 1462412919185084786533391)
          ·
            refine ⟨2193619378777627179800087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462412919185084786533391 2193619378777627179800087)
            ·
              refine ⟨3290429068166440769700131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193619378777627179800087 3290429068166440769700131)
              ·
                refine ⟨4935643602249661154550197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290429068166440769700131 4935643602249661154550197)
                ·
                  refine ⟨462716587710905733239081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4935643602249661154550197 462716587710905733239081)
                  ·
                    rfl

theorem cell21_2027559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 5].length) (baseStart_2027559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027559 prefixEnd_2027559 := by exact prefixLift 2027559
  have htrace : WordTrace (prefixWord ++ tailWord_2027559) baseStart_2027559 baseEnd_2027559 := by
    simpa [prefixWord, tailWord_2027559, baseEnd_2027559] using wordTrace_append hprefix tailTrace_2027559
  have hstable : (prefixWord ++ tailWord_2027559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027559).length < 2 ^ (prefixWord ++ tailWord_2027559).sum := by decide
  have hdescent : baseEnd_2027559 < baseStart_2027559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027567 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 5]
def baseStart_2027567 : Nat := 118140960795 + 2027567 * 2 ^ 59
def prefixEnd_2027567 : Nat := 4983230072969 + 3 ^ 40 * 2027567 * 2
def baseEnd_2027567 : Nat := 462718413419899497105731

theorem tailTrace_2027567 : CollatzResearch.WordTrace tailWord_2027567 prefixEnd_2027567 462718413419899497105731 := by
  unfold tailWord_2027567
  simp only [CollatzResearch.WordTrace]
  refine ⟨73951443845478514719880955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49300962563652343146587303 73951443845478514719880955)
  ·
    refine ⟨110927165768217772079821433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73951443845478514719880955 110927165768217772079821433)
    ·
      refine ⟨83195374326163329059866075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110927165768217772079821433 83195374326163329059866075)
      ·
        refine ⟨124793061489244993589799113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83195374326163329059866075 124793061489244993589799113)
        ·
          refine ⟨93594796116933745192349335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124793061489244993589799113 93594796116933745192349335)
          ·
            refine ⟨140392194175400617788524003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93594796116933745192349335 140392194175400617788524003)
            ·
              refine ⟨210588291263100926682786005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140392194175400617788524003 210588291263100926682786005)
              ·
                refine ⟨4935663076478927969127797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 210588291263100926682786005 4935663076478927969127797)
                ·
                  refine ⟨462718413419899497105731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4935663076478927969127797 462718413419899497105731)
                  ·
                    rfl

theorem cell21_2027567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_2027567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027567 prefixEnd_2027567 := by exact prefixLift 2027567
  have htrace : WordTrace (prefixWord ++ tailWord_2027567) baseStart_2027567 baseEnd_2027567 := by
    simpa [prefixWord, tailWord_2027567, baseEnd_2027567] using wordTrace_append hprefix tailTrace_2027567
  have hstable : (prefixWord ++ tailWord_2027567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027567).length < 2 ^ (prefixWord ++ tailWord_2027567).sum := by decide
  have hdescent : baseEnd_2027567 < baseStart_2027567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027677 : List Nat := [1, 4, 2, 1, 1, 3, 2, 4, 3]
def baseStart_2027677 : Nat := 118140960795 + 2027677 * 2 ^ 59
def prefixEnd_2027677 : Nat := 4983230072969 + 3 ^ 40 * 2027677 * 2
def baseEnd_2027677 : Nat := 462743516918563750272173

theorem tailTrace_2027677 : CollatzResearch.WordTrace tailWord_2027677 prefixEnd_2027677 462743516918563750272173 := by
  unfold tailWord_2027677
  simp only [CollatzResearch.WordTrace]
  refine ⟨73955455875080003506385285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49303637250053335670923523 73955455875080003506385285)
  ·
    refine ⟨13866647976577500657447241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73955455875080003506385285 13866647976577500657447241)
    ·
      refine ⟨10399985982433125493085431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13866647976577500657447241 10399985982433125493085431)
      ·
        refine ⟨15599978973649688239628147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10399985982433125493085431 15599978973649688239628147)
        ·
          refine ⟨23399968460474532359442221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15599978973649688239628147 23399968460474532359442221)
          ·
            refine ⟨8774988172677949634790833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23399968460474532359442221 8774988172677949634790833)
            ·
              refine ⟨6581241129508462226093125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8774988172677949634790833 6581241129508462226093125)
              ·
                refine ⟨1233982711782836667392461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6581241129508462226093125 1233982711782836667392461)
                ·
                  refine ⟨462743516918563750272173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233982711782836667392461 462743516918563750272173)
                  ·
                    rfl

theorem cell21_2027677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_2027677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027677 prefixEnd_2027677 := by exact prefixLift 2027677
  have htrace : WordTrace (prefixWord ++ tailWord_2027677) baseStart_2027677 baseEnd_2027677 := by
    simpa [prefixWord, tailWord_2027677, baseEnd_2027677] using wordTrace_append hprefix tailTrace_2027677
  have hstable : (prefixWord ++ tailWord_2027677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027677).length < 2 ^ (prefixWord ++ tailWord_2027677).sum := by decide
  have hdescent : baseEnd_2027677 < baseStart_2027677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027736 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 5]
def baseStart_2027736 : Nat := 118140960795 + 2027736 * 2 ^ 59
def prefixEnd_2027736 : Nat := 4983230072969 + 3 ^ 40 * 2027736 * 2
def baseEnd_2027736 : Nat := 462756981522392758788719

theorem tailTrace_2027736 : CollatzResearch.WordTrace tailWord_2027736 prefixEnd_2027736 462756981522392758788719 := by
  unfold tailWord_2027736
  simp only [CollatzResearch.WordTrace]
  refine ⟨36978803890933128291391531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49305071854577504388522041 36978803890933128291391531)
  ·
    refine ⟨55468205836399692437087297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36978803890933128291391531 55468205836399692437087297)
    ·
      refine ⟨41601154377299769327815473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55468205836399692437087297 41601154377299769327815473)
      ·
        refine ⟨31200865782974826995861605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41601154377299769327815473 31200865782974826995861605)
        ·
          refine ⟨5850162334307780061724051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31200865782974826995861605 5850162334307780061724051)
          ·
            refine ⟨8775243501461670092586077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850162334307780061724051 8775243501461670092586077)
            ·
              refine ⟨3290716313048126284719779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8775243501461670092586077 3290716313048126284719779)
              ·
                refine ⟨4936074469572189427079669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290716313048126284719779 4936074469572189427079669)
                ·
                  refine ⟨462756981522392758788719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4936074469572189427079669 462756981522392758788719)
                  ·
                    rfl

theorem cell21_2027736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_2027736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027736 prefixEnd_2027736 := by exact prefixLift 2027736
  have htrace : WordTrace (prefixWord ++ tailWord_2027736) baseStart_2027736 baseEnd_2027736 := by
    simpa [prefixWord, tailWord_2027736, baseEnd_2027736] using wordTrace_append hprefix tailTrace_2027736
  have hstable : (prefixWord ++ tailWord_2027736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027736).length < 2 ^ (prefixWord ++ tailWord_2027736).sum := by decide
  have hdescent : baseEnd_2027736 < baseStart_2027736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027812 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 5]
def baseStart_2027812 : Nat := 118140960795 + 2027812 * 2 ^ 59
def prefixEnd_2027812 : Nat := 4983230072969 + 3 ^ 40 * 2027812 * 2
def baseEnd_2027812 : Nat := 462774325757833515521897

theorem tailTrace_2027812 : CollatzResearch.WordTrace tailWord_2027812 prefixEnd_2027812 462774325757833515521897 := by
  unfold tailWord_2027812
  simp only [CollatzResearch.WordTrace]
  refine ⟨36980189864795460781274845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49306919819727281041699793 36980189864795460781274845)
  ·
    refine ⟨13867571199298297792978067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36980189864795460781274845 13867571199298297792978067)
    ·
      refine ⟨20801356798947446689467101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13867571199298297792978067 20801356798947446689467101)
      ·
        refine ⟨7800508799605292508550163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20801356798947446689467101 7800508799605292508550163)
        ·
          refine ⟨11700763199407938762825245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7800508799605292508550163 11700763199407938762825245)
          ·
            refine ⟨4387786199777977036059467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11700763199407938762825245 4387786199777977036059467)
            ·
              refine ⟨6581679299666965554089201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4387786199777977036059467 6581679299666965554089201)
              ·
                refine ⟨4936259474750224165566901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6581679299666965554089201 4936259474750224165566901)
                ·
                  refine ⟨462774325757833515521897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4936259474750224165566901 462774325757833515521897)
                  ·
                    rfl

theorem cell21_2027812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_2027812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027812 prefixEnd_2027812 := by exact prefixLift 2027812
  have htrace : WordTrace (prefixWord ++ tailWord_2027812) baseStart_2027812 baseEnd_2027812 := by
    simpa [prefixWord, tailWord_2027812, baseEnd_2027812] using wordTrace_append hprefix tailTrace_2027812
  have hstable : (prefixWord ++ tailWord_2027812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027812).length < 2 ^ (prefixWord ++ tailWord_2027812).sum := by decide
  have hdescent : baseEnd_2027812 < baseStart_2027812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027829 : List Nat := [1, 3, 3, 1, 2, 1, 4, 3, 3]
def baseStart_2027829 : Nat := 118140960795 + 2027829 * 2 ^ 59
def prefixEnd_2027829 : Nat := 4983230072969 + 3 ^ 40 * 2027829 * 2
def baseEnd_2027829 : Nat := 462778205389445263738529

theorem tailTrace_2027829 : CollatzResearch.WordTrace tailWord_2027829 prefixEnd_2027829 462778205389445263738529 := by
  unfold tailWord_2027829
  simp only [CollatzResearch.WordTrace]
  refine ⟨73960999770529333465918541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49307333180352888977279027 73960999770529333465918541)
  ·
    refine ⟨27735374913948500049719453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73960999770529333465918541 27735374913948500049719453)
    ·
      refine ⟨10400765592730687518644795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27735374913948500049719453 10400765592730687518644795)
      ·
        refine ⟨15601148389096031277967193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10400765592730687518644795 15601148389096031277967193)
        ·
          refine ⟨11700861291822023458475395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15601148389096031277967193 11700861291822023458475395)
          ·
            refine ⟨17551291937733035187713093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11700861291822023458475395 17551291937733035187713093)
            ·
              refine ⟨3290867238324944097696205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17551291937733035187713093 3290867238324944097696205)
              ·
                refine ⟨1234075214371854036636077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3290867238324944097696205 1234075214371854036636077)
                ·
                  refine ⟨462778205389445263738529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234075214371854036636077 462778205389445263738529)
                  ·
                    rfl

theorem cell21_2027829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_2027829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027829 prefixEnd_2027829 := by exact prefixLift 2027829
  have htrace : WordTrace (prefixWord ++ tailWord_2027829) baseStart_2027829 baseEnd_2027829 := by
    simpa [prefixWord, tailWord_2027829, baseEnd_2027829] using wordTrace_append hprefix tailTrace_2027829
  have hstable : (prefixWord ++ tailWord_2027829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027829).length < 2 ^ (prefixWord ++ tailWord_2027829).sum := by decide
  have hdescent : baseEnd_2027829 < baseStart_2027829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027860 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 4]
def baseStart_2027860 : Nat := 118140960795 + 2027860 * 2 ^ 59
def prefixEnd_2027860 : Nat := 4983230072969 + 3 ^ 40 * 2027860 * 2
def baseEnd_2027860 : Nat := 462785280011796098721799

theorem tailTrace_2027860 : CollatzResearch.WordTrace tailWord_2027860 prefixEnd_2027860 462785280011796098721799 := by
  unfold tailWord_2027860
  simp only [CollatzResearch.WordTrace]
  refine ⟨36981065216708512880148517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49308086955611350506864689 36981065216708512880148517)
  ·
    refine ⟨6933949728132846165027847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36981065216708512880148517 6933949728132846165027847)
    ·
      refine ⟨10400924592199269247541771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6933949728132846165027847 10400924592199269247541771)
      ·
        refine ⟨15601386888298903871312657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10400924592199269247541771 15601386888298903871312657)
        ·
          refine ⟨11701040166224177903484493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15601386888298903871312657 11701040166224177903484493)
          ·
            refine ⟨4387890062334066713806685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11701040166224177903484493 4387890062334066713806685)
            ·
              refine ⟨1645458773375275017677507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4387890062334066713806685 1645458773375275017677507)
              ·
                refine ⟨2468188160062912526516261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645458773375275017677507 2468188160062912526516261)
                ·
                  refine ⟨462785280011796098721799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2468188160062912526516261 462785280011796098721799)
                  ·
                    rfl

theorem cell21_2027860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_2027860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027860 prefixEnd_2027860 := by exact prefixLift 2027860
  have htrace : WordTrace (prefixWord ++ tailWord_2027860) baseStart_2027860 baseEnd_2027860 := by
    simpa [prefixWord, tailWord_2027860, baseEnd_2027860] using wordTrace_append hprefix tailTrace_2027860
  have hstable : (prefixWord ++ tailWord_2027860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027860).length < 2 ^ (prefixWord ++ tailWord_2027860).sum := by decide
  have hdescent : baseEnd_2027860 < baseStart_2027860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027871 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 5]
def baseStart_2027871 : Nat := 118140960795 + 2027871 * 2 ^ 59
def prefixEnd_2027871 : Nat := 4983230072969 + 3 ^ 40 * 2027871 * 2
def baseEnd_2027871 : Nat := 462787790361662524038443

theorem tailTrace_2027871 : CollatzResearch.WordTrace tailWord_2027871 prefixEnd_2027871 462787790361662524038443 := by
  unfold tailWord_2027871
  simp only [CollatzResearch.WordTrace]
  refine ⟨73962531636377174638947467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49308354424251449759298311 73962531636377174638947467)
  ·
    refine ⟨110943797454565761958421201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73962531636377174638947467 110943797454565761958421201)
    ·
      refine ⟨83207848090924321468815901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110943797454565761958421201 83207848090924321468815901)
      ·
        refine ⟨31202943034096620550805963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83207848090924321468815901 31202943034096620550805963)
        ·
          refine ⟨46804414551144930826208945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31202943034096620550805963 46804414551144930826208945)
          ·
            refine ⟨35103310913358698119656709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46804414551144930826208945 35103310913358698119656709)
            ·
              refine ⟨6581870796254755897435633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35103310913358698119656709 6581870796254755897435633)
              ·
                refine ⟨4936403097191066923076725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6581870796254755897435633 4936403097191066923076725)
                ·
                  refine ⟨462787790361662524038443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4936403097191066923076725 462787790361662524038443)
                  ·
                    rfl

theorem cell21_2027871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_2027871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027871 prefixEnd_2027871 := by exact prefixLift 2027871
  have htrace : WordTrace (prefixWord ++ tailWord_2027871) baseStart_2027871 baseEnd_2027871 := by
    simpa [prefixWord, tailWord_2027871, baseEnd_2027871] using wordTrace_append hprefix tailTrace_2027871
  have hstable : (prefixWord ++ tailWord_2027871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027871).length < 2 ^ (prefixWord ++ tailWord_2027871).sum := by decide
  have hdescent : baseEnd_2027871 < baseStart_2027871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027874 : List Nat := [3, 3, 2, 1, 1, 2, 4, 5]
def baseStart_2027874 : Nat := 118140960795 + 2027874 * 2 ^ 59
def prefixEnd_2027874 : Nat := 4983230072969 + 3 ^ 40 * 2027874 * 2
def baseEnd_2027874 : Nat := 154262825000845061829479

theorem tailTrace_2027874 : CollatzResearch.WordTrace tailWord_2027874 prefixEnd_2027874 154262825000845061829479 := by
  unfold tailWord_2027874
  simp only [CollatzResearch.WordTrace]
  refine ⟨18490660263841576537826669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49308427370244204100871117 18490660263841576537826669)
  ·
    refine ⟨6933997598940591201685001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18490660263841576537826669 6933997598940591201685001)
    ·
      refine ⟨5200498199205443401263751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6933997598940591201685001 5200498199205443401263751)
      ·
        refine ⟨7800747298808165101895627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5200498199205443401263751 7800747298808165101895627)
        ·
          refine ⟨11701120948212247652843441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7800747298808165101895627 11701120948212247652843441)
          ·
            refine ⟨8775840711159185739632581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11701120948212247652843441 8775840711159185739632581)
            ·
              refine ⟨1645470133342347326181109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8775840711159185739632581 1645470133342347326181109)
              ·
                refine ⟨154262825000845061829479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1645470133342347326181109 154262825000845061829479)
                ·
                  rfl

theorem cell21_2027874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_2027874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027874 prefixEnd_2027874 := by exact prefixLift 2027874
  have htrace : WordTrace (prefixWord ++ tailWord_2027874) baseStart_2027874 baseEnd_2027874 := by
    simpa [prefixWord, tailWord_2027874, baseEnd_2027874] using wordTrace_append hprefix tailTrace_2027874
  have hstable : (prefixWord ++ tailWord_2027874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027874).length < 2 ^ (prefixWord ++ tailWord_2027874).sum := by decide
  have hdescent : baseEnd_2027874 < baseStart_2027874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027905 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 5]
def baseStart_2027905 : Nat := 118140960795 + 2027905 * 2 ^ 59
def prefixEnd_2027905 : Nat := 4983230072969 + 3 ^ 40 * 2027905 * 2
def baseEnd_2027905 : Nat := 462795549624886020471707

theorem tailTrace_2027905 : CollatzResearch.WordTrace tailWord_2027905 prefixEnd_2027905 462795549624886020471707 := by
  unfold tailWord_2027905
  simp only [CollatzResearch.WordTrace]
  refine ⟨73963771718253998445685169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49309181145502665630456779 73963771718253998445685169)
  ·
    refine ⟨55472828788690498834263877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73963771718253998445685169 55472828788690498834263877)
    ·
      refine ⟨10401155397879468531424477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55472828788690498834263877 10401155397879468531424477)
      ·
        refine ⟨3900433274204800699284179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10401155397879468531424477 3900433274204800699284179)
        ·
          refine ⟨5850649911307201048926269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900433274204800699284179 5850649911307201048926269)
          ·
            refine ⟨2193993716740200393347351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5850649911307201048926269 2193993716740200393347351)
            ·
              refine ⟨3290990575110300590021027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193993716740200393347351 3290990575110300590021027)
              ·
                refine ⟨4936485862665450885031541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290990575110300590021027 4936485862665450885031541)
                ·
                  refine ⟨462795549624886020471707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4936485862665450885031541 462795549624886020471707)
                  ·
                    rfl

theorem cell21_2027905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_2027905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027905 prefixEnd_2027905 := by exact prefixLift 2027905
  have htrace : WordTrace (prefixWord ++ tailWord_2027905) baseStart_2027905 baseEnd_2027905 := by
    simpa [prefixWord, tailWord_2027905, baseEnd_2027905] using wordTrace_append hprefix tailTrace_2027905
  have hstable : (prefixWord ++ tailWord_2027905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027905).length < 2 ^ (prefixWord ++ tailWord_2027905).sum := by decide
  have hdescent : baseEnd_2027905 < baseStart_2027905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027916 : List Nat := [2, 2, 1, 2, 1, 4, 1, 8]
def baseStart_2027916 : Nat := 118140960795 + 2027916 * 2 ^ 59
def prefixEnd_2027916 : Nat := 4983230072969 + 3 ^ 40 * 2027916 * 2
def baseEnd_2027916 : Nat := 154266019991584148596117

theorem tailTrace_2027916 : CollatzResearch.WordTrace tailWord_2027916 prefixEnd_2027916 154266019991584148596117 := by
  unfold tailWord_2027916
  simp only [CollatzResearch.WordTrace]
  refine ⟨36982086460607073662167801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49309448614142764882890401 36982086460607073662167801)
  ·
    refine ⟨27736564845455305246625851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36982086460607073662167801 27736564845455305246625851)
    ·
      refine ⟨41604847268182957869938777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27736564845455305246625851 41604847268182957869938777)
      ·
        refine ⟨31203635451137218402454083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41604847268182957869938777 31203635451137218402454083)
        ·
          refine ⟨46805453176705827603681125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31203635451137218402454083 46805453176705827603681125)
          ·
            refine ⟨8776022470632342675690211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46805453176705827603681125 8776022470632342675690211)
            ·
              refine ⟨13164033705948514013535317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8776022470632342675690211 13164033705948514013535317)
              ·
                refine ⟨154266019991584148596117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13164033705948514013535317 154266019991584148596117)
                ·
                  rfl

theorem cell21_2027916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_2027916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027916 prefixEnd_2027916 := by exact prefixLift 2027916
  have htrace : WordTrace (prefixWord ++ tailWord_2027916) baseStart_2027916 baseEnd_2027916 := by
    simpa [prefixWord, tailWord_2027916, baseEnd_2027916] using wordTrace_append hprefix tailTrace_2027916
  have hstable : (prefixWord ++ tailWord_2027916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027916).length < 2 ^ (prefixWord ++ tailWord_2027916).sum := by decide
  have hdescent : baseEnd_2027916 < baseStart_2027916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027978 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_2027978 : Nat := 118140960795 + 2027978 * 2 ^ 59
def prefixEnd_2027978 : Nat := 4983230072969 + 3 ^ 40 * 2027978 * 2
def baseEnd_2027978 : Nat := 462812209219454115754891

theorem tailTrace_2027978 : CollatzResearch.WordTrace tailWord_2027978 prefixEnd_2027978 462812209219454115754891 := by
  unfold tailWord_2027978
  simp only [CollatzResearch.WordTrace]
  refine ⟨18491608561747382978273147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49310956164659687942061725 18491608561747382978273147)
  ·
    refine ⟨27737412842621074467409721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18491608561747382978273147 27737412842621074467409721)
    ·
      refine ⟨20803059631965805850557291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27737412842621074467409721 20803059631965805850557291)
      ·
        refine ⟨31204589447948708775835937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20803059631965805850557291 31204589447948708775835937)
        ·
          refine ⟨23403442085961531581876953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31204589447948708775835937 23403442085961531581876953)
          ·
            refine ⟨17552581564471148686407715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23403442085961531581876953 17552581564471148686407715)
            ·
              refine ⟨26328872346706723029611573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17552581564471148686407715 26328872346706723029611573)
              ·
                refine ⟨2468331782503755284026085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26328872346706723029611573 2468331782503755284026085)
                ·
                  refine ⟨462812209219454115754891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2468331782503755284026085 462812209219454115754891)
                  ·
                    rfl

theorem cell21_2027978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_2027978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2027978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2027978 prefixEnd_2027978 := by exact prefixLift 2027978
  have htrace : WordTrace (prefixWord ++ tailWord_2027978) baseStart_2027978 baseEnd_2027978 := by
    simpa [prefixWord, tailWord_2027978, baseEnd_2027978] using wordTrace_append hprefix tailTrace_2027978
  have hstable : (prefixWord ++ tailWord_2027978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027978).length < 2 ^ (prefixWord ++ tailWord_2027978).sum := by decide
  have hdescent : baseEnd_2027978 < baseStart_2027978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028074 : List Nat := [3, 1, 4, 1, 1, 3, 3, 2, 3]
def baseStart_2028074 : Nat := 118140960795 + 2028074 * 2 ^ 59
def prefixEnd_2028074 : Nat := 4983230072969 + 3 ^ 40 * 2028074 * 2
def baseEnd_2028074 : Nat := 462834117727379282154695

theorem tailTrace_2028074 : CollatzResearch.WordTrace tailWord_2028074 prefixEnd_2028074 462834117727379282154695 := by
  unfold tailWord_2028074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18492483913660435077146819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49313290436427826872391517 18492483913660435077146819)
  ·
    refine ⟨27738725870490652615720229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18492483913660435077146819 27738725870490652615720229)
    ·
      refine ⟨5201011100716997365447543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27738725870490652615720229 5201011100716997365447543)
      ·
        refine ⟨7801516651075496048171315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5201011100716997365447543 7801516651075496048171315)
        ·
          refine ⟨11702274976613244072256973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801516651075496048171315 11702274976613244072256973)
          ·
            refine ⟨4388353116229966527096365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11702274976613244072256973 4388353116229966527096365)
            ·
              refine ⟨1645632418586237447661137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4388353116229966527096365 1645632418586237447661137)
              ·
                refine ⟨1234224313939678085745853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1645632418586237447661137 1234224313939678085745853)
                ·
                  refine ⟨462834117727379282154695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234224313939678085745853 462834117727379282154695)
                  ·
                    rfl

theorem cell21_2028074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_2028074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028074 prefixEnd_2028074 := by exact prefixLift 2028074
  have htrace : WordTrace (prefixWord ++ tailWord_2028074) baseStart_2028074 baseEnd_2028074 := by
    simpa [prefixWord, tailWord_2028074, baseEnd_2028074] using wordTrace_append hprefix tailTrace_2028074
  have hstable : (prefixWord ++ tailWord_2028074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028074).length < 2 ^ (prefixWord ++ tailWord_2028074).sum := by decide
  have hdescent : baseEnd_2028074 < baseStart_2028074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028102 : List Nat := [6, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2028102 : Nat := 118140960795 + 2028102 * 2 ^ 59
def prefixEnd_2028102 : Nat := 4983230072969 + 3 ^ 40 * 2028102 * 2
def baseEnd_2028102 : Nat := 154280169236285818562657

theorem tailTrace_2028102 : CollatzResearch.WordTrace tailWord_2028102 prefixEnd_2028102 154280169236285818562657 := by
  unfold tailWord_2028102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311592403079384409081455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49313971265693534060404373 2311592403079384409081455)
  ·
    refine ⟨3467388604619076613622183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2311592403079384409081455 3467388604619076613622183)
    ·
      refine ⟨5201082906928614920433275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3467388604619076613622183 5201082906928614920433275)
      ·
        refine ⟨7801624360392922380649913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5201082906928614920433275 7801624360392922380649913)
        ·
          refine ⟨5851218270294691785487435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7801624360392922380649913 5851218270294691785487435)
          ·
            refine ⟨8776827405442037678231153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5851218270294691785487435 8776827405442037678231153)
            ·
              refine ⟨6582620554081528258673365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8776827405442037678231153 6582620554081528258673365)
              ·
                refine ⟨154280169236285818562657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6582620554081528258673365 154280169236285818562657)
                ·
                  rfl

theorem cell21_2028102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2028102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028102 prefixEnd_2028102 := by exact prefixLift 2028102
  have htrace : WordTrace (prefixWord ++ tailWord_2028102) baseStart_2028102 baseEnd_2028102 := by
    simpa [prefixWord, tailWord_2028102, baseEnd_2028102] using wordTrace_append hprefix tailTrace_2028102
  have hstable : (prefixWord ++ tailWord_2028102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028102).length < 2 ^ (prefixWord ++ tailWord_2028102).sum := by decide
  have hdescent : baseEnd_2028102 < baseStart_2028102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028133 : List Nat := [1, 3, 1, 3, 4, 1, 1, 4, 3]
def baseStart_2028133 : Nat := 118140960795 + 2028133 * 2 ^ 59
def prefixEnd_2028133 : Nat := 4983230072969 + 3 ^ 40 * 2028133 * 2
def baseEnd_2028133 : Nat := 462847582331208290671241

theorem tailTrace_2028133 : CollatzResearch.WordTrace tailWord_2028133 prefixEnd_2028133 462847582331208290671241 := by
  unfold tailWord_2028133
  simp only [CollatzResearch.WordTrace]
  refine ⟨73972087561427993384985053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49314725040951995589990035 73972087561427993384985053)
  ·
    refine ⟨27739532835535497519369395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73972087561427993384985053 27739532835535497519369395)
    ·
      refine ⟨41609299253303246279054093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27739532835535497519369395 41609299253303246279054093)
      ·
        refine ⟨15603487219988717354645285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41609299253303246279054093 15603487219988717354645285)
        ·
          refine ⟨2925653853747884503995991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15603487219988717354645285 2925653853747884503995991)
          ·
            refine ⟨4388480780621826755993987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925653853747884503995991 4388480780621826755993987)
            ·
              refine ⟨6582721170932740133990981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388480780621826755993987 6582721170932740133990981)
              ·
                refine ⟨1234260219549888775123309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6582721170932740133990981 1234260219549888775123309)
                ·
                  refine ⟨462847582331208290671241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234260219549888775123309 462847582331208290671241)
                  ·
                    rfl

theorem cell21_2028133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_2028133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028133 prefixEnd_2028133 := by exact prefixLift 2028133
  have htrace : WordTrace (prefixWord ++ tailWord_2028133) baseStart_2028133 baseEnd_2028133 := by
    simpa [prefixWord, tailWord_2028133, baseEnd_2028133] using wordTrace_append hprefix tailTrace_2028133
  have hstable : (prefixWord ++ tailWord_2028133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028133).length < 2 ^ (prefixWord ++ tailWord_2028133).sum := by decide
  have hdescent : baseEnd_2028133 < baseStart_2028133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028161 : List Nat := [1, 2, 4, 2, 1, 1, 5, 5]
def baseStart_2028161 : Nat := 118140960795 + 2028161 * 2 ^ 59
def prefixEnd_2028161 : Nat := 4983230072969 + 3 ^ 40 * 2028161 * 2
def baseEnd_2028161 : Nat := 154284657437562154734839

theorem tailTrace_2028161 : CollatzResearch.WordTrace tailWord_2028161 prefixEnd_2028161 154284657437562154734839 := by
  unfold tailWord_2028161
  simp only [CollatzResearch.WordTrace]
  refine ⟨73973108805326554167004337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49315405870217702778002891 73973108805326554167004337)
  ·
    refine ⟨55479831603994915625253253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73973108805326554167004337 55479831603994915625253253)
    ·
      refine ⟨10402468425749046679734985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55479831603994915625253253 10402468425749046679734985)
      ·
        refine ⟨7801851319311785009801239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10402468425749046679734985 7801851319311785009801239)
        ·
          refine ⟨11702776978967677514701859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801851319311785009801239 11702776978967677514701859)
          ·
            refine ⟨17554165468451516272052789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11702776978967677514701859 17554165468451516272052789)
            ·
              refine ⟨1645703012667329650504949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17554165468451516272052789 1645703012667329650504949)
              ·
                refine ⟨154284657437562154734839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1645703012667329650504949 154284657437562154734839)
                ·
                  rfl

theorem cell21_2028161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 5].length) (baseStart_2028161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028161 prefixEnd_2028161 := by exact prefixLift 2028161
  have htrace : WordTrace (prefixWord ++ tailWord_2028161) baseStart_2028161 baseEnd_2028161 := by
    simpa [prefixWord, tailWord_2028161, baseEnd_2028161] using wordTrace_append hprefix tailTrace_2028161
  have hstable : (prefixWord ++ tailWord_2028161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028161).length < 2 ^ (prefixWord ++ tailWord_2028161).sum := by decide
  have hdescent : baseEnd_2028161 < baseStart_2028161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028192 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 5]
def baseStart_2028192 : Nat := 118140960795 + 2028192 * 2 ^ 59
def prefixEnd_2028192 : Nat := 4983230072969 + 3 ^ 40 * 2028192 * 2
def baseEnd_2028192 : Nat := 462861046935037299187787

theorem tailTrace_2028192 : CollatzResearch.WordTrace tailWord_2028192 prefixEnd_2028192 462861046935037299187787 := by
  unfold tailWord_2028192
  simp only [CollatzResearch.WordTrace]
  refine ⟨36987119734107123230691415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49316159645476164307588553 36987119734107123230691415)
  ·
    refine ⟨55480679601160684846037123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36987119734107123230691415 55480679601160684846037123)
    ·
      refine ⟨83221019401741027269055685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55480679601160684846037123 83221019401741027269055685)
      ·
        refine ⟨15603941137826442612947941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83221019401741027269055685 15603941137826442612947941)
        ·
          refine ⟨2925738963342457989927739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15603941137826442612947941 2925738963342457989927739)
          ·
            refine ⟨4388608445013686984891609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925738963342457989927739 4388608445013686984891609)
            ·
              refine ⟨3291456333760265238668707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4388608445013686984891609 3291456333760265238668707)
              ·
                refine ⟨4937184500640397858003061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291456333760265238668707 4937184500640397858003061)
                ·
                  refine ⟨462861046935037299187787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4937184500640397858003061 462861046935037299187787)
                  ·
                    rfl

theorem cell21_2028192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_2028192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028192 prefixEnd_2028192 := by exact prefixLift 2028192
  have htrace : WordTrace (prefixWord ++ tailWord_2028192) baseStart_2028192 baseEnd_2028192 := by
    simpa [prefixWord, tailWord_2028192, baseEnd_2028192] using wordTrace_append hprefix tailTrace_2028192
  have hstable : (prefixWord ++ tailWord_2028192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028192).length < 2 ^ (prefixWord ++ tailWord_2028192).sum := by decide
  have hdescent : baseEnd_2028192 < baseStart_2028192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028220 : List Nat := [2, 2, 2, 3, 1, 1, 3, 7]
def baseStart_2028220 : Nat := 118140960795 + 2028220 * 2 ^ 59
def prefixEnd_2028220 : Nat := 4983230072969 + 3 ^ 40 * 2028220 * 2
def baseEnd_2028220 : Nat := 154289145638838490907021

theorem tailTrace_2028220 : CollatzResearch.WordTrace tailWord_2028220 prefixEnd_2028220 154289145638838490907021 := by
  unfold tailWord_2028220
  simp only [CollatzResearch.WordTrace]
  refine ⟨36987630356056403621701057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49316840474741871495601409 36987630356056403621701057)
  ·
    refine ⟨27740722767042302716275793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36987630356056403621701057 27740722767042302716275793)
    ·
      refine ⟨20805542075281727037206845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27740722767042302716275793 20805542075281727037206845)
      ·
        refine ⟨7802078278230647638952567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20805542075281727037206845 7802078278230647638952567)
        ·
          refine ⟨11703117417345971458428851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7802078278230647638952567 11703117417345971458428851)
          ·
            refine ⟨17554676126018957187643277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11703117417345971458428851 17554676126018957187643277)
            ·
              refine ⟨6583003547257108945366229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17554676126018957187643277 6583003547257108945366229)
              ·
                refine ⟨154289145638838490907021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6583003547257108945366229 154289145638838490907021)
                ·
                  rfl

theorem cell21_2028220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_2028220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028220 prefixEnd_2028220 := by exact prefixLift 2028220
  have htrace : WordTrace (prefixWord ++ tailWord_2028220) baseStart_2028220 baseEnd_2028220 := by
    simpa [prefixWord, tailWord_2028220, baseEnd_2028220] using wordTrace_append hprefix tailTrace_2028220
  have hstable : (prefixWord ++ tailWord_2028220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028220).length < 2 ^ (prefixWord ++ tailWord_2028220).sum := by decide
  have hdescent : baseEnd_2028220 < baseStart_2028220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028344 : List Nat := [2, 1, 2, 1, 3, 2, 4, 3, 3]
def baseStart_2028344 : Nat := 118140960795 + 2028344 * 2 ^ 59
def prefixEnd_2028344 : Nat := 4983230072969 + 3 ^ 40 * 2028344 * 2
def baseEnd_2028344 : Nat := 462895735405918812654143

theorem tailTrace_2028344 : CollatzResearch.WordTrace tailWord_2028344 prefixEnd_2028344 462895735405918812654143 := by
  unfold tailWord_2028344
  simp only [CollatzResearch.WordTrace]
  refine ⟨36989891681831788210458043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49319855575775717613944057 36989891681831788210458043)
  ·
    refine ⟨55484837522747682315687065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36989891681831788210458043 55484837522747682315687065)
    ·
      refine ⟨41613628142060761736765299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55484837522747682315687065 41613628142060761736765299)
      ·
        refine ⟨62420442213091142605147949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41613628142060761736765299 62420442213091142605147949)
        ·
          refine ⟨23407665829909178476930481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62420442213091142605147949 23407665829909178476930481)
          ·
            refine ⟨17555749372431883857697861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23407665829909178476930481 17555749372431883857697861)
            ·
              refine ⟨3291703007330978223318349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17555749372431883857697861 3291703007330978223318349)
              ·
                refine ⟨1234388627749116833744381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3291703007330978223318349 1234388627749116833744381)
                ·
                  refine ⟨462895735405918812654143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234388627749116833744381 462895735405918812654143)
                  ·
                    rfl

theorem cell21_2028344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 3].length) (baseStart_2028344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028344 prefixEnd_2028344 := by exact prefixLift 2028344
  have htrace : WordTrace (prefixWord ++ tailWord_2028344) baseStart_2028344 baseEnd_2028344 := by
    simpa [prefixWord, tailWord_2028344, baseEnd_2028344] using wordTrace_append hprefix tailTrace_2028344
  have hstable : (prefixWord ++ tailWord_2028344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028344).length < 2 ^ (prefixWord ++ tailWord_2028344).sum := by decide
  have hdescent : baseEnd_2028344 < baseStart_2028344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028355 : List Nat := [1, 1, 1, 3, 1, 4, 10]
def baseStart_2028355 : Nat := 118140960795 + 2028355 * 2 ^ 59
def prefixEnd_2028355 : Nat := 4983230072969 + 3 ^ 40 * 2028355 * 2
def baseEnd_2028355 : Nat := 51433138417309470885643

theorem tailTrace_2028355 : CollatzResearch.WordTrace tailWord_2028355 prefixEnd_2028355 51433138417309470885643 := by
  unfold tailWord_2028355
  simp only [CollatzResearch.WordTrace]
  refine ⟨73980184566623725299566519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49320123044415816866377679 73980184566623725299566519)
  ·
    refine ⟨110970276849935587949349779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73980184566623725299566519 110970276849935587949349779)
    ·
      refine ⟨166455415274903381924024669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110970276849935587949349779 166455415274903381924024669)
      ·
        refine ⟨62420780728088768221509251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166455415274903381924024669 62420780728088768221509251)
        ·
          refine ⟨93631171092133152332263877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62420780728088768221509251 93631171092133152332263877)
          ·
            refine ⟨17555844579774966062299477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93631171092133152332263877 17555844579774966062299477)
            ·
              refine ⟨51433138417309470885643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17555844579774966062299477 51433138417309470885643)
              ·
                rfl

theorem cell21_2028355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 10].length) (baseStart_2028355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028355 prefixEnd_2028355 := by exact prefixLift 2028355
  have htrace : WordTrace (prefixWord ++ tailWord_2028355) baseStart_2028355 baseEnd_2028355 := by
    simpa [prefixWord, tailWord_2028355, baseEnd_2028355] using wordTrace_append hprefix tailTrace_2028355
  have hstable : (prefixWord ++ tailWord_2028355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028355).length < 2 ^ (prefixWord ++ tailWord_2028355).sum := by decide
  have hdescent : baseEnd_2028355 < baseStart_2028355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028375 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 4]
def baseStart_2028375 : Nat := 118140960795 + 2028375 * 2 ^ 59
def prefixEnd_2028375 : Nat := 4983230072969 + 3 ^ 40 * 2028375 * 2
def baseEnd_2028375 : Nat := 462902810028269647637413

theorem tailTrace_2028375 : CollatzResearch.WordTrace tailWord_2028375 prefixEnd_2028375 462902810028269647637413 := by
  unfold tailWord_2028375
  simp only [CollatzResearch.WordTrace]
  refine ⟨73980914026551268715294579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49320609351034179143529719 73980914026551268715294579)
  ·
    refine ⟨110971371039826903072941869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73980914026551268715294579 110971371039826903072941869)
    ·
      refine ⟨41614264139935088652353201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110971371039826903072941869 41614264139935088652353201)
      ·
        refine ⟨31210698104951316489264901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41614264139935088652353201 31210698104951316489264901)
        ·
          refine ⟨5852005894678371841737169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31210698104951316489264901 5852005894678371841737169)
          ·
            refine ⟨4389004421008778881302877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5852005894678371841737169 4389004421008778881302877)
            ·
              refine ⟨1645876657878292080488579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4389004421008778881302877 1645876657878292080488579)
              ·
                refine ⟨2468814986817438120732869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645876657878292080488579 2468814986817438120732869)
                ·
                  refine ⟨462902810028269647637413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2468814986817438120732869 462902810028269647637413)
                  ·
                    rfl

theorem cell21_2028375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 4].length) (baseStart_2028375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028375 prefixEnd_2028375 := by exact prefixLift 2028375
  have htrace : WordTrace (prefixWord ++ tailWord_2028375) baseStart_2028375 baseEnd_2028375 := by
    simpa [prefixWord, tailWord_2028375, baseEnd_2028375] using wordTrace_append hprefix tailTrace_2028375
  have hstable : (prefixWord ++ tailWord_2028375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028375).length < 2 ^ (prefixWord ++ tailWord_2028375).sum := by decide
  have hdescent : baseEnd_2028375 < baseStart_2028375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028468 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2028468 : Nat := 118140960795 + 2028468 * 2 ^ 59
def prefixEnd_2028468 : Nat := 4983230072969 + 3 ^ 40 * 2028468 * 2
def baseEnd_2028468 : Nat := 462924033895322152587223

theorem tailTrace_2028468 : CollatzResearch.WordTrace tailWord_2028468 prefixEnd_2028468 462924033895322152587223 := by
  unfold tailWord_2028468
  simp only [CollatzResearch.WordTrace]
  refine ⟨36992153007607172799215029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49322870676809563732286705 36992153007607172799215029)
  ·
    refine ⟨3468014344463172449926409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36992153007607172799215029 3468014344463172449926409)
    ·
      refine ⟨2601010758347379337444807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3468014344463172449926409 2601010758347379337444807)
      ·
        refine ⟨3901516137521069006167211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2601010758347379337444807 3901516137521069006167211)
        ·
          refine ⟨5852274206281603509250817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901516137521069006167211 5852274206281603509250817)
          ·
            refine ⟨4389205654711202631938113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5852274206281603509250817 4389205654711202631938113)
            ·
              refine ⟨3291904241033401973953585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4389205654711202631938113 3291904241033401973953585)
              ·
                refine ⟨2468928180775051480465189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3291904241033401973953585 2468928180775051480465189)
                ·
                  refine ⟨462924033895322152587223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2468928180775051480465189 462924033895322152587223)
                  ·
                    rfl

theorem cell21_2028468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2028468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028468 prefixEnd_2028468 := by exact prefixLift 2028468
  have htrace : WordTrace (prefixWord ++ tailWord_2028468) baseStart_2028468 baseEnd_2028468 := by
    simpa [prefixWord, tailWord_2028468, baseEnd_2028468] using wordTrace_append hprefix tailTrace_2028468
  have hstable : (prefixWord ++ tailWord_2028468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028468).length < 2 ^ (prefixWord ++ tailWord_2028468).sum := by decide
  have hdescent : baseEnd_2028468 < baseStart_2028468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028600 : List Nat := [2, 1, 2, 1, 5, 2, 2, 6]
def baseStart_2028600 : Nat := 118140960795 + 2028600 * 2 ^ 59
def prefixEnd_2028600 : Nat := 4983230072969 + 3 ^ 40 * 2028600 * 2
def baseEnd_2028600 : Nat := 154318052697906418795651

theorem tailTrace_2028600 : CollatzResearch.WordTrace tailWord_2028600 prefixEnd_2028600 154318052697906418795651 := by
  unfold tailWord_2028600
  simp only [CollatzResearch.WordTrace]
  refine ⟨36994560225368066071117627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49326080300490754761490169 36994560225368066071117627)
  ·
    refine ⟨55491840338052099106676441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36994560225368066071117627 55491840338052099106676441)
    ·
      refine ⟨41618880253539074330007331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55491840338052099106676441 41618880253539074330007331)
      ·
        refine ⟨62428320380308611495010997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41618880253539074330007331 62428320380308611495010997)
        ·
          refine ⟨5852655035653932327657281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62428320380308611495010997 5852655035653932327657281)
          ·
            refine ⟨4389491276740449245742961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5852655035653932327657281 4389491276740449245742961)
            ·
              refine ⟨3292118457555336934307221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4389491276740449245742961 3292118457555336934307221)
              ·
                refine ⟨154318052697906418795651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3292118457555336934307221 154318052697906418795651)
                ·
                  rfl

theorem cell21_2028600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_2028600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028600 prefixEnd_2028600 := by exact prefixLift 2028600
  have htrace : WordTrace (prefixWord ++ tailWord_2028600) baseStart_2028600 baseEnd_2028600 := by
    simpa [prefixWord, tailWord_2028600, baseEnd_2028600] using wordTrace_append hprefix tailTrace_2028600
  have hstable : (prefixWord ++ tailWord_2028600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028600).length < 2 ^ (prefixWord ++ tailWord_2028600).sum := by decide
  have hdescent : baseEnd_2028600 < baseStart_2028600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028631 : List Nat := [1, 1, 3, 2, 2, 1, 1, 7, 3]
def baseStart_2028631 : Nat := 118140960795 + 2028631 * 2 ^ 59
def prefixEnd_2028631 : Nat := 4983230072969 + 3 ^ 40 * 2028631 * 2
def baseEnd_2028631 : Nat := 462961232716070091370223

theorem tailTrace_2028631 : CollatzResearch.WordTrace tailWord_2028631 prefixEnd_2028631 462961232716070091370223 := by
  unfold tailWord_2028631
  simp only [CollatzResearch.WordTrace]
  refine ⟨73990251113623824436613747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49326834075749216291075831 73990251113623824436613747)
  ·
    refine ⟨110985376670435736654920621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73990251113623824436613747 110985376670435736654920621)
    ·
      refine ⟨41619516251413401245595233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110985376670435736654920621 41619516251413401245595233)
      ·
        refine ⟨31214637188560050934196425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41619516251413401245595233 31214637188560050934196425)
        ·
          refine ⟨23410977891420038200647319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31214637188560050934196425 23410977891420038200647319)
          ·
            refine ⟨35116466837130057300970979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23410977891420038200647319 35116466837130057300970979)
            ·
              refine ⟨52674700255695085951456469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35116466837130057300970979 52674700255695085951456469)
              ·
                refine ⟨1234563287242853576987261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52674700255695085951456469 1234563287242853576987261)
                ·
                  refine ⟨462961232716070091370223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234563287242853576987261 462961232716070091370223)
                  ·
                    rfl

theorem cell21_2028631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 3].length) (baseStart_2028631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028631 prefixEnd_2028631 := by exact prefixLift 2028631
  have htrace : WordTrace (prefixWord ++ tailWord_2028631) baseStart_2028631 baseEnd_2028631 := by
    simpa [prefixWord, tailWord_2028631, baseEnd_2028631] using wordTrace_append hprefix tailTrace_2028631
  have hstable : (prefixWord ++ tailWord_2028631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028631).length < 2 ^ (prefixWord ++ tailWord_2028631).sum := by decide
  have hdescent : baseEnd_2028631 < baseStart_2028631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028662 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_2028662 : Nat := 118140960795 + 2028662 * 2 ^ 59
def prefixEnd_2028662 : Nat := 4983230072969 + 3 ^ 40 * 2028662 * 2
def baseEnd_2028662 : Nat := 462968307338420926353493

theorem tailTrace_2028662 : CollatzResearch.WordTrace tailWord_2028662 prefixEnd_2028662 462968307338420926353493 := by
  unfold tailWord_2028662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624461361031969795687015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49327587851007677820661493 4624461361031969795687015)
  ·
    refine ⟨6936692041547954693530523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4624461361031969795687015 6936692041547954693530523)
    ·
      refine ⟨10405038062321932040295785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6936692041547954693530523 10405038062321932040295785)
      ·
        refine ⟨7803778546741449030221839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10405038062321932040295785 7803778546741449030221839)
        ·
          refine ⟨11705667820112173545332759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7803778546741449030221839 11705667820112173545332759)
          ·
            refine ⟨17558501730168260317999139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11705667820112173545332759 17558501730168260317999139)
            ·
              refine ⟨26337752595252390476998709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17558501730168260317999139 26337752595252390476998709)
              ·
                refine ⟨2469164305804911607218629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26337752595252390476998709 2469164305804911607218629)
                ·
                  refine ⟨462968307338420926353493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2469164305804911607218629 462968307338420926353493)
                  ·
                    rfl

theorem cell21_2028662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_2028662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028662 prefixEnd_2028662 := by exact prefixLift 2028662
  have htrace : WordTrace (prefixWord ++ tailWord_2028662) baseStart_2028662 baseEnd_2028662 := by
    simpa [prefixWord, tailWord_2028662, baseEnd_2028662] using wordTrace_append hprefix tailTrace_2028662
  have hstable : (prefixWord ++ tailWord_2028662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028662).length < 2 ^ (prefixWord ++ tailWord_2028662).sum := by decide
  have hdescent : baseEnd_2028662 < baseStart_2028662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028758 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_2028758 : Nat := 118140960795 + 2028758 * 2 ^ 59
def prefixEnd_2028758 : Nat := 4983230072969 + 3 ^ 40 * 2028758 * 2
def baseEnd_2028758 : Nat := 462990215846346092753297

theorem tailTrace_2028758 : CollatzResearch.WordTrace tailWord_2028758 prefixEnd_2028758 462990215846346092753297 := by
  unfold tailWord_2028758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624680199010232820405433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49329922122775816750991285 4624680199010232820405433)
  ·
    refine ⟨3468510149257674615304075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4624680199010232820405433 3468510149257674615304075)
    ·
      refine ⟨5202765223886511922956113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3468510149257674615304075 5202765223886511922956113)
      ·
        refine ⟨3902073917914883942217085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5202765223886511922956113 3902073917914883942217085)
        ·
          refine ⟨1463277719218081478331407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3902073917914883942217085 1463277719218081478331407)
          ·
            refine ⟨2194916578827122217497111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463277719218081478331407 2194916578827122217497111)
            ·
              refine ⟨3292374868240683326245667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2194916578827122217497111 3292374868240683326245667)
              ·
                refine ⟨4938562302361024989368501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292374868240683326245667 4938562302361024989368501)
                ·
                  refine ⟨462990215846346092753297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4938562302361024989368501 462990215846346092753297)
                  ·
                    rfl

theorem cell21_2028758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_2028758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028758 prefixEnd_2028758 := by exact prefixLift 2028758
  have htrace : WordTrace (prefixWord ++ tailWord_2028758) baseStart_2028758 baseEnd_2028758 := by
    simpa [prefixWord, tailWord_2028758, baseEnd_2028758] using wordTrace_append hprefix tailTrace_2028758
  have hstable : (prefixWord ++ tailWord_2028758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028758).length < 2 ^ (prefixWord ++ tailWord_2028758).sum := by decide
  have hdescent : baseEnd_2028758 < baseStart_2028758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028814 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_2028814 : Nat := 118140960795 + 2028814 * 2 ^ 59
def prefixEnd_2028814 : Nat := 4983230072969 + 3 ^ 40 * 2028814 * 2
def baseEnd_2028814 : Nat := 463002995809302439819849

theorem tailTrace_2028814 : CollatzResearch.WordTrace tailWord_2028814 prefixEnd_2028814 463002995809302439819849 := by
  unfold tailWord_2028814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9249615708995105836315687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49331283781307231127016997 9249615708995105836315687)
  ·
    refine ⟨13874423563492658754473531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9249615708995105836315687 13874423563492658754473531)
    ·
      refine ⟨20811635345238988131710297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13874423563492658754473531 20811635345238988131710297)
      ·
        refine ⟨15608726508929241098782723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20811635345238988131710297 15608726508929241098782723)
        ·
          refine ⟨23413089763393861648174085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15608726508929241098782723 23413089763393861648174085)
          ·
            refine ⟨4389954330636349059032641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23413089763393861648174085 4389954330636349059032641)
            ·
              refine ⟨3292465747977261794274481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4389954330636349059032641 3292465747977261794274481)
              ·
                refine ⟨2469349310982946345705861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3292465747977261794274481 2469349310982946345705861)
                ·
                  refine ⟨463002995809302439819849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2469349310982946345705861 463002995809302439819849)
                  ·
                    rfl

theorem cell21_2028814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_2028814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028814 prefixEnd_2028814 := by exact prefixLift 2028814
  have htrace : WordTrace (prefixWord ++ tailWord_2028814) baseStart_2028814 baseEnd_2028814 := by
    simpa [prefixWord, tailWord_2028814, baseEnd_2028814] using wordTrace_append hprefix tailTrace_2028814
  have hstable : (prefixWord ++ tailWord_2028814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028814).length < 2 ^ (prefixWord ++ tailWord_2028814).sum := by decide
  have hdescent : baseEnd_2028814 < baseStart_2028814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028825 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 11]
def baseStart_2028825 : Nat := 118140960795 + 2028825 * 2 ^ 59
def prefixEnd_2028825 : Nat := 4983230072969 + 3 ^ 40 * 2028825 * 2
def baseEnd_2028825 : Nat := 463005506159168865136493

theorem tailTrace_2028825 : CollatzResearch.WordTrace tailWord_2028825 prefixEnd_2028825 463005506159168865136493 := by
  unfold tailWord_2028825
  simp only [CollatzResearch.WordTrace]
  refine ⟨73997326874920995569175929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49331551249947330379450619 73997326874920995569175929)
  ·
    refine ⟨55497995156190746676881947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73997326874920995569175929 55497995156190746676881947)
    ·
      refine ⟨83246992734286120015322921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55497995156190746676881947 83246992734286120015322921)
      ·
        refine ⟨62435244550714590011492191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83246992734286120015322921 62435244550714590011492191)
        ·
          refine ⟨93652866826071885017238287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62435244550714590011492191 93652866826071885017238287)
          ·
            refine ⟨140479300239107827525857431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93652866826071885017238287 140479300239107827525857431)
            ·
              refine ⟨210718950358661741288786147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140479300239107827525857431 210718950358661741288786147)
              ·
                refine ⟨316078425537992611933179221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210718950358661741288786147 316078425537992611933179221)
                ·
                  refine ⟨463005506159168865136493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 316078425537992611933179221 463005506159168865136493)
                  ·
                    rfl

theorem cell21_2028825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_2028825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028825 prefixEnd_2028825 := by exact prefixLift 2028825
  have htrace : WordTrace (prefixWord ++ tailWord_2028825) baseStart_2028825 baseEnd_2028825 := by
    simpa [prefixWord, tailWord_2028825, baseEnd_2028825] using wordTrace_append hprefix tailTrace_2028825
  have hstable : (prefixWord ++ tailWord_2028825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028825).length < 2 ^ (prefixWord ++ tailWord_2028825).sum := by decide
  have hdescent : baseEnd_2028825 < baseStart_2028825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028856 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_2028856 : Nat := 118140960795 + 2028856 * 2 ^ 59
def prefixEnd_2028856 : Nat := 4983230072969 + 3 ^ 40 * 2028856 * 2
def baseEnd_2028856 : Nat := 463012580781519700119763

theorem tailTrace_2028856 : CollatzResearch.WordTrace tailWord_2028856 prefixEnd_2028856 463012580781519700119763 := by
  unfold tailWord_2028856
  simp only [CollatzResearch.WordTrace]
  refine ⟨36999228768904343931777211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49332305025205791909036281 36999228768904343931777211)
  ·
    refine ⟨55498843153356515897665817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36999228768904343931777211 55498843153356515897665817)
    ·
      refine ⟨41624132365017386923249363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55498843153356515897665817 41624132365017386923249363)
      ·
        refine ⟨62436198547526080384874045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41624132365017386923249363 62436198547526080384874045)
        ·
          refine ⟨23413574455322280144327767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62436198547526080384874045 23413574455322280144327767)
          ·
            refine ⟨35120361682983420216491651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23413574455322280144327767 35120361682983420216491651)
            ·
              refine ⟨52680542524475130324737477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35120361682983420216491651 52680542524475130324737477)
              ·
                refine ⟨9877601723339086935888277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52680542524475130324737477 9877601723339086935888277)
                ·
                  refine ⟨463012580781519700119763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9877601723339086935888277 463012580781519700119763)
                  ·
                    rfl

theorem cell21_2028856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_2028856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028856 prefixEnd_2028856 := by exact prefixLift 2028856
  have htrace : WordTrace (prefixWord ++ tailWord_2028856) baseStart_2028856 baseEnd_2028856 := by
    simpa [prefixWord, tailWord_2028856, baseEnd_2028856] using wordTrace_append hprefix tailTrace_2028856
  have hstable : (prefixWord ++ tailWord_2028856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028856).length < 2 ^ (prefixWord ++ tailWord_2028856).sum := by decide
  have hdescent : baseEnd_2028856 < baseStart_2028856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028873 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 4]
def baseStart_2028873 : Nat := 118140960795 + 2028873 * 2 ^ 59
def prefixEnd_2028873 : Nat := 4983230072969 + 3 ^ 40 * 2028873 * 2
def baseEnd_2028873 : Nat := 463016460413131448336395

theorem tailTrace_2028873 : CollatzResearch.WordTrace tailWord_2028873 prefixEnd_2028873 463016460413131448336395 := by
  unfold tailWord_2028873
  simp only [CollatzResearch.WordTrace]
  refine ⟨73999077578747099766923273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49332718385831399844615515 73999077578747099766923273)
  ·
    refine ⟨55499308184060324825192455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73999077578747099766923273 55499308184060324825192455)
    ·
      refine ⟨83248962276090487237788683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55499308184060324825192455 83248962276090487237788683)
      ·
        refine ⟨124873443414135730856683025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83248962276090487237788683 124873443414135730856683025)
        ·
          refine ⟨93655082560601798142512269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124873443414135730856683025 93655082560601798142512269)
          ·
            refine ⟨35120655960225674303442101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93655082560601798142512269 35120655960225674303442101)
            ·
              refine ⟨3292561496271156965947697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35120655960225674303442101 3292561496271156965947697)
              ·
                refine ⟨2469421122203367724460773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3292561496271156965947697 2469421122203367724460773)
                ·
                  refine ⟨463016460413131448336395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2469421122203367724460773 463016460413131448336395)
                  ·
                    rfl

theorem cell21_2028873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_2028873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028873 prefixEnd_2028873 := by exact prefixLift 2028873
  have htrace : WordTrace (prefixWord ++ tailWord_2028873) baseStart_2028873 baseEnd_2028873 := by
    simpa [prefixWord, tailWord_2028873, baseEnd_2028873] using wordTrace_append hprefix tailTrace_2028873
  have hstable : (prefixWord ++ tailWord_2028873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028873).length < 2 ^ (prefixWord ++ tailWord_2028873).sum := by decide
  have hdescent : baseEnd_2028873 < baseStart_2028873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028904 : List Nat := [2, 1, 4, 2, 3, 1, 1, 7]
def baseStart_2028904 : Nat := 118140960795 + 2028904 * 2 ^ 59
def prefixEnd_2028904 : Nat := 4983230072969 + 3 ^ 40 * 2028904 * 2
def baseEnd_2028904 : Nat := 154341178345160761106555

theorem tailTrace_2028904 : CollatzResearch.WordTrace tailWord_2028904 prefixEnd_2028904 154341178345160761106555 := by
  unfold tailWord_2028904
  simp only [CollatzResearch.WordTrace]
  refine ⟨37000104120817396030650883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49333472161089861374201177 37000104120817396030650883)
  ·
    refine ⟨55500156181226094045976325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37000104120817396030650883 55500156181226094045976325)
    ·
      refine ⟨10406279283979892633620561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55500156181226094045976325 10406279283979892633620561)
      ·
        refine ⟨7804709462984919475215421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10406279283979892633620561 7804709462984919475215421)
        ·
          refine ⟨2926766048619344803205783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7804709462984919475215421 2926766048619344803205783)
          ·
            refine ⟨4390149072929017204808675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926766048619344803205783 4390149072929017204808675)
            ·
              refine ⟨6585223609393525807213013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390149072929017204808675 6585223609393525807213013)
              ·
                refine ⟨154341178345160761106555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6585223609393525807213013 154341178345160761106555)
                ·
                  rfl

theorem cell21_2028904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_2028904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028904 prefixEnd_2028904 := by exact prefixLift 2028904
  have htrace : WordTrace (prefixWord ++ tailWord_2028904) baseStart_2028904 baseEnd_2028904 := by
    simpa [prefixWord, tailWord_2028904, baseEnd_2028904] using wordTrace_append hprefix tailTrace_2028904
  have hstable : (prefixWord ++ tailWord_2028904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028904).length < 2 ^ (prefixWord ++ tailWord_2028904).sum := by decide
  have hdescent : baseEnd_2028904 < baseStart_2028904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028910 : List Nat := [4, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_2028910 : Nat := 118140960795 + 2028910 * 2 ^ 59
def prefixEnd_2028910 : Nat := 4983230072969 + 3 ^ 40 * 2028910 * 2
def baseEnd_2028910 : Nat := 463024904317227606219653

theorem tailTrace_2028910 : CollatzResearch.WordTrace tailWord_2028910 prefixEnd_2028910 463024904317227606219653 := by
  unfold tailWord_2028910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9250053384951631885752523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49333618053075370057346789 9250053384951631885752523)
  ·
    refine ⟨13875080077427447828628785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9250053384951631885752523 13875080077427447828628785)
    ·
      refine ⟨10406310058070585871471589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13875080077427447828628785 10406310058070585871471589)
      ·
        refine ⟨1951183135888234850900923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10406310058070585871471589 1951183135888234850900923)
        ·
          refine ⟨2926774703832352276351385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951183135888234850900923 2926774703832352276351385)
          ·
            refine ⟨2195081027874264207263539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2926774703832352276351385 2195081027874264207263539)
            ·
              refine ⟨3292621541811396310895309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195081027874264207263539 3292621541811396310895309)
              ·
                refine ⟨1234733078179273616585741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3292621541811396310895309 1234733078179273616585741)
                ·
                  refine ⟨463024904317227606219653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234733078179273616585741 463024904317227606219653)
                  ·
                    rfl

theorem cell21_2028910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_2028910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028910 prefixEnd_2028910 := by exact prefixLift 2028910
  have htrace : WordTrace (prefixWord ++ tailWord_2028910) baseStart_2028910 baseEnd_2028910 := by
    simpa [prefixWord, tailWord_2028910, baseEnd_2028910] using wordTrace_append hprefix tailTrace_2028910
  have hstable : (prefixWord ++ tailWord_2028910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028910).length < 2 ^ (prefixWord ++ tailWord_2028910).sum := by decide
  have hdescent : baseEnd_2028910 < baseStart_2028910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028935 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 5]
def baseStart_2028935 : Nat := 118140960795 + 2028935 * 2 ^ 59
def prefixEnd_2028935 : Nat := 4983230072969 + 3 ^ 40 * 2028935 * 2
def baseEnd_2028935 : Nat := 463030609657833118302935

theorem tailTrace_2028935 : CollatzResearch.WordTrace tailWord_2028935 prefixEnd_2028935 463030609657833118302935 := by
  unfold tailWord_2028935
  simp only [CollatzResearch.WordTrace]
  refine ⟨74001338904522484355680259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49334225936348322903786839 74001338904522484355680259)
  ·
    refine ⟨111002008356783726533520389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74001338904522484355680259 111002008356783726533520389)
    ·
      refine ⟨20812876566896948725035073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111002008356783726533520389 20812876566896948725035073)
      ·
        refine ⟨15609657425172711543776305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20812876566896948725035073 15609657425172711543776305)
        ·
          refine ⟨11707243068879533657832229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15609657425172711543776305 11707243068879533657832229)
          ·
            refine ⟨2195108075414912560843543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11707243068879533657832229 2195108075414912560843543)
            ·
              refine ⟨3292662113122368841265315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195108075414912560843543 3292662113122368841265315)
              ·
                refine ⟨4938993169683553261897973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292662113122368841265315 4938993169683553261897973)
                ·
                  refine ⟨463030609657833118302935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4938993169683553261897973 463030609657833118302935)
                  ·
                    rfl

theorem cell21_2028935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 5].length) (baseStart_2028935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2028935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2028935 prefixEnd_2028935 := by exact prefixLift 2028935
  have htrace : WordTrace (prefixWord ++ tailWord_2028935) baseStart_2028935 baseEnd_2028935 := by
    simpa [prefixWord, tailWord_2028935, baseEnd_2028935] using wordTrace_append hprefix tailTrace_2028935
  have hstable : (prefixWord ++ tailWord_2028935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028935).length < 2 ^ (prefixWord ++ tailWord_2028935).sum := by decide
  have hdescent : baseEnd_2028935 < baseStart_2028935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029042 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_2029042 : Nat := 118140960795 + 2029042 * 2 ^ 59
def prefixEnd_2029042 : Nat := 4983230072969 + 3 ^ 40 * 2029042 * 2
def baseEnd_2029042 : Nat := 463055028515624710019383

theorem tailTrace_2029042 : CollatzResearch.WordTrace tailWord_2029042 prefixEnd_2029042 463055028515624710019383 := by
  unfold tailWord_2029042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18501310378783710407456345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49336827676756561086550253 18501310378783710407456345)
  ·
    refine ⟨13875982784087782805592259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18501310378783710407456345 13875982784087782805592259)
    ·
      refine ⟨20813974176131674208388389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13875982784087782805592259 20813974176131674208388389)
      ·
        refine ⟨3902620158024688914072823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20813974176131674208388389 3902620158024688914072823)
        ·
          refine ⟨5853930237037033371109235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902620158024688914072823 5853930237037033371109235)
          ·
            refine ⟨8780895355555550056663853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5853930237037033371109235 8780895355555550056663853)
            ·
              refine ⟨3292835758333331271248945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8780895355555550056663853 3292835758333331271248945)
              ·
                refine ⟨2469626818749998453436709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3292835758333331271248945 2469626818749998453436709)
                ·
                  refine ⟨463055028515624710019383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2469626818749998453436709 463055028515624710019383)
                  ·
                    rfl

theorem cell21_2029042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_2029042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029042 prefixEnd_2029042 := by exact prefixLift 2029042
  have htrace : WordTrace (prefixWord ++ tailWord_2029042) baseStart_2029042 baseEnd_2029042 := by
    simpa [prefixWord, tailWord_2029042, baseEnd_2029042] using wordTrace_append hprefix tailTrace_2029042
  have hstable : (prefixWord ++ tailWord_2029042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029042).length < 2 ^ (prefixWord ++ tailWord_2029042).sum := by decide
  have hdescent : baseEnd_2029042 < baseStart_2029042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029084 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_2029084 : Nat := 118140960795 + 2029084 * 2 ^ 59
def prefixEnd_2029084 : Nat := 4983230072969 + 3 ^ 40 * 2029084 * 2
def baseEnd_2029084 : Nat := 463064613487841970319297

theorem tailTrace_2029084 : CollatzResearch.WordTrace tailWord_2029084 prefixEnd_2029084 463064613487841970319297 := by
  unfold tailWord_2029084
  simp only [CollatzResearch.WordTrace]
  refine ⟨37003386690491341401427153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49337848920655121868569537 37003386690491341401427153)
  ·
    refine ⟨27752540017868506051070365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37003386690491341401427153 27752540017868506051070365)
    ·
      refine ⟨10407202506700689769151387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27752540017868506051070365 10407202506700689769151387)
      ·
        refine ⟨15610803760051034653727081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10407202506700689769151387 15610803760051034653727081)
        ·
          refine ⟨11708102820038275990295311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15610803760051034653727081 11708102820038275990295311)
          ·
            refine ⟨17562154230057413985442967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11708102820038275990295311 17562154230057413985442967)
            ·
              refine ⟨26343231345086120978164451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17562154230057413985442967 26343231345086120978164451)
              ·
                refine ⟨39514847017629181467246677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26343231345086120978164451 39514847017629181467246677)
                ·
                  refine ⟨463064613487841970319297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39514847017629181467246677 463064613487841970319297)
                  ·
                    rfl

theorem cell21_2029084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_2029084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029084 prefixEnd_2029084 := by exact prefixLift 2029084
  have htrace : WordTrace (prefixWord ++ tailWord_2029084) baseStart_2029084 baseEnd_2029084 := by
    simpa [prefixWord, tailWord_2029084, baseEnd_2029084] using wordTrace_append hprefix tailTrace_2029084
  have hstable : (prefixWord ++ tailWord_2029084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029084).length < 2 ^ (prefixWord ++ tailWord_2029084).sum := by decide
  have hdescent : baseEnd_2029084 < baseStart_2029084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029087 : List Nat := [1, 1, 2, 4, 1, 1, 5, 3, 3]
def baseStart_2029087 : Nat := 118140960795 + 2029087 * 2 ^ 59
def prefixEnd_2029087 : Nat := 4983230072969 + 3 ^ 40 * 2029087 * 2
def baseEnd_2029087 : Nat := 463065298128714631769291

theorem tailTrace_2029087 : CollatzResearch.WordTrace tailWord_2029087 prefixEnd_2029087 463065298128714631769291 := by
  unfold tailWord_2029087
  simp only [CollatzResearch.WordTrace]
  refine ⟨74006882799971814315213515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49337921866647876210142343 74006882799971814315213515)
  ·
    refine ⟨111010324199957721472820273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74006882799971814315213515 111010324199957721472820273)
    ·
      refine ⟨83257743149968291104615205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111010324199957721472820273 83257743149968291104615205)
      ·
        refine ⟨15610826840619054582115351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83257743149968291104615205 15610826840619054582115351)
        ·
          refine ⟨23416240260928581873173027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15610826840619054582115351 23416240260928581873173027)
          ·
            refine ⟨35124360391392872809759541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23416240260928581873173027 35124360391392872809759541)
            ·
              refine ⟨3292908786693081825914957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35124360391392872809759541 3292908786693081825914957)
              ·
                refine ⟨1234840795009905684718109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3292908786693081825914957 1234840795009905684718109)
                ·
                  refine ⟨463065298128714631769291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234840795009905684718109 463065298128714631769291)
                  ·
                    rfl

theorem cell21_2029087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 3].length) (baseStart_2029087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029087 prefixEnd_2029087 := by exact prefixLift 2029087
  have htrace : WordTrace (prefixWord ++ tailWord_2029087) baseStart_2029087 baseEnd_2029087 := by
    simpa [prefixWord, tailWord_2029087, baseEnd_2029087] using wordTrace_append hprefix tailTrace_2029087
  have hstable : (prefixWord ++ tailWord_2029087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029087).length < 2 ^ (prefixWord ++ tailWord_2029087).sum := by decide
  have hdescent : baseEnd_2029087 < baseStart_2029087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029129 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 5]
def baseStart_2029129 : Nat := 118140960795 + 2029129 * 2 ^ 59
def prefixEnd_2029129 : Nat := 4983230072969 + 3 ^ 40 * 2029129 * 2
def baseEnd_2029129 : Nat := 463074883100931892069205

theorem tailTrace_2029129 : CollatzResearch.WordTrace tailWord_2029129 prefixEnd_2029129 463074883100931892069205 := by
  unfold tailWord_2029129
  simp only [CollatzResearch.WordTrace]
  refine ⟨74008414665819655488242441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49338943110546436992161627 74008414665819655488242441)
  ·
    refine ⟨55506310999364741616181831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74008414665819655488242441 55506310999364741616181831)
    ·
      refine ⟨83259466499047112424272747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55506310999364741616181831 83259466499047112424272747)
      ·
        refine ⟨124889199748570668636409121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83259466499047112424272747 124889199748570668636409121)
        ·
          refine ⟨93666899811428001477306841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124889199748570668636409121 93666899811428001477306841)
          ·
            refine ⟨70250174858571001107980131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93666899811428001477306841 70250174858571001107980131)
            ·
              refine ⟨105375262287856501661970197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70250174858571001107980131 105375262287856501661970197)
              ·
                refine ⟨4939465419743273515404853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105375262287856501661970197 4939465419743273515404853)
                ·
                  refine ⟨463074883100931892069205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4939465419743273515404853 463074883100931892069205)
                  ·
                    rfl

theorem cell21_2029129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_2029129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029129 prefixEnd_2029129 := by exact prefixLift 2029129
  have htrace : WordTrace (prefixWord ++ tailWord_2029129) baseStart_2029129 baseEnd_2029129 := by
    simpa [prefixWord, tailWord_2029129, baseEnd_2029129] using wordTrace_append hprefix tailTrace_2029129
  have hstable : (prefixWord ++ tailWord_2029129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029129).length < 2 ^ (prefixWord ++ tailWord_2029129).sum := by decide
  have hdescent : baseEnd_2029129 < baseStart_2029129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029149 : List Nat := [1, 4, 4, 2, 2, 8]
def baseStart_2029149 : Nat := 118140960795 + 2029149 * 2 ^ 59
def prefixEnd_2029149 : Nat := 4983230072969 + 3 ^ 40 * 2029149 * 2
def baseEnd_2029149 : Nat := 17151090643459863027253

theorem tailTrace_2029149 : CollatzResearch.WordTrace tailWord_2029149 prefixEnd_2029149 17151090643459863027253 := by
  unfold tailWord_2029149
  simp only [CollatzResearch.WordTrace]
  refine ⟨74009144125747198903970501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49339429417164799269313667 74009144125747198903970501)
  ·
    refine ⟨13876714523577599794494469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74009144125747198903970501 13876714523577599794494469)
    ·
      refine ⟨2601883973170799961467713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13876714523577599794494469 2601883973170799961467713)
      ·
        refine ⟨1951412979878099971100785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2601883973170799961467713 1951412979878099971100785)
        ·
          refine ⟨1463559734908574978325589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1951412979878099971100785 1463559734908574978325589)
          ·
            refine ⟨17151090643459863027253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1463559734908574978325589 17151090643459863027253)
            ·
              rfl

theorem cell21_2029149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 8].length) (baseStart_2029149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029149 prefixEnd_2029149 := by exact prefixLift 2029149
  have htrace : WordTrace (prefixWord ++ tailWord_2029149) baseStart_2029149 baseEnd_2029149 := by
    simpa [prefixWord, tailWord_2029149, baseEnd_2029149] using wordTrace_append hprefix tailTrace_2029149
  have hstable : (prefixWord ++ tailWord_2029149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029149).length < 2 ^ (prefixWord ++ tailWord_2029149).sum := by decide
  have hdescent : baseEnd_2029149 < baseStart_2029149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029318 : List Nat := [6, 2, 2, 1, 10]
def baseStart_2029318 : Nat := 118140960795 + 2029318 * 2 ^ 59
def prefixEnd_2029318 : Nat := 4983230072969 + 3 ^ 40 * 2029318 * 2
def baseEnd_2029318 : Nat := 5717506363900118066899

theorem tailTrace_2029318 : CollatzResearch.WordTrace tailWord_2029318 prefixEnd_2029318 5717506363900118066899 := by
  unfold tailWord_2029318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2312978376941716898964769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49343538708089960511248405 2312978376941716898964769)
  ·
    refine ⟨1734733782706287674223577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2312978376941716898964769 1734733782706287674223577)
    ·
      refine ⟨1301050337029715755667683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1734733782706287674223577 1301050337029715755667683)
      ·
        refine ⟨1951575505544573633501525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301050337029715755667683 1951575505544573633501525)
        ·
          refine ⟨5717506363900118066899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1951575505544573633501525 5717506363900118066899)
          ·
            rfl

theorem cell21_2029318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 10].length) (baseStart_2029318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029318 prefixEnd_2029318 := by exact prefixLift 2029318
  have htrace : WordTrace (prefixWord ++ tailWord_2029318) baseStart_2029318 baseEnd_2029318 := by
    simpa [prefixWord, tailWord_2029318, baseEnd_2029318] using wordTrace_append hprefix tailTrace_2029318
  have hstable : (prefixWord ++ tailWord_2029318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029318).length < 2 ^ (prefixWord ++ tailWord_2029318).sum := by decide
  have hdescent : baseEnd_2029318 < baseStart_2029318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029402 : List Nat := [3, 1, 1, 2, 1, 3, 2, 8]
def baseStart_2029402 : Nat := 118140960795 + 2029402 * 2 ^ 59
def prefixEnd_2029402 : Nat := 4983230072969 + 3 ^ 40 * 2029402 * 2
def baseEnd_2029402 : Nat := 154379061806781361339549

theorem tailTrace_2029402 : CollatzResearch.WordTrace tailWord_2029402 prefixEnd_2029402 154379061806781361339549 := by
  unfold tailWord_2029402
  simp only [CollatzResearch.WordTrace]
  refine ⟨18504592948457655778232615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49345581195887082075286973 18504592948457655778232615)
  ·
    refine ⟨27756889422686483667348923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18504592948457655778232615 27756889422686483667348923)
    ·
      refine ⟨41635334134029725501023385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27756889422686483667348923 41635334134029725501023385)
      ·
        refine ⟨31226500600522294125767539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41635334134029725501023385 31226500600522294125767539)
        ·
          refine ⟨46839750900783441188651309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31226500600522294125767539 46839750900783441188651309)
          ·
            refine ⟨17564906587793790445744241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46839750900783441188651309 17564906587793790445744241)
            ·
              refine ⟨13173679940845342834308181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17564906587793790445744241 13173679940845342834308181)
              ·
                refine ⟨154379061806781361339549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13173679940845342834308181 154379061806781361339549)
                ·
                  rfl

theorem cell21_2029402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_2029402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029402 prefixEnd_2029402 := by exact prefixLift 2029402
  have htrace : WordTrace (prefixWord ++ tailWord_2029402) baseStart_2029402 baseEnd_2029402 := by
    simpa [prefixWord, tailWord_2029402, baseEnd_2029402] using wordTrace_append hprefix tailTrace_2029402
  have hstable : (prefixWord ++ tailWord_2029402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029402).length < 2 ^ (prefixWord ++ tailWord_2029402).sum := by decide
  have hdescent : baseEnd_2029402 < baseStart_2029402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029599 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 8]
def baseStart_2029599 : Nat := 118140960795 + 2029599 * 2 ^ 59
def prefixEnd_2029599 : Nat := 4983230072969 + 3 ^ 40 * 2029599 * 2
def baseEnd_2029599 : Nat := 463182143504315519234911

theorem tailTrace_2029599 : CollatzResearch.WordTrace tailWord_2029599 prefixEnd_2029599 463182143504315519234911 := by
  unfold tailWord_2029599
  simp only [CollatzResearch.WordTrace]
  refine ⟨74025556974116925757851851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49350371316077950505234567 74025556974116925757851851)
  ·
    refine ⟨111038335461175388636777777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74025556974116925757851851 111038335461175388636777777)
    ·
      refine ⟨83278751595881541477583333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111038335461175388636777777 83278751595881541477583333)
      ·
        refine ⟨15614765924227789027046875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83278751595881541477583333 15614765924227789027046875)
        ·
          refine ⟨23422148886341683540570313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15614765924227789027046875 23422148886341683540570313)
          ·
            refine ⟨17566611664756262655427735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23422148886341683540570313 17566611664756262655427735)
            ·
              refine ⟨26349917497134393983141603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17566611664756262655427735 26349917497134393983141603)
              ·
                refine ⟨39524876245701590974712405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26349917497134393983141603 39524876245701590974712405)
                ·
                  refine ⟨463182143504315519234911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39524876245701590974712405 463182143504315519234911)
                  ·
                    rfl

theorem cell21_2029599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_2029599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029599 prefixEnd_2029599 := by exact prefixLift 2029599
  have htrace : WordTrace (prefixWord ++ tailWord_2029599) baseStart_2029599 baseEnd_2029599 := by
    simpa [prefixWord, tailWord_2029599, baseEnd_2029599] using wordTrace_append hprefix tailTrace_2029599
  have hstable : (prefixWord ++ tailWord_2029599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029599).length < 2 ^ (prefixWord ++ tailWord_2029599).sum := by decide
  have hdescent : baseEnd_2029599 < baseStart_2029599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029633 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 4]
def baseStart_2029633 : Nat := 118140960795 + 2029633 * 2 ^ 59
def prefixEnd_2029633 : Nat := 4983230072969 + 3 ^ 40 * 2029633 * 2
def baseEnd_2029633 : Nat := 463189902767539015668175

theorem tailTrace_2029633 : CollatzResearch.WordTrace tailWord_2029633 prefixEnd_2029633 463189902767539015668175 := by
  unfold tailWord_2029633
  simp only [CollatzResearch.WordTrace]
  refine ⟨74026797055993749564589553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49351198037329166376393035 74026797055993749564589553)
  ·
    refine ⟨55520097791995312173442165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74026797055993749564589553 55520097791995312173442165)
    ·
      refine ⟨5205009167999560516260203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55520097791995312173442165 5205009167999560516260203)
      ·
        refine ⟨7807513751999340774390305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5205009167999560516260203 7807513751999340774390305)
        ·
          refine ⟨5855635313999505580792729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7807513751999340774390305 5855635313999505580792729)
          ·
            refine ⟨4391726485499629185594547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5855635313999505580792729 4391726485499629185594547)
            ·
              refine ⟨6587589728249443778391821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391726485499629185594547 6587589728249443778391821)
              ·
                refine ⟨2470346148093541416896933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6587589728249443778391821 2470346148093541416896933)
                ·
                  refine ⟨463189902767539015668175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470346148093541416896933 463189902767539015668175)
                  ·
                    rfl

theorem cell21_2029633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_2029633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029633 prefixEnd_2029633 := by exact prefixLift 2029633
  have htrace : WordTrace (prefixWord ++ tailWord_2029633) baseStart_2029633 baseEnd_2029633 := by
    simpa [prefixWord, tailWord_2029633, baseEnd_2029633] using wordTrace_append hprefix tailTrace_2029633
  have hstable : (prefixWord ++ tailWord_2029633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029633).length < 2 ^ (prefixWord ++ tailWord_2029633).sum := by decide
  have hdescent : baseEnd_2029633 < baseStart_2029633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029692 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 4]
def baseStart_2029692 : Nat := 118140960795 + 2029692 * 2 ^ 59
def prefixEnd_2029692 : Nat := 4983230072969 + 3 ^ 40 * 2029692 * 2
def baseEnd_2029692 : Nat := 463203367371368024184721

theorem tailTrace_2029692 : CollatzResearch.WordTrace tailWord_2029692 prefixEnd_2029692 463203367371368024184721 := by
  unfold tailWord_2029692
  simp only [CollatzResearch.WordTrace]
  refine ⟨37014474481390001320493665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49352632641853335093991553 37014474481390001320493665)
  ·
    refine ⟨27760855861042500990370249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37014474481390001320493665 27760855861042500990370249)
    ·
      refine ⟨20820641895781875742777687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27760855861042500990370249 20820641895781875742777687)
      ·
        refine ⟨31230962843672813614166531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20820641895781875742777687 31230962843672813614166531)
        ·
          refine ⟨46846444265509220421249797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31230962843672813614166531 46846444265509220421249797)
          ·
            refine ⟨8783708299782978828984337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46846444265509220421249797 8783708299782978828984337)
            ·
              refine ⟨6587781224837234121738253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8783708299782978828984337 6587781224837234121738253)
              ·
                refine ⟨2470417959313962795651845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6587781224837234121738253 2470417959313962795651845)
                ·
                  refine ⟨463203367371368024184721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470417959313962795651845 463203367371368024184721)
                  ·
                    rfl

theorem cell21_2029692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_2029692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029692 prefixEnd_2029692 := by exact prefixLift 2029692
  have htrace : WordTrace (prefixWord ++ tailWord_2029692) baseStart_2029692 baseEnd_2029692 := by
    simpa [prefixWord, tailWord_2029692, baseEnd_2029692] using wordTrace_append hprefix tailTrace_2029692
  have hstable : (prefixWord ++ tailWord_2029692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029692).length < 2 ^ (prefixWord ++ tailWord_2029692).sum := by decide
  have hdescent : baseEnd_2029692 < baseStart_2029692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029718 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2029718 : Nat := 118140960795 + 2029718 * 2 ^ 59
def prefixEnd_2029718 : Nat := 4983230072969 + 3 ^ 40 * 2029718 * 2
def baseEnd_2029718 : Nat := 463209300925597756751335

theorem tailTrace_2029718 : CollatzResearch.WordTrace tailWord_2029718 prefixEnd_2029718 463209300925597756751335 := by
  unfold tailWord_2029718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4626868578792863067589613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49353264840457206054289205 4626868578792863067589613)
  ·
    refine ⟨1735075717047323650346105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4626868578792863067589613 1735075717047323650346105)
    ·
      refine ⟨1301306787785492737759579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1735075717047323650346105 1301306787785492737759579)
      ·
        refine ⟨1951960181678239106639369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301306787785492737759579 1951960181678239106639369)
        ·
          refine ⟨1463970136258679329979527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1951960181678239106639369 1463970136258679329979527)
          ·
            refine ⟨2195955204388018994969291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463970136258679329979527 2195955204388018994969291)
            ·
              refine ⟨3293932806582028492453937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195955204388018994969291 3293932806582028492453937)
              ·
                refine ⟨2470449604936521369340453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3293932806582028492453937 2470449604936521369340453)
                ·
                  refine ⟨463209300925597756751335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470449604936521369340453 463209300925597756751335)
                  ·
                    rfl

theorem cell21_2029718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2029718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029718 prefixEnd_2029718 := by exact prefixLift 2029718
  have htrace : WordTrace (prefixWord ++ tailWord_2029718) baseStart_2029718 baseEnd_2029718 := by
    simpa [prefixWord, tailWord_2029718, baseEnd_2029718] using wordTrace_append hprefix tailTrace_2029718
  have hstable : (prefixWord ++ tailWord_2029718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029718).length < 2 ^ (prefixWord ++ tailWord_2029718).sum := by decide
  have hdescent : baseEnd_2029718 < baseStart_2029718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029788 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 5]
def baseStart_2029788 : Nat := 118140960795 + 2029788 * 2 ^ 59
def prefixEnd_2029788 : Nat := 4983230072969 + 3 ^ 40 * 2029788 * 2
def baseEnd_2029788 : Nat := 463225275879293190584525

theorem tailTrace_2029788 : CollatzResearch.WordTrace tailWord_2029788 prefixEnd_2029788 463225275879293190584525 := by
  unfold tailWord_2029788
  simp only [CollatzResearch.WordTrace]
  refine ⟨37016225185216105518241009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49354966913621474024321345 37016225185216105518241009)
  ·
    refine ⟨27762168888912079138680757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37016225185216105518241009 27762168888912079138680757)
    ·
      refine ⟨2602703333335507419251321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27762168888912079138680757 2602703333335507419251321)
      ·
        refine ⟨1952027500001630564438491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2602703333335507419251321 1952027500001630564438491)
        ·
          refine ⟨2928041250002445846657737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952027500001630564438491 2928041250002445846657737)
          ·
            refine ⟨2196030937501834384993303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2928041250002445846657737 2196030937501834384993303)
            ·
              refine ⟨3294046406252751577489955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196030937501834384993303 3294046406252751577489955)
              ·
                refine ⟨4941069609379127366234933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294046406252751577489955 4941069609379127366234933)
                ·
                  refine ⟨463225275879293190584525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4941069609379127366234933 463225275879293190584525)
                  ·
                    rfl

theorem cell21_2029788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_2029788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029788 prefixEnd_2029788 := by exact prefixLift 2029788
  have htrace : WordTrace (prefixWord ++ tailWord_2029788) baseStart_2029788 baseEnd_2029788 := by
    simpa [prefixWord, tailWord_2029788, baseEnd_2029788] using wordTrace_append hprefix tailTrace_2029788
  have hstable : (prefixWord ++ tailWord_2029788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029788).length < 2 ^ (prefixWord ++ tailWord_2029788).sum := by decide
  have hdescent : baseEnd_2029788 < baseStart_2029788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029799 : List Nat := [1, 1, 5, 3, 1, 2, 2, 6]
def baseStart_2029799 : Nat := 118140960795 + 2029799 * 2 ^ 59
def prefixEnd_2029799 : Nat := 4983230072969 + 3 ^ 40 * 2029799 * 2
def baseEnd_2029799 : Nat := 154409262076386538633723

theorem tailTrace_2029799 : CollatzResearch.WordTrace tailWord_2029799 prefixEnd_2029799 154409262076386538633723 := by
  unfold tailWord_2029799
  simp only [CollatzResearch.WordTrace]
  refine ⟨74032851573392359915132451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49355234382261573276754967 74032851573392359915132451)
  ·
    refine ⟨111049277360088539872698677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74032851573392359915132451 111049277360088539872698677)
    ·
      refine ⟨10410869752508300613065501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111049277360088539872698677 10410869752508300613065501)
      ·
        refine ⟨3904076157190612729899563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10410869752508300613065501 3904076157190612729899563)
        ·
          refine ⟨5856114235785919094849345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3904076157190612729899563 5856114235785919094849345)
          ·
            refine ⟨4392085676839439321137009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5856114235785919094849345 4392085676839439321137009)
            ·
              refine ⟨3294064257629579490852757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4392085676839439321137009 3294064257629579490852757)
              ·
                refine ⟨154409262076386538633723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3294064257629579490852757 154409262076386538633723)
                ·
                  rfl

theorem cell21_2029799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 6].length) (baseStart_2029799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029799 prefixEnd_2029799 := by exact prefixLift 2029799
  have htrace : WordTrace (prefixWord ++ tailWord_2029799) baseStart_2029799 baseEnd_2029799 := by
    simpa [prefixWord, tailWord_2029799, baseEnd_2029799] using wordTrace_append hprefix tailTrace_2029799
  have hstable : (prefixWord ++ tailWord_2029799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029799).length < 2 ^ (prefixWord ++ tailWord_2029799).sum := by decide
  have hdescent : baseEnd_2029799 < baseStart_2029799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029841 : List Nat := [1, 2, 2, 1, 1, 14]
def baseStart_2029841 : Nat := 118140960795 + 2029841 * 2 ^ 59
def prefixEnd_2029841 : Nat := 4983230072969 + 3 ^ 40 * 2029841 * 2
def baseEnd_2029841 : Nat := 17156939674125069488929

theorem tailTrace_2029841 : CollatzResearch.WordTrace tailWord_2029841 prefixEnd_2029841 17156939674125069488929 := by
  unfold tailWord_2029841
  simp only [CollatzResearch.WordTrace]
  refine ⟨74034383439240201088161377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49356255626160134058774251 74034383439240201088161377)
  ·
    refine ⟨55525787579430150816121033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74034383439240201088161377 55525787579430150816121033)
    ·
      refine ⟨41644340684572613112090775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55525787579430150816121033 41644340684572613112090775)
      ·
        refine ⟨62466511026858919668136163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41644340684572613112090775 62466511026858919668136163)
        ·
          refine ⟨93699766540288379502204245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62466511026858919668136163 93699766540288379502204245)
          ·
            refine ⟨17156939674125069488929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 93699766540288379502204245 17156939674125069488929)
            ·
              rfl

theorem cell21_2029841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 14].length) (baseStart_2029841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029841 prefixEnd_2029841 := by exact prefixLift 2029841
  have htrace : WordTrace (prefixWord ++ tailWord_2029841) baseStart_2029841 baseEnd_2029841 := by
    simpa [prefixWord, tailWord_2029841, baseEnd_2029841] using wordTrace_append hprefix tailTrace_2029841
  have hstable : (prefixWord ++ tailWord_2029841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029841).length < 2 ^ (prefixWord ++ tailWord_2029841).sum := by decide
  have hdescent : baseEnd_2029841 < baseStart_2029841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029847 : List Nat := [1, 1, 3, 4, 1, 2, 4, 2, 3]
def baseStart_2029847 : Nat := 118140960795 + 2029847 * 2 ^ 59
def prefixEnd_2029847 : Nat := 4983230072969 + 3 ^ 40 * 2029847 * 2
def baseEnd_2029847 : Nat := 463238740483122199101071

theorem tailTrace_2029847 : CollatzResearch.WordTrace tailWord_2029847 prefixEnd_2029847 463238740483122199101071 := by
  unfold tailWord_2029847
  simp only [CollatzResearch.WordTrace]
  refine ⟨74034602277218464112879795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49356401518145642741919863 74034602277218464112879795)
  ·
    refine ⟨111051903415827696169319693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74034602277218464112879795 111051903415827696169319693)
    ·
      refine ⟨41644463780935386063494885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111051903415827696169319693 41644463780935386063494885)
      ·
        refine ⟨7808336958925384886905291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41644463780935386063494885 7808336958925384886905291)
        ·
          refine ⟨11712505438388077330357937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808336958925384886905291 11712505438388077330357937)
          ·
            refine ⟨8784379078791057997768453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11712505438388077330357937 8784379078791057997768453)
            ·
              refine ⟨1647071077273323374581585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8784379078791057997768453 1647071077273323374581585)
              ·
                refine ⟨1235303307954992530936189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647071077273323374581585 1235303307954992530936189)
                ·
                  refine ⟨463238740483122199101071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235303307954992530936189 463238740483122199101071)
                  ·
                    rfl

theorem cell21_2029847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 3].length) (baseStart_2029847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029847 prefixEnd_2029847 := by exact prefixLift 2029847
  have htrace : WordTrace (prefixWord ++ tailWord_2029847) baseStart_2029847 baseEnd_2029847 := by
    simpa [prefixWord, tailWord_2029847, baseEnd_2029847] using wordTrace_append hprefix tailTrace_2029847
  have hstable : (prefixWord ++ tailWord_2029847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029847).length < 2 ^ (prefixWord ++ tailWord_2029847).sum := by decide
  have hdescent : baseEnd_2029847 < baseStart_2029847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029903 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 4]
def baseStart_2029903 : Nat := 118140960795 + 2029903 * 2 ^ 59
def prefixEnd_2029903 : Nat := 4983230072969 + 3 ^ 40 * 2029903 * 2
def baseEnd_2029903 : Nat := 463251520446078546167623

theorem tailTrace_2029903 : CollatzResearch.WordTrace tailWord_2029903 prefixEnd_2029903 463251520446078546167623 := by
  unfold tailWord_2029903
  simp only [CollatzResearch.WordTrace]
  refine ⟨74036644765015585676918363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49357763176677057117945575 74036644765015585676918363)
  ·
    refine ⟨111054967147523378515377545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74036644765015585676918363 111054967147523378515377545)
    ·
      refine ⟨83291225360642533886533159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111054967147523378515377545 83291225360642533886533159)
      ·
        refine ⟨124936838040963800829799739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83291225360642533886533159 124936838040963800829799739)
        ·
          refine ⟨187405257061445701244699609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124936838040963800829799739 187405257061445701244699609)
          ·
            refine ⟨140553942796084275933524707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187405257061445701244699609 140553942796084275933524707)
            ·
              refine ⟨210830914194126413900287061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140553942796084275933524707 210830914194126413900287061)
              ·
                refine ⟨2470674775712418912893989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 210830914194126413900287061 2470674775712418912893989)
                ·
                  refine ⟨463251520446078546167623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470674775712418912893989 463251520446078546167623)
                  ·
                    rfl

theorem cell21_2029903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 4].length) (baseStart_2029903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029903 prefixEnd_2029903 := by exact prefixLift 2029903
  have htrace : WordTrace (prefixWord ++ tailWord_2029903) baseStart_2029903 baseEnd_2029903 := by
    simpa [prefixWord, tailWord_2029903, baseEnd_2029903] using wordTrace_append hprefix tailTrace_2029903
  have hstable : (prefixWord ++ tailWord_2029903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029903).length < 2 ^ (prefixWord ++ tailWord_2029903).sum := by decide
  have hdescent : baseEnd_2029903 < baseStart_2029903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029906 : List Nat := [3, 2, 2, 1, 1, 1, 4, 4, 3]
def baseStart_2029906 : Nat := 118140960795 + 2029906 * 2 ^ 59
def prefixEnd_2029906 : Nat := 4983230072969 + 3 ^ 40 * 2029906 * 2
def baseEnd_2029906 : Nat := 463252205086951207617617

theorem tailTrace_2029906 : CollatzResearch.WordTrace tailWord_2029906 prefixEnd_2029906 463252205086951207617617 := by
  unfold tailWord_2029906
  simp only [CollatzResearch.WordTrace]
  refine ⟨18509188546001179297319393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49357836122669811459518381 18509188546001179297319393)
  ·
    refine ⟨13881891409500884472989545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18509188546001179297319393 13881891409500884472989545)
    ·
      refine ⟨10411418557125663354742159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13881891409500884472989545 10411418557125663354742159)
      ·
        refine ⟨15617127835688495032113239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10411418557125663354742159 15617127835688495032113239)
        ·
          refine ⟨23425691753532742548169859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15617127835688495032113239 23425691753532742548169859)
          ·
            refine ⟨35138537630299113822254789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23425691753532742548169859 35138537630299113822254789)
            ·
              refine ⟨6588475805681083841672773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35138537630299113822254789 6588475805681083841672773)
              ·
                refine ⟨1235339213565203220313645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6588475805681083841672773 1235339213565203220313645)
                ·
                  refine ⟨463252205086951207617617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235339213565203220313645 463252205086951207617617)
                  ·
                    rfl

theorem cell21_2029906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_2029906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2029906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2029906 prefixEnd_2029906 := by exact prefixLift 2029906
  have htrace : WordTrace (prefixWord ++ tailWord_2029906) baseStart_2029906 baseEnd_2029906 := by
    simpa [prefixWord, tailWord_2029906, baseEnd_2029906] using wordTrace_append hprefix tailTrace_2029906
  have hstable : (prefixWord ++ tailWord_2029906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029906).length < 2 ^ (prefixWord ++ tailWord_2029906).sum := by decide
  have hdescent : baseEnd_2029906 < baseStart_2029906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030055 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 6]
def baseStart_2030055 : Nat := 118140960795 + 2030055 * 2 ^ 59
def prefixEnd_2030055 : Nat := 4983230072969 + 3 ^ 40 * 2030055 * 2
def baseEnd_2030055 : Nat := 463286208916960059633979

theorem tailTrace_2030055 : CollatzResearch.WordTrace tailWord_2030055 prefixEnd_2030055 463286208916960059633979 := by
  unfold tailWord_2030055
  simp only [CollatzResearch.WordTrace]
  refine ⟨74042188660464915636451619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49361459106976610424301079 74042188660464915636451619)
  ·
    refine ⟨111063282990697373454677429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74042188660464915636451619 111063282990697373454677429)
    ·
      refine ⟨10412182780377878761376009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111063282990697373454677429 10412182780377878761376009)
      ·
        refine ⟨7809137085283409071032007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10412182780377878761376009 7809137085283409071032007)
        ·
          refine ⟨11713705627925113606548011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809137085283409071032007 11713705627925113606548011)
          ·
            refine ⟨17570558441887670409822017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11713705627925113606548011 17570558441887670409822017)
            ·
              refine ⟨13177918831415752807366513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17570558441887670409822017 13177918831415752807366513)
              ·
                refine ⟨9883439123561814605524885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13177918831415752807366513 9883439123561814605524885)
                ·
                  refine ⟨463286208916960059633979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9883439123561814605524885 463286208916960059633979)
                  ·
                    rfl

theorem cell21_2030055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_2030055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030055 prefixEnd_2030055 := by exact prefixLift 2030055
  have htrace : WordTrace (prefixWord ++ tailWord_2030055) baseStart_2030055 baseEnd_2030055 := by
    simpa [prefixWord, tailWord_2030055, baseEnd_2030055] using wordTrace_append hprefix tailTrace_2030055
  have hstable : (prefixWord ++ tailWord_2030055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030055).length < 2 ^ (prefixWord ++ tailWord_2030055).sum := by decide
  have hdescent : baseEnd_2030055 < baseStart_2030055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030058 : List Nat := [3, 1, 3, 1, 3, 1, 1, 5, 3]
def baseStart_2030058 : Nat := 118140960795 + 2030058 * 2 ^ 59
def prefixEnd_2030058 : Nat := 4983230072969 + 3 ^ 40 * 2030058 * 2
def baseEnd_2030058 : Nat := 463286893557832721083973

theorem tailTrace_2030058 : CollatzResearch.WordTrace tailWord_2030058 prefixEnd_2030058 463286893557832721083973 := by
  unfold tailWord_2030058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18510574519863511787202707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49361532052969364765873885 18510574519863511787202707)
  ·
    refine ⟨27765861779795267680804061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18510574519863511787202707 27765861779795267680804061)
    ·
      refine ⟨10412198167423225380301523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27765861779795267680804061 10412198167423225380301523)
      ·
        refine ⟨15618297251134838070452285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10412198167423225380301523 15618297251134838070452285)
        ·
          refine ⟨5856861469175564276419607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15618297251134838070452285 5856861469175564276419607)
          ·
            refine ⟨8785292203763346414629411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856861469175564276419607 8785292203763346414629411)
            ·
              refine ⟨13177938305645019621944117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8785292203763346414629411 13177938305645019621944117)
              ·
                refine ⟨1235431716154220589557261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13177938305645019621944117 1235431716154220589557261)
                ·
                  refine ⟨463286893557832721083973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235431716154220589557261 463286893557832721083973)
                  ·
                    rfl

theorem cell21_2030058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_2030058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030058 prefixEnd_2030058 := by exact prefixLift 2030058
  have htrace : WordTrace (prefixWord ++ tailWord_2030058) baseStart_2030058 baseEnd_2030058 := by
    simpa [prefixWord, tailWord_2030058, baseEnd_2030058] using wordTrace_append hprefix tailTrace_2030058
  have hstable : (prefixWord ++ tailWord_2030058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030058).length < 2 ^ (prefixWord ++ tailWord_2030058).sum := by decide
  have hdescent : baseEnd_2030058 < baseStart_2030058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030103 : List Nat := [1, 1, 3, 6, 1, 1, 1, 7]
def baseStart_2030103 : Nat := 118140960795 + 2030103 * 2 ^ 59
def prefixEnd_2030103 : Nat := 4983230072969 + 3 ^ 40 * 2030103 * 2
def baseEnd_2030103 : Nat := 154432387723640880944627

theorem tailTrace_2030103 : CollatzResearch.WordTrace tailWord_2030103 prefixEnd_2030103 154432387723640880944627 := by
  unfold tailWord_2030103
  simp only [CollatzResearch.WordTrace]
  refine ⟨74043939364291019834198963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49362626242860679889465975 74043939364291019834198963)
  ·
    refine ⟨111065909046436529751298445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74043939364291019834198963 111065909046436529751298445)
    ·
      refine ⟨41649715892413698656736917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111065909046436529751298445 41649715892413698656736917)
      ·
        refine ⟨1952330432456892124534543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41649715892413698656736917 1952330432456892124534543)
        ·
          refine ⟨2928495648685338186801815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952330432456892124534543 2928495648685338186801815)
          ·
            refine ⟨4392743473028007280202723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928495648685338186801815 4392743473028007280202723)
            ·
              refine ⟨6589115209542010920304085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392743473028007280202723 6589115209542010920304085)
              ·
                refine ⟨154432387723640880944627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6589115209542010920304085 154432387723640880944627)
                ·
                  rfl

theorem cell21_2030103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 7].length) (baseStart_2030103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030103 prefixEnd_2030103 := by exact prefixLift 2030103
  have htrace : WordTrace (prefixWord ++ tailWord_2030103) baseStart_2030103 baseEnd_2030103 := by
    simpa [prefixWord, tailWord_2030103, baseEnd_2030103] using wordTrace_append hprefix tailTrace_2030103
  have hstable : (prefixWord ++ tailWord_2030103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030103).length < 2 ^ (prefixWord ++ tailWord_2030103).sum := by decide
  have hdescent : baseEnd_2030103 < baseStart_2030103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030131 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 4]
def baseStart_2030131 : Nat := 118140960795 + 2030131 * 2 ^ 59
def prefixEnd_2030131 : Nat := 4983230072969 + 3 ^ 40 * 2030131 * 2
def baseEnd_2030131 : Nat := 463303553152400816367157

theorem tailTrace_2030131 : CollatzResearch.WordTrace tailWord_2030131 prefixEnd_2030131 463303553152400816367157 := by
  unfold tailWord_2030131
  simp only [CollatzResearch.WordTrace]
  refine ⟨74044960608189580616218247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49363307072126387077478831 74044960608189580616218247)
  ·
    refine ⟨111067440912284370924327371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74044960608189580616218247 111067440912284370924327371)
    ·
      refine ⟨166601161368426556386491057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111067440912284370924327371 166601161368426556386491057)
      ·
        refine ⟨124950871026319917289868293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166601161368426556386491057 124950871026319917289868293)
        ·
          refine ⟨23428288317434984491850305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124950871026319917289868293 23428288317434984491850305)
          ·
            refine ⟨17571216238076238368887729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23428288317434984491850305 17571216238076238368887729)
            ·
              refine ⟨13178412178557178776665797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17571216238076238368887729 13178412178557178776665797)
              ·
                refine ⟨2470952283479471020624837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13178412178557178776665797 2470952283479471020624837)
                ·
                  refine ⟨463303553152400816367157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470952283479471020624837 463303553152400816367157)
                  ·
                    rfl

theorem cell21_2030131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 4].length) (baseStart_2030131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030131 prefixEnd_2030131 := by exact prefixLift 2030131
  have htrace : WordTrace (prefixWord ++ tailWord_2030131) baseStart_2030131 baseEnd_2030131 := by
    simpa [prefixWord, tailWord_2030131, baseEnd_2030131] using wordTrace_append hprefix tailTrace_2030131
  have hstable : (prefixWord ++ tailWord_2030131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030131).length < 2 ^ (prefixWord ++ tailWord_2030131).sum := by decide
  have hdescent : baseEnd_2030131 < baseStart_2030131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030134 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2030134 : Nat := 118140960795 + 2030134 * 2 ^ 59
def prefixEnd_2030134 : Nat := 4983230072969 + 3 ^ 40 * 2030134 * 2
def baseEnd_2030134 : Nat := 463304237793273477817151

theorem tailTrace_2030134 : CollatzResearch.WordTrace tailWord_2030134 prefixEnd_2030134 463304237793273477817151 := by
  unfold tailWord_2030134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627816876698669508036091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49363380018119141419051637 4627816876698669508036091)
  ·
    refine ⟨6941725315048004262054137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4627816876698669508036091 6941725315048004262054137)
    ·
      refine ⟨5206293986286003196540603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6941725315048004262054137 5206293986286003196540603)
      ·
        refine ⟨7809440979429004794810905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5206293986286003196540603 7809440979429004794810905)
        ·
          refine ⟨5857080734571753596108179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7809440979429004794810905 5857080734571753596108179)
          ·
            refine ⟨8785621101857630394162269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5857080734571753596108179 8785621101857630394162269)
            ·
              refine ⟨3294607913196611397810851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8785621101857630394162269 3294607913196611397810851)
              ·
                refine ⟨4941911869794917096716277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294607913196611397810851 4941911869794917096716277)
                ·
                  refine ⟨463304237793273477817151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4941911869794917096716277 463304237793273477817151)
                  ·
                    rfl

theorem cell21_2030134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2030134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030134 prefixEnd_2030134 := by exact prefixLift 2030134
  have htrace : WordTrace (prefixWord ++ tailWord_2030134) baseStart_2030134 baseEnd_2030134 := by
    simpa [prefixWord, tailWord_2030134, baseEnd_2030134] using wordTrace_append hprefix tailTrace_2030134
  have hstable : (prefixWord ++ tailWord_2030134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030134).length < 2 ^ (prefixWord ++ tailWord_2030134).sum := by decide
  have hdescent : baseEnd_2030134 < baseStart_2030134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030238 : List Nat := [4, 3, 1, 1, 1, 1, 10]
def baseStart_2030238 : Nat := 118140960795 + 2030238 * 2 ^ 59
def prefixEnd_2030238 : Nat := 4983230072969 + 3 ^ 40 * 2030238 * 2
def baseEnd_2030238 : Nat := 51480885778910267564845

theorem tailTrace_2030238 : CollatzResearch.WordTrace tailWord_2030238 prefixEnd_2030238 51480885778910267564845 := by
  unfold tailWord_2030238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9256107902350242236295421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49365908812534625260242245 9256107902350242236295421)
  ·
    refine ⟨3471040463381340838610783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9256107902350242236295421 3471040463381340838610783)
    ·
      refine ⟨5206560695072011257916175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3471040463381340838610783 5206560695072011257916175)
      ·
        refine ⟨7809841042608016886874263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5206560695072011257916175 7809841042608016886874263)
        ·
          refine ⟨11714761563912025330311395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809841042608016886874263 11714761563912025330311395)
          ·
            refine ⟨17572142345868037995467093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11714761563912025330311395 17572142345868037995467093)
            ·
              refine ⟨51480885778910267564845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17572142345868037995467093 51480885778910267564845)
              ·
                rfl

theorem cell21_2030238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 10].length) (baseStart_2030238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030238 prefixEnd_2030238 := by exact prefixLift 2030238
  have htrace : WordTrace (prefixWord ++ tailWord_2030238) baseStart_2030238 baseEnd_2030238 := by
    simpa [prefixWord, tailWord_2030238, baseEnd_2030238] using wordTrace_append hprefix tailTrace_2030238
  have hstable : (prefixWord ++ tailWord_2030238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030238).length < 2 ^ (prefixWord ++ tailWord_2030238).sum := by decide
  have hdescent : baseEnd_2030238 < baseStart_2030238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030241 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 4]
def baseStart_2030241 : Nat := 118140960795 + 2030241 * 2 ^ 59
def prefixEnd_2030241 : Nat := 4983230072969 + 3 ^ 40 * 2030241 * 2
def baseEnd_2030241 : Nat := 463328656651065069533599

theorem tailTrace_2030241 : CollatzResearch.WordTrace tailWord_2030241 prefixEnd_2030241 463328656651065069533599 := by
  unfold tailWord_2030241
  simp only [CollatzResearch.WordTrace]
  refine ⟨74048972637791069402722577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49365981758527379601815051 74048972637791069402722577)
  ·
    refine ⟨55536729478343302052041933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74048972637791069402722577 55536729478343302052041933)
    ·
      refine ⟨20826273554378738269515725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55536729478343302052041933 20826273554378738269515725)
      ·
        refine ⟨7809852582892026851068397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20826273554378738269515725 7809852582892026851068397)
        ·
          refine ⟨2928694718584510069150649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7809852582892026851068397 2928694718584510069150649)
          ·
            refine ⟨2196521038938382551862987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2928694718584510069150649 2196521038938382551862987)
            ·
              refine ⟨3294781558407573827794481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196521038938382551862987 3294781558407573827794481)
              ·
                refine ⟨2471086168805680370845861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3294781558407573827794481 2471086168805680370845861)
                ·
                  refine ⟨463328656651065069533599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2471086168805680370845861 463328656651065069533599)
                  ·
                    rfl

theorem cell21_2030241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_2030241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030241 prefixEnd_2030241 := by exact prefixLift 2030241
  have htrace : WordTrace (prefixWord ++ tailWord_2030241) baseStart_2030241 baseEnd_2030241 := by
    simpa [prefixWord, tailWord_2030241, baseEnd_2030241] using wordTrace_append hprefix tailTrace_2030241
  have hstable : (prefixWord ++ tailWord_2030241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030241).length < 2 ^ (prefixWord ++ tailWord_2030241).sum := by decide
  have hdescent : baseEnd_2030241 < baseStart_2030241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030278 : List Nat := [6, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2030278 : Nat := 118140960795 + 2030278 * 2 ^ 59
def prefixEnd_2030278 : Nat := 4983230072969 + 3 ^ 40 * 2030278 * 2
def baseEnd_2030278 : Nat := 463337100555161227416857

theorem tailTrace_2030278 : CollatzResearch.WordTrace tailWord_2030278 prefixEnd_2030278 463337100555161227416857 := by
  unfold tailWord_2030278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314072566833032022556859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49366881425771349814546325 2314072566833032022556859)
  ·
    refine ⟨3471108850249548033835289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2314072566833032022556859 3471108850249548033835289)
    ·
      refine ⟨2603331637687161025376467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3471108850249548033835289 2603331637687161025376467)
      ·
        refine ⟨3904997456530741538064701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603331637687161025376467 3904997456530741538064701)
        ·
          refine ⟨1464374046199028076774263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3904997456530741538064701 1464374046199028076774263)
          ·
            refine ⟨2196561069298542115161395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464374046199028076774263 2196561069298542115161395)
            ·
              refine ⟨3294841603947813172742093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196561069298542115161395 3294841603947813172742093)
              ·
                refine ⟨1235565601480429939778285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3294841603947813172742093 1235565601480429939778285)
                ·
                  refine ⟨463337100555161227416857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235565601480429939778285 463337100555161227416857)
                  ·
                    rfl

theorem cell21_2030278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2030278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030278 prefixEnd_2030278 := by exact prefixLift 2030278
  have htrace : WordTrace (prefixWord ++ tailWord_2030278) baseStart_2030278 baseEnd_2030278 := by
    simpa [prefixWord, tailWord_2030278, baseEnd_2030278] using wordTrace_append hprefix tailTrace_2030278
  have hstable : (prefixWord ++ tailWord_2030278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030278).length < 2 ^ (prefixWord ++ tailWord_2030278).sum := by decide
  have hdescent : baseEnd_2030278 < baseStart_2030278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030286 : List Nat := [4, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_2030286 : Nat := 118140960795 + 2030286 * 2 ^ 59
def prefixEnd_2030286 : Nat := 4983230072969 + 3 ^ 40 * 2030286 * 2
def baseEnd_2030286 : Nat := 463338926264154991283507

theorem tailTrace_2030286 : CollatzResearch.WordTrace tailWord_2030286 prefixEnd_2030286 463338926264154991283507 := by
  unfold tailWord_2030286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9256326740328505261013839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49367075948418694725407141 9256326740328505261013839)
  ·
    refine ⟨13884490110492757891520759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9256326740328505261013839 13884490110492757891520759)
    ·
      refine ⟨20826735165739136837281139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13884490110492757891520759 20826735165739136837281139)
      ·
        refine ⟨31240102748608705255921709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20826735165739136837281139 31240102748608705255921709)
        ·
          refine ⟨11715038530728264470970641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31240102748608705255921709 11715038530728264470970641)
          ·
            refine ⟨8786278898046198353227981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11715038530728264470970641 8786278898046198353227981)
            ·
              refine ⟨3294854586767324382460493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8786278898046198353227981 3294854586767324382460493)
              ·
                refine ⟨1235570470037746643422685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3294854586767324382460493 1235570470037746643422685)
                ·
                  refine ⟨463338926264154991283507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235570470037746643422685 463338926264154991283507)
                  ·
                    rfl

theorem cell21_2030286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_2030286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030286 prefixEnd_2030286 := by exact prefixLift 2030286
  have htrace : WordTrace (prefixWord ++ tailWord_2030286) baseStart_2030286 baseEnd_2030286 := by
    simpa [prefixWord, tailWord_2030286, baseEnd_2030286] using wordTrace_append hprefix tailTrace_2030286
  have hstable : (prefixWord ++ tailWord_2030286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030286).length < 2 ^ (prefixWord ++ tailWord_2030286).sum := by decide
  have hdescent : baseEnd_2030286 < baseStart_2030286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030300 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 6]
def baseStart_2030300 : Nat := 118140960795 + 2030300 * 2 ^ 59
def prefixEnd_2030300 : Nat := 4983230072969 + 3 ^ 40 * 2030300 * 2
def baseEnd_2030300 : Nat := 463342121254894078050145

theorem tailTrace_2030300 : CollatzResearch.WordTrace tailWord_2030300 prefixEnd_2030300 463342121254894078050145 := by
  unfold tailWord_2030300
  simp only [CollatzResearch.WordTrace]
  refine ⟨37025562272288661239560177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49367416363051548319413569 37025562272288661239560177)
  ·
    refine ⟨27769171704216495929670133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37025562272288661239560177 27769171704216495929670133)
    ·
      refine ⟨2603359847270296493406575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27769171704216495929670133 2603359847270296493406575)
      ·
        refine ⟨3905039770905444740109863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603359847270296493406575 3905039770905444740109863)
        ·
          refine ⟨5857559656358167110164795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3905039770905444740109863 5857559656358167110164795)
          ·
            refine ⟨8786339484537250665247193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5857559656358167110164795 8786339484537250665247193)
            ·
              refine ⟨6589754613402937998935395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8786339484537250665247193 6589754613402937998935395)
              ·
                refine ⟨9884631920104406998403093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6589754613402937998935395 9884631920104406998403093)
                ·
                  refine ⟨463342121254894078050145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9884631920104406998403093 463342121254894078050145)
                  ·
                    rfl

theorem cell21_2030300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_2030300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030300 prefixEnd_2030300 := by exact prefixLift 2030300
  have htrace : WordTrace (prefixWord ++ tailWord_2030300) baseStart_2030300 baseEnd_2030300 := by
    simpa [prefixWord, tailWord_2030300, baseEnd_2030300] using wordTrace_append hprefix tailTrace_2030300
  have hstable : (prefixWord ++ tailWord_2030300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030300).length < 2 ^ (prefixWord ++ tailWord_2030300).sum := by decide
  have hdescent : baseEnd_2030300 < baseStart_2030300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030421 : List Nat := [1, 3, 2, 2, 2, 1, 1, 6, 3]
def baseStart_2030421 : Nat := 118140960795 + 2030421 * 2 ^ 59
def prefixEnd_2030421 : Nat := 4983230072969 + 3 ^ 40 * 2030421 * 2
def baseEnd_2030421 : Nat := 463369735103424756533231

theorem tailTrace_2030421 : CollatzResearch.WordTrace tailWord_2030421 prefixEnd_2030421 463369735103424756533231 := by
  unfold tailWord_2030421
  simp only [CollatzResearch.WordTrace]
  refine ⟨74055537777138960144275117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49370358518092640096183411 74055537777138960144275117)
  ·
    refine ⟨27770826666427110054103169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74055537777138960144275117 27770826666427110054103169)
    ·
      refine ⟨20828119999820332540577377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27770826666427110054103169 20828119999820332540577377)
      ·
        refine ⟨15621089999865249405433033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20828119999820332540577377 15621089999865249405433033)
        ·
          refine ⟨11715817499898937054074775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15621089999865249405433033 11715817499898937054074775)
          ·
            refine ⟨17573726249848405581112163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11715817499898937054074775 17573726249848405581112163)
            ·
              refine ⟨26360589374772608371668245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17573726249848405581112163 26360589374772608371668245)
              ·
                refine ⟨1235652626942466017421949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26360589374772608371668245 1235652626942466017421949)
                ·
                  refine ⟨463369735103424756533231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235652626942466017421949 463369735103424756533231)
                  ·
                    rfl

theorem cell21_2030421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_2030421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030421 prefixEnd_2030421 := by exact prefixLift 2030421
  have htrace : WordTrace (prefixWord ++ tailWord_2030421) baseStart_2030421 baseEnd_2030421 := by
    simpa [prefixWord, tailWord_2030421, baseEnd_2030421] using wordTrace_append hprefix tailTrace_2030421
  have hstable : (prefixWord ++ tailWord_2030421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030421).length < 2 ^ (prefixWord ++ tailWord_2030421).sum := by decide
  have hdescent : baseEnd_2030421 < baseStart_2030421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030449 : List Nat := [1, 2, 2, 2, 1, 5, 1, 7]
def baseStart_2030449 : Nat := 118140960795 + 2030449 * 2 ^ 59
def prefixEnd_2030449 : Nat := 4983230072969 + 3 ^ 40 * 2030449 * 2
def baseEnd_2030449 : Nat := 154458708361634310022169

theorem tailTrace_2030449 : CollatzResearch.WordTrace tailWord_2030449 prefixEnd_2030449 154458708361634310022169 := by
  unfold tailWord_2030449
  simp only [CollatzResearch.WordTrace]
  refine ⟨74056559021037520926294401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49371039347358347284196267 74056559021037520926294401)
  ·
    refine ⟨55542419265778140694720801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74056559021037520926294401 55542419265778140694720801)
    ·
      refine ⟨41656814449333605521040601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55542419265778140694720801 41656814449333605521040601)
      ·
        refine ⟨31242610837000204140780451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41656814449333605521040601 31242610837000204140780451)
        ·
          refine ⟨46863916255500306211170677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31242610837000204140780451 46863916255500306211170677)
          ·
            refine ⟨4393492148953153707297251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46863916255500306211170677 4393492148953153707297251)
            ·
              refine ⟨6590238223429730560945877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4393492148953153707297251 6590238223429730560945877)
              ·
                refine ⟨154458708361634310022169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6590238223429730560945877 154458708361634310022169)
                ·
                  rfl

theorem cell21_2030449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 7].length) (baseStart_2030449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030449 prefixEnd_2030449 := by exact prefixLift 2030449
  have htrace : WordTrace (prefixWord ++ tailWord_2030449) baseStart_2030449 baseEnd_2030449 := by
    simpa [prefixWord, tailWord_2030449, baseEnd_2030449] using wordTrace_append hprefix tailTrace_2030449
  have hstable : (prefixWord ++ tailWord_2030449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030449).length < 2 ^ (prefixWord ++ tailWord_2030449).sum := by decide
  have hdescent : baseEnd_2030449 < baseStart_2030449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030463 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 7]
def baseStart_2030463 : Nat := 118140960795 + 2030463 * 2 ^ 59
def prefixEnd_2030463 : Nat := 4983230072969 + 3 ^ 40 * 2030463 * 2
def baseEnd_2030463 : Nat := 463379320075642016833145

theorem tailTrace_2030463 : CollatzResearch.WordTrace tailWord_2030463 prefixEnd_2030463 463379320075642016833145 := by
  unfold tailWord_2030463
  simp only [CollatzResearch.WordTrace]
  refine ⟨74057069642986801317304043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49371379761991200878202695 74057069642986801317304043)
  ·
    refine ⟨111085604464480201975956065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74057069642986801317304043 111085604464480201975956065)
    ·
      refine ⟨83314203348360151481967049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111085604464480201975956065 83314203348360151481967049)
      ·
        refine ⟨62485652511270113611475287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83314203348360151481967049 62485652511270113611475287)
        ·
          refine ⟨93728478766905170417212931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62485652511270113611475287 93728478766905170417212931)
          ·
            refine ⟨140592718150357755625819397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93728478766905170417212931 140592718150357755625819397)
            ·
              refine ⟨26361134653192079179841137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140592718150357755625819397 26361134653192079179841137)
              ·
                refine ⟨19770850989894059384880853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26361134653192079179841137 19770850989894059384880853)
                ·
                  refine ⟨463379320075642016833145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19770850989894059384880853 463379320075642016833145)
                  ·
                    rfl

theorem cell21_2030463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_2030463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030463 prefixEnd_2030463 := by exact prefixLift 2030463
  have htrace : WordTrace (prefixWord ++ tailWord_2030463) baseStart_2030463 baseEnd_2030463 := by
    simpa [prefixWord, tailWord_2030463, baseEnd_2030463] using wordTrace_append hprefix tailTrace_2030463
  have hstable : (prefixWord ++ tailWord_2030463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030463).length < 2 ^ (prefixWord ++ tailWord_2030463).sum := by decide
  have hdescent : baseEnd_2030463 < baseStart_2030463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030486 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2030486 : Nat := 118140960795 + 2030486 * 2 ^ 59
def prefixEnd_2030486 : Nat := 4983230072969 + 3 ^ 40 * 2030486 * 2
def baseEnd_2030486 : Nat := 463384568988999087949765

theorem tailTrace_2030486 : CollatzResearch.WordTrace tailWord_2030486 prefixEnd_2030486 463384568988999087949765 := by
  unfold tailWord_2030486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4628619282618967265336957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49371939014602317496927541 4628619282618967265336957)
  ·
    refine ⟨1735732230982112724501359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4628619282618967265336957 1735732230982112724501359)
    ·
      refine ⟨2603598346473169086752039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735732230982112724501359 2603598346473169086752039)
      ·
        refine ⟨3905397519709753630128059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603598346473169086752039 3905397519709753630128059)
        ·
          refine ⟨5858096279564630445192089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3905397519709753630128059 5858096279564630445192089)
          ·
            refine ⟨4393572209673472833894067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5858096279564630445192089 4393572209673472833894067)
            ·
              refine ⟨6590358314510209250841101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4393572209673472833894067 6590358314510209250841101)
              ·
                refine ⟨2471384367941328469065413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6590358314510209250841101 2471384367941328469065413)
                ·
                  refine ⟨463384568988999087949765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2471384367941328469065413 463384568988999087949765)
                  ·
                    rfl

theorem cell21_2030486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2030486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030486 prefixEnd_2030486 := by exact prefixLift 2030486
  have htrace : WordTrace (prefixWord ++ tailWord_2030486) baseStart_2030486 baseEnd_2030486 := by
    simpa [prefixWord, tailWord_2030486, baseEnd_2030486] using wordTrace_append hprefix tailTrace_2030486
  have hstable : (prefixWord ++ tailWord_2030486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030486).length < 2 ^ (prefixWord ++ tailWord_2030486).sum := by decide
  have hdescent : baseEnd_2030486 < baseStart_2030486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030525 : List Nat := [1, 4, 1, 2, 4, 9]
def baseStart_2030525 : Nat := 118140960795 + 2030525 * 2 ^ 59
def prefixEnd_2030525 : Nat := 4983230072969 + 3 ^ 40 * 2030525 * 2
def baseEnd_2030525 : Nat := 17162721085938655066655

theorem tailTrace_2030525 : CollatzResearch.WordTrace tailWord_2030525 prefixEnd_2030525 17162721085938655066655 := by
  unfold tailWord_2030525
  simp only [CollatzResearch.WordTrace]
  refine ⟨74059330968762185906061029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49372887312508123937374019 74059330968762185906061029)
  ·
    refine ⟨13886124556642909857386443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74059330968762185906061029 13886124556642909857386443)
    ·
      refine ⟨20829186834964364786079665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13886124556642909857386443 20829186834964364786079665)
      ·
        refine ⟨15621890126223273589559749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20829186834964364786079665 15621890126223273589559749)
        ·
          refine ⟨2929104398666863798042453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15621890126223273589559749 2929104398666863798042453)
          ·
            refine ⟨17162721085938655066655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2929104398666863798042453 17162721085938655066655)
            ·
              rfl

theorem cell21_2030525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 9].length) (baseStart_2030525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030525 prefixEnd_2030525 := by exact prefixLift 2030525
  have htrace : WordTrace (prefixWord ++ tailWord_2030525) baseStart_2030525 baseEnd_2030525 := by
    simpa [prefixWord, tailWord_2030525, baseEnd_2030525] using wordTrace_append hprefix tailTrace_2030525
  have hstable : (prefixWord ++ tailWord_2030525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030525).length < 2 ^ (prefixWord ++ tailWord_2030525).sum := by decide
  have hdescent : baseEnd_2030525 < baseStart_2030525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030534 : List Nat := [6, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2030534 : Nat := 118140960795 + 2030534 * 2 ^ 59
def prefixEnd_2030534 : Nat := 4983230072969 + 3 ^ 40 * 2030534 * 2
def baseEnd_2030534 : Nat := 154465174414320557049889

theorem tailTrace_2030534 : CollatzResearch.WordTrace tailWord_2030534 prefixEnd_2030534 154465174414320557049889 := by
  unfold tailWord_2030534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314364350804049388848083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49373106150486386962092437 2314364350804049388848083)
  ·
    refine ⟨3471546526206074083272125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2314364350804049388848083 3471546526206074083272125)
    ·
      refine ⟨1301829947327277781227047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3471546526206074083272125 1301829947327277781227047)
      ·
        refine ⟨1952744920990916671840571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301829947327277781227047 1952744920990916671840571)
        ·
          refine ⟨2929117381486375007760857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952744920990916671840571 2929117381486375007760857)
          ·
            refine ⟨2196838036114781255820643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2929117381486375007760857 2196838036114781255820643)
            ·
              refine ⟨3295257054172171883730965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196838036114781255820643 3295257054172171883730965)
              ·
                refine ⟨154465174414320557049889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3295257054172171883730965 154465174414320557049889)
                ·
                  rfl

theorem cell21_2030534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2030534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030534 prefixEnd_2030534 := by exact prefixLift 2030534
  have htrace : WordTrace (prefixWord ++ tailWord_2030534) baseStart_2030534 baseEnd_2030534 := by
    simpa [prefixWord, tailWord_2030534, baseEnd_2030534] using wordTrace_append hprefix tailTrace_2030534
  have hstable : (prefixWord ++ tailWord_2030534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030534).length < 2 ^ (prefixWord ++ tailWord_2030534).sum := by decide
  have hdescent : baseEnd_2030534 < baseStart_2030534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030542 : List Nat := [4, 1, 1, 1, 2, 5, 1, 6]
def baseStart_2030542 : Nat := 118140960795 + 2030542 * 2 ^ 59
def prefixEnd_2030542 : Nat := 4983230072969 + 3 ^ 40 * 2030542 * 2
def baseEnd_2030542 : Nat := 154465782983985145005439

theorem tailTrace_2030542 : CollatzResearch.WordTrace tailWord_2030542 prefixEnd_2030542 154465782983985145005439 := by
  unfold tailWord_2030542
  simp only [CollatzResearch.WordTrace]
  refine ⟨9257493876212574726178735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49373300673133731872953253 9257493876212574726178735)
  ·
    refine ⟨13886240814318862089268103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9257493876212574726178735 13886240814318862089268103)
    ·
      refine ⟨20829361221478293133902155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13886240814318862089268103 20829361221478293133902155)
      ·
        refine ⟨31244041832217439700853233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20829361221478293133902155 31244041832217439700853233)
        ·
          refine ⟨23433031374163079775639925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31244041832217439700853233 23433031374163079775639925)
          ·
            refine ⟨2196846691327788728966243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23433031374163079775639925 2196846691327788728966243)
            ·
              refine ⟨3295270036991683093449365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196846691327788728966243 3295270036991683093449365)
              ·
                refine ⟨154465782983985145005439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3295270036991683093449365 154465782983985145005439)
                ·
                  rfl

theorem cell21_2030542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_2030542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030542 prefixEnd_2030542 := by exact prefixLift 2030542
  have htrace : WordTrace (prefixWord ++ tailWord_2030542) baseStart_2030542 baseEnd_2030542 := by
    simpa [prefixWord, tailWord_2030542, baseEnd_2030542] using wordTrace_append hprefix tailTrace_2030542
  have hstable : (prefixWord ++ tailWord_2030542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030542).length < 2 ^ (prefixWord ++ tailWord_2030542).sum := by decide
  have hdescent : baseEnd_2030542 < baseStart_2030542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030590 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2030590 : Nat := 118140960795 + 2030590 * 2 ^ 59
def prefixEnd_2030590 : Nat := 4983230072969 + 3 ^ 40 * 2030590 * 2
def baseEnd_2030590 : Nat := 463408303205918018216219

theorem tailTrace_2030590 : CollatzResearch.WordTrace tailWord_2030590 prefixEnd_2030590 463408303205918018216219 := by
  unfold tailWord_2030590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9257712714190837750897153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49374467809017801338118149 9257712714190837750897153)
  ·
    refine ⟨6943284535643128313172865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9257712714190837750897153 6943284535643128313172865)
    ·
      refine ⟨5207463401732346234879649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6943284535643128313172865 5207463401732346234879649)
      ·
        refine ⟨3905597551299259676159737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5207463401732346234879649 3905597551299259676159737)
        ·
          refine ⟨2929198163474444757119803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3905597551299259676159737 2929198163474444757119803)
          ·
            refine ⟨4393797245211667135679705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2929198163474444757119803 4393797245211667135679705)
            ·
              refine ⟨3295347933908750351759779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4393797245211667135679705 3295347933908750351759779)
              ·
                refine ⟨4943021900863125527639669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295347933908750351759779 4943021900863125527639669)
                ·
                  refine ⟨463408303205918018216219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4943021900863125527639669 463408303205918018216219)
                  ·
                    rfl

theorem cell21_2030590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2030590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030590 prefixEnd_2030590 := by exact prefixLift 2030590
  have htrace : WordTrace (prefixWord ++ tailWord_2030590) baseStart_2030590 baseEnd_2030590 := by
    simpa [prefixWord, tailWord_2030590, baseEnd_2030590] using wordTrace_append hprefix tailTrace_2030590
  have hstable : (prefixWord ++ tailWord_2030590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030590).length < 2 ^ (prefixWord ++ tailWord_2030590).sum := by decide
  have hdescent : baseEnd_2030590 < baseStart_2030590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030604 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 4]
def baseStart_2030604 : Nat := 118140960795 + 2030604 * 2 ^ 59
def prefixEnd_2030604 : Nat := 4983230072969 + 3 ^ 40 * 2030604 * 2
def baseEnd_2030604 : Nat := 463411498196657104982857

theorem tailTrace_2030604 : CollatzResearch.WordTrace tailWord_2030604 prefixEnd_2030604 463411498196657104982857 := by
  unfold tailWord_2030604
  simp only [CollatzResearch.WordTrace]
  refine ⟨37031106167737991199093433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49374808223650654932124577 37031106167737991199093433)
  ·
    refine ⟨27773329625803493399320075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37031106167737991199093433 27773329625803493399320075)
    ·
      refine ⟨41659994438705240098980113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27773329625803493399320075 41659994438705240098980113)
      ·
        refine ⟨31244995829028930074235085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41659994438705240098980113 31244995829028930074235085)
        ·
          refine ⟨11716873435885848777838157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31244995829028930074235085 11716873435885848777838157)
          ·
            refine ⟨4393827538457193291689309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11716873435885848777838157 4393827538457193291689309)
            ·
              refine ⟨1647685326921447484383491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4393827538457193291689309 1647685326921447484383491)
              ·
                refine ⟨2471527990382171226575237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647685326921447484383491 2471527990382171226575237)
                ·
                  refine ⟨463411498196657104982857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2471527990382171226575237 463411498196657104982857)
                  ·
                    rfl

theorem cell21_2030604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_2030604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030604 prefixEnd_2030604 := by exact prefixLift 2030604
  have htrace : WordTrace (prefixWord ++ tailWord_2030604) baseStart_2030604 baseEnd_2030604 := by
    simpa [prefixWord, tailWord_2030604, baseEnd_2030604] using wordTrace_append hprefix tailTrace_2030604
  have hstable : (prefixWord ++ tailWord_2030604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030604).length < 2 ^ (prefixWord ++ tailWord_2030604).sum := by decide
  have hdescent : baseEnd_2030604 < baseStart_2030604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030610 : List Nat := [3, 2, 5, 1, 2, 1, 2, 5]
def baseStart_2030610 : Nat := 118140960795 + 2030610 * 2 ^ 59
def prefixEnd_2030610 : Nat := 4983230072969 + 3 ^ 40 * 2030610 * 2
def baseEnd_2030610 : Nat := 154470955826134142627615

theorem tailTrace_2030610 : CollatzResearch.WordTrace tailWord_2030610 prefixEnd_2030610 154470955826134142627615 := by
  unfold tailWord_2030610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18515607793363561355726321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49374954115636163615270189 18515607793363561355726321)
  ·
    refine ⟨13886705845022671016794741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18515607793363561355726321 13886705845022671016794741)
    ·
      refine ⟨1301878672970875407824507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13886705845022671016794741 1301878672970875407824507)
      ·
        refine ⟨1952818009456313111736761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301878672970875407824507 1952818009456313111736761)
        ·
          refine ⟨1464613507092234833802571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1952818009456313111736761 1464613507092234833802571)
          ·
            refine ⟨2196920260638352250703857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464613507092234833802571 2196920260638352250703857)
            ·
              refine ⟨1647690195478764188027893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196920260638352250703857 1647690195478764188027893)
              ·
                refine ⟨154470955826134142627615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1647690195478764188027893 154470955826134142627615)
                ·
                  rfl

theorem cell21_2030610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_2030610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030610 prefixEnd_2030610 := by exact prefixLift 2030610
  have htrace : WordTrace (prefixWord ++ tailWord_2030610) baseStart_2030610 baseEnd_2030610 := by
    simpa [prefixWord, tailWord_2030610, baseEnd_2030610] using wordTrace_append hprefix tailTrace_2030610
  have hstable : (prefixWord ++ tailWord_2030610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030610).length < 2 ^ (prefixWord ++ tailWord_2030610).sum := by decide
  have hdescent : baseEnd_2030610 < baseStart_2030610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030624 : List Nat := [2, 1, 1, 7, 2, 1, 1, 3, 3]
def baseStart_2030624 : Nat := 118140960795 + 2030624 * 2 ^ 59
def prefixEnd_2030624 : Nat := 4983230072969 + 3 ^ 40 * 2030624 * 2
def baseEnd_2030624 : Nat := 463416062469141514649483

theorem tailTrace_2030624 : CollatzResearch.WordTrace tailWord_2030624 prefixEnd_2030624 463416062469141514649483 := by
  unfold tailWord_2030624
  simp only [CollatzResearch.WordTrace]
  refine ⟨37031470897701762906957463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49375294530269017209276617 37031470897701762906957463)
  ·
    refine ⟨55547206346552644360436195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37031470897701762906957463 55547206346552644360436195)
    ·
      refine ⟨83320809519828966540654293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55547206346552644360436195 83320809519828966540654293)
      ·
        refine ⟨1952831473120991403296585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 83320809519828966540654293 1952831473120991403296585)
        ·
          refine ⟨1464623604840743552472439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1952831473120991403296585 1464623604840743552472439)
          ·
            refine ⟨2196935407261115328708659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464623604840743552472439 2196935407261115328708659)
            ·
              refine ⟨3295403110891672993062989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196935407261115328708659 3295403110891672993062989)
              ·
                refine ⟨1235776166584377372398621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3295403110891672993062989 1235776166584377372398621)
                ·
                  refine ⟨463416062469141514649483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235776166584377372398621 463416062469141514649483)
                  ·
                    rfl

theorem cell21_2030624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 3].length) (baseStart_2030624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030624 prefixEnd_2030624 := by exact prefixLift 2030624
  have htrace : WordTrace (prefixWord ++ tailWord_2030624) baseStart_2030624 baseEnd_2030624 := by
    simpa [prefixWord, tailWord_2030624, baseEnd_2030624] using wordTrace_append hprefix tailTrace_2030624
  have hstable : (prefixWord ++ tailWord_2030624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030624).length < 2 ^ (prefixWord ++ tailWord_2030624).sum := by decide
  have hdescent : baseEnd_2030624 < baseStart_2030624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030649 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 5]
def baseStart_2030649 : Nat := 118140960795 + 2030649 * 2 ^ 59
def prefixEnd_2030649 : Nat := 4983230072969 + 3 ^ 40 * 2030649 * 2
def baseEnd_2030649 : Nat := 463421767809747026732765

theorem tailTrace_2030649 : CollatzResearch.WordTrace tailWord_2030649 prefixEnd_2030649 463421767809747026732765 := by
  unfold tailWord_2030649
  simp only [CollatzResearch.WordTrace]
  refine ⟨74063853620312955083575001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49375902413541970055716667 74063853620312955083575001)
  ·
    refine ⟨55547890215234716312681251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74063853620312955083575001 55547890215234716312681251)
    ·
      refine ⟨83321835322852074469021877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55547890215234716312681251 83321835322852074469021877)
      ·
        refine ⟨7811422061517381981470801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83321835322852074469021877 7811422061517381981470801)
        ·
          refine ⟨5858566546138036486103101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7811422061517381981470801 5858566546138036486103101)
          ·
            refine ⟨2196962454801763682288663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5858566546138036486103101 2196962454801763682288663)
            ·
              refine ⟨3295443682202645523432995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196962454801763682288663 3295443682202645523432995)
              ·
                refine ⟨4943165523303968285149493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295443682202645523432995 4943165523303968285149493)
                ·
                  refine ⟨463421767809747026732765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4943165523303968285149493 463421767809747026732765)
                  ·
                    rfl

theorem cell21_2030649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_2030649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030649 prefixEnd_2030649 := by exact prefixLift 2030649
  have htrace : WordTrace (prefixWord ++ tailWord_2030649) baseStart_2030649 baseEnd_2030649 := by
    simpa [prefixWord, tailWord_2030649, baseEnd_2030649] using wordTrace_append hprefix tailTrace_2030649
  have hstable : (prefixWord ++ tailWord_2030649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030649).length < 2 ^ (prefixWord ++ tailWord_2030649).sum := by decide
  have hdescent : baseEnd_2030649 < baseStart_2030649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030663 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 4]
def baseStart_2030663 : Nat := 118140960795 + 2030663 * 2 ^ 59
def prefixEnd_2030663 : Nat := 4983230072969 + 3 ^ 40 * 2030663 * 2
def baseEnd_2030663 : Nat := 463424962800486113499403

theorem tailTrace_2030663 : CollatzResearch.WordTrace tailWord_2030663 prefixEnd_2030663 463424962800486113499403 := by
  unfold tailWord_2030663
  simp only [CollatzResearch.WordTrace]
  refine ⟨74064364242262235474584643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49376242828174823649723095 74064364242262235474584643)
  ·
    refine ⟨111096546363393353211876965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74064364242262235474584643 111096546363393353211876965)
    ·
      refine ⟨20830602443136253727226931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111096546363393353211876965 20830602443136253727226931)
      ·
        refine ⟨31245903664704380590840397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20830602443136253727226931 31245903664704380590840397)
        ·
          refine ⟨11717213874264142721565149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31245903664704380590840397 11717213874264142721565149)
          ·
            refine ⟨4393955202849053520586931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11717213874264142721565149 4393955202849053520586931)
            ·
              refine ⟨6590932804273580280880397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4393955202849053520586931 6590932804273580280880397)
              ·
                refine ⟨2471599801602592605330149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6590932804273580280880397 2471599801602592605330149)
                ·
                  refine ⟨463424962800486113499403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2471599801602592605330149 463424962800486113499403)
                  ·
                    rfl

theorem cell21_2030663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 4].length) (baseStart_2030663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030663 prefixEnd_2030663 := by exact prefixLift 2030663
  have htrace : WordTrace (prefixWord ++ tailWord_2030663) baseStart_2030663 baseEnd_2030663 := by
    simpa [prefixWord, tailWord_2030663, baseEnd_2030663] using wordTrace_append hprefix tailTrace_2030663
  have hstable : (prefixWord ++ tailWord_2030663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030663).length < 2 ^ (prefixWord ++ tailWord_2030663).sum := by decide
  have hdescent : baseEnd_2030663 < baseStart_2030663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030756 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 4]
def baseStart_2030756 : Nat := 118140960795 + 2030756 * 2 ^ 59
def prefixEnd_2030756 : Nat := 4983230072969 + 3 ^ 40 * 2030756 * 2
def baseEnd_2030756 : Nat := 463446186667538618449213

theorem tailTrace_2030756 : CollatzResearch.WordTrace tailWord_2030756 prefixEnd_2030756 463446186667538618449213 := by
  unfold tailWord_2030756
  simp only [CollatzResearch.WordTrace]
  refine ⟨37033878115462656178860061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49378504153950208238480081 37033878115462656178860061)
  ·
    refine ⟨13887704293298496067072523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37033878115462656178860061 13887704293298496067072523)
    ·
      refine ⟨20831556439947744100608785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13887704293298496067072523 20831556439947744100608785)
      ·
        refine ⟨15623667329960808075456589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20831556439947744100608785 15623667329960808075456589)
        ·
          refine ⟨5858875248735303028296221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15623667329960808075456589 5858875248735303028296221)
          ·
            refine ⟨2197078218275738635611083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5858875248735303028296221 2197078218275738635611083)
            ·
              refine ⟨3295617327413607953416625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197078218275738635611083 3295617327413607953416625)
              ·
                refine ⟨2471712995560205965062469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3295617327413607953416625 2471712995560205965062469)
                ·
                  refine ⟨463446186667538618449213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2471712995560205965062469 463446186667538618449213)
                  ·
                    rfl

theorem cell21_2030756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_2030756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030756 prefixEnd_2030756 := by exact prefixLift 2030756
  have htrace : WordTrace (prefixWord ++ tailWord_2030756) baseStart_2030756 baseEnd_2030756 := by
    simpa [prefixWord, tailWord_2030756, baseEnd_2030756] using wordTrace_append hprefix tailTrace_2030756
  have hstable : (prefixWord ++ tailWord_2030756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030756).length < 2 ^ (prefixWord ++ tailWord_2030756).sum := by decide
  have hdescent : baseEnd_2030756 < baseStart_2030756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030767 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 5]
def baseStart_2030767 : Nat := 118140960795 + 2030767 * 2 ^ 59
def prefixEnd_2030767 : Nat := 4983230072969 + 3 ^ 40 * 2030767 * 2
def baseEnd_2030767 : Nat := 463448697017405043765857

theorem tailTrace_2030767 : CollatzResearch.WordTrace tailWord_2030767 prefixEnd_2030767 463448697017405043765857 := by
  unfold tailWord_2030767
  simp only [CollatzResearch.WordTrace]
  refine ⟨74068157433885461236370555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49378771622590307490913703 74068157433885461236370555)
  ·
    refine ⟨111102236150828191854555833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74068157433885461236370555 111102236150828191854555833)
    ·
      refine ⟨83326677113121143890916875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111102236150828191854555833 83326677113121143890916875)
      ·
        refine ⟨124990015669681715836375313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83326677113121143890916875 124990015669681715836375313)
        ·
          refine ⟨93742511752261286877281485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124990015669681715836375313 93742511752261286877281485)
          ·
            refine ⟨35153441907097982578980557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93742511752261286877281485 35153441907097982578980557)
            ·
              refine ⟨13182540715161743467117709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35153441907097982578980557 13182540715161743467117709)
              ·
                refine ⟨4943452768185653800169141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13182540715161743467117709 4943452768185653800169141)
                ·
                  refine ⟨463448697017405043765857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4943452768185653800169141 463448697017405043765857)
                  ·
                    rfl

theorem cell21_2030767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_2030767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030767 prefixEnd_2030767 := by exact prefixLift 2030767
  have htrace : WordTrace (prefixWord ++ tailWord_2030767) baseStart_2030767 baseEnd_2030767 := by
    simpa [prefixWord, tailWord_2030767, baseEnd_2030767] using wordTrace_append hprefix tailTrace_2030767
  have hstable : (prefixWord ++ tailWord_2030767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030767).length < 2 ^ (prefixWord ++ tailWord_2030767).sum := by decide
  have hdescent : baseEnd_2030767 < baseStart_2030767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030829 : List Nat := [1, 5, 1, 2, 2, 1, 1, 8]
def baseStart_2030829 : Nat := 118140960795 + 2030829 * 2 ^ 59
def prefixEnd_2030829 : Nat := 4983230072969 + 3 ^ 40 * 2030829 * 2
def baseEnd_2030829 : Nat := 154487615420702237910799

theorem tailTrace_2030829 : CollatzResearch.WordTrace tailWord_2030829 prefixEnd_2030829 154487615420702237910799 := by
  unfold tailWord_2030829
  simp only [CollatzResearch.WordTrace]
  refine ⟨74070418759660845825127541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49380279173107230550085027 74070418759660845825127541)
  ·
    refine ⟨6944101758718204296105707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74070418759660845825127541 6944101758718204296105707)
    ·
      refine ⟨10416152638077306444158561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6944101758718204296105707 10416152638077306444158561)
      ·
        refine ⟨7812114478557979833118921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10416152638077306444158561 7812114478557979833118921)
        ·
          refine ⟨5859085858918484874839191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7812114478557979833118921 5859085858918484874839191)
          ·
            refine ⟨8788628788377727312258787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5859085858918484874839191 8788628788377727312258787)
            ·
              refine ⟨13182943182566590968388181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8788628788377727312258787 13182943182566590968388181)
              ·
                refine ⟨154487615420702237910799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13182943182566590968388181 154487615420702237910799)
                ·
                  rfl

theorem cell21_2030829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 8].length) (baseStart_2030829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030829 prefixEnd_2030829 := by exact prefixLift 2030829
  have htrace : WordTrace (prefixWord ++ tailWord_2030829) baseStart_2030829 baseEnd_2030829 := by
    simpa [prefixWord, tailWord_2030829, baseEnd_2030829] using wordTrace_append hprefix tailTrace_2030829
  have hstable : (prefixWord ++ tailWord_2030829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030829).length < 2 ^ (prefixWord ++ tailWord_2030829).sum := by decide
  have hdescent : baseEnd_2030829 < baseStart_2030829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030936 : List Nat := [2, 1, 2, 2, 1, 1, 3, 6, 3]
def baseStart_2030936 : Nat := 118140960795 + 2030936 * 2 ^ 59
def prefixEnd_2030936 : Nat := 4983230072969 + 3 ^ 40 * 2030936 * 2
def baseEnd_2030936 : Nat := 463487265119898305448845

theorem tailTrace_2030936 : CollatzResearch.WordTrace tailWord_2030936 prefixEnd_2030936 463487265119898305448845 := by
  unfold tailWord_2030936
  simp only [CollatzResearch.WordTrace]
  refine ⟨37037160685136601549636331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49382880913515468732848441 37037160685136601549636331)
  ·
    refine ⟨55555741027704902324454497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37037160685136601549636331 55555741027704902324454497)
    ·
      refine ⟨41666805770778676743340873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55555741027704902324454497 41666805770778676743340873)
      ·
        refine ⟨31250104328084007557505655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41666805770778676743340873 31250104328084007557505655)
        ·
          refine ⟨46875156492126011336258483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31250104328084007557505655 46875156492126011336258483)
          ·
            refine ⟨70312734738189017004387725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46875156492126011336258483 70312734738189017004387725)
            ·
              refine ⟨26367275526820881376645397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70312734738189017004387725 26367275526820881376645397)
              ·
                refine ⟨1235966040319728814530253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26367275526820881376645397 1235966040319728814530253)
                ·
                  refine ⟨463487265119898305448845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235966040319728814530253 463487265119898305448845)
                  ·
                    rfl

theorem cell21_2030936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 3].length) (baseStart_2030936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2030936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2030936 prefixEnd_2030936 := by exact prefixLift 2030936
  have htrace : WordTrace (prefixWord ++ tailWord_2030936) baseStart_2030936 baseEnd_2030936 := by
    simpa [prefixWord, tailWord_2030936, baseEnd_2030936] using wordTrace_append hprefix tailTrace_2030936
  have hstable : (prefixWord ++ tailWord_2030936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030936).length < 2 ^ (prefixWord ++ tailWord_2030936).sum := by decide
  have hdescent : baseEnd_2030936 < baseStart_2030936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031071 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 5]
def baseStart_2031071 : Nat := 118140960795 + 2031071 * 2 ^ 59
def prefixEnd_2031071 : Nat := 4983230072969 + 3 ^ 40 * 2031071 * 2
def baseEnd_2031071 : Nat := 463518073959168070698569

theorem tailTrace_2031071 : CollatzResearch.WordTrace tailWord_2031071 prefixEnd_2031071 463518073959168070698569 := by
  unfold tailWord_2031071
  simp only [CollatzResearch.WordTrace]
  refine ⟨74079245224784121155437067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49386163483189414103624711 74079245224784121155437067)
  ·
    refine ⟨111118867837176181733155601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74079245224784121155437067 111118867837176181733155601)
    ·
      refine ⟨83339150877882136299866701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111118867837176181733155601 83339150877882136299866701)
      ·
        refine ⟨31252181579205801112450013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83339150877882136299866701 31252181579205801112450013)
        ·
          refine ⟨11719568092202175417168755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31252181579205801112450013 11719568092202175417168755)
          ·
            refine ⟨17579352138303263125753133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11719568092202175417168755 17579352138303263125753133)
            ·
              refine ⟨6592257051863723672157425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17579352138303263125753133 6592257051863723672157425)
              ·
                refine ⟨4944192788897792754118069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6592257051863723672157425 4944192788897792754118069)
                ·
                  refine ⟨463518073959168070698569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4944192788897792754118069 463518073959168070698569)
                  ·
                    rfl

theorem cell21_2031071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_2031071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031071 prefixEnd_2031071 := by exact prefixLift 2031071
  have htrace : WordTrace (prefixWord ++ tailWord_2031071) baseStart_2031071 baseEnd_2031071 := by
    simpa [prefixWord, tailWord_2031071, baseEnd_2031071] using wordTrace_append hprefix tailTrace_2031071
  have hstable : (prefixWord ++ tailWord_2031071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031071).length < 2 ^ (prefixWord ++ tailWord_2031071).sum := by decide
  have hdescent : baseEnd_2031071 < baseStart_2031071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031088 : List Nat := [2, 1, 1, 1, 3, 4, 1, 5, 3]
def baseStart_2031088 : Nat := 118140960795 + 2031088 * 2 ^ 59
def prefixEnd_2031088 : Nat := 4983230072969 + 3 ^ 40 * 2031088 * 2
def baseEnd_2031088 : Nat := 463521953590779818915201

theorem tailTrace_2031088 : CollatzResearch.WordTrace tailWord_2031088 prefixEnd_2031088 463521953590779818915201 := by
  unfold tailWord_2031088
  simp only [CollatzResearch.WordTrace]
  refine ⟨37039932632861266529402959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49386576843815022039203945 37039932632861266529402959)
  ·
    refine ⟨55559898949291899794104439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37039932632861266529402959 55559898949291899794104439)
    ·
      refine ⟨83339848423937849691156659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55559898949291899794104439 83339848423937849691156659)
      ·
        refine ⟨125009772635906774536734989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83339848423937849691156659 125009772635906774536734989)
        ·
          refine ⟨46878664738465040451275621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125009772635906774536734989 46878664738465040451275621)
          ·
            refine ⟨8789749638462195084614179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46878664738465040451275621 8789749638462195084614179)
            ·
              refine ⟨13184624457693292626921269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8789749638462195084614179 13184624457693292626921269)
              ·
                refine ⟨1236058542908746183773869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13184624457693292626921269 1236058542908746183773869)
                ·
                  refine ⟨463521953590779818915201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236058542908746183773869 463521953590779818915201)
                  ·
                    rfl

theorem cell21_2031088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 3].length) (baseStart_2031088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031088 prefixEnd_2031088 := by exact prefixLift 2031088
  have htrace : WordTrace (prefixWord ++ tailWord_2031088) baseStart_2031088 baseEnd_2031088 := by
    simpa [prefixWord, tailWord_2031088, baseEnd_2031088] using wordTrace_append hprefix tailTrace_2031088
  have hstable : (prefixWord ++ tailWord_2031088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031088).length < 2 ^ (prefixWord ++ tailWord_2031088).sum := by decide
  have hdescent : baseEnd_2031088 < baseStart_2031088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031178 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_2031178 : Nat := 118140960795 + 2031178 * 2 ^ 59
def prefixEnd_2031178 : Nat := 4983230072969 + 3 ^ 40 * 2031178 * 2
def baseEnd_2031178 : Nat := 463542492816959662415017

theorem tailTrace_2031178 : CollatzResearch.WordTrace tailWord_2031178 prefixEnd_2031178 463542492816959662415017 := by
  unfold tailWord_2031178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18520786958849119607395547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49388765223597652286388125 18520786958849119607395547)
  ·
    refine ⟨27781180438273679411093321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18520786958849119607395547 27781180438273679411093321)
    ·
      refine ⟨20835885328705259558319991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27781180438273679411093321 20835885328705259558319991)
      ·
        refine ⟨31253827993057889337479987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20835885328705259558319991 31253827993057889337479987)
        ·
          refine ⟨46880741989586834006219981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31253827993057889337479987 46880741989586834006219981)
          ·
            refine ⟨17580278246095062752332493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46880741989586834006219981 17580278246095062752332493)
            ·
              refine ⟨6592604342285648532124685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17580278246095062752332493 6592604342285648532124685)
              ·
                refine ⟨2472226628357118199546757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6592604342285648532124685 2472226628357118199546757)
                ·
                  refine ⟨463542492816959662415017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2472226628357118199546757 463542492816959662415017)
                  ·
                    rfl

theorem cell21_2031178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_2031178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031178 prefixEnd_2031178 := by exact prefixLift 2031178
  have htrace : WordTrace (prefixWord ++ tailWord_2031178) baseStart_2031178 baseEnd_2031178 := by
    simpa [prefixWord, tailWord_2031178, baseEnd_2031178] using wordTrace_append hprefix tailTrace_2031178
  have hstable : (prefixWord ++ tailWord_2031178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031178).length < 2 ^ (prefixWord ++ tailWord_2031178).sum := by decide
  have hdescent : baseEnd_2031178 < baseStart_2031178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031268 : List Nat := [2, 3, 1, 2, 2, 3, 8]
def baseStart_2031268 : Nat := 118140960795 + 2031268 * 2 ^ 59
def prefixEnd_2031268 : Nat := 4983230072969 + 3 ^ 40 * 2031268 * 2
def baseEnd_2031268 : Nat := 51507003560348833990537

theorem tailTrace_2031268 : CollatzResearch.WordTrace tailWord_2031268 prefixEnd_2031268 51507003560348833990537 := by
  unfold tailWord_2031268
  simp only [CollatzResearch.WordTrace]
  refine ⟨37043215202535211900179229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49390953603380282533572305 37043215202535211900179229)
  ·
    refine ⟨13891205700950704462567211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37043215202535211900179229 13891205700950704462567211)
    ·
      refine ⟨20836808551426056693850817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13891205700950704462567211 20836808551426056693850817)
      ·
        refine ⟨15627606413569542520388113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20836808551426056693850817 15627606413569542520388113)
        ·
          refine ⟨11720704810177156890291085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15627606413569542520388113 11720704810177156890291085)
          ·
            refine ⟨4395264303816433833859157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11720704810177156890291085 4395264303816433833859157)
            ·
              refine ⟨51507003560348833990537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4395264303816433833859157 51507003560348833990537)
              ·
                rfl

theorem cell21_2031268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 8].length) (baseStart_2031268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031268 prefixEnd_2031268 := by exact prefixLift 2031268
  have htrace : WordTrace (prefixWord ++ tailWord_2031268) baseStart_2031268 baseEnd_2031268 := by
    simpa [prefixWord, tailWord_2031268, baseEnd_2031268] using wordTrace_append hprefix tailTrace_2031268
  have hstable : (prefixWord ++ tailWord_2031268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031268).length < 2 ^ (prefixWord ++ tailWord_2031268).sum := by decide
  have hdescent : baseEnd_2031268 < baseStart_2031268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031313 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 6]
def baseStart_2031313 : Nat := 118140960795 + 2031313 * 2 ^ 59
def prefixEnd_2031313 : Nat := 4983230072969 + 3 ^ 40 * 2031313 * 2
def baseEnd_2031313 : Nat := 463573301656229427664741

theorem tailTrace_2031313 : CollatzResearch.WordTrace tailWord_2031313 prefixEnd_2031313 463573301656229427664741 := by
  unfold tailWord_2031313
  simp only [CollatzResearch.WordTrace]
  refine ⟨74088071689907396485746593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49392047793271597657164395 74088071689907396485746593)
  ·
    refine ⟨55566053767430547364309945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74088071689907396485746593 55566053767430547364309945)
    ·
      refine ⟨41674540325572910523232459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55566053767430547364309945 41674540325572910523232459)
      ·
        refine ⟨62511810488359365784848689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41674540325572910523232459 62511810488359365784848689)
        ·
          refine ⟨46883857866269524338636517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62511810488359365784848689 46883857866269524338636517)
          ·
            refine ⟨8790723349925535813494347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46883857866269524338636517 8790723349925535813494347)
            ·
              refine ⟨13186085024888303720241521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8790723349925535813494347 13186085024888303720241521)
              ·
                refine ⟨9889563768666227790181141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13186085024888303720241521 9889563768666227790181141)
                ·
                  refine ⟨463573301656229427664741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9889563768666227790181141 463573301656229427664741)
                  ·
                    rfl

theorem cell21_2031313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_2031313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031313 prefixEnd_2031313 := by exact prefixLift 2031313
  have htrace : WordTrace (prefixWord ++ tailWord_2031313) baseStart_2031313 baseEnd_2031313 := by
    simpa [prefixWord, tailWord_2031313, baseEnd_2031313] using wordTrace_append hprefix tailTrace_2031313
  have hstable : (prefixWord ++ tailWord_2031313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031313).length < 2 ^ (prefixWord ++ tailWord_2031313).sum := by decide
  have hdescent : baseEnd_2031313 < baseStart_2031313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031333 : List Nat := [1, 3, 1, 4, 1, 1, 5, 2, 3]
def baseStart_2031333 : Nat := 118140960795 + 2031333 * 2 ^ 59
def prefixEnd_2031333 : Nat := 4983230072969 + 3 ^ 40 * 2031333 * 2
def baseEnd_2031333 : Nat := 463577865928713837331367

theorem tailTrace_2031333 : CollatzResearch.WordTrace tailWord_2031333 prefixEnd_2031333 463577865928713837331367 := by
  unfold tailWord_2031333
  simp only [CollatzResearch.WordTrace]
  refine ⟨74088801149834939901474653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49392534099889959934316435 74088801149834939901474653)
  ·
    refine ⟨27783300431188102463052995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74088801149834939901474653 27783300431188102463052995)
    ·
      refine ⟨41674950646782153694579493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27783300431188102463052995 41674950646782153694579493)
      ·
        refine ⟨7814053246271653817733655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41674950646782153694579493 7814053246271653817733655)
        ·
          refine ⟨11721079869407480726600483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7814053246271653817733655 11721079869407480726600483)
          ·
            refine ⟨17581619804111221089900725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11721079869407480726600483 17581619804111221089900725)
            ·
              refine ⟨1648276856635426977178193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17581619804111221089900725 1648276856635426977178193)
              ·
                refine ⟨1236207642476570232883645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648276856635426977178193 1236207642476570232883645)
                ·
                  refine ⟨463577865928713837331367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236207642476570232883645 463577865928713837331367)
                  ·
                    rfl

theorem cell21_2031333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_2031333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031333 prefixEnd_2031333 := by exact prefixLift 2031333
  have htrace : WordTrace (prefixWord ++ tailWord_2031333) baseStart_2031333 baseEnd_2031333 := by
    simpa [prefixWord, tailWord_2031333, baseEnd_2031333] using wordTrace_append hprefix tailTrace_2031333
  have hstable : (prefixWord ++ tailWord_2031333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031333).length < 2 ^ (prefixWord ++ tailWord_2031333).sum := by decide
  have hdescent : baseEnd_2031333 < baseStart_2031333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031392 : List Nat := [2, 1, 1, 5, 1, 1, 3, 4, 3]
def baseStart_2031392 : Nat := 118140960795 + 2031392 * 2 ^ 59
def prefixEnd_2031392 : Nat := 4983230072969 + 3 ^ 40 * 2031392 * 2
def baseEnd_2031392 : Nat := 463591330532542845847913

theorem tailTrace_2031392 : CollatzResearch.WordTrace tailWord_2031392 prefixEnd_2031392 463591330532542845847913 := by
  unfold tailWord_2031392
  simp only [CollatzResearch.WordTrace]
  refine ⟨37045476528310596488936215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49393968704414128651914953 37045476528310596488936215)
  ·
    refine ⟨55568214792465894733404323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37045476528310596488936215 55568214792465894733404323)
    ·
      refine ⟨83352322188698842100106485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55568214792465894733404323 83352322188698842100106485)
      ·
        refine ⟨7814280205190516446884983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83352322188698842100106485 7814280205190516446884983)
        ·
          refine ⟨11721420307785774670327475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7814280205190516446884983 11721420307785774670327475)
          ·
            refine ⟨17582130461678662005491213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11721420307785774670327475 17582130461678662005491213)
            ·
              refine ⟨6593298923129498252059205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17582130461678662005491213 6593298923129498252059205)
              ·
                refine ⟨1236243548086780922261101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6593298923129498252059205 1236243548086780922261101)
                ·
                  refine ⟨463591330532542845847913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236243548086780922261101 463591330532542845847913)
                  ·
                    rfl

theorem cell21_2031392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 3].length) (baseStart_2031392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031392 prefixEnd_2031392 := by exact prefixLift 2031392
  have htrace : WordTrace (prefixWord ++ tailWord_2031392) baseStart_2031392 baseEnd_2031392 := by
    simpa [prefixWord, tailWord_2031392, baseEnd_2031392] using wordTrace_append hprefix tailTrace_2031392
  have hstable : (prefixWord ++ tailWord_2031392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031392).length < 2 ^ (prefixWord ++ tailWord_2031392).sum := by decide
  have hdescent : baseEnd_2031392 < baseStart_2031392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031434 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_2031434 : Nat := 118140960795 + 2031434 * 2 ^ 59
def prefixEnd_2031434 : Nat := 4983230072969 + 3 ^ 40 * 2031434 * 2
def baseEnd_2031434 : Nat := 463600915504760106147827

theorem tailTrace_2031434 : CollatzResearch.WordTrace tailWord_2031434 prefixEnd_2031434 463600915504760106147827 := by
  unfold tailWord_2031434
  simp only [CollatzResearch.WordTrace]
  refine ⟨18523121230617258537725339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49394989948312689433934237 18523121230617258537725339)
  ·
    refine ⟨27784681845925887806588009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18523121230617258537725339 27784681845925887806588009)
    ·
      refine ⟨20838511384444415854941007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27784681845925887806588009 20838511384444415854941007)
      ·
        refine ⟨31257767076666623782411511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20838511384444415854941007 31257767076666623782411511)
        ·
          refine ⟨46886650614999935673617267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31257767076666623782411511 46886650614999935673617267)
          ·
            refine ⟨70329975922499903510425901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46886650614999935673617267 70329975922499903510425901)
            ·
              refine ⟨26373740970937463816409713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70329975922499903510425901 26373740970937463816409713)
              ·
                refine ⟨19780305728203097862307285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26373740970937463816409713 19780305728203097862307285)
                ·
                  refine ⟨463600915504760106147827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19780305728203097862307285 463600915504760106147827)
                  ·
                    rfl

theorem cell21_2031434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_2031434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031434 prefixEnd_2031434 := by exact prefixLift 2031434
  have htrace : WordTrace (prefixWord ++ tailWord_2031434) baseStart_2031434 baseEnd_2031434 := by
    simpa [prefixWord, tailWord_2031434, baseEnd_2031434] using wordTrace_append hprefix tailTrace_2031434
  have hstable : (prefixWord ++ tailWord_2031434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031434).length < 2 ^ (prefixWord ++ tailWord_2031434).sum := by decide
  have hdescent : baseEnd_2031434 < baseStart_2031434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031437 : List Nat := [1, 6, 1, 2, 1, 2, 8]
def baseStart_2031437 : Nat := 118140960795 + 2031437 * 2 ^ 59
def prefixEnd_2031437 : Nat := 4983230072969 + 3 ^ 40 * 2031437 * 2
def baseEnd_2031437 : Nat := 51511288905070307510869

theorem tailTrace_2031437 : CollatzResearch.WordTrace tailWord_2031437 prefixEnd_2031437 51511288905070307510869 := by
  unfold tailWord_2031437
  simp only [CollatzResearch.WordTrace]
  refine ⟨74092594341458165663260565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49395062894305443775507043 74092594341458165663260565)
  ·
    refine ⟨3473090359755851515465339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74092594341458165663260565 3473090359755851515465339)
    ·
      refine ⟨5209635539633777273198009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3473090359755851515465339 5209635539633777273198009)
      ·
        refine ⟨3907226654725332954898507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5209635539633777273198009 3907226654725332954898507)
        ·
          refine ⟨5860839982087999432347761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907226654725332954898507 5860839982087999432347761)
          ·
            refine ⟨4395629986565999574260821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5860839982087999432347761 4395629986565999574260821)
            ·
              refine ⟨51511288905070307510869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4395629986565999574260821 51511288905070307510869)
              ·
                rfl

theorem cell21_2031437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 8].length) (baseStart_2031437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031437 prefixEnd_2031437 := by exact prefixLift 2031437
  have htrace : WordTrace (prefixWord ++ tailWord_2031437) baseStart_2031437 baseEnd_2031437 := by
    simpa [prefixWord, tailWord_2031437, baseEnd_2031437] using wordTrace_append hprefix tailTrace_2031437
  have hstable : (prefixWord ++ tailWord_2031437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031437).length < 2 ^ (prefixWord ++ tailWord_2031437).sum := by decide
  have hdescent : baseEnd_2031437 < baseStart_2031437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031465 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 4]
def baseStart_2031465 : Nat := 118140960795 + 2031465 * 2 ^ 59
def prefixEnd_2031465 : Nat := 4983230072969 + 3 ^ 40 * 2031465 * 2
def baseEnd_2031465 : Nat := 463607990127110941131097

theorem tailTrace_2031465 : CollatzResearch.WordTrace tailWord_2031465 prefixEnd_2031465 463607990127110941131097 := by
  unfold tailWord_2031465
  simp only [CollatzResearch.WordTrace]
  refine ⟨74093615585356726445279849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49395743723571150963519899 74093615585356726445279849)
  ·
    refine ⟨55570211689017544833959887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74093615585356726445279849 55570211689017544833959887)
    ·
      refine ⟨83355317533526317250939831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55570211689017544833959887 83355317533526317250939831)
      ·
        refine ⟨125032976300289475876409747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83355317533526317250939831 125032976300289475876409747)
        ·
          refine ⟨187549464450434213814614621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125032976300289475876409747 187549464450434213814614621)
          ·
            refine ⟨70331049168912830180480483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187549464450434213814614621 70331049168912830180480483)
            ·
              refine ⟨105496573753369245270720725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70331049168912830180480483 105496573753369245270720725)
              ·
                refine ⟨2472575947344591686032517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105496573753369245270720725 2472575947344591686032517)
                ·
                  refine ⟨463607990127110941131097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2472575947344591686032517 463607990127110941131097)
                  ·
                    rfl

theorem cell21_2031465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_2031465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031465 prefixEnd_2031465 := by exact prefixLift 2031465
  have htrace : WordTrace (prefixWord ++ tailWord_2031465) baseStart_2031465 baseEnd_2031465 := by
    simpa [prefixWord, tailWord_2031465, baseEnd_2031465] using wordTrace_append hprefix tailTrace_2031465
  have hstable : (prefixWord ++ tailWord_2031465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031465).length < 2 ^ (prefixWord ++ tailWord_2031465).sum := by decide
  have hdescent : baseEnd_2031465 < baseStart_2031465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031502 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_2031502 : Nat := 118140960795 + 2031502 * 2 ^ 59
def prefixEnd_2031502 : Nat := 4983230072969 + 3 ^ 40 * 2031502 * 2
def baseEnd_2031502 : Nat := 463616434031207099014355

theorem tailTrace_2031502 : CollatzResearch.WordTrace tailWord_2031502 prefixEnd_2031502 463616434031207099014355 := by
  unfold tailWord_2031502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9261870635777835220547095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49396643390815121176251173 9261870635777835220547095)
  ·
    refine ⟨13892805953666752830820643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9261870635777835220547095 13892805953666752830820643)
    ·
      refine ⟨20839208930500129246230965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13892805953666752830820643 20839208930500129246230965)
      ·
        refine ⟨1953675837234387116834153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20839208930500129246230965 1953675837234387116834153)
        ·
          refine ⟨1465256877925790337625615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1953675837234387116834153 1465256877925790337625615)
          ·
            refine ⟨2197885316888685506438423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465256877925790337625615 2197885316888685506438423)
            ·
              refine ⟨3296827975333028259657635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197885316888685506438423 3296827975333028259657635)
              ·
                refine ⟨4945241962999542389486453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296827975333028259657635 4945241962999542389486453)
                ·
                  refine ⟨463616434031207099014355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4945241962999542389486453 463616434031207099014355)
                  ·
                    rfl

theorem cell21_2031502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_2031502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031502 prefixEnd_2031502 := by exact prefixLift 2031502
  have htrace : WordTrace (prefixWord ++ tailWord_2031502) baseStart_2031502 baseEnd_2031502 := by
    simpa [prefixWord, tailWord_2031502, baseEnd_2031502] using wordTrace_append hprefix tailTrace_2031502
  have hstable : (prefixWord ++ tailWord_2031502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031502).length < 2 ^ (prefixWord ++ tailWord_2031502).sum := by decide
  have hdescent : baseEnd_2031502 < baseStart_2031502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031516 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 4]
def baseStart_2031516 : Nat := 118140960795 + 2031516 * 2 ^ 59
def prefixEnd_2031516 : Nat := 4983230072969 + 3 ^ 40 * 2031516 * 2
def baseEnd_2031516 : Nat := 463619629021946185780993

theorem tailTrace_2031516 : CollatzResearch.WordTrace tailWord_2031516 prefixEnd_2031516 463619629021946185780993 := by
  unfold tailWord_2031516
  simp only [CollatzResearch.WordTrace]
  refine ⟨37047737854085981077693201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49396983805447974770257601 37047737854085981077693201)
  ·
    refine ⟨27785803390564485808269901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37047737854085981077693201 27785803390564485808269901)
    ·
      refine ⟨10419676271461682178101213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27785803390564485808269901 10419676271461682178101213)
      ·
        refine ⟨3907378601798130816787955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10419676271461682178101213 3907378601798130816787955)
        ·
          refine ⟨5861067902697196225181933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907378601798130816787955 5861067902697196225181933)
          ·
            refine ⟨2197900463511448584443225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5861067902697196225181933 2197900463511448584443225)
            ·
              refine ⟨1648425347633586438332419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2197900463511448584443225 1648425347633586438332419)
              ·
                refine ⟨2472638021450379657498629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648425347633586438332419 2472638021450379657498629)
                ·
                  refine ⟨463619629021946185780993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2472638021450379657498629 463619629021946185780993)
                  ·
                    rfl

theorem cell21_2031516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_2031516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031516 prefixEnd_2031516 := by exact prefixLift 2031516
  have htrace : WordTrace (prefixWord ++ tailWord_2031516) baseStart_2031516 baseEnd_2031516 := by
    simpa [prefixWord, tailWord_2031516, baseEnd_2031516] using wordTrace_append hprefix tailTrace_2031516
  have hstable : (prefixWord ++ tailWord_2031516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031516).length < 2 ^ (prefixWord ++ tailWord_2031516).sum := by decide
  have hdescent : baseEnd_2031516 < baseStart_2031516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031617 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 6]
def baseStart_2031617 : Nat := 118140960795 + 2031617 * 2 ^ 59
def prefixEnd_2031617 : Nat := 4983230072969 + 3 ^ 40 * 2031617 * 2
def baseEnd_2031617 : Nat := 463642678597992454597453

theorem tailTrace_2031617 : CollatzResearch.WordTrace tailWord_2031617 prefixEnd_2031617 463642678597992454597453 := by
  unfold tailWord_2031617
  simp only [CollatzResearch.WordTrace]
  refine ⟨74099159480806056404813105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49399439653870704269875403 74099159480806056404813105)
  ·
    refine ⟨55574369610604542303609829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74099159480806056404813105 55574369610604542303609829)
    ·
      refine ⟨10420194301988351681926843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55574369610604542303609829 10420194301988351681926843)
      ·
        refine ⟨15630291452982527522890265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10420194301988351681926843 15630291452982527522890265)
        ·
          refine ⟨11722718589736895642167699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15630291452982527522890265 11722718589736895642167699)
          ·
            refine ⟨17584077884605343463251549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11722718589736895642167699 17584077884605343463251549)
            ·
              refine ⟨6594029206727003798719331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17584077884605343463251549 6594029206727003798719331)
              ·
                refine ⟨9891043810090505698078997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594029206727003798719331 9891043810090505698078997)
                ·
                  refine ⟨463642678597992454597453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9891043810090505698078997 463642678597992454597453)
                  ·
                    rfl

theorem cell21_2031617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_2031617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031617 prefixEnd_2031617 := by exact prefixLift 2031617
  have htrace : WordTrace (prefixWord ++ tailWord_2031617) baseStart_2031617 baseEnd_2031617 := by
    simpa [prefixWord, tailWord_2031617, baseEnd_2031617] using wordTrace_append hprefix tailTrace_2031617
  have hstable : (prefixWord ++ tailWord_2031617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031617).length < 2 ^ (prefixWord ++ tailWord_2031617).sum := by decide
  have hdescent : baseEnd_2031617 < baseStart_2031617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031679 : List Nat := [1, 1, 2, 2, 3, 1, 2, 6, 3]
def baseStart_2031679 : Nat := 118140960795 + 2031679 * 2 ^ 59
def prefixEnd_2031679 : Nat := 4983230072969 + 3 ^ 40 * 2031679 * 2
def baseEnd_2031679 : Nat := 463656827842694124563993

theorem tailTrace_2031679 : CollatzResearch.WordTrace tailWord_2031679 prefixEnd_2031679 463656827842694124563993 := by
  unfold tailWord_2031679
  simp only [CollatzResearch.WordTrace]
  refine ⟨74101420806581440993570091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49400947204387627329046727 74101420806581440993570091)
  ·
    refine ⟨111152131209872161490355137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74101420806581440993570091 111152131209872161490355137)
    ·
      refine ⟨83364098407404121117766353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111152131209872161490355137 83364098407404121117766353)
      ·
        refine ⟨62523073805553090838324765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83364098407404121117766353 62523073805553090838324765)
        ·
          refine ⟨23446152677082409064371787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62523073805553090838324765 23446152677082409064371787)
          ·
            refine ⟨35169229015623613596557681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23446152677082409064371787 35169229015623613596557681)
            ·
              refine ⟨26376921761717710197418261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35169229015623613596557681 26376921761717710197418261)
              ·
                refine ⟨1236418207580517665503981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26376921761717710197418261 1236418207580517665503981)
                ·
                  refine ⟨463656827842694124563993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236418207580517665503981 463656827842694124563993)
                  ·
                    rfl

theorem cell21_2031679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 3].length) (baseStart_2031679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031679 prefixEnd_2031679 := by exact prefixLift 2031679
  have htrace : WordTrace (prefixWord ++ tailWord_2031679) baseStart_2031679 baseEnd_2031679 := by
    simpa [prefixWord, tailWord_2031679, baseEnd_2031679] using wordTrace_append hprefix tailTrace_2031679
  have hstable : (prefixWord ++ tailWord_2031679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031679).length < 2 ^ (prefixWord ++ tailWord_2031679).sum := by decide
  have hdescent : baseEnd_2031679 < baseStart_2031679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031772 : List Nat := [2, 2, 3, 2, 1, 1, 4, 3, 3]
def baseStart_2031772 : Nat := 118140960795 + 2031772 * 2 ^ 59
def prefixEnd_2031772 : Nat := 4983230072969 + 3 ^ 40 * 2031772 * 2
def baseEnd_2031772 : Nat := 463678051709746629513803

theorem tailTrace_2031772 : CollatzResearch.WordTrace tailWord_2031772 prefixEnd_2031772 463678051709746629513803 := by
  unfold tailWord_2031772
  simp only [CollatzResearch.WordTrace]
  refine ⟨37052406397622258938352785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49403208530163011917803713 37052406397622258938352785)
  ·
    refine ⟨27789304798216694203764589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37052406397622258938352785 27789304798216694203764589)
    ·
      refine ⟨10420989299331260326411721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27789304798216694203764589 10420989299331260326411721)
      ·
        refine ⟨7815741974498445244808791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10420989299331260326411721 7815741974498445244808791)
        ·
          refine ⟨11723612961747667867213187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7815741974498445244808791 11723612961747667867213187)
          ·
            refine ⟨17585419442621501800819781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11723612961747667867213187 17585419442621501800819781)
            ·
              refine ⟨3297266145491531587653709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17585419442621501800819781 3297266145491531587653709)
              ·
                refine ⟨1236474804559324345370141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3297266145491531587653709 1236474804559324345370141)
                ·
                  refine ⟨463678051709746629513803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236474804559324345370141 463678051709746629513803)
                  ·
                    rfl

theorem cell21_2031772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_2031772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031772 prefixEnd_2031772 := by exact prefixLift 2031772
  have htrace : WordTrace (prefixWord ++ tailWord_2031772) baseStart_2031772 baseEnd_2031772 := by
    simpa [prefixWord, tailWord_2031772, baseEnd_2031772] using wordTrace_append hprefix tailTrace_2031772
  have hstable : (prefixWord ++ tailWord_2031772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031772).length < 2 ^ (prefixWord ++ tailWord_2031772).sum := by decide
  have hdescent : baseEnd_2031772 < baseStart_2031772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031845 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 6]
def baseStart_2031845 : Nat := 118140960795 + 2031845 * 2 ^ 59
def prefixEnd_2031845 : Nat := 4983230072969 + 3 ^ 40 * 2031845 * 2
def baseEnd_2031845 : Nat := 463694711304314724796987

theorem tailTrace_2031845 : CollatzResearch.WordTrace tailWord_2031845 prefixEnd_2031845 463694711304314724796987 := by
  unfold tailWord_2031845
  simp only [CollatzResearch.WordTrace]
  refine ⟨74107475323980051344112989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49404983549320034229408659 74107475323980051344112989)
  ·
    refine ⟨27790303246492519254042371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74107475323980051344112989 27790303246492519254042371)
    ·
      refine ⟨41685454869738778881063557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27790303246492519254042371 41685454869738778881063557)
      ·
        refine ⟨7816022788076021040199417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41685454869738778881063557 7816022788076021040199417)
        ·
          refine ⟨5862017091057015780149563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7816022788076021040199417 5862017091057015780149563)
          ·
            refine ⟨8793025636585523670224345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5862017091057015780149563 8793025636585523670224345)
            ·
              refine ⟨6594769227439142752668259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8793025636585523670224345 6594769227439142752668259)
              ·
                refine ⟨9892153841158714129002389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594769227439142752668259 9892153841158714129002389)
                ·
                  refine ⟨463694711304314724796987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9892153841158714129002389 463694711304314724796987)
                  ·
                    rfl

theorem cell21_2031845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_2031845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031845 prefixEnd_2031845 := by exact prefixLift 2031845
  have htrace : WordTrace (prefixWord ++ tailWord_2031845) baseStart_2031845 baseEnd_2031845 := by
    simpa [prefixWord, tailWord_2031845, baseEnd_2031845] using wordTrace_append hprefix tailTrace_2031845
  have hstable : (prefixWord ++ tailWord_2031845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031845).length < 2 ^ (prefixWord ++ tailWord_2031845).sum := by decide
  have hdescent : baseEnd_2031845 < baseStart_2031845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031859 : List Nat := [1, 1, 1, 2, 2, 4, 4, 6]
def baseStart_2031859 : Nat := 118140960795 + 2031859 * 2 ^ 59
def prefixEnd_2031859 : Nat := 4983230072969 + 3 ^ 40 * 2031859 * 2
def baseEnd_2031859 : Nat := 154565968765017937187875

theorem tailTrace_2031859 : CollatzResearch.WordTrace tailWord_2031859 prefixEnd_2031859 154565968765017937187875 := by
  unfold tailWord_2031859
  simp only [CollatzResearch.WordTrace]
  refine ⟨74107985945929331735122631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49405323963952887823415087 74107985945929331735122631)
  ·
    refine ⟨111161978918893997602683947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74107985945929331735122631 111161978918893997602683947)
    ·
      refine ⟨166742968378340996404025921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111161978918893997602683947 166742968378340996404025921)
      ·
        refine ⟨125057226283755747303019441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166742968378340996404025921 125057226283755747303019441)
        ·
          refine ⟨93792919712816810477264581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125057226283755747303019441 93792919712816810477264581)
          ·
            refine ⟨17586172446153151964487109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93792919712816810477264581 17586172446153151964487109)
            ·
              refine ⟨3297407333653715993341333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17586172446153151964487109 3297407333653715993341333)
              ·
                refine ⟨154565968765017937187875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3297407333653715993341333 154565968765017937187875)
                ·
                  rfl

theorem cell21_2031859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 6].length) (baseStart_2031859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031859 prefixEnd_2031859 := by exact prefixLift 2031859
  have htrace : WordTrace (prefixWord ++ tailWord_2031859) baseStart_2031859 baseEnd_2031859 := by
    simpa [prefixWord, tailWord_2031859, baseEnd_2031859] using wordTrace_append hprefix tailTrace_2031859
  have hstable : (prefixWord ++ tailWord_2031859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031859).length < 2 ^ (prefixWord ++ tailWord_2031859).sum := by decide
  have hdescent : baseEnd_2031859 < baseStart_2031859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031907 : List Nat := [1, 1, 1, 4, 2, 2, 3, 4, 3]
def baseStart_2031907 : Nat := 118140960795 + 2031907 * 2 ^ 59
def prefixEnd_2031907 : Nat := 4983230072969 + 3 ^ 40 * 2031907 * 2
def baseEnd_2031907 : Nat := 463708860549016394763527

theorem tailTrace_2031907 : CollatzResearch.WordTrace tailWord_2031907 prefixEnd_2031907 463708860549016394763527 := by
  unfold tailWord_2031907
  simp only [CollatzResearch.WordTrace]
  refine ⟨74109736649755435932869975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49406491099836957288579983 74109736649755435932869975)
  ·
    refine ⟨111164604974633153899304963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74109736649755435932869975 111164604974633153899304963)
    ·
      refine ⟨166746907461949730848957445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111164604974633153899304963 166746907461949730848957445)
      ·
        refine ⟨31265045149115574534179521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166746907461949730848957445 31265045149115574534179521)
        ·
          refine ⟨23448783861836680900634641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31265045149115574534179521 23448783861836680900634641)
          ·
            refine ⟨17586587896377510675475981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23448783861836680900634641 17586587896377510675475981)
            ·
              refine ⟨6594970461141566503303493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17586587896377510675475981 6594970461141566503303493)
              ·
                refine ⟨1236556961464043719369405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6594970461141566503303493 1236556961464043719369405)
                ·
                  refine ⟨463708860549016394763527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236556961464043719369405 463708860549016394763527)
                  ·
                    rfl

theorem cell21_2031907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 3].length) (baseStart_2031907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2031907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2031907 prefixEnd_2031907 := by exact prefixLift 2031907
  have htrace : WordTrace (prefixWord ++ tailWord_2031907) baseStart_2031907 baseEnd_2031907 := by
    simpa [prefixWord, tailWord_2031907, baseEnd_2031907] using wordTrace_append hprefix tailTrace_2031907
  have hstable : (prefixWord ++ tailWord_2031907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031907).length < 2 ^ (prefixWord ++ tailWord_2031907).sum := by decide
  have hdescent : baseEnd_2031907 < baseStart_2031907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032011 : List Nat := [1, 1, 1, 1, 4, 6, 7]
def baseStart_2032011 : Nat := 118140960795 + 2032011 * 2 ^ 59
def prefixEnd_2032011 : Nat := 4983230072969 + 3 ^ 40 * 2032011 * 2
def baseEnd_2032011 : Nat := 51525843862881702781109

theorem tailTrace_2032011 : CollatzResearch.WordTrace tailWord_2032011 prefixEnd_2032011 51525843862881702781109 := by
  unfold tailWord_2032011
  simp only [CollatzResearch.WordTrace]
  refine ⟨74113529841378661694655887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49409019894252441129770591 74113529841378661694655887)
  ·
    refine ⟨111170294762067992541983831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74113529841378661694655887 111170294762067992541983831)
    ·
      refine ⟨166755442143101988812975747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111170294762067992541983831 166755442143101988812975747)
      ·
        refine ⟨250133163214652983219463621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166755442143101988812975747 250133163214652983219463621)
        ·
          refine ⟨46899968102747434353649429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250133163214652983219463621 46899968102747434353649429)
          ·
            refine ⟨2198436004816285985327317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46899968102747434353649429 2198436004816285985327317)
            ·
              refine ⟨51525843862881702781109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2198436004816285985327317 51525843862881702781109)
              ·
                rfl

theorem cell21_2032011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 7].length) (baseStart_2032011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032011 prefixEnd_2032011 := by exact prefixLift 2032011
  have htrace : WordTrace (prefixWord ++ tailWord_2032011) baseStart_2032011 baseEnd_2032011 := by
    simpa [prefixWord, tailWord_2032011, baseEnd_2032011] using wordTrace_append hprefix tailTrace_2032011
  have hstable : (prefixWord ++ tailWord_2032011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032011).length < 2 ^ (prefixWord ++ tailWord_2032011).sum := by decide
  have hdescent : baseEnd_2032011 < baseStart_2032011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032076 : List Nat := [2, 2, 1, 4, 3, 1, 1, 4, 3]
def baseStart_2032076 : Nat := 118140960795 + 2032076 * 2 ^ 59
def prefixEnd_2032076 : Nat := 4983230072969 + 3 ^ 40 * 2032076 * 2
def baseEnd_2032076 : Nat := 463747428651509656446515

theorem tailTrace_2032076 : CollatzResearch.WordTrace tailWord_2032076 prefixEnd_2032076 463747428651509656446515 := by
  unfold tailWord_2032076
  simp only [CollatzResearch.WordTrace]
  refine ⟨37057950293071588897886041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49410600390762118530514721 37057950293071588897886041)
  ·
    refine ⟨27793462719803691673414531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37057950293071588897886041 27793462719803691673414531)
    ·
      refine ⟨41690194079705537510121797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27793462719803691673414531 41690194079705537510121797)
      ·
        refine ⟨7816911389944788283147837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41690194079705537510121797 7816911389944788283147837)
        ·
          refine ⟨2931341771229295606180439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7816911389944788283147837 2931341771229295606180439)
          ·
            refine ⟨4397012656843943409270659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931341771229295606180439 4397012656843943409270659)
            ·
              refine ⟨6595518985265915113905989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397012656843943409270659 6595518985265915113905989)
              ·
                refine ⟨1236659809737359083857373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6595518985265915113905989 1236659809737359083857373)
                ·
                  refine ⟨463747428651509656446515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236659809737359083857373 463747428651509656446515)
                  ·
                    rfl

theorem cell21_2032076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_2032076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032076 prefixEnd_2032076 := by exact prefixLift 2032076
  have htrace : WordTrace (prefixWord ++ tailWord_2032076) baseStart_2032076 baseEnd_2032076 := by
    simpa [prefixWord, tailWord_2032076, baseEnd_2032076] using wordTrace_append hprefix tailTrace_2032076
  have hstable : (prefixWord ++ tailWord_2032076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032076).length < 2 ^ (prefixWord ++ tailWord_2032076).sum := by decide
  have hdescent : baseEnd_2032076 < baseStart_2032076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032104 : List Nat := [2, 1, 4, 1, 1, 4, 3, 5]
def baseStart_2032104 : Nat := 118140960795 + 2032104 * 2 ^ 59
def prefixEnd_2032104 : Nat := 4983230072969 + 3 ^ 40 * 2032104 * 2
def baseEnd_2032104 : Nat := 154584606210995943326597

theorem tailTrace_2032104 : CollatzResearch.WordTrace tailWord_2032104 prefixEnd_2032104 154584606210995943326597 := by
  unfold tailWord_2032104
  simp only [CollatzResearch.WordTrace]
  refine ⟨37058460915020869288895683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49411281220027825718527577 37058460915020869288895683)
  ·
    refine ⟨55587691372531303933343525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37058460915020869288895683 55587691372531303933343525)
    ·
      refine ⟨10422692132349619487501911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55587691372531303933343525 10422692132349619487501911)
      ·
        refine ⟨15634038198524429231252867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10422692132349619487501911 15634038198524429231252867)
        ·
          refine ⟨23451057297786643846879301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15634038198524429231252867 23451057297786643846879301)
          ·
            refine ⟨4397073243334995721289869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23451057297786643846879301 4397073243334995721289869)
            ·
              refine ⟨1648902466250623395483701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4397073243334995721289869 1648902466250623395483701)
              ·
                refine ⟨154584606210995943326597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1648902466250623395483701 154584606210995943326597)
                ·
                  rfl

theorem cell21_2032104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_2032104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032104 prefixEnd_2032104 := by exact prefixLift 2032104
  have htrace : WordTrace (prefixWord ++ tailWord_2032104) baseStart_2032104 baseEnd_2032104 := by
    simpa [prefixWord, tailWord_2032104, baseEnd_2032104] using wordTrace_append hprefix tailTrace_2032104
  have hstable : (prefixWord ++ tailWord_2032104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032104).length < 2 ^ (prefixWord ++ tailWord_2032104).sum := by decide
  have hdescent : baseEnd_2032104 < baseStart_2032104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032118 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_2032118 : Nat := 118140960795 + 2032118 * 2 ^ 59
def prefixEnd_2032118 : Nat := 4983230072969 + 3 ^ 40 * 2032118 * 2
def baseEnd_2032118 : Nat := 463757013623726916746429

theorem tailTrace_2032118 : CollatzResearch.WordTrace tailWord_2032118 prefixEnd_2032118 463757013623726916746429 := by
  unfold tailWord_2032118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4632339528249438685550063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49411621634660679312534005 4632339528249438685550063)
  ·
    refine ⟨6948509292374158028325095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4632339528249438685550063 6948509292374158028325095)
    ·
      refine ⟨10422763938561237042487643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6948509292374158028325095 10422763938561237042487643)
      ·
        refine ⟨15634145907841855563731465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10422763938561237042487643 15634145907841855563731465)
        ·
          refine ⟨11725609430881391672798599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15634145907841855563731465 11725609430881391672798599)
          ·
            refine ⟨17588414146322087509197899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11725609430881391672798599 17588414146322087509197899)
            ·
              refine ⟨26382621219483131263796849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17588414146322087509197899 26382621219483131263796849)
              ·
                refine ⟨19786965914612348447847637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26382621219483131263796849 19786965914612348447847637)
                ·
                  refine ⟨463757013623726916746429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19786965914612348447847637 463757013623726916746429)
                  ·
                    rfl

theorem cell21_2032118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_2032118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032118 prefixEnd_2032118 := by exact prefixLift 2032118
  have htrace : WordTrace (prefixWord ++ tailWord_2032118) baseStart_2032118 baseEnd_2032118 := by
    simpa [prefixWord, tailWord_2032118, baseEnd_2032118] using wordTrace_append hprefix tailTrace_2032118
  have hstable : (prefixWord ++ tailWord_2032118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032118).length < 2 ^ (prefixWord ++ tailWord_2032118).sum := by decide
  have hdescent : baseEnd_2032118 < baseStart_2032118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032135 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 5]
def baseStart_2032135 : Nat := 118140960795 + 2032135 * 2 ^ 59
def prefixEnd_2032135 : Nat := 4983230072969 + 3 ^ 40 * 2032135 * 2
def baseEnd_2032135 : Nat := 463760893255338664963061

theorem tailTrace_2032135 : CollatzResearch.WordTrace tailWord_2032135 prefixEnd_2032135 463760893255338664963061 := by
  unfold tailWord_2032135
  simp only [CollatzResearch.WordTrace]
  refine ⟨74118052492929430872169859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49412034995286287248113239 74118052492929430872169859)
  ·
    refine ⟨111177078739394146308254789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74118052492929430872169859 111177078739394146308254789)
    ·
      refine ⟨20845702263636402432797773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111177078739394146308254789 20845702263636402432797773)
      ·
        refine ⟨7817138348863650912299165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20845702263636402432797773 7817138348863650912299165)
        ·
          refine ⟨2931426880823869092112187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7817138348863650912299165 2931426880823869092112187)
          ·
            refine ⟨4397140321235803638168281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931426880823869092112187 4397140321235803638168281)
            ·
              refine ⟨3297855240926852728626211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4397140321235803638168281 3297855240926852728626211)
              ·
                refine ⟨4946782861390279092939317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297855240926852728626211 4946782861390279092939317)
                ·
                  refine ⟨463760893255338664963061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4946782861390279092939317 463760893255338664963061)
                  ·
                    rfl

theorem cell21_2032135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 5].length) (baseStart_2032135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032135 prefixEnd_2032135 := by exact prefixLift 2032135
  have htrace : WordTrace (prefixWord ++ tailWord_2032135) baseStart_2032135 baseEnd_2032135 := by
    simpa [prefixWord, tailWord_2032135, baseEnd_2032135] using wordTrace_append hprefix tailTrace_2032135
  have hstable : (prefixWord ++ tailWord_2032135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032135).length < 2 ^ (prefixWord ++ tailWord_2032135).sum := by decide
  have hdescent : baseEnd_2032135 < baseStart_2032135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032163 : List Nat := [1, 1, 1, 4, 4, 2, 1, 7]
def baseStart_2032163 : Nat := 118140960795 + 2032163 * 2 ^ 59
def prefixEnd_2032163 : Nat := 4983230072969 + 3 ^ 40 * 2032163 * 2
def baseEnd_2032163 : Nat := 154589094412272279498779

theorem tailTrace_2032163 : CollatzResearch.WordTrace tailWord_2032163 prefixEnd_2032163 154589094412272279498779 := by
  unfold tailWord_2032163
  simp only [CollatzResearch.WordTrace]
  refine ⟨74119073736827991654189143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49412715824551994436126095 74119073736827991654189143)
  ·
    refine ⟨111178610605241987481283715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74119073736827991654189143 111178610605241987481283715)
    ·
      refine ⟨166767915907862981221925573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111178610605241987481283715 166767915907862981221925573)
      ·
        refine ⟨31268984232724308979111045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166767915907862981221925573 31268984232724308979111045)
        ·
          refine ⟨5862934543635807933583321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31268984232724308979111045 5862934543635807933583321)
          ·
            refine ⟨4397200907726855950187491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5862934543635807933583321 4397200907726855950187491)
            ·
              refine ⟨6595801361590283925281237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397200907726855950187491 6595801361590283925281237)
              ·
                refine ⟨154589094412272279498779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6595801361590283925281237 154589094412272279498779)
                ·
                  rfl

theorem cell21_2032163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 7].length) (baseStart_2032163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032163 prefixEnd_2032163 := by exact prefixLift 2032163
  have htrace : WordTrace (prefixWord ++ tailWord_2032163) baseStart_2032163 baseEnd_2032163 := by
    simpa [prefixWord, tailWord_2032163, baseEnd_2032163] using wordTrace_append hprefix tailTrace_2032163
  have hstable : (prefixWord ++ tailWord_2032163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032163).length < 2 ^ (prefixWord ++ tailWord_2032163).sum := by decide
  have hdescent : baseEnd_2032163 < baseStart_2032163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032177 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 7]
def baseStart_2032177 : Nat := 118140960795 + 2032177 * 2 ^ 59
def prefixEnd_2032177 : Nat := 4983230072969 + 3 ^ 40 * 2032177 * 2
def baseEnd_2032177 : Nat := 463770478227555925262975

theorem tailTrace_2032177 : CollatzResearch.WordTrace tailWord_2032177 prefixEnd_2032177 463770478227555925262975 := by
  unfold tailWord_2032177
  simp only [CollatzResearch.WordTrace]
  refine ⟨74119584358777272045198785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49413056239184848030132523 74119584358777272045198785)
  ·
    refine ⟨55589688269082954033899089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74119584358777272045198785 55589688269082954033899089)
    ·
      refine ⟨41692266201812215525424317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55589688269082954033899089 41692266201812215525424317)
      ·
        refine ⟨15634599825679580822034119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41692266201812215525424317 15634599825679580822034119)
        ·
          refine ⟨23451899738519371233051179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15634599825679580822034119 23451899738519371233051179)
          ·
            refine ⟨35177849607779056849576769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23451899738519371233051179 35177849607779056849576769)
            ·
              refine ⟨26383387205834292637182577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35177849607779056849576769 26383387205834292637182577)
              ·
                refine ⟨19787540404375719477886933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26383387205834292637182577 19787540404375719477886933)
                ·
                  refine ⟨463770478227555925262975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19787540404375719477886933 463770478227555925262975)
                  ·
                    rfl

theorem cell21_2032177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_2032177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032177 prefixEnd_2032177 := by exact prefixLift 2032177
  have htrace : WordTrace (prefixWord ++ tailWord_2032177) baseStart_2032177 baseEnd_2032177 := by
    simpa [prefixWord, tailWord_2032177, baseEnd_2032177] using wordTrace_append hprefix tailTrace_2032177
  have hstable : (prefixWord ++ tailWord_2032177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032177).length < 2 ^ (prefixWord ++ tailWord_2032177).sum := by decide
  have hdescent : baseEnd_2032177 < baseStart_2032177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032242 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2032242 : Nat := 118140960795 + 2032242 * 2 ^ 59
def prefixEnd_2032242 : Nat := 4983230072969 + 3 ^ 40 * 2032242 * 2
def baseEnd_2032242 : Nat := 463785312113130256679509

theorem tailTrace_2032242 : CollatzResearch.WordTrace tailWord_2032242 prefixEnd_2032242 463785312113130256679509 := by
  unfold tailWord_2032242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18530488775885447036578745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49414636735694525430876653 18530488775885447036578745)
  ·
    refine ⟨13897866581914085277434059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18530488775885447036578745 13897866581914085277434059)
    ·
      refine ⟨20846799872871127916151089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13897866581914085277434059 20846799872871127916151089)
      ·
        refine ⟨15635099904653345937113317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20846799872871127916151089 15635099904653345937113317)
        ·
          refine ⟨2931581232122502363208747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15635099904653345937113317 2931581232122502363208747)
          ·
            refine ⟨4397371848183753544813121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931581232122502363208747 4397371848183753544813121)
            ·
              refine ⟨3298028886137815158609841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4397371848183753544813121 3298028886137815158609841)
              ·
                refine ⟨2473521664603361368957381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3298028886137815158609841 2473521664603361368957381)
                ·
                  refine ⟨463785312113130256679509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2473521664603361368957381 463785312113130256679509)
                  ·
                    rfl

theorem cell21_2032242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2032242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032242 prefixEnd_2032242 := by exact prefixLift 2032242
  have htrace : WordTrace (prefixWord ++ tailWord_2032242) baseStart_2032242 baseEnd_2032242 := by
    simpa [prefixWord, tailWord_2032242, baseEnd_2032242] using wordTrace_append hprefix tailTrace_2032242
  have hstable : (prefixWord ++ tailWord_2032242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032242).length < 2 ^ (prefixWord ++ tailWord_2032242).sum := by decide
  have hdescent : baseEnd_2032242 < baseStart_2032242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032270 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_2032270 : Nat := 118140960795 + 2032270 * 2 ^ 59
def prefixEnd_2032270 : Nat := 4983230072969 + 3 ^ 40 * 2032270 * 2
def baseEnd_2032270 : Nat := 463791702094608430212785

theorem tailTrace_2032270 : CollatzResearch.WordTrace tailWord_2032270 prefixEnd_2032270 463791702094608430212785 := by
  unfold tailWord_2032270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9265372043430043616041783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49415317564960232618889509 9265372043430043616041783)
  ·
    refine ⟨13898058065145065424062675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9265372043430043616041783 13898058065145065424062675)
    ·
      refine ⟨20847087097717598136094013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13898058065145065424062675 20847087097717598136094013)
      ·
        refine ⟨7817657661644099301035255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20847087097717598136094013 7817657661644099301035255)
        ·
          refine ⟨11726486492466148951552883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7817657661644099301035255 11726486492466148951552883)
          ·
            refine ⟨17589729738699223427329325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11726486492466148951552883 17589729738699223427329325)
            ·
              refine ⟨6596148652012208785248497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17589729738699223427329325 6596148652012208785248497)
              ·
                refine ⟨4947111489009156588936373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6596148652012208785248497 4947111489009156588936373)
                ·
                  refine ⟨463791702094608430212785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4947111489009156588936373 463791702094608430212785)
                  ·
                    rfl

theorem cell21_2032270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_2032270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032270 prefixEnd_2032270 := by exact prefixLift 2032270
  have htrace : WordTrace (prefixWord ++ tailWord_2032270) baseStart_2032270 baseEnd_2032270 := by
    simpa [prefixWord, tailWord_2032270, baseEnd_2032270] using wordTrace_append hprefix tailTrace_2032270
  have hstable : (prefixWord ++ tailWord_2032270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032270).length < 2 ^ (prefixWord ++ tailWord_2032270).sum := by decide
  have hdescent : baseEnd_2032270 < baseStart_2032270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032301 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 6]
def baseStart_2032301 : Nat := 118140960795 + 2032301 * 2 ^ 59
def prefixEnd_2032301 : Nat := 4983230072969 + 3 ^ 40 * 2032301 * 2
def baseEnd_2032301 : Nat := 463798776716959265196055

theorem tailTrace_2032301 : CollatzResearch.WordTrace tailWord_2032301 prefixEnd_2032301 463798776716959265196055 := by
  unfold tailWord_2032301
  simp only [CollatzResearch.WordTrace]
  refine ⟨74124107010328041222712757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49416071340218694148475171 74124107010328041222712757)
  ·
    refine ⟨6949135032218253864629321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74124107010328041222712757 6949135032218253864629321)
    ·
      refine ⟨5211851274163690398471991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6949135032218253864629321 5211851274163690398471991)
      ·
        refine ⟨7817776911245535597707987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211851274163690398471991 7817776911245535597707987)
        ·
          refine ⟨11726665366868303396561981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7817776911245535597707987 11726665366868303396561981)
          ·
            refine ⟨4397499512575613773710743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11726665366868303396561981 4397499512575613773710743)
            ·
              refine ⟨6596249268863420660566115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397499512575613773710743 6596249268863420660566115)
              ·
                refine ⟨9894373903295130990849173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6596249268863420660566115 9894373903295130990849173)
                ·
                  refine ⟨463798776716959265196055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9894373903295130990849173 463798776716959265196055)
                  ·
                    rfl

theorem cell21_2032301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_2032301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032301 prefixEnd_2032301 := by exact prefixLift 2032301
  have htrace : WordTrace (prefixWord ++ tailWord_2032301) baseStart_2032301 baseEnd_2032301 := by
    simpa [prefixWord, tailWord_2032301, baseEnd_2032301] using wordTrace_append hprefix tailTrace_2032301
  have hstable : (prefixWord ++ tailWord_2032301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032301).length < 2 ^ (prefixWord ++ tailWord_2032301).sum := by decide
  have hdescent : baseEnd_2032301 < baseStart_2032301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032318 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_2032318 : Nat := 118140960795 + 2032318 * 2 ^ 59
def prefixEnd_2032318 : Nat := 4983230072969 + 3 ^ 40 * 2032318 * 2
def baseEnd_2032318 : Nat := 463802656348571013412687

theorem tailTrace_2032318 : CollatzResearch.WordTrace tailWord_2032318 prefixEnd_2032318 463802656348571013412687 := by
  unfold tailWord_2032318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9265590881408306640760201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49416484700844302084054405 9265590881408306640760201)
  ·
    refine ⟨6949193161056229980570151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9265590881408306640760201 6949193161056229980570151)
    ·
      refine ⟨10423789741584344970855227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6949193161056229980570151 10423789741584344970855227)
      ·
        refine ⟨15635684612376517456282841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10423789741584344970855227 15635684612376517456282841)
        ·
          refine ⟨11726763459282388092212131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15635684612376517456282841 11726763459282388092212131)
          ·
            refine ⟨17590145188923582138318197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11726763459282388092212131 17590145188923582138318197)
            ·
              refine ⟨1649076111461585825467331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17590145188923582138318197 1649076111461585825467331)
              ·
                refine ⟨2473614167192378738200997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649076111461585825467331 2473614167192378738200997)
                ·
                  refine ⟨463802656348571013412687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2473614167192378738200997 463802656348571013412687)
                  ·
                    rfl

theorem cell21_2032318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_2032318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032318 prefixEnd_2032318 := by exact prefixLift 2032318
  have htrace : WordTrace (prefixWord ++ tailWord_2032318) baseStart_2032318 baseEnd_2032318 := by
    simpa [prefixWord, tailWord_2032318, baseEnd_2032318] using wordTrace_append hprefix tailTrace_2032318
  have hstable : (prefixWord ++ tailWord_2032318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032318).length < 2 ^ (prefixWord ++ tailWord_2032318).sum := by decide
  have hdescent : baseEnd_2032318 < baseStart_2032318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032332 : List Nat := [2, 2, 1, 5, 1, 1, 4, 5]
def baseStart_2032332 : Nat := 118140960795 + 2032332 * 2 ^ 59
def prefixEnd_2032332 : Nat := 4983230072969 + 3 ^ 40 * 2032332 * 2
def baseEnd_2032332 : Nat := 154601950446436700059775

theorem tailTrace_2032332 : CollatzResearch.WordTrace tailWord_2032332 prefixEnd_2032332 154601950446436700059775 := by
  unfold tailWord_2032332
  simp only [CollatzResearch.WordTrace]
  refine ⟨37062618836607866758545625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49416825115477155678060833 37062618836607866758545625)
  ·
    refine ⟨27796964127455900068909219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37062618836607866758545625 27796964127455900068909219)
    ·
      refine ⟨41695446191183850103363829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27796964127455900068909219 41695446191183850103363829)
      ·
        refine ⟨3908948080423485947190359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41695446191183850103363829 3908948080423485947190359)
        ·
          refine ⟨5863422120635228920785539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3908948080423485947190359 5863422120635228920785539)
          ·
            refine ⟨8795133180952843381178309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5863422120635228920785539 8795133180952843381178309)
            ·
              refine ⟨1649087471428658133970933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8795133180952843381178309 1649087471428658133970933)
              ·
                refine ⟨154601950446436700059775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1649087471428658133970933 154601950446436700059775)
                ·
                  rfl

theorem cell21_2032332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_2032332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032332 prefixEnd_2032332 := by exact prefixLift 2032332
  have htrace : WordTrace (prefixWord ++ tailWord_2032332) baseStart_2032332 baseEnd_2032332 := by
    simpa [prefixWord, tailWord_2032332, baseEnd_2032332] using wordTrace_append hprefix tailTrace_2032332
  have hstable : (prefixWord ++ tailWord_2032332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032332).length < 2 ^ (prefixWord ++ tailWord_2032332).sum := by decide
  have hdescent : baseEnd_2032332 < baseStart_2032332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032391 : List Nat := [1, 1, 4, 4, 1, 1, 2, 7]
def baseStart_2032391 : Nat := 118140960795 + 2032391 * 2 ^ 59
def prefixEnd_2032391 : Nat := 4983230072969 + 3 ^ 40 * 2032391 * 2
def baseEnd_2032391 : Nat := 154606438647713036231957

theorem tailTrace_2032391 : CollatzResearch.WordTrace tailWord_2032391 prefixEnd_2032391 154606438647713036231957 := by
  unfold tailWord_2032391
  simp only [CollatzResearch.WordTrace]
  refine ⟨74127389580001986593489027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49418259720001324395659351 74127389580001986593489027)
  ·
    refine ⟨111191084370002979890233541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74127389580001986593489027 111191084370002979890233541)
    ·
      refine ⟨20848328319375558729418789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111191084370002979890233541 20848328319375558729418789)
      ·
        refine ⟨3909061559882917261766023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20848328319375558729418789 3909061559882917261766023)
        ·
          refine ⟨5863592339824375892649035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909061559882917261766023 5863592339824375892649035)
          ·
            refine ⟨8795388509736563838973553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5863592339824375892649035 8795388509736563838973553)
            ·
              refine ⟨6596541382302422879230165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8795388509736563838973553 6596541382302422879230165)
              ·
                refine ⟨154606438647713036231957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6596541382302422879230165 154606438647713036231957)
                ·
                  rfl

theorem cell21_2032391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 7].length) (baseStart_2032391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032391 prefixEnd_2032391 := by exact prefixLift 2032391
  have htrace : WordTrace (prefixWord ++ tailWord_2032391) baseStart_2032391 baseEnd_2032391 := by
    simpa [prefixWord, tailWord_2032391, baseEnd_2032391] using wordTrace_append hprefix tailTrace_2032391
  have hstable : (prefixWord ++ tailWord_2032391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032391).length < 2 ^ (prefixWord ++ tailWord_2032391).sum := by decide
  have hdescent : baseEnd_2032391 < baseStart_2032391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032532 : List Nat := [2, 4, 2, 1, 1, 1, 5, 2, 3]
def baseStart_2032532 : Nat := 118140960795 + 2032532 * 2 ^ 59
def prefixEnd_2032532 : Nat := 4983230072969 + 3 ^ 40 * 2032532 * 2
def baseEnd_2032532 : Nat := 463851494064154196845583

theorem tailTrace_2032532 : CollatzResearch.WordTrace tailWord_2032532 prefixEnd_2032532 463851494064154196845583 := by
  unfold tailWord_2032532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37066266136245583837185925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49421688181660778449581233 37066266136245583837185925)
  ·
    refine ⟨6949924900546046969472361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37066266136245583837185925 6949924900546046969472361)
    ·
      refine ⟨5212443675409535227104271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6949924900546046969472361 5212443675409535227104271)
      ·
        refine ⟨7818665513114302840656407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5212443675409535227104271 7818665513114302840656407)
        ·
          refine ⟨11727998269671454260984611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7818665513114302840656407 11727998269671454260984611)
          ·
            refine ⟨17591997404507181391476917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11727998269671454260984611 17591997404507181391476917)
            ·
              refine ⟨1649249756672548255450961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17591997404507181391476917 1649249756672548255450961)
              ·
                refine ⟨1236937317504411191588221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649249756672548255450961 1236937317504411191588221)
                ·
                  refine ⟨463851494064154196845583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236937317504411191588221 463851494064154196845583)
                  ·
                    rfl

theorem cell21_2032532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_2032532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032532 prefixEnd_2032532 := by exact prefixLift 2032532
  have htrace : WordTrace (prefixWord ++ tailWord_2032532) baseStart_2032532 baseEnd_2032532 := by
    simpa [prefixWord, tailWord_2032532, baseEnd_2032532] using wordTrace_append hprefix tailTrace_2032532
  have hstable : (prefixWord ++ tailWord_2032532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032532).length < 2 ^ (prefixWord ++ tailWord_2032532).sum := by decide
  have hdescent : baseEnd_2032532 < baseStart_2032532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032543 : List Nat := [1, 1, 2, 5, 2, 2, 2, 6]
def baseStart_2032543 : Nat := 118140960795 + 2032543 * 2 ^ 59
def prefixEnd_2032543 : Nat := 4983230072969 + 3 ^ 40 * 2032543 * 2
def baseEnd_2032543 : Nat := 154618001471340207387409

theorem tailTrace_2032543 : CollatzResearch.WordTrace tailWord_2032543 prefixEnd_2032543 154618001471340207387409 := by
  unfold tailWord_2032543
  simp only [CollatzResearch.WordTrace]
  refine ⟨74132933475451316553022283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49421955650300877702014855 74132933475451316553022283)
  ·
    refine ⟨111199400213176974829533425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74132933475451316553022283 111199400213176974829533425)
    ·
      refine ⟨83399550159882731122150069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111199400213176974829533425 83399550159882731122150069)
      ·
        refine ⟨7818707827489006042701569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83399550159882731122150069 7818707827489006042701569)
        ·
          refine ⟨5864030870616754532026177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7818707827489006042701569 5864030870616754532026177)
          ·
            refine ⟨4398023152962565899019633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5864030870616754532026177 4398023152962565899019633)
            ·
              refine ⟨3298517364721924424264725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4398023152962565899019633 3298517364721924424264725)
              ·
                refine ⟨154618001471340207387409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3298517364721924424264725 154618001471340207387409)
                ·
                  rfl

theorem cell21_2032543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 6].length) (baseStart_2032543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032543 prefixEnd_2032543 := by exact prefixLift 2032543
  have htrace : WordTrace (prefixWord ++ tailWord_2032543) baseStart_2032543 baseEnd_2032543 := by
    simpa [prefixWord, tailWord_2032543, baseEnd_2032543] using wordTrace_append hprefix tailTrace_2032543
  have hstable : (prefixWord ++ tailWord_2032543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032543).length < 2 ^ (prefixWord ++ tailWord_2032543).sum := by decide
  have hdescent : baseEnd_2032543 < baseStart_2032543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032546 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_2032546 : Nat := 118140960795 + 2032546 * 2 ^ 59
def prefixEnd_2032546 : Nat := 4983230072969 + 3 ^ 40 * 2032546 * 2
def baseEnd_2032546 : Nat := 463854689054893283612221

theorem tailTrace_2032546 : CollatzResearch.WordTrace tailWord_2032546 prefixEnd_2032546 463854689054893283612221 := by
  unfold tailWord_2032546
  simp only [CollatzResearch.WordTrace]
  refine ⟨18533260723610112016345373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49422028596293632043587661 18533260723610112016345373)
  ·
    refine ⟨6949972771353792006129515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18533260723610112016345373 6949972771353792006129515)
    ·
      refine ⟨10424959157030688009194273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6949972771353792006129515 10424959157030688009194273)
      ·
        refine ⟨7818719367773016006895705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10424959157030688009194273 7818719367773016006895705)
        ·
          refine ⟨5864039525829762005171779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7818719367773016006895705 5864039525829762005171779)
          ·
            refine ⟨8796059288744643007757669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864039525829762005171779 8796059288744643007757669)
            ·
              refine ⟨1649261116639620563954563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8796059288744643007757669 1649261116639620563954563)
              ·
                refine ⟨2473891674959430845931845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649261116639620563954563 2473891674959430845931845)
                ·
                  refine ⟨463854689054893283612221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2473891674959430845931845 463854689054893283612221)
                  ·
                    rfl

theorem cell21_2032546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_2032546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032546 prefixEnd_2032546 := by exact prefixLift 2032546
  have htrace : WordTrace (prefixWord ++ tailWord_2032546) baseStart_2032546 baseEnd_2032546 := by
    simpa [prefixWord, tailWord_2032546, baseEnd_2032546] using wordTrace_append hprefix tailTrace_2032546
  have hstable : (prefixWord ++ tailWord_2032546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032546).length < 2 ^ (prefixWord ++ tailWord_2032546).sum := by decide
  have hdescent : baseEnd_2032546 < baseStart_2032546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032591 : List Nat := [1, 1, 2, 1, 1, 6, 4, 2, 3]
def baseStart_2032591 : Nat := 118140960795 + 2032591 * 2 ^ 59
def prefixEnd_2032591 : Nat := 4983230072969 + 3 ^ 40 * 2032591 * 2
def baseEnd_2032591 : Nat := 463864958667983205362129

theorem tailTrace_2032591 : CollatzResearch.WordTrace tailWord_2032591 prefixEnd_2032591 463864958667983205362129 := by
  unfold tailWord_2032591
  simp only [CollatzResearch.WordTrace]
  refine ⟨74134684179277420750769627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49423122786184947167179751 74134684179277420750769627)
  ·
    refine ⟨111202026268916131126154441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74134684179277420750769627 111202026268916131126154441)
    ·
      refine ⟨83401519701687098344615831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111202026268916131126154441 83401519701687098344615831)
      ·
        refine ⟨125102279552530647516923747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83401519701687098344615831 125102279552530647516923747)
        ·
          refine ⟨187653419328795971275385621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125102279552530647516923747 187653419328795971275385621)
          ·
            refine ⟨8796254031037311153533701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187653419328795971275385621 8796254031037311153533701)
            ·
              refine ⟨1649297630819495841287569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8796254031037311153533701 1649297630819495841287569)
              ·
                refine ⟨1236973223114621880965677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649297630819495841287569 1236973223114621880965677)
                ·
                  refine ⟨463864958667983205362129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236973223114621880965677 463864958667983205362129)
                  ·
                    rfl

theorem cell21_2032591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 3].length) (baseStart_2032591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032591 prefixEnd_2032591 := by exact prefixLift 2032591
  have htrace : WordTrace (prefixWord ++ tailWord_2032591) baseStart_2032591 baseEnd_2032591 := by
    simpa [prefixWord, tailWord_2032591, baseEnd_2032591] using wordTrace_append hprefix tailTrace_2032591
  have hstable : (prefixWord ++ tailWord_2032591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032591).length < 2 ^ (prefixWord ++ tailWord_2032591).sum := by decide
  have hdescent : baseEnd_2032591 < baseStart_2032591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032605 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 4]
def baseStart_2032605 : Nat := 118140960795 + 2032605 * 2 ^ 59
def prefixEnd_2032605 : Nat := 4983230072969 + 3 ^ 40 * 2032605 * 2
def baseEnd_2032605 : Nat := 463868153658722292128767

theorem tailTrace_2032605 : CollatzResearch.WordTrace tailWord_2032605 prefixEnd_2032605 463868153658722292128767 := by
  unfold tailWord_2032605
  simp only [CollatzResearch.WordTrace]
  refine ⟨74135194801226701141779269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49423463200817800761186179 74135194801226701141779269)
  ·
    refine ⟨13900349025230006464083613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74135194801226701141779269 13900349025230006464083613)
    ·
      refine ⟨5212630884461252424031355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13900349025230006464083613 5212630884461252424031355)
      ·
        refine ⟨7818946326691878636047033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5212630884461252424031355 7818946326691878636047033)
        ·
          refine ⟨5864209745018908977035275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7818946326691878636047033 5864209745018908977035275)
          ·
            refine ⟨8796314617528363465552913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864209745018908977035275 8796314617528363465552913)
            ·
              refine ⟨6597235963146272599164685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8796314617528363465552913 6597235963146272599164685)
              ·
                refine ⟨2473963486179852224686757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6597235963146272599164685 2473963486179852224686757)
                ·
                  refine ⟨463868153658722292128767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2473963486179852224686757 463868153658722292128767)
                  ·
                    rfl

theorem cell21_2032605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_2032605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032605 prefixEnd_2032605 := by exact prefixLift 2032605
  have htrace : WordTrace (prefixWord ++ tailWord_2032605) baseStart_2032605 baseEnd_2032605 := by
    simpa [prefixWord, tailWord_2032605, baseEnd_2032605] using wordTrace_append hprefix tailTrace_2032605
  have hstable : (prefixWord ++ tailWord_2032605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032605).length < 2 ^ (prefixWord ++ tailWord_2032605).sum := by decide
  have hdescent : baseEnd_2032605 < baseStart_2032605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032650 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_2032650 : Nat := 118140960795 + 2032650 * 2 ^ 59
def prefixEnd_2032650 : Nat := 4983230072969 + 3 ^ 40 * 2032650 * 2
def baseEnd_2032650 : Nat := 463878423271812213878675

theorem tailTrace_2032650 : CollatzResearch.WordTrace tailWord_2032650 prefixEnd_2032650 463878423271812213878675 := by
  unfold tailWord_2032650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534209021515918456791851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49424557390709115884778269 18534209021515918456791851)
  ·
    refine ⟨27801313532273877685187777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18534209021515918456791851 27801313532273877685187777)
    ·
      refine ⟨20850985149205408263890833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27801313532273877685187777 20850985149205408263890833)
      ·
        refine ⟨15638238861904056197918125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20850985149205408263890833 15638238861904056197918125)
        ·
          refine ⟨5864339573214021074219297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15638238861904056197918125 5864339573214021074219297)
          ·
            refine ⟨4398254679910515805664473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5864339573214021074219297 4398254679910515805664473)
            ·
              refine ⟨3298691009932886854248355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4398254679910515805664473 3298691009932886854248355)
              ·
                refine ⟨4948036514899330281372533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3298691009932886854248355 4948036514899330281372533)
                ·
                  refine ⟨463878423271812213878675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4948036514899330281372533 463878423271812213878675)
                  ·
                    rfl

theorem cell21_2032650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_2032650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032650 prefixEnd_2032650 := by exact prefixLift 2032650
  have htrace : WordTrace (prefixWord ++ tailWord_2032650) baseStart_2032650 baseEnd_2032650 := by
    simpa [prefixWord, tailWord_2032650, baseEnd_2032650] using wordTrace_append hprefix tailTrace_2032650
  have hstable : (prefixWord ++ tailWord_2032650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032650).length < 2 ^ (prefixWord ++ tailWord_2032650).sum := by decide
  have hdescent : baseEnd_2032650 < baseStart_2032650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032709 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 5]
def baseStart_2032709 : Nat := 118140960795 + 2032709 * 2 ^ 59
def prefixEnd_2032709 : Nat := 4983230072969 + 3 ^ 40 * 2032709 * 2
def baseEnd_2032709 : Nat := 463891887875641222395221

theorem tailTrace_2032709 : CollatzResearch.WordTrace tailWord_2032709 prefixEnd_2032709 463891887875641222395221 := by
  unfold tailWord_2032709
  simp only [CollatzResearch.WordTrace]
  refine ⟨74138987992849926903565181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49425991995233284602376787 74138987992849926903565181)
  ·
    refine ⟨27802120497318722588836943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74138987992849926903565181 27802120497318722588836943)
    ·
      refine ⟨41703180745978083883255415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27802120497318722588836943 41703180745978083883255415)
      ·
        refine ⟨62554771118967125824883123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41703180745978083883255415 62554771118967125824883123)
        ·
          refine ⟨93832156678450688737324685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62554771118967125824883123 93832156678450688737324685)
          ·
            refine ⟨35187058754419008276496757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93832156678450688737324685 35187058754419008276496757)
            ·
              refine ⟨3298786758226782025921571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35187058754419008276496757 3298786758226782025921571)
              ·
                refine ⟨4948180137340173038882357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3298786758226782025921571 4948180137340173038882357)
                ·
                  refine ⟨463891887875641222395221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4948180137340173038882357 463891887875641222395221)
                  ·
                    rfl

theorem cell21_2032709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_2032709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032709 prefixEnd_2032709 := by exact prefixLift 2032709
  have htrace : WordTrace (prefixWord ++ tailWord_2032709) baseStart_2032709 baseEnd_2032709 := by
    simpa [prefixWord, tailWord_2032709, baseEnd_2032709] using wordTrace_append hprefix tailTrace_2032709
  have hstable : (prefixWord ++ tailWord_2032709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032709).length < 2 ^ (prefixWord ++ tailWord_2032709).sum := by decide
  have hdescent : baseEnd_2032709 < baseStart_2032709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032875 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 6]
def baseStart_2032875 : Nat := 118140960795 + 2032875 * 2 ^ 59
def prefixEnd_2032875 : Nat := 4983230072969 + 3 ^ 40 * 2032875 * 2
def baseEnd_2032875 : Nat := 463929771337261822628215

theorem tailTrace_2032875 : CollatzResearch.WordTrace tailWord_2032875 prefixEnd_2032875 463929771337261822628215 := by
  unfold tailWord_2032875
  simp only [CollatzResearch.WordTrace]
  refine ⟨74145042510248537254108079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49430028340165691502738719 74145042510248537254108079)
  ·
    refine ⟨111217563765372805881162119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74145042510248537254108079 111217563765372805881162119)
    ·
      refine ⟨166826345648059208821743179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111217563765372805881162119 166826345648059208821743179)
      ·
        refine ⟨250239518472088813232614769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166826345648059208821743179 250239518472088813232614769)
        ·
          refine ⟨187679638854066609924461077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250239518472088813232614769 187679638854066609924461077)
          ·
            refine ⟨8797483071284372340209113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187679638854066609924461077 8797483071284372340209113)
            ·
              refine ⟨6598112303463279255156835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8797483071284372340209113 6598112303463279255156835)
              ·
                refine ⟨9897168455194918882735253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598112303463279255156835 9897168455194918882735253)
                ·
                  refine ⟨463929771337261822628215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9897168455194918882735253 463929771337261822628215)
                  ·
                    rfl

theorem cell21_2032875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_2032875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032875 prefixEnd_2032875 := by exact prefixLift 2032875
  have htrace : WordTrace (prefixWord ++ tailWord_2032875) baseStart_2032875 baseEnd_2032875 := by
    simpa [prefixWord, tailWord_2032875, baseEnd_2032875] using wordTrace_append hprefix tailTrace_2032875
  have hstable : (prefixWord ++ tailWord_2032875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032875).length < 2 ^ (prefixWord ++ tailWord_2032875).sum := by decide
  have hdescent : baseEnd_2032875 < baseStart_2032875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032878 : List Nat := [4, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_2032878 : Nat := 118140960795 + 2032878 * 2 ^ 59
def prefixEnd_2032878 : Nat := 4983230072969 + 3 ^ 40 * 2032878 * 2
def baseEnd_2032878 : Nat := 463930455978134484078209

theorem tailTrace_2032878 : CollatzResearch.WordTrace tailWord_2032878 prefixEnd_2032878 463930455978134484078209 := by
  unfold tailWord_2032878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9268143991154708595808411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49430101286158445844311525 9268143991154708595808411)
  ·
    refine ⟨13902215986732062893712617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9268143991154708595808411 13902215986732062893712617)
    ·
      refine ⟨10426661990049047170284463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13902215986732062893712617 10426661990049047170284463)
      ·
        refine ⟨15639992985073570755426695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10426661990049047170284463 15639992985073570755426695)
        ·
          refine ⟨23459989477610356133140043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15639992985073570755426695 23459989477610356133140043)
          ·
            refine ⟨35189984216415534199710065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23459989477610356133140043 35189984216415534199710065)
            ·
              refine ⟨26392488162311650649782549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35189984216415534199710065 26392488162311650649782549)
              ·
                refine ⟨1237147882608358624208557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26392488162311650649782549 1237147882608358624208557)
                ·
                  refine ⟨463930455978134484078209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237147882608358624208557 463930455978134484078209)
                  ·
                    rfl

theorem cell21_2032878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_2032878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032878 prefixEnd_2032878 := by exact prefixLift 2032878
  have htrace : WordTrace (prefixWord ++ tailWord_2032878) baseStart_2032878 baseEnd_2032878 := by
    simpa [prefixWord, tailWord_2032878, baseEnd_2032878] using wordTrace_append hprefix tailTrace_2032878
  have hstable : (prefixWord ++ tailWord_2032878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032878).length < 2 ^ (prefixWord ++ tailWord_2032878).sum := by decide
  have hdescent : baseEnd_2032878 < baseStart_2032878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032965 : List Nat := [1, 3, 1, 1, 1, 2, 1, 11]
def baseStart_2032965 : Nat := 118140960795 + 2032965 * 2 ^ 59
def prefixEnd_2032965 : Nat := 4983230072969 + 3 ^ 40 * 2032965 * 2
def baseEnd_2032965 : Nat := 154650103521147222042677

theorem tailTrace_2032965 : CollatzResearch.WordTrace tailWord_2032965 prefixEnd_2032965 154650103521147222042677 := by
  unfold tailWord_2032965
  simp only [CollatzResearch.WordTrace]
  refine ⟨74148325079922482624884349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49432216719948321749922899 74148325079922482624884349)
  ·
    refine ⟨27805621904970930984331631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74148325079922482624884349 27805621904970930984331631)
    ·
      refine ⟨41708432857456396476497447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27805621904970930984331631 41708432857456396476497447)
      ·
        refine ⟨62562649286184594714746171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41708432857456396476497447 62562649286184594714746171)
        ·
          refine ⟨93843973929276892072119257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62562649286184594714746171 93843973929276892072119257)
          ·
            refine ⟨70382980446957669054089443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93843973929276892072119257 70382980446957669054089443)
            ·
              refine ⟨105574470670436503581134165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70382980446957669054089443 105574470670436503581134165)
              ·
                refine ⟨154650103521147222042677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 105574470670436503581134165 154650103521147222042677)
                ·
                  rfl

theorem cell21_2032965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 11].length) (baseStart_2032965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2032965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2032965 prefixEnd_2032965 := by exact prefixLift 2032965
  have htrace : WordTrace (prefixWord ++ tailWord_2032965) baseStart_2032965 baseEnd_2032965 := by
    simpa [prefixWord, tailWord_2032965, baseEnd_2032965] using wordTrace_append hprefix tailTrace_2032965
  have hstable : (prefixWord ++ tailWord_2032965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032965).length < 2 ^ (prefixWord ++ tailWord_2032965).sum := by decide
  have hdescent : baseEnd_2032965 < baseStart_2032965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033002 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_2033002 : Nat := 118140960795 + 2033002 * 2 ^ 59
def prefixEnd_2033002 : Nat := 4983230072969 + 3 ^ 40 * 2033002 * 2
def baseEnd_2033002 : Nat := 463958754467537824011289

theorem tailTrace_2033002 : CollatzResearch.WordTrace tailWord_2033002 prefixEnd_2033002 463958754467537824011289 := by
  unfold tailWord_2033002
  simp only [CollatzResearch.WordTrace]
  refine ⟨18537418645197109485995315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49433116387192291962654173 18537418645197109485995315)
  ·
    refine ⟨27806127967795664228992973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18537418645197109485995315 27806127967795664228992973)
    ·
      refine ⟨10427297987923374085872365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27806127967795664228992973 10427297987923374085872365)
      ·
        refine ⟨3910236745471265282202137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10427297987923374085872365 3910236745471265282202137)
        ·
          refine ⟨2932677559103448961651603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3910236745471265282202137 2932677559103448961651603)
          ·
            refine ⟨4399016338655173442477405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932677559103448961651603 4399016338655173442477405)
            ·
              refine ⟨1649631126995690040929027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4399016338655173442477405 1649631126995690040929027)
              ·
                refine ⟨2474446690493535061393541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649631126995690040929027 2474446690493535061393541)
                ·
                  refine ⟨463958754467537824011289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474446690493535061393541 463958754467537824011289)
                  ·
                    rfl

theorem cell21_2033002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_2033002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033002 prefixEnd_2033002 := by exact prefixLift 2033002
  have htrace : WordTrace (prefixWord ++ tailWord_2033002) baseStart_2033002 baseEnd_2033002 := by
    simpa [prefixWord, tailWord_2033002, baseEnd_2033002] using wordTrace_append hprefix tailTrace_2033002
  have hstable : (prefixWord ++ tailWord_2033002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033002).length < 2 ^ (prefixWord ++ tailWord_2033002).sum := by decide
  have hdescent : baseEnd_2033002 < baseStart_2033002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033022 : List Nat := [4, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_2033022 : Nat := 118140960795 + 2033022 * 2 ^ 59
def prefixEnd_2033022 : Nat := 4983230072969 + 3 ^ 40 * 2033022 * 2
def baseEnd_2033022 : Nat := 463963318740022233677915

theorem tailTrace_2033022 : CollatzResearch.WordTrace tailWord_2033022 prefixEnd_2033022 463963318740022233677915 := by
  unfold tailWord_2033022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9268800505089497669963665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49433602693810654239806213 9268800505089497669963665)
  ·
    refine ⟨6951600378817123252472749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9268800505089497669963665 6951600378817123252472749)
    ·
      refine ⟨2606850142056421219677281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6951600378817123252472749 2606850142056421219677281)
      ·
        refine ⟨1955137606542315914757961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2606850142056421219677281 1955137606542315914757961)
        ·
          refine ⟨1466353204906736936068471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1955137606542315914757961 1466353204906736936068471)
          ·
            refine ⟨2199529807360105404102707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466353204906736936068471 2199529807360105404102707)
            ·
              refine ⟨3299294711040158106154061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199529807360105404102707 3299294711040158106154061)
              ·
                refine ⟨1237235516640059289807773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3299294711040158106154061 1237235516640059289807773)
                ·
                  refine ⟨463963318740022233677915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237235516640059289807773 463963318740022233677915)
                  ·
                    rfl

theorem cell21_2033022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_2033022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033022 prefixEnd_2033022 := by exact prefixLift 2033022
  have htrace : WordTrace (prefixWord ++ tailWord_2033022) baseStart_2033022 baseEnd_2033022 := by
    simpa [prefixWord, tailWord_2033022, baseEnd_2033022] using wordTrace_append hprefix tailTrace_2033022
  have hstable : (prefixWord ++ tailWord_2033022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033022).length < 2 ^ (prefixWord ++ tailWord_2033022).sum := by decide
  have hdescent : baseEnd_2033022 < baseStart_2033022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033027 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 6]
def baseStart_2033027 : Nat := 118140960795 + 2033027 * 2 ^ 59
def prefixEnd_2033027 : Nat := 4983230072969 + 3 ^ 40 * 2033027 * 2
def baseEnd_2033027 : Nat := 463964459808143336094571

theorem tailTrace_2033027 : CollatzResearch.WordTrace tailWord_2033027 prefixEnd_2033027 463964459808143336094571 := by
  unfold tailWord_2033027
  simp only [CollatzResearch.WordTrace]
  refine ⟨74150586405697867213641335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49433724270465244809094223 74150586405697867213641335)
  ·
    refine ⟨111225879608546800820462003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74150586405697867213641335 111225879608546800820462003)
    ·
      refine ⟨166838819412820201230693005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111225879608546800820462003 166838819412820201230693005)
      ·
        refine ⟨62564557279807575461509877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166838819412820201230693005 62564557279807575461509877)
        ·
          refine ⟨5865427244981960199516551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62564557279807575461509877 5865427244981960199516551)
          ·
            refine ⟨8798140867472940299274827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5865427244981960199516551 8798140867472940299274827)
            ·
              refine ⟨13197211301209410448912241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798140867472940299274827 13197211301209410448912241)
              ·
                refine ⟨9897908475907057836684181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13197211301209410448912241 9897908475907057836684181)
                ·
                  refine ⟨463964459808143336094571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9897908475907057836684181 463964459808143336094571)
                  ·
                    rfl

theorem cell21_2033027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_2033027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033027 prefixEnd_2033027 := by exact prefixLift 2033027
  have htrace : WordTrace (prefixWord ++ tailWord_2033027) baseStart_2033027 baseEnd_2033027 := by
    simpa [prefixWord, tailWord_2033027, baseEnd_2033027] using wordTrace_append hprefix tailTrace_2033027
  have hstable : (prefixWord ++ tailWord_2033027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033027).length < 2 ^ (prefixWord ++ tailWord_2033027).sum := by decide
  have hdescent : baseEnd_2033027 < baseStart_2033027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033044 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_2033044 : Nat := 118140960795 + 2033044 * 2 ^ 59
def prefixEnd_2033044 : Nat := 4983230072969 + 3 ^ 40 * 2033044 * 2
def baseEnd_2033044 : Nat := 463968339439755084311203

theorem tailTrace_2033044 : CollatzResearch.WordTrace tailWord_2033044 prefixEnd_2033044 463968339439755084311203 := by
  unfold tailWord_2033044
  simp only [CollatzResearch.WordTrace]
  refine ⟨37075603223318139558505093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49434137631090852744673457 37075603223318139558505093)
  ·
    refine ⟨6951675604372151167219705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37075603223318139558505093 6951675604372151167219705)
    ·
      refine ⟨5213756703279113375414779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6951675604372151167219705 5213756703279113375414779)
      ·
        refine ⟨7820635054918670063122169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5213756703279113375414779 7820635054918670063122169)
        ·
          refine ⟨5865476291189002547341627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7820635054918670063122169 5865476291189002547341627)
          ·
            refine ⟨8798214436783503821012441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5865476291189002547341627 8798214436783503821012441)
            ·
              refine ⟨6598660827587627865759331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8798214436783503821012441 6598660827587627865759331)
              ·
                refine ⟨9897991241381441798638997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598660827587627865759331 9897991241381441798638997)
                ·
                  refine ⟨463968339439755084311203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9897991241381441798638997 463968339439755084311203)
                  ·
                    rfl

theorem cell21_2033044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_2033044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033044 prefixEnd_2033044 := by exact prefixLift 2033044
  have htrace : WordTrace (prefixWord ++ tailWord_2033044) baseStart_2033044 baseEnd_2033044 := by
    simpa [prefixWord, tailWord_2033044, baseEnd_2033044] using wordTrace_append hprefix tailTrace_2033044
  have hstable : (prefixWord ++ tailWord_2033044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033044).length < 2 ^ (prefixWord ++ tailWord_2033044).sum := by decide
  have hdescent : baseEnd_2033044 < baseStart_2033044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033058 : List Nat := [3, 3, 1, 2, 1, 2, 1, 8]
def baseStart_2033058 : Nat := 118140960795 + 2033058 * 2 ^ 59
def prefixEnd_2033058 : Nat := 4983230072969 + 3 ^ 40 * 2033058 * 2
def baseEnd_2033058 : Nat := 154657178143498057025947

theorem tailTrace_2033058 : CollatzResearch.WordTrace tailWord_2033058 prefixEnd_2033058 154657178143498057025947 := by
  unfold tailWord_2033058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18537929267146389877004957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49434478045723706338679885 18537929267146389877004957)
  ·
    refine ⟨6951723475179896203876859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18537929267146389877004957 6951723475179896203876859)
    ·
      refine ⟨10427585212769844305815289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6951723475179896203876859 10427585212769844305815289)
      ·
        refine ⟨7820688909577383229361467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10427585212769844305815289 7820688909577383229361467)
        ·
          refine ⟨11731033364366074844042201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820688909577383229361467 11731033364366074844042201)
          ·
            refine ⟨8798275023274556133031651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11731033364366074844042201 8798275023274556133031651)
            ·
              refine ⟨13197412534911834199547477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798275023274556133031651 13197412534911834199547477)
              ·
                refine ⟨154657178143498057025947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13197412534911834199547477 154657178143498057025947)
                ·
                  rfl

theorem cell21_2033058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_2033058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033058 prefixEnd_2033058 := by exact prefixLift 2033058
  have htrace : WordTrace (prefixWord ++ tailWord_2033058) baseStart_2033058 baseEnd_2033058 := by
    simpa [prefixWord, tailWord_2033058, baseEnd_2033058] using wordTrace_append hprefix tailTrace_2033058
  have hstable : (prefixWord ++ tailWord_2033058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033058).length < 2 ^ (prefixWord ++ tailWord_2033058).sum := by decide
  have hdescent : baseEnd_2033058 < baseStart_2033058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033103 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 4]
def baseStart_2033103 : Nat := 118140960795 + 2033103 * 2 ^ 59
def prefixEnd_2033103 : Nat := 4983230072969 + 3 ^ 40 * 2033103 * 2
def baseEnd_2033103 : Nat := 463981804043584092827749

theorem tailTrace_2033103 : CollatzResearch.WordTrace tailWord_2033103 prefixEnd_2033103 463981804043584092827749 := by
  unfold tailWord_2033103
  simp only [CollatzResearch.WordTrace]
  refine ⟨74153358353422532193407963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49435572235615021462271975 74153358353422532193407963)
  ·
    refine ⟨111230037530133798290111945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74153358353422532193407963 111230037530133798290111945)
    ·
      refine ⟨83422528147600348717583959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111230037530133798290111945 83422528147600348717583959)
      ·
        refine ⟨125133792221400523076375939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83422528147600348717583959 125133792221400523076375939)
        ·
          refine ⟨187700688332100784614563909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125133792221400523076375939 187700688332100784614563909)
          ·
            refine ⟨35193879062268897115230733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187700688332100784614563909 35193879062268897115230733)
            ·
              refine ⟨13197704648350836418211525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35193879062268897115230733 13197704648350836418211525)
              ·
                refine ⟨2474569621565781828414661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13197704648350836418211525 2474569621565781828414661)
                ·
                  refine ⟨463981804043584092827749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474569621565781828414661 463981804043584092827749)
                  ·
                    rfl

theorem cell21_2033103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 4].length) (baseStart_2033103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033103 prefixEnd_2033103 := by exact prefixLift 2033103
  have htrace : WordTrace (prefixWord ++ tailWord_2033103) baseStart_2033103 baseEnd_2033103 := by
    simpa [prefixWord, tailWord_2033103, baseEnd_2033103] using wordTrace_append hprefix tailTrace_2033103
  have hstable : (prefixWord ++ tailWord_2033103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033103).length < 2 ^ (prefixWord ++ tailWord_2033103).sum := by decide
  have hdescent : baseEnd_2033103 < baseStart_2033103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033154 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2033154 : Nat := 118140960795 + 2033154 * 2 ^ 59
def prefixEnd_2033154 : Nat := 4983230072969 + 3 ^ 40 * 2033154 * 2
def baseEnd_2033154 : Nat := 463993442938419337477645

theorem tailTrace_2033154 : CollatzResearch.WordTrace tailWord_2033154 prefixEnd_2033154 463993442938419337477645 := by
  unfold tailWord_2033154
  simp only [CollatzResearch.WordTrace]
  refine ⟨18538804619059441975878629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49436812317491845269009677 18538804619059441975878629)
  ·
    refine ⟨3476025866073645370477243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18538804619059441975878629 3476025866073645370477243)
    ·
      refine ⟨5214038799110468055715865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3476025866073645370477243 5214038799110468055715865)
      ·
        refine ⟨3910529099332851041786899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5214038799110468055715865 3910529099332851041786899)
        ·
          refine ⟨5865793648999276562680349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910529099332851041786899 5865793648999276562680349)
          ·
            refine ⟨2199672618374728711005131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5865793648999276562680349 2199672618374728711005131)
            ·
              refine ⟨3299508927562093066507697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199672618374728711005131 3299508927562093066507697)
              ·
                refine ⟨2474631695671569799880773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3299508927562093066507697 2474631695671569799880773)
                ·
                  refine ⟨463993442938419337477645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474631695671569799880773 463993442938419337477645)
                  ·
                    rfl

theorem cell21_2033154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2033154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033154 prefixEnd_2033154 := by exact prefixLift 2033154
  have htrace : WordTrace (prefixWord ++ tailWord_2033154) baseStart_2033154 baseEnd_2033154 := by
    simpa [prefixWord, tailWord_2033154, baseEnd_2033154] using wordTrace_append hprefix tailTrace_2033154
  have hstable : (prefixWord ++ tailWord_2033154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033154).length < 2 ^ (prefixWord ++ tailWord_2033154).sum := by decide
  have hdescent : baseEnd_2033154 < baseStart_2033154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033317 : List Nat := [1, 3, 1, 2, 1, 2, 3, 5, 3]
def baseStart_2033317 : Nat := 118140960795 + 2033317 * 2 ^ 59
def prefixEnd_2033317 : Nat := 4983230072969 + 3 ^ 40 * 2033317 * 2
def baseEnd_2033317 : Nat := 464030641759167276260645

theorem tailTrace_2033317 : CollatzResearch.WordTrace tailWord_2033317 prefixEnd_2033317 464030641759167276260645 := by
  unfold tailWord_2033317
  simp only [CollatzResearch.WordTrace]
  refine ⟨74161163574647246741698205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49440775716431497827798803 74161163574647246741698205)
  ·
    refine ⟨27810436340492717528136827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74161163574647246741698205 27810436340492717528136827)
    ·
      refine ⟨41715654510739076292205241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27810436340492717528136827 41715654510739076292205241)
      ·
        refine ⟨31286740883054307219153931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41715654510739076292205241 31286740883054307219153931)
        ·
          refine ⟨46930111324581460828730897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31286740883054307219153931 46930111324581460828730897)
          ·
            refine ⟨35197583493436095621548173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46930111324581460828730897 35197583493436095621548173)
            ·
              refine ⟨13199093810038535858080565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35197583493436095621548173 13199093810038535858080565)
              ·
                refine ⟨1237415044691112736695053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13199093810038535858080565 1237415044691112736695053)
                ·
                  refine ⟨464030641759167276260645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237415044691112736695053 464030641759167276260645)
                  ·
                    rfl

theorem cell21_2033317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_2033317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033317 prefixEnd_2033317 := by exact prefixLift 2033317
  have htrace : WordTrace (prefixWord ++ tailWord_2033317) baseStart_2033317 baseEnd_2033317 := by
    simpa [prefixWord, tailWord_2033317, baseEnd_2033317] using wordTrace_append hprefix tailTrace_2033317
  have hstable : (prefixWord ++ tailWord_2033317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033317).length < 2 ^ (prefixWord ++ tailWord_2033317).sum := by decide
  have hdescent : baseEnd_2033317 < baseStart_2033317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033320 : List Nat := [2, 1, 7, 1, 1, 1, 8]
def baseStart_2033320 : Nat := 118140960795 + 2033320 * 2 ^ 59
def prefixEnd_2033320 : Nat := 4983230072969 + 3 ^ 40 * 2033320 * 2
def baseEnd_2033320 : Nat := 51559036266671104190071

theorem tailTrace_2033320 : CollatzResearch.WordTrace tailWord_2033320 prefixEnd_2033320 51559036266671104190071 := by
  unfold tailWord_2033320
  simp only [CollatzResearch.WordTrace]
  refine ⟨37080636496818189127028707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49440848662424252169371609 37080636496818189127028707)
  ·
    refine ⟨55620954745227283690543061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37080636496818189127028707 55620954745227283690543061)
    ·
      refine ⟨1303616126841264461497103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 55620954745227283690543061 1303616126841264461497103)
      ·
        refine ⟨1955424190261896692245655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303616126841264461497103 1955424190261896692245655)
        ·
          refine ⟨2933136285392845038368483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955424190261896692245655 2933136285392845038368483)
          ·
            refine ⟨4399704428089267557552725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933136285392845038368483 4399704428089267557552725)
            ·
              refine ⟨51559036266671104190071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4399704428089267557552725 51559036266671104190071)
              ·
                rfl

theorem cell21_2033320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 8].length) (baseStart_2033320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033320 prefixEnd_2033320 := by exact prefixLift 2033320
  have htrace : WordTrace (prefixWord ++ tailWord_2033320) baseStart_2033320 baseEnd_2033320 := by
    simpa [prefixWord, tailWord_2033320, baseEnd_2033320] using wordTrace_append hprefix tailTrace_2033320
  have hstable : (prefixWord ++ tailWord_2033320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033320).length < 2 ^ (prefixWord ++ tailWord_2033320).sum := by decide
  have hdescent : baseEnd_2033320 < baseStart_2033320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033334 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2033334 : Nat := 118140960795 + 2033334 * 2 ^ 59
def prefixEnd_2033334 : Nat := 4983230072969 + 3 ^ 40 * 2033334 * 2
def baseEnd_2033334 : Nat := 464034521390779024477277

theorem tailTrace_2033334 : CollatzResearch.WordTrace tailWord_2033334 prefixEnd_2033334 464034521390779024477277 := by
  unfold tailWord_2033334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4635111475974103665316691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49441189077057105763378037 4635111475974103665316691)
  ·
    refine ⟨6952667213961155497975037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4635111475974103665316691 6952667213961155497975037)
    ·
      refine ⟨2607250205235433311740639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6952667213961155497975037 2607250205235433311740639)
      ·
        refine ⟨3910875307853149967610959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607250205235433311740639 3910875307853149967610959)
        ·
          refine ⟨5866312961779724951416439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910875307853149967610959 5866312961779724951416439)
          ·
            refine ⟨8799469442669587427124659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866312961779724951416439 8799469442669587427124659)
            ·
              refine ⟨13199204164004381140686989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799469442669587427124659 13199204164004381140686989)
              ·
                refine ⟨4949701561501642927757621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13199204164004381140686989 4949701561501642927757621)
                ·
                  refine ⟨464034521390779024477277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4949701561501642927757621 464034521390779024477277)
                  ·
                    rfl

theorem cell21_2033334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2033334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033334 prefixEnd_2033334 := by exact prefixLift 2033334
  have htrace : WordTrace (prefixWord ++ tailWord_2033334) baseStart_2033334 baseEnd_2033334 := by
    simpa [prefixWord, tailWord_2033334, baseEnd_2033334] using wordTrace_append hprefix tailTrace_2033334
  have hstable : (prefixWord ++ tailWord_2033334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033334).length < 2 ^ (prefixWord ++ tailWord_2033334).sum := by decide
  have hdescent : baseEnd_2033334 < baseStart_2033334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033362 : List Nat := [3, 2, 2, 2, 2, 2, 1, 7]
def baseStart_2033362 : Nat := 118140960795 + 2033362 * 2 ^ 59
def prefixEnd_2033362 : Nat := 4983230072969 + 3 ^ 40 * 2033362 * 2
def baseEnd_2033362 : Nat := 154680303790752399336851

theorem tailTrace_2033362 : CollatzResearch.WordTrace tailWord_2033362 prefixEnd_2033362 154680303790752399336851 := by
  unfold tailWord_2033362
  simp only [CollatzResearch.WordTrace]
  refine ⟨18540701214871054856771585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49441869906322812951390893 18540701214871054856771585)
  ·
    refine ⟨13905525911153291142578689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18540701214871054856771585 13905525911153291142578689)
    ·
      refine ⟨10429144433364968356934017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13905525911153291142578689 10429144433364968356934017)
      ·
        refine ⟨7821858325023726267700513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10429144433364968356934017 7821858325023726267700513)
        ·
          refine ⟨5866393743767794700775385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7821858325023726267700513 5866393743767794700775385)
          ·
            refine ⟨4399795307825846025581539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5866393743767794700775385 4399795307825846025581539)
            ·
              refine ⟨6599692961738769038372309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4399795307825846025581539 6599692961738769038372309)
              ·
                refine ⟨154680303790752399336851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6599692961738769038372309 154680303790752399336851)
                ·
                  rfl

theorem cell21_2033362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_2033362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033362 prefixEnd_2033362 := by exact prefixLift 2033362
  have htrace : WordTrace (prefixWord ++ tailWord_2033362) baseStart_2033362 baseEnd_2033362 := by
    simpa [prefixWord, tailWord_2033362, baseEnd_2033362] using wordTrace_append hprefix tailTrace_2033362
  have hstable : (prefixWord ++ tailWord_2033362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033362).length < 2 ^ (prefixWord ++ tailWord_2033362).sum := by decide
  have hdescent : baseEnd_2033362 < baseStart_2033362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033379 : List Nat := [1, 1, 1, 7, 3, 1, 7]
def baseStart_2033379 : Nat := 118140960795 + 2033379 * 2 ^ 59
def prefixEnd_2033379 : Nat := 4983230072969 + 3 ^ 40 * 2033379 * 2
def baseEnd_2033379 : Nat := 51560532333763216247465

theorem tailTrace_2033379 : CollatzResearch.WordTrace tailWord_2033379 prefixEnd_2033379 51560532333763216247465 := by
  unfold tailWord_2033379
  simp only [CollatzResearch.WordTrace]
  refine ⟨74163424900422631330455191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49442283266948420886970127 74163424900422631330455191)
  ·
    refine ⟨111245137350633946995682787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74163424900422631330455191 111245137350633946995682787)
    ·
      refine ⟨166867706025950920493524181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111245137350633946995682787 166867706025950920493524181)
      ·
        refine ⟨3910961859983224699066973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 166867706025950920493524181 3910961859983224699066973)
        ·
          refine ⟨1466610697493709262150115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3910961859983224699066973 1466610697493709262150115)
          ·
            refine ⟨2199916046240563893225173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466610697493709262150115 2199916046240563893225173)
            ·
              refine ⟨51560532333763216247465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2199916046240563893225173 51560532333763216247465)
              ·
                rfl

theorem cell21_2033379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 7].length) (baseStart_2033379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033379 prefixEnd_2033379 := by exact prefixLift 2033379
  have htrace : WordTrace (prefixWord ++ tailWord_2033379) baseStart_2033379 baseEnd_2033379 := by
    simpa [prefixWord, tailWord_2033379, baseEnd_2033379] using wordTrace_append hprefix tailTrace_2033379
  have hstable : (prefixWord ++ tailWord_2033379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033379).length < 2 ^ (prefixWord ++ tailWord_2033379).sum := by decide
  have hdescent : baseEnd_2033379 < baseStart_2033379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033393 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 5]
def baseStart_2033393 : Nat := 118140960795 + 2033393 * 2 ^ 59
def prefixEnd_2033393 : Nat := 4983230072969 + 3 ^ 40 * 2033393 * 2
def baseEnd_2033393 : Nat := 464047985994608032993823

theorem tailTrace_2033393 : CollatzResearch.WordTrace tailWord_2033393 prefixEnd_2033393 464047985994608032993823 := by
  unfold tailWord_2033393
  simp only [CollatzResearch.WordTrace]
  refine ⟨74163935522371911721464833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49442623681581274480976555 74163935522371911721464833)
  ·
    refine ⟨55622951641778933791098625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74163935522371911721464833 55622951641778933791098625)
    ·
      refine ⟨41717213731334200343323969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55622951641778933791098625 41717213731334200343323969)
      ·
        refine ⟨31287910298500650257492977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41717213731334200343323969 31287910298500650257492977)
        ·
          refine ⟨23465932723875487693119733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31287910298500650257492977 23465932723875487693119733)
          ·
            refine ⟨2199931192863326971229975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23465932723875487693119733 2199931192863326971229975)
            ·
              refine ⟨3299896789294990456844963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199931192863326971229975 3299896789294990456844963)
              ·
                refine ⟨4949845183942485685267445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3299896789294990456844963 4949845183942485685267445)
                ·
                  refine ⟨464047985994608032993823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4949845183942485685267445 464047985994608032993823)
                  ·
                    rfl

theorem cell21_2033393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_2033393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033393 prefixEnd_2033393 := by exact prefixLift 2033393
  have htrace : WordTrace (prefixWord ++ tailWord_2033393) baseStart_2033393 baseEnd_2033393 := by
    simpa [prefixWord, tailWord_2033393, baseEnd_2033393] using wordTrace_append hprefix tailTrace_2033393
  have hstable : (prefixWord ++ tailWord_2033393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033393).length < 2 ^ (prefixWord ++ tailWord_2033393).sum := by decide
  have hdescent : baseEnd_2033393 < baseStart_2033393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033396 : List Nat := [2, 6, 1, 1, 1, 2, 2, 6]
def baseStart_2033396 : Nat := 118140960795 + 2033396 * 2 ^ 59
def prefixEnd_2033396 : Nat := 4983230072969 + 3 ^ 40 * 2033396 * 2
def baseEnd_2033396 : Nat := 154682890211826898147939

theorem tailTrace_2033396 : CollatzResearch.WordTrace tailWord_2033396 prefixEnd_2033396 154682890211826898147939 := by
  unfold tailWord_2033396
  simp only [CollatzResearch.WordTrace]
  refine ⟨37082022470680521616912021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49442696627574028822549361 37082022470680521616912021)
  ·
    refine ⟨1738219803313149450792751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37082022470680521616912021 1738219803313149450792751)
    ·
      refine ⟨2607329704969724176189127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1738219803313149450792751 2607329704969724176189127)
      ·
        refine ⟨3910994557454586264283691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607329704969724176189127 3910994557454586264283691)
        ·
          refine ⟨5866491836181879396425537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910994557454586264283691 5866491836181879396425537)
          ·
            refine ⟨4399868877136409547319153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5866491836181879396425537 4399868877136409547319153)
            ·
              refine ⟨3299901657852307160489365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4399868877136409547319153 3299901657852307160489365)
              ·
                refine ⟨154682890211826898147939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3299901657852307160489365 154682890211826898147939)
                ·
                  rfl

theorem cell21_2033396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_2033396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033396 prefixEnd_2033396 := by exact prefixLift 2033396
  have htrace : WordTrace (prefixWord ++ tailWord_2033396) baseStart_2033396 baseEnd_2033396 := by
    simpa [prefixWord, tailWord_2033396, baseEnd_2033396] using wordTrace_append hprefix tailTrace_2033396
  have hstable : (prefixWord ++ tailWord_2033396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033396).length < 2 ^ (prefixWord ++ tailWord_2033396).sum := by decide
  have hdescent : baseEnd_2033396 < baseStart_2033396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033435 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 7]
def baseStart_2033435 : Nat := 118140960795 + 2033435 * 2 ^ 59
def prefixEnd_2033435 : Nat := 4983230072969 + 3 ^ 40 * 2033435 * 2
def baseEnd_2033435 : Nat := 464057570966825293293737

theorem tailTrace_2033435 : CollatzResearch.WordTrace tailWord_2033435 prefixEnd_2033435 464057570966825293293737 := by
  unfold tailWord_2033435
  simp only [CollatzResearch.WordTrace]
  refine ⟨74165467388219752894493759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49443644925479835262995839 74165467388219752894493759)
  ·
    refine ⟨111248201082329629341740639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74165467388219752894493759 111248201082329629341740639)
    ·
      refine ⟨166872301623494444012610959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111248201082329629341740639 166872301623494444012610959)
      ·
        refine ⟨250308452435241666018916439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166872301623494444012610959 250308452435241666018916439)
        ·
          refine ⟨375462678652862499028374659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250308452435241666018916439 375462678652862499028374659)
          ·
            refine ⟨563194017979293748542561989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375462678652862499028374659 563194017979293748542561989)
            ·
              refine ⟨105598878371117577851730373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 563194017979293748542561989 105598878371117577851730373)
              ·
                refine ⟨19799789694584545847199445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105598878371117577851730373 19799789694584545847199445)
                ·
                  refine ⟨464057570966825293293737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19799789694584545847199445 464057570966825293293737)
                  ·
                    rfl

theorem cell21_2033435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_2033435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033435 prefixEnd_2033435 := by exact prefixLift 2033435
  have htrace : WordTrace (prefixWord ++ tailWord_2033435) baseStart_2033435 baseEnd_2033435 := by
    simpa [prefixWord, tailWord_2033435, baseEnd_2033435] using wordTrace_append hprefix tailTrace_2033435
  have hstable : (prefixWord ++ tailWord_2033435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033435).length < 2 ^ (prefixWord ++ tailWord_2033435).sum := by decide
  have hdescent : baseEnd_2033435 < baseStart_2033435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033469 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 5]
def baseStart_2033469 : Nat := 118140960795 + 2033469 * 2 ^ 59
def prefixEnd_2033469 : Nat := 4983230072969 + 3 ^ 40 * 2033469 * 2
def baseEnd_2033469 : Nat := 464065330230048789727001

theorem tailTrace_2033469 : CollatzResearch.WordTrace tailWord_2033469 prefixEnd_2033469 464065330230048789727001 := by
  unfold tailWord_2033469
  simp only [CollatzResearch.WordTrace]
  refine ⟨74166707470096576701231461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49444471646731051134154307 74166707470096576701231461)
  ·
    refine ⟨13906257650643108131480899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74166707470096576701231461 13906257650643108131480899)
    ·
      refine ⟨20859386475964662197221349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13906257650643108131480899 20859386475964662197221349)
      ·
        refine ⟨3911134964243374161979003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20859386475964662197221349 3911134964243374161979003)
        ·
          refine ⟨5866702446365061242968505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911134964243374161979003 5866702446365061242968505)
          ·
            refine ⟨4400026834773795932226379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5866702446365061242968505 4400026834773795932226379)
            ·
              refine ⟨6600040252160693898339569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400026834773795932226379 6600040252160693898339569)
              ·
                refine ⟨4950030189120520423754677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6600040252160693898339569 4950030189120520423754677)
                ·
                  refine ⟨464065330230048789727001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4950030189120520423754677 464065330230048789727001)
                  ·
                    rfl

theorem cell21_2033469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_2033469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033469 prefixEnd_2033469 := by exact prefixLift 2033469
  have htrace : WordTrace (prefixWord ++ tailWord_2033469) baseStart_2033469 baseEnd_2033469 := by
    simpa [prefixWord, tailWord_2033469, baseEnd_2033469] using wordTrace_append hprefix tailTrace_2033469
  have hstable : (prefixWord ++ tailWord_2033469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033469).length < 2 ^ (prefixWord ++ tailWord_2033469).sum := by decide
  have hdescent : baseEnd_2033469 < baseStart_2033469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033500 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 6]
def baseStart_2033500 : Nat := 118140960795 + 2033500 * 2 ^ 59
def prefixEnd_2033500 : Nat := 4983230072969 + 3 ^ 40 * 2033500 * 2
def baseEnd_2033500 : Nat := 464072404852399624710271

theorem tailTrace_2033500 : CollatzResearch.WordTrace tailWord_2033500 prefixEnd_2033500 464072404852399624710271 := by
  unfold tailWord_2033500
  simp only [CollatzResearch.WordTrace]
  refine ⟨37083919066492134497804977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49445225421989512663739969 37083919066492134497804977)
  ·
    refine ⟨27812939299869100873353733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37083919066492134497804977 27812939299869100873353733)
    ·
      refine ⟨5214926118725456413753825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27812939299869100873353733 5214926118725456413753825)
      ·
        refine ⟨3911194589044092310315369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5214926118725456413753825 3911194589044092310315369)
        ·
          refine ⟨2933395941783069232736527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3911194589044092310315369 2933395941783069232736527)
          ·
            refine ⟨4400093912674603849104791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933395941783069232736527 4400093912674603849104791)
            ·
              refine ⟨6600140869011905773657187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400093912674603849104791 6600140869011905773657187)
              ·
                refine ⟨9900211303517858660485781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6600140869011905773657187 9900211303517858660485781)
                ·
                  refine ⟨464072404852399624710271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9900211303517858660485781 464072404852399624710271)
                  ·
                    rfl

theorem cell21_2033500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_2033500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033500 prefixEnd_2033500 := by exact prefixLift 2033500
  have htrace : WordTrace (prefixWord ++ tailWord_2033500) baseStart_2033500 baseEnd_2033500 := by
    simpa [prefixWord, tailWord_2033500, baseEnd_2033500] using wordTrace_append hprefix tailTrace_2033500
  have hstable : (prefixWord ++ tailWord_2033500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033500).length < 2 ^ (prefixWord ++ tailWord_2033500).sum := by decide
  have hdescent : baseEnd_2033500 < baseStart_2033500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033587 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 7]
def baseStart_2033587 : Nat := 118140960795 + 2033587 * 2 ^ 59
def prefixEnd_2033587 : Nat := 4983230072969 + 3 ^ 40 * 2033587 * 2
def baseEnd_2033587 : Nat := 464092259437706806760093

theorem tailTrace_2033587 : CollatzResearch.WordTrace tailWord_2033587 prefixEnd_2033587 464092259437706806760093 := by
  unfold tailWord_2033587
  simp only [CollatzResearch.WordTrace]
  refine ⟨74171011283669082854027015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49447340855779388569351343 74171011283669082854027015)
  ·
    refine ⟨111256516925503624281040523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74171011283669082854027015 111256516925503624281040523)
    ·
      refine ⟨166884775388255436421560785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111256516925503624281040523 166884775388255436421560785)
      ·
        refine ⟨125163581541191577316170589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166884775388255436421560785 125163581541191577316170589)
        ·
          refine ⟨46936343077946841493563971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125163581541191577316170589 46936343077946841493563971)
          ·
            refine ⟨70404514616920262240345957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46936343077946841493563971 70404514616920262240345957)
            ·
              refine ⟨13200846490672549170064867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70404514616920262240345957 13200846490672549170064867)
              ·
                refine ⟨19801269736008823755097301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13200846490672549170064867 19801269736008823755097301)
                ·
                  refine ⟨464092259437706806760093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19801269736008823755097301 464092259437706806760093)
                  ·
                    rfl

theorem cell21_2033587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_2033587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033587 prefixEnd_2033587 := by exact prefixLift 2033587
  have htrace : WordTrace (prefixWord ++ tailWord_2033587) baseStart_2033587 baseEnd_2033587 := by
    simpa [prefixWord, tailWord_2033587, baseEnd_2033587] using wordTrace_append hprefix tailTrace_2033587
  have hstable : (prefixWord ++ tailWord_2033587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033587).length < 2 ^ (prefixWord ++ tailWord_2033587).sum := by decide
  have hdescent : baseEnd_2033587 < baseStart_2033587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033635 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 4]
def baseStart_2033635 : Nat := 118140960795 + 2033635 * 2 ^ 59
def prefixEnd_2033635 : Nat := 4983230072969 + 3 ^ 40 * 2033635 * 2
def baseEnd_2033635 : Nat := 464103213691669389959995

theorem tailTrace_2033635 : CollatzResearch.WordTrace tailWord_2033635 prefixEnd_2033635 464103213691669389959995 := by
  unfold tailWord_2033635
  simp only [CollatzResearch.WordTrace]
  refine ⟨74172761987495187051774359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49448507991663458034516239 74172761987495187051774359)
  ·
    refine ⟨111259142981242780577661539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74172761987495187051774359 111259142981242780577661539)
    ·
      refine ⟨166888714471864170866492309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111259142981242780577661539 166888714471864170866492309)
      ·
        refine ⟨7822908490868633009366827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166888714471864170866492309 7822908490868633009366827)
        ·
          refine ⟨11734362736302949514050241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7822908490868633009366827 11734362736302949514050241)
          ·
            refine ⟨8800772052227212135537681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11734362736302949514050241 8800772052227212135537681)
            ·
              refine ⟨6600579039170409101653261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8800772052227212135537681 6600579039170409101653261)
              ·
                refine ⟨2475217139688903413119973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6600579039170409101653261 2475217139688903413119973)
                ·
                  refine ⟨464103213691669389959995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2475217139688903413119973 464103213691669389959995)
                  ·
                    rfl

theorem cell21_2033635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 4].length) (baseStart_2033635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033635 prefixEnd_2033635 := by exact prefixLift 2033635
  have htrace : WordTrace (prefixWord ++ tailWord_2033635) baseStart_2033635 baseEnd_2033635 := by
    simpa [prefixWord, tailWord_2033635, baseEnd_2033635] using wordTrace_append hprefix tailTrace_2033635
  have hstable : (prefixWord ++ tailWord_2033635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033635).length < 2 ^ (prefixWord ++ tailWord_2033635).sum := by decide
  have hdescent : baseEnd_2033635 < baseStart_2033635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033700 : List Nat := [2, 3, 1, 4, 3, 1, 2, 5]
def baseStart_2033700 : Nat := 118140960795 + 2033700 * 2 ^ 59
def prefixEnd_2033700 : Nat := 4983230072969 + 3 ^ 40 * 2033700 * 2
def baseEnd_2033700 : Nat := 154706015859081240458843

theorem tailTrace_2033700 : CollatzResearch.WordTrace tailWord_2033700 prefixEnd_2033700 154706015859081240458843 := by
  unfold tailWord_2033700
  simp only [CollatzResearch.WordTrace]
  refine ⟨37087566366129851576445277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49450088488173135435260369 37087566366129851576445277)
  ·
    refine ⟨13907837387298694341166979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37087566366129851576445277 13907837387298694341166979)
    ·
      refine ⟨20861756080948041511750469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13907837387298694341166979 20861756080948041511750469)
      ·
        refine ⟨3911579265177757783453213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20861756080948041511750469 3911579265177757783453213)
        ·
          refine ⟨1466842224441659168794955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3911579265177757783453213 1466842224441659168794955)
          ·
            refine ⟨2200263336662488753192433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466842224441659168794955 2200263336662488753192433)
            ·
              refine ⟨1650197502496866564894325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2200263336662488753192433 1650197502496866564894325)
              ·
                refine ⟨154706015859081240458843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1650197502496866564894325 154706015859081240458843)
                ·
                  rfl

theorem cell21_2033700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 5].length) (baseStart_2033700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033700 prefixEnd_2033700 := by exact prefixLift 2033700
  have htrace : WordTrace (prefixWord ++ tailWord_2033700) baseStart_2033700 baseEnd_2033700 := by
    simpa [prefixWord, tailWord_2033700, baseEnd_2033700] using wordTrace_append hprefix tailTrace_2033700
  have hstable : (prefixWord ++ tailWord_2033700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033700).length < 2 ^ (prefixWord ++ tailWord_2033700).sum := by decide
  have hdescent : baseEnd_2033700 < baseStart_2033700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033714 : List Nat := [3, 2, 1, 1, 2, 5, 1, 3, 3]
def baseStart_2033714 : Nat := 118140960795 + 2033714 * 2 ^ 59
def prefixEnd_2033714 : Nat := 4983230072969 + 3 ^ 40 * 2033714 * 2
def baseEnd_2033714 : Nat := 464121242567982808143167

theorem tailTrace_2033714 : CollatzResearch.WordTrace tailWord_2033714 prefixEnd_2033714 464121242567982808143167 := by
  unfold tailWord_2033714
  simp only [CollatzResearch.WordTrace]
  refine ⟨18543910838552245885975049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49450428902805989029266797 18543910838552245885975049)
  ·
    refine ⟨13907933128914184414481287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18543910838552245885975049 13907933128914184414481287)
    ·
      refine ⟨20861899693371276621721931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13907933128914184414481287 20861899693371276621721931)
      ·
        refine ⟨31292849540056914932582897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20861899693371276621721931 31292849540056914932582897)
        ·
          refine ⟨23469637155042686199437173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31292849540056914932582897 23469637155042686199437173)
          ·
            refine ⟨2200278483285251831197235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23469637155042686199437173 2200278483285251831197235)
            ·
              refine ⟨3300417724927877746795853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200278483285251831197235 3300417724927877746795853)
              ·
                refine ⟨1237656646847954155048445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3300417724927877746795853 1237656646847954155048445)
                ·
                  refine ⟨464121242567982808143167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237656646847954155048445 464121242567982808143167)
                  ·
                    rfl

theorem cell21_2033714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_2033714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033714 prefixEnd_2033714 := by exact prefixLift 2033714
  have htrace : WordTrace (prefixWord ++ tailWord_2033714) baseStart_2033714 baseEnd_2033714 := by
    simpa [prefixWord, tailWord_2033714, baseEnd_2033714] using wordTrace_append hprefix tailTrace_2033714
  have hstable : (prefixWord ++ tailWord_2033714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033714).length < 2 ^ (prefixWord ++ tailWord_2033714).sum := by decide
  have hdescent : baseEnd_2033714 < baseStart_2033714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033773 : List Nat := [1, 5, 1, 1, 2, 1, 2, 5, 3]
def baseStart_2033773 : Nat := 118140960795 + 2033773 * 2 ^ 59
def prefixEnd_2033773 : Nat := 4983230072969 + 3 ^ 40 * 2033773 * 2
def baseEnd_2033773 : Nat := 464134707171811816659713

theorem tailTrace_2033773 : CollatzResearch.WordTrace tailWord_2033773 prefixEnd_2033773 464134707171811816659713 := by
  unfold tailWord_2033773
  simp only [CollatzResearch.WordTrace]
  refine ⟨74177795260995236620297973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49451863507330157746865315 74177795260995236620297973)
  ·
    refine ⟨6954168305718303433152935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74177795260995236620297973 6954168305718303433152935)
    ·
      refine ⟨10431252458577455149729403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6954168305718303433152935 10431252458577455149729403)
      ·
        refine ⟨15646878687866182724594105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10431252458577455149729403 15646878687866182724594105)
        ·
          refine ⟨11735159015899637043445579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15646878687866182724594105 11735159015899637043445579)
          ·
            refine ⟨17602738523849455565168369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11735159015899637043445579 17602738523849455565168369)
            ·
              refine ⟨13202053892887091673876277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17602738523849455565168369 13202053892887091673876277)
              ·
                refine ⟨1237692552458164844425901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13202053892887091673876277 1237692552458164844425901)
                ·
                  refine ⟨464134707171811816659713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237692552458164844425901 464134707171811816659713)
                  ·
                    rfl

theorem cell21_2033773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_2033773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033773 prefixEnd_2033773 := by exact prefixLift 2033773
  have htrace : WordTrace (prefixWord ++ tailWord_2033773) baseStart_2033773 baseEnd_2033773 := by
    simpa [prefixWord, tailWord_2033773, baseEnd_2033773] using wordTrace_append hprefix tailTrace_2033773
  have hstable : (prefixWord ++ tailWord_2033773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033773).length < 2 ^ (prefixWord ++ tailWord_2033773).sum := by decide
  have hdescent : baseEnd_2033773 < baseStart_2033773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033838 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_2033838 : Nat := 118140960795 + 2033838 * 2 ^ 59
def prefixEnd_2033838 : Nat := 4983230072969 + 3 ^ 40 * 2033838 * 2
def baseEnd_2033838 : Nat := 464149541057386148076247

theorem tailTrace_2033838 : CollatzResearch.WordTrace tailWord_2033838 prefixEnd_2033838 464149541057386148076247 := by
  unfold tailWord_2033838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272520750719969090176771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49453444003839835147609445 9272520750719969090176771)
  ·
    refine ⟨13908781126079953635265157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9272520750719969090176771 13908781126079953635265157)
    ·
      refine ⟨2607896461139991306612217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13908781126079953635265157 2607896461139991306612217)
      ·
        refine ⟨1955922345854993479959163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2607896461139991306612217 1955922345854993479959163)
        ·
          refine ⟨2933883518782490219938745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955922345854993479959163 2933883518782490219938745)
          ·
            refine ⟨2200412639086867664954059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2933883518782490219938745 2200412639086867664954059)
            ·
              refine ⟨3300618958630301497431089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200412639086867664954059 3300618958630301497431089)
              ·
                refine ⟨2475464218972726123073317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3300618958630301497431089 2475464218972726123073317)
                ·
                  refine ⟨464149541057386148076247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2475464218972726123073317 464149541057386148076247)
                  ·
                    rfl

theorem cell21_2033838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_2033838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033838 prefixEnd_2033838 := by exact prefixLift 2033838
  have htrace : WordTrace (prefixWord ++ tailWord_2033838) baseStart_2033838 baseEnd_2033838 := by
    simpa [prefixWord, tailWord_2033838, baseEnd_2033838] using wordTrace_append hprefix tailTrace_2033838
  have hstable : (prefixWord ++ tailWord_2033838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033838).length < 2 ^ (prefixWord ++ tailWord_2033838).sum := by decide
  have hdescent : baseEnd_2033838 < baseStart_2033838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033970 : List Nat := [3, 2, 1, 1, 5, 2, 1, 6]
def baseStart_2033970 : Nat := 118140960795 + 2033970 * 2 ^ 59
def prefixEnd_2033970 : Nat := 4983230072969 + 3 ^ 40 * 2033970 * 2
def baseEnd_2033970 : Nat := 154726555085261083958659

theorem tailTrace_2033970 : CollatzResearch.WordTrace tailWord_2033970 prefixEnd_2033970 154726555085261083958659 := by
  unfold tailWord_2033970
  simp only [CollatzResearch.WordTrace]
  refine ⟨18546245110320384816304841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49456653627521026176812909 18546245110320384816304841)
  ·
    refine ⟨13909683832740288612228631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18546245110320384816304841 13909683832740288612228631)
    ·
      refine ⟨20864525749110432918342947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13909683832740288612228631 20864525749110432918342947)
      ·
        refine ⟨31296788623665649377514421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20864525749110432918342947 31296788623665649377514421)
        ·
          refine ⟨2934073933468654629141977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31296788623665649377514421 2934073933468654629141977)
          ·
            refine ⟨2200555450101490971856483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2934073933468654629141977 2200555450101490971856483)
            ·
              refine ⟨3300833175152236457784725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200555450101490971856483 3300833175152236457784725)
              ·
                refine ⟨154726555085261083958659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3300833175152236457784725 154726555085261083958659)
                ·
                  rfl

theorem cell21_2033970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_2033970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2033970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2033970 prefixEnd_2033970 := by exact prefixLift 2033970
  have htrace : WordTrace (prefixWord ++ tailWord_2033970) baseStart_2033970 baseEnd_2033970 := by
    simpa [prefixWord, tailWord_2033970, baseEnd_2033970] using wordTrace_append hprefix tailTrace_2033970
  have hstable : (prefixWord ++ tailWord_2033970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033970).length < 2 ^ (prefixWord ++ tailWord_2033970).sum := by decide
  have hdescent : baseEnd_2033970 < baseStart_2033970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034001 : List Nat := [1, 2, 2, 1, 4, 3, 2, 3, 3]
def baseStart_2034001 : Nat := 118140960795 + 2034001 * 2 ^ 59
def prefixEnd_2034001 : Nat := 4983230072969 + 3 ^ 40 * 2034001 * 2
def baseEnd_2034001 : Nat := 464186739878134086859247

theorem tailTrace_2034001 : CollatzResearch.WordTrace tailWord_2034001 prefixEnd_2034001 464186739878134086859247 := by
  unfold tailWord_2034001
  simp only [CollatzResearch.WordTrace]
  refine ⟨74186111104169231559597857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49457407402779487706398571 74186111104169231559597857)
  ·
    refine ⟨55639583328126923669698393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74186111104169231559597857 55639583328126923669698393)
    ·
      refine ⟨41729687496095192752273795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55639583328126923669698393 41729687496095192752273795)
      ·
        refine ⟨62594531244142789128410693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41729687496095192752273795 62594531244142789128410693)
        ·
          refine ⟨11736474608276772961577005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62594531244142789128410693 11736474608276772961577005)
          ·
            refine ⟨4401177978103789860591377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11736474608276772961577005 4401177978103789860591377)
            ·
              refine ⟨3300883483577842395443533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4401177978103789860591377 3300883483577842395443533)
              ·
                refine ⟨1237831306341690898291325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3300883483577842395443533 1237831306341690898291325)
                ·
                  refine ⟨464186739878134086859247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237831306341690898291325 464186739878134086859247)
                  ·
                    rfl

theorem cell21_2034001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 3].length) (baseStart_2034001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034001 prefixEnd_2034001 := by exact prefixLift 2034001
  have htrace : WordTrace (prefixWord ++ tailWord_2034001) baseStart_2034001 baseEnd_2034001 := by
    simpa [prefixWord, tailWord_2034001, baseEnd_2034001] using wordTrace_append hprefix tailTrace_2034001
  have hstable : (prefixWord ++ tailWord_2034001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034001).length < 2 ^ (prefixWord ++ tailWord_2034001).sum := by decide
  have hdescent : baseEnd_2034001 < baseStart_2034001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034043 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 5]
def baseStart_2034043 : Nat := 118140960795 + 2034043 * 2 ^ 59
def prefixEnd_2034043 : Nat := 4983230072969 + 3 ^ 40 * 2034043 * 2
def baseEnd_2034043 : Nat := 464196324850351347159161

theorem tailTrace_2034043 : CollatzResearch.WordTrace tailWord_2034043 prefixEnd_2034043 464196324850351347159161 := by
  unfold tailWord_2034043
  simp only [CollatzResearch.WordTrace]
  refine ⟨74187642970017072732626783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49458428646678048488417855 74187642970017072732626783)
  ·
    refine ⟨111281464455025609098940175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74187642970017072732626783 111281464455025609098940175)
    ·
      refine ⟨166922196682538413648410263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111281464455025609098940175 166922196682538413648410263)
      ·
        refine ⟨250383295023807620472615395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166922196682538413648410263 250383295023807620472615395)
        ·
          refine ⟨375574942535711430708923093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250383295023807620472615395 375574942535711430708923093)
          ·
            refine ⟨8802537715680736657240385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 375574942535711430708923093 8802537715680736657240385)
            ·
              refine ⟨6601903286760552492930289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8802537715680736657240385 6601903286760552492930289)
              ·
                refine ⟨4951427465070414369697717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6601903286760552492930289 4951427465070414369697717)
                ·
                  refine ⟨464196324850351347159161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4951427465070414369697717 464196324850351347159161)
                  ·
                    rfl

theorem cell21_2034043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_2034043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034043 prefixEnd_2034043 := by exact prefixLift 2034043
  have htrace : WordTrace (prefixWord ++ tailWord_2034043) baseStart_2034043 baseEnd_2034043 := by
    simpa [prefixWord, tailWord_2034043, baseEnd_2034043] using wordTrace_append hprefix tailTrace_2034043
  have hstable : (prefixWord ++ tailWord_2034043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034043).length < 2 ^ (prefixWord ++ tailWord_2034043).sum := by decide
  have hdescent : baseEnd_2034043 < baseStart_2034043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034074 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_2034074 : Nat := 118140960795 + 2034074 * 2 ^ 59
def prefixEnd_2034074 : Nat := 4983230072969 + 3 ^ 40 * 2034074 * 2
def baseEnd_2034074 : Nat := 464203399472702182142431

theorem tailTrace_2034074 : CollatzResearch.WordTrace tailWord_2034074 prefixEnd_2034074 464203399472702182142431 := by
  unfold tailWord_2034074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18547193408226191256751319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49459182421936510018003517 18547193408226191256751319)
  ·
    refine ⟨27820790112339286885126979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18547193408226191256751319 27820790112339286885126979)
    ·
      refine ⟨41731185168508930327690469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27820790112339286885126979 41731185168508930327690469)
      ·
        refine ⟨7824597219095424436441963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41731185168508930327690469 7824597219095424436441963)
        ·
          refine ⟨11736895828643136654662945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7824597219095424436441963 11736895828643136654662945)
          ·
            refine ⟨8802671871482352490997209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11736895828643136654662945 8802671871482352490997209)
            ·
              refine ⟨6602003903611764368247907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8802671871482352490997209 6602003903611764368247907)
              ·
                refine ⟨9903005855417646552371861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6602003903611764368247907 9903005855417646552371861)
                ·
                  refine ⟨464203399472702182142431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9903005855417646552371861 464203399472702182142431)
                  ·
                    rfl

theorem cell21_2034074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_2034074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034074 prefixEnd_2034074 := by exact prefixLift 2034074
  have htrace : WordTrace (prefixWord ++ tailWord_2034074) baseStart_2034074 baseEnd_2034074 := by
    simpa [prefixWord, tailWord_2034074, baseEnd_2034074] using wordTrace_append hprefix tailTrace_2034074
  have hstable : (prefixWord ++ tailWord_2034074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034074).length < 2 ^ (prefixWord ++ tailWord_2034074).sum := by decide
  have hdescent : baseEnd_2034074 < baseStart_2034074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034077 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 5]
def baseStart_2034077 : Nat := 118140960795 + 2034077 * 2 ^ 59
def prefixEnd_2034077 : Nat := 4983230072969 + 3 ^ 40 * 2034077 * 2
def baseEnd_2034077 : Nat := 464204084113574843592425

theorem tailTrace_2034077 : CollatzResearch.WordTrace tailWord_2034077 prefixEnd_2034077 464204084113574843592425 := by
  unfold tailWord_2034077
  simp only [CollatzResearch.WordTrace]
  refine ⟨74188883051893896539364485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49459255367929264359576323 74188883051893896539364485)
  ·
    refine ⟨13910415572230105601130841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74188883051893896539364485 13910415572230105601130841)
    ·
      refine ⟨10432811679172579200848131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13910415572230105601130841 10432811679172579200848131)
      ·
        refine ⟨15649217518758868801272197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10432811679172579200848131 15649217518758868801272197)
        ·
          refine ⟨2934228284767287900238537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15649217518758868801272197 2934228284767287900238537)
          ·
            refine ⟨2200671213575465925178903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2934228284767287900238537 2200671213575465925178903)
            ·
              refine ⟨3301006820363198887768355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200671213575465925178903 3301006820363198887768355)
              ·
                refine ⟨4951510230544798331652533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301006820363198887768355 4951510230544798331652533)
                ·
                  refine ⟨464204084113574843592425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4951510230544798331652533 464204084113574843592425)
                  ·
                    rfl

theorem cell21_2034077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_2034077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034077 prefixEnd_2034077 := by exact prefixLift 2034077
  have htrace : WordTrace (prefixWord ++ tailWord_2034077) baseStart_2034077 baseEnd_2034077 := by
    simpa [prefixWord, tailWord_2034077, baseEnd_2034077] using wordTrace_append hprefix tailTrace_2034077
  have hstable : (prefixWord ++ tailWord_2034077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034077).length < 2 ^ (prefixWord ++ tailWord_2034077).sum := by decide
  have hdescent : baseEnd_2034077 < baseStart_2034077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034195 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 5]
def baseStart_2034195 : Nat := 118140960795 + 2034195 * 2 ^ 59
def prefixEnd_2034195 : Nat := 4983230072969 + 3 ^ 40 * 2034195 * 2
def baseEnd_2034195 : Nat := 464231013321232860625517

theorem tailTrace_2034195 : CollatzResearch.WordTrace tailWord_2034195 prefixEnd_2034195 464231013321232860625517 := by
  unfold tailWord_2034195
  simp only [CollatzResearch.WordTrace]
  refine ⟨74193186865466402692160039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49462124576977601794773359 74193186865466402692160039)
  ·
    refine ⟨111289780298199604038240059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74193186865466402692160039 111289780298199604038240059)
    ·
      refine ⟨166934670447299406057360089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111289780298199604038240059 166934670447299406057360089)
      ·
        refine ⟨125201002835474554543020067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166934670447299406057360089 125201002835474554543020067)
        ·
          refine ⟨187801504253211831814530101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125201002835474554543020067 187801504253211831814530101)
          ·
            refine ⟨17606391023738609232612197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187801504253211831814530101 17606391023738609232612197)
            ·
              refine ⟨3301198316950989231114787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17606391023738609232612197 3301198316950989231114787)
              ·
                refine ⟨4951797475426483846672181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301198316950989231114787 4951797475426483846672181)
                ·
                  refine ⟨464231013321232860625517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4951797475426483846672181 464231013321232860625517)
                  ·
                    rfl

theorem cell21_2034195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 5].length) (baseStart_2034195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034195 prefixEnd_2034195 := by exact prefixLift 2034195
  have htrace : WordTrace (prefixWord ++ tailWord_2034195) baseStart_2034195 baseEnd_2034195 := by
    simpa [prefixWord, tailWord_2034195, baseEnd_2034195] using wordTrace_append hprefix tailTrace_2034195
  have hstable : (prefixWord ++ tailWord_2034195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034195).length < 2 ^ (prefixWord ++ tailWord_2034195).sum := by decide
  have hdescent : baseEnd_2034195 < baseStart_2034195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034221 : List Nat := [1, 5, 4, 1, 2, 1, 1, 3, 3]
def baseStart_2034221 : Nat := 118140960795 + 2034221 * 2 ^ 59
def prefixEnd_2034221 : Nat := 4983230072969 + 3 ^ 40 * 2034221 * 2
def baseEnd_2034221 : Nat := 464236946875462593192131

theorem tailTrace_2034221 : CollatzResearch.WordTrace tailWord_2034221 prefixEnd_2034221 464236946875462593192131 := by
  unfold tailWord_2034221
  simp only [CollatzResearch.WordTrace]
  refine ⟨74194135163372209132606517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49462756775581472755071011 74194135163372209132606517)
  ·
    refine ⟨6955700171566144606181861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74194135163372209132606517 6955700171566144606181861)
    ·
      refine ⟨1304193782168652113659099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6955700171566144606181861 1304193782168652113659099)
      ·
        refine ⟨1956290673252978170488649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304193782168652113659099 1956290673252978170488649)
        ·
          refine ⟨1467218004939733627866487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1956290673252978170488649 1467218004939733627866487)
          ·
            refine ⟨2200827007409600441799731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467218004939733627866487 2200827007409600441799731)
            ·
              refine ⟨3301240511114400662699597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200827007409600441799731 3301240511114400662699597)
              ·
                refine ⟨1237965191667900248512349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3301240511114400662699597 1237965191667900248512349)
                ·
                  refine ⟨464236946875462593192131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237965191667900248512349 464236946875462593192131)
                  ·
                    rfl

theorem cell21_2034221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_2034221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034221 prefixEnd_2034221 := by exact prefixLift 2034221
  have htrace : WordTrace (prefixWord ++ tailWord_2034221) baseStart_2034221 baseEnd_2034221 := by
    simpa [prefixWord, tailWord_2034221, baseEnd_2034221] using wordTrace_append hprefix tailTrace_2034221
  have hstable : (prefixWord ++ tailWord_2034221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034221).length < 2 ^ (prefixWord ++ tailWord_2034221).sum := by decide
  have hdescent : baseEnd_2034221 < baseStart_2034221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034246 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2034246 : Nat := 118140960795 + 2034246 * 2 ^ 59
def prefixEnd_2034246 : Nat := 4983230072969 + 3 ^ 40 * 2034246 * 2
def baseEnd_2034246 : Nat := 464242652216068105275413

theorem tailTrace_2034246 : CollatzResearch.WordTrace tailWord_2034246 prefixEnd_2034246 464242652216068105275413 := by
  unfold tailWord_2034246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2318595218383801200070831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49463364658854425601511061 2318595218383801200070831)
  ·
    refine ⟨3477892827575701800106247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2318595218383801200070831 3477892827575701800106247)
    ·
      refine ⟨5216839241363552700159371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3477892827575701800106247 5216839241363552700159371)
      ·
        refine ⟨7825258862045329050239057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5216839241363552700159371 7825258862045329050239057)
        ·
          refine ⟨5868944146533996787679293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7825258862045329050239057 5868944146533996787679293)
          ·
            refine ⟨2200854054950248795379735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5868944146533996787679293 2200854054950248795379735)
            ·
              refine ⟨3301281082425373193069603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200854054950248795379735 3301281082425373193069603)
              ·
                refine ⟨4951921623638059789604405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301281082425373193069603 4951921623638059789604405)
                ·
                  refine ⟨464242652216068105275413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4951921623638059789604405 464242652216068105275413)
                  ·
                    rfl

theorem cell21_2034246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2034246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034246 prefixEnd_2034246 := by exact prefixLift 2034246
  have htrace : WordTrace (prefixWord ++ tailWord_2034246) baseStart_2034246 baseEnd_2034246 := by
    simpa [prefixWord, tailWord_2034246, baseEnd_2034246] using wordTrace_append hprefix tailTrace_2034246
  have hstable : (prefixWord ++ tailWord_2034246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034246).length < 2 ^ (prefixWord ++ tailWord_2034246).sum := by decide
  have hdescent : baseEnd_2034246 < baseStart_2034246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034260 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2034260 : Nat := 118140960795 + 2034260 * 2 ^ 59
def prefixEnd_2034260 : Nat := 4983230072969 + 3 ^ 40 * 2034260 * 2
def baseEnd_2034260 : Nat := 464245847206807192042051

theorem tailTrace_2034260 : CollatzResearch.WordTrace tailWord_2034260 prefixEnd_2034260 464245847206807192042051 := by
  unfold tailWord_2034260
  simp only [CollatzResearch.WordTrace]
  refine ⟨37097778805115459396638117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49463705073487279195517489 37097778805115459396638117)
  ·
    refine ⟨6955833525959148636869647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37097778805115459396638117 6955833525959148636869647)
    ·
      refine ⟨10433750288938722955304471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6955833525959148636869647 10433750288938722955304471)
      ·
        refine ⟨15650625433408084432956707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10433750288938722955304471 15650625433408084432956707)
        ·
          refine ⟨23475938150112126649435061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15650625433408084432956707 23475938150112126649435061)
          ·
            refine ⟨2200869201573011873384537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23475938150112126649435061 2200869201573011873384537)
            ·
              refine ⟨1650651901179758905038403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2200869201573011873384537 1650651901179758905038403)
              ·
                refine ⟨2475977851769638357557605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650651901179758905038403 2475977851769638357557605)
                ·
                  refine ⟨464245847206807192042051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2475977851769638357557605 464245847206807192042051)
                  ·
                    rfl

theorem cell21_2034260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2034260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034260 prefixEnd_2034260 := by exact prefixLift 2034260
  have htrace : WordTrace (prefixWord ++ tailWord_2034260) baseStart_2034260 baseEnd_2034260 := by
    simpa [prefixWord, tailWord_2034260, baseEnd_2034260] using wordTrace_append hprefix tailTrace_2034260
  have hstable : (prefixWord ++ tailWord_2034260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034260).length < 2 ^ (prefixWord ++ tailWord_2034260).sum := by decide
  have hdescent : baseEnd_2034260 < baseStart_2034260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034353 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 4]
def baseStart_2034353 : Nat := 118140960795 + 2034353 * 2 ^ 59
def prefixEnd_2034353 : Nat := 4983230072969 + 3 ^ 40 * 2034353 * 2
def baseEnd_2034353 : Nat := 464267071073859696991861

theorem tailTrace_2034353 : CollatzResearch.WordTrace tailWord_2034353 prefixEnd_2034353 464267071073859696991861 := by
  unfold tailWord_2034353
  simp only [CollatzResearch.WordTrace]
  refine ⟨74198949598893995676411713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49465966399262663784274475 74198949598893995676411713)
  ·
    refine ⟨55649212199170496757308785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74198949598893995676411713 55649212199170496757308785)
    ·
      refine ⟨41736909149377872567981589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55649212199170496757308785 41736909149377872567981589)
      ·
        refine ⟨1956417616377087776624137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41736909149377872567981589 1956417616377087776624137)
        ·
          refine ⟨1467313212282815832468103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1956417616377087776624137 1467313212282815832468103)
          ·
            refine ⟨2200969818424223748702155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467313212282815832468103 2200969818424223748702155)
            ·
              refine ⟨3301454727636335623053233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200969818424223748702155 3301454727636335623053233)
              ·
                refine ⟨2476091045727251717289925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301454727636335623053233 2476091045727251717289925)
                ·
                  refine ⟨464267071073859696991861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476091045727251717289925 464267071073859696991861)
                  ·
                    rfl

theorem cell21_2034353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 4].length) (baseStart_2034353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034353 prefixEnd_2034353 := by exact prefixLift 2034353
  have htrace : WordTrace (prefixWord ++ tailWord_2034353) baseStart_2034353 baseEnd_2034353 := by
    simpa [prefixWord, tailWord_2034353, baseEnd_2034353] using wordTrace_append hprefix tailTrace_2034353
  have hstable : (prefixWord ++ tailWord_2034353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034353).length < 2 ^ (prefixWord ++ tailWord_2034353).sum := by decide
  have hdescent : baseEnd_2034353 < baseStart_2034353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034364 : List Nat := [2, 2, 2, 3, 1, 1, 1, 6, 3]
def baseStart_2034364 : Nat := 118140960795 + 2034364 * 2 ^ 59
def prefixEnd_2034364 : Nat := 4983230072969 + 3 ^ 40 * 2034364 * 2
def baseEnd_2034364 : Nat := 464269581423726122308505

theorem tailTrace_2034364 : CollatzResearch.WordTrace tailWord_2034364 prefixEnd_2034364 464269581423726122308505 := by
  unfold tailWord_2034364
  simp only [CollatzResearch.WordTrace]
  refine ⟨37099675400927072277531073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49466233867902763036708097 37099675400927072277531073)
  ·
    refine ⟨27824756550695304208148305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37099675400927072277531073 27824756550695304208148305)
    ·
      refine ⟨20868567413021478156111229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27824756550695304208148305 20868567413021478156111229)
      ·
        refine ⟨7825712779883054308541711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20868567413021478156111229 7825712779883054308541711)
        ·
          refine ⟨11738569169824581462812567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825712779883054308541711 11738569169824581462812567)
          ·
            refine ⟨17607853754736872194218851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11738569169824581462812567 17607853754736872194218851)
            ·
              refine ⟨26411780632105308291328277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17607853754736872194218851 26411780632105308291328277)
              ·
                refine ⟨1238052217129936326156013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26411780632105308291328277 1238052217129936326156013)
                ·
                  refine ⟨464269581423726122308505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238052217129936326156013 464269581423726122308505)
                  ·
                    rfl

theorem cell21_2034364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_2034364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034364 prefixEnd_2034364 := by exact prefixLift 2034364
  have htrace : WordTrace (prefixWord ++ tailWord_2034364) baseStart_2034364 baseEnd_2034364 := by
    simpa [prefixWord, tailWord_2034364, baseEnd_2034364] using wordTrace_append hprefix tailTrace_2034364
  have hstable : (prefixWord ++ tailWord_2034364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034364).length < 2 ^ (prefixWord ++ tailWord_2034364).sum := by decide
  have hdescent : baseEnd_2034364 < baseStart_2034364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034392 : List Nat := [2, 1, 2, 2, 3, 3, 1, 7]
def baseStart_2034392 : Nat := 118140960795 + 2034392 * 2 ^ 59
def prefixEnd_2034392 : Nat := 4983230072969 + 3 ^ 40 * 2034392 * 2
def baseEnd_2034392 : Nat := 154758657135068098613927

theorem tailTrace_2034392 : CollatzResearch.WordTrace tailWord_2034392 prefixEnd_2034392 154758657135068098613927 := by
  unfold tailWord_2034392
  simp only [CollatzResearch.WordTrace]
  refine ⟨37100186022876352668540715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49466914697168470224720953 37100186022876352668540715)
  ·
    refine ⟨55650279034314529002811073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37100186022876352668540715 55650279034314529002811073)
    ·
      refine ⟨41737709275735896752108305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55650279034314529002811073 41737709275735896752108305)
      ·
        refine ⟨31303281956801922564081229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41737709275735896752108305 31303281956801922564081229)
        ·
          refine ⟨11738730733800720961530461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31303281956801922564081229 11738730733800720961530461)
          ·
            refine ⟨4402024025175270360573923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11738730733800720961530461 4402024025175270360573923)
            ·
              refine ⟨6603036037762905540860885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4402024025175270360573923 6603036037762905540860885)
              ·
                refine ⟨154758657135068098613927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6603036037762905540860885 154758657135068098613927)
                ·
                  rfl

theorem cell21_2034392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_2034392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034392 prefixEnd_2034392 := by exact prefixLift 2034392
  have htrace : WordTrace (prefixWord ++ tailWord_2034392) baseStart_2034392 baseEnd_2034392 := by
    simpa [prefixWord, tailWord_2034392, baseEnd_2034392] using wordTrace_append hprefix tailTrace_2034392
  have hstable : (prefixWord ++ tailWord_2034392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034392).length < 2 ^ (prefixWord ++ tailWord_2034392).sum := by decide
  have hdescent : baseEnd_2034392 < baseStart_2034392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034451 : List Nat := [1, 1, 1, 2, 1, 3, 3, 9]
def baseStart_2034451 : Nat := 118140960795 + 2034451 * 2 ^ 59
def prefixEnd_2034451 : Nat := 4983230072969 + 3 ^ 40 * 2034451 * 2
def baseEnd_2034451 : Nat := 154763145336344434786109

theorem tailTrace_2034451 : CollatzResearch.WordTrace tailWord_2034451 prefixEnd_2034451 154763145336344434786109 := by
  unfold tailWord_2034451
  simp only [CollatzResearch.WordTrace]
  refine ⟨74202523952538958413479207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49468349301692638942319471 74202523952538958413479207)
  ·
    refine ⟨111303785928808437620218811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74202523952538958413479207 111303785928808437620218811)
    ·
      refine ⟨166955678893212656430328217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111303785928808437620218811 166955678893212656430328217)
      ·
        refine ⟨125216759169909492322746163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166955678893212656430328217 125216759169909492322746163)
        ·
          refine ⟨187825138754864238484119245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125216759169909492322746163 187825138754864238484119245)
          ·
            refine ⟨70434427033074089431544717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187825138754864238484119245 70434427033074089431544717)
            ·
              refine ⟨26412910137402783536829269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70434427033074089431544717 26412910137402783536829269)
              ·
                refine ⟨154763145336344434786109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26412910137402783536829269 154763145336344434786109)
                ·
                  rfl

theorem cell21_2034451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 9].length) (baseStart_2034451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034451 prefixEnd_2034451 := by exact prefixLift 2034451
  have htrace : WordTrace (prefixWord ++ tailWord_2034451) baseStart_2034451 baseEnd_2034451 := by
    simpa [prefixWord, tailWord_2034451, baseEnd_2034451] using wordTrace_append hprefix tailTrace_2034451
  have hstable : (prefixWord ++ tailWord_2034451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034451).length < 2 ^ (prefixWord ++ tailWord_2034451).sum := by decide
  have hdescent : baseEnd_2034451 < baseStart_2034451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034468 : List Nat := [2, 3, 1, 3, 3, 9]
def baseStart_2034468 : Nat := 118140960795 + 2034468 * 2 ^ 59
def prefixEnd_2034468 : Nat := 4983230072969 + 3 ^ 40 * 2034468 * 2
def baseEnd_2034468 : Nat := 17196048727431298243517

theorem tailTrace_2034468 : CollatzResearch.WordTrace tailWord_2034468 prefixEnd_2034468 17196048727431298243517 := by
  unfold tailWord_2034468
  simp only [CollatzResearch.WordTrace]
  refine ⟨37101571996738685158424029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49468762662318246877898705 37101571996738685158424029)
  ·
    refine ⟨13913089498777006934409011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37101571996738685158424029 13913089498777006934409011)
    ·
      refine ⟨20869634248165510401613517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13913089498777006934409011 20869634248165510401613517)
      ·
        refine ⟨7826112843062066400605069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20869634248165510401613517 7826112843062066400605069)
        ·
          refine ⟨2934792316148274900226901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7826112843062066400605069 2934792316148274900226901)
          ·
            refine ⟨17196048727431298243517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2934792316148274900226901 17196048727431298243517)
            ·
              rfl

theorem cell21_2034468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 9].length) (baseStart_2034468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034468 prefixEnd_2034468 := by exact prefixLift 2034468
  have htrace : WordTrace (prefixWord ++ tailWord_2034468) baseStart_2034468 baseEnd_2034468 := by
    simpa [prefixWord, tailWord_2034468, baseEnd_2034468] using wordTrace_append hprefix tailTrace_2034468
  have hstable : (prefixWord ++ tailWord_2034468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034468).length < 2 ^ (prefixWord ++ tailWord_2034468).sum := by decide
  have hdescent : baseEnd_2034468 < baseStart_2034468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034474 : List Nat := [3, 1, 4, 3, 1, 1, 1, 4, 3]
def baseStart_2034474 : Nat := 118140960795 + 2034474 * 2 ^ 59
def prefixEnd_2034474 : Nat := 4983230072969 + 3 ^ 40 * 2034474 * 2
def baseEnd_2034474 : Nat := 464294684922390375474947

theorem tailTrace_2034474 : CollatzResearch.WordTrace tailWord_2034474 prefixEnd_2034474 464294684922390375474947 := by
  unfold tailWord_2034474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18550840707863908335391619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49468908554303755561044317 18550840707863908335391619)
  ·
    refine ⟨27826261061795862503087429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18550840707863908335391619 27826261061795862503087429)
    ·
      refine ⟨5217423949086724219328893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27826261061795862503087429 5217423949086724219328893)
      ·
        refine ⟨1956533980907521582248335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5217423949086724219328893 1956533980907521582248335)
        ·
          refine ⟨2934800971361282373372503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956533980907521582248335 2934800971361282373372503)
          ·
            refine ⟨4402201457041923560058755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934800971361282373372503 4402201457041923560058755)
            ·
              refine ⟨6603302185562885340088133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4402201457041923560058755 6603302185562885340088133)
              ·
                refine ⟨1238119159793041001266525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6603302185562885340088133 1238119159793041001266525)
                ·
                  refine ⟨464294684922390375474947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238119159793041001266525 464294684922390375474947)
                  ·
                    rfl

theorem cell21_2034474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_2034474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034474 prefixEnd_2034474 := by exact prefixLift 2034474
  have htrace : WordTrace (prefixWord ++ tailWord_2034474) baseStart_2034474 baseEnd_2034474 := by
    simpa [prefixWord, tailWord_2034474, baseEnd_2034474] using wordTrace_append hprefix tailTrace_2034474
  have hstable : (prefixWord ++ tailWord_2034474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034474).length < 2 ^ (prefixWord ++ tailWord_2034474).sum := by decide
  have hdescent : baseEnd_2034474 < baseStart_2034474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034485 : List Nat := [1, 3, 3, 1, 3, 3, 1, 6]
def baseStart_2034485 : Nat := 118140960795 + 2034485 * 2 ^ 59
def prefixEnd_2034485 : Nat := 4983230072969 + 3 ^ 40 * 2034485 * 2
def baseEnd_2034485 : Nat := 154765731757418933597197

theorem tailTrace_2034485 : CollatzResearch.WordTrace tailWord_2034485 prefixEnd_2034485 154765731757418933597197 := by
  unfold tailWord_2034485
  simp only [CollatzResearch.WordTrace]
  refine ⟨74203764034415782220216909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49469176022943854813477939 74203764034415782220216909)
  ·
    refine ⟨27826411512905918332581341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74203764034415782220216909 27826411512905918332581341)
    ·
      refine ⟨10434904317339719374718003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27826411512905918332581341 10434904317339719374718003)
      ·
        refine ⟨15652356476009579062077005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10434904317339719374718003 15652356476009579062077005)
        ·
          refine ⟨5869633678503592148278877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15652356476009579062077005 5869633678503592148278877)
          ·
            refine ⟨2201112629438847055604579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5869633678503592148278877 2201112629438847055604579)
            ·
              refine ⟨3301668944158270583406869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2201112629438847055604579 3301668944158270583406869)
              ·
                refine ⟨154765731757418933597197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3301668944158270583406869 154765731757418933597197)
                ·
                  rfl

theorem cell21_2034485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 6].length) (baseStart_2034485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034485 prefixEnd_2034485 := by exact prefixLift 2034485
  have htrace : WordTrace (prefixWord ++ tailWord_2034485) baseStart_2034485 baseEnd_2034485 := by
    simpa [prefixWord, tailWord_2034485, baseEnd_2034485] using wordTrace_append hprefix tailTrace_2034485
  have hstable : (prefixWord ++ tailWord_2034485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034485).length < 2 ^ (prefixWord ++ tailWord_2034485).sum := by decide
  have hdescent : baseEnd_2034485 < baseStart_2034485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034527 : List Nat := [1, 1, 2, 3, 1, 3, 10]
def baseStart_2034527 : Nat := 118140960795 + 2034527 * 2 ^ 59
def prefixEnd_2034527 : Nat := 4983230072969 + 3 ^ 40 * 2034527 * 2
def baseEnd_2034527 : Nat := 51589642249386006787945

theorem tailTrace_2034527 : CollatzResearch.WordTrace tailWord_2034527 prefixEnd_2034527 51589642249386006787945 := by
  unfold tailWord_2034527
  simp only [CollatzResearch.WordTrace]
  refine ⟨74205295900263623393245835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49470197266842415595497223 74205295900263623393245835)
  ·
    refine ⟨111307943850395435089868753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74205295900263623393245835 111307943850395435089868753)
    ·
      refine ⟨83480957887796576317401565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111307943850395435089868753 83480957887796576317401565)
      ·
        refine ⟨31305359207923716119025587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83480957887796576317401565 31305359207923716119025587)
        ·
          refine ⟨46958038811885574178538381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31305359207923716119025587 46958038811885574178538381)
          ·
            refine ⟨17609264554457090316951893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46958038811885574178538381 17609264554457090316951893)
            ·
              refine ⟨51589642249386006787945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17609264554457090316951893 51589642249386006787945)
              ·
                rfl

theorem cell21_2034527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 10].length) (baseStart_2034527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034527 prefixEnd_2034527 := by exact prefixLift 2034527
  have htrace : WordTrace (prefixWord ++ tailWord_2034527) baseStart_2034527 baseEnd_2034527 := by
    simpa [prefixWord, tailWord_2034527, baseEnd_2034527] using wordTrace_append hprefix tailTrace_2034527
  have hstable : (prefixWord ++ tailWord_2034527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034527).length < 2 ^ (prefixWord ++ tailWord_2034527).sum := by decide
  have hdescent : baseEnd_2034527 < baseStart_2034527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034578 : List Nat := [3, 2, 3, 2, 3, 1, 7]
def baseStart_2034578 : Nat := 118140960795 + 2034578 * 2 ^ 59
def prefixEnd_2034578 : Nat := 4983230072969 + 3 ^ 40 * 2034578 * 2
def baseEnd_2034578 : Nat := 51590935459923256193489

theorem tailTrace_2034578 : CollatzResearch.WordTrace tailWord_2034578 prefixEnd_2034578 51590935459923256193489 := by
  unfold tailWord_2034578
  simp only [CollatzResearch.WordTrace]
  refine ⟨18551789005769714775838097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49471437348719239402234925 18551789005769714775838097)
  ·
    refine ⟨13913841754327286081878573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18551789005769714775838097 13913841754327286081878573)
    ·
      refine ⟨5217690657872732280704465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13913841754327286081878573 5217690657872732280704465)
      ·
        refine ⟨3913267993404549210528349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5217690657872732280704465 3913267993404549210528349)
        ·
          refine ⟨1467475497526705953948131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3913267993404549210528349 1467475497526705953948131)
          ·
            refine ⟨2201213246290058930922197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467475497526705953948131 2201213246290058930922197)
            ·
              refine ⟨51590935459923256193489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2201213246290058930922197 51590935459923256193489)
              ·
                rfl

theorem cell21_2034578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 7].length) (baseStart_2034578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034578 prefixEnd_2034578 := by exact prefixLift 2034578
  have htrace : WordTrace (prefixWord ++ tailWord_2034578) baseStart_2034578 baseEnd_2034578 := by
    simpa [prefixWord, tailWord_2034578, baseEnd_2034578] using wordTrace_append hprefix tailTrace_2034578
  have hstable : (prefixWord ++ tailWord_2034578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034578).length < 2 ^ (prefixWord ++ tailWord_2034578).sum := by decide
  have hdescent : baseEnd_2034578 < baseStart_2034578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034589 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 6]
def baseStart_2034589 : Nat := 118140960795 + 2034589 * 2 ^ 59
def prefixEnd_2034589 : Nat := 4983230072969 + 3 ^ 40 * 2034589 * 2
def baseEnd_2034589 : Nat := 464320929489175731058045

theorem tailTrace_2034589 : CollatzResearch.WordTrace tailWord_2034589 prefixEnd_2034589 464320929489175731058045 := by
  unfold tailWord_2034589
  simp only [CollatzResearch.WordTrace]
  refine ⟨74207557226039007982002821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49471704817359338654668547 74207557226039007982002821)
  ·
    refine ⟨13913916979882313996625529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74207557226039007982002821 13913916979882313996625529)
    ·
      refine ⟨10435437734911735497469147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13913916979882313996625529 10435437734911735497469147)
      ·
        refine ⟨15653156602367603246203721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10435437734911735497469147 15653156602367603246203721)
        ·
          refine ⟨11739867451775702434652791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15653156602367603246203721 11739867451775702434652791)
          ·
            refine ⟨17609801177663553651979187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11739867451775702434652791 17609801177663553651979187)
            ·
              refine ⟨26414701766495330477968781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17609801177663553651979187 26414701766495330477968781)
              ·
                refine ⟨9905513162435748929238293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26414701766495330477968781 9905513162435748929238293)
                ·
                  refine ⟨464320929489175731058045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9905513162435748929238293 464320929489175731058045)
                  ·
                    rfl

theorem cell21_2034589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_2034589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034589 prefixEnd_2034589 := by exact prefixLift 2034589
  have htrace : WordTrace (prefixWord ++ tailWord_2034589) baseStart_2034589 baseEnd_2034589 := by
    simpa [prefixWord, tailWord_2034589, baseEnd_2034589] using wordTrace_append hprefix tailTrace_2034589
  have hstable : (prefixWord ++ tailWord_2034589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034589).length < 2 ^ (prefixWord ++ tailWord_2034589).sum := by decide
  have hdescent : baseEnd_2034589 < baseStart_2034589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034730 : List Nat := [3, 1, 4, 1, 3, 2, 2, 5]
def baseStart_2034730 : Nat := 118140960795 + 2034730 * 2 ^ 59
def prefixEnd_2034730 : Nat := 4983230072969 + 3 ^ 40 * 2034730 * 2
def baseEnd_2034730 : Nat := 154784369203396939735919

theorem tailTrace_2034730 : CollatzResearch.WordTrace tailWord_2034730 prefixEnd_2034730 154784369203396939735919 := by
  unfold tailWord_2034730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18553174979632047265721411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49475133279018792708590429 18553174979632047265721411)
  ·
    refine ⟨27829762469448070898582117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18553174979632047265721411 27829762469448070898582117)
    ·
      refine ⟨5218080463021513293484147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27829762469448070898582117 5218080463021513293484147)
      ·
        refine ⟨7827120694532269940226221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5218080463021513293484147 7827120694532269940226221)
        ·
          refine ⟨2935170260449601227584833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7827120694532269940226221 2935170260449601227584833)
          ·
            refine ⟨2201377695337200920688625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2935170260449601227584833 2201377695337200920688625)
            ·
              refine ⟨1651033271502900690516469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2201377695337200920688625 1651033271502900690516469)
              ·
                refine ⟨154784369203396939735919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1651033271502900690516469 154784369203396939735919)
                ·
                  rfl

theorem cell21_2034730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_2034730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034730 prefixEnd_2034730 := by exact prefixLift 2034730
  have htrace : WordTrace (prefixWord ++ tailWord_2034730) baseStart_2034730 baseEnd_2034730 := by
    simpa [prefixWord, tailWord_2034730, baseEnd_2034730] using wordTrace_append hprefix tailTrace_2034730
  have hstable : (prefixWord ++ tailWord_2034730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034730).length < 2 ^ (prefixWord ++ tailWord_2034730).sum := by decide
  have hdescent : baseEnd_2034730 < baseStart_2034730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034744 : List Nat := [2, 1, 2, 1, 5, 1, 3, 3, 3]
def baseStart_2034744 : Nat := 118140960795 + 2034744 * 2 ^ 59
def prefixEnd_2034744 : Nat := 4983230072969 + 3 ^ 40 * 2034744 * 2
def baseEnd_2034744 : Nat := 464356302600929905974395

theorem tailTrace_2034744 : CollatzResearch.WordTrace tailWord_2034744 prefixEnd_2034744 464356302600929905974395 := by
  unfold tailWord_2034744
  simp only [CollatzResearch.WordTrace]
  refine ⟨37106605270238734726947643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49475473693651646302596857 37106605270238734726947643)
  ·
    refine ⟨55659907905358102090421465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37106605270238734726947643 55659907905358102090421465)
    ·
      refine ⟨41744930929018576567816099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55659907905358102090421465 41744930929018576567816099)
      ·
        refine ⟨62617396393527864851724149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41744930929018576567816099 62617396393527864851724149)
        ·
          refine ⟨5870380911893237329849139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62617396393527864851724149 5870380911893237329849139)
          ·
            refine ⟨8805571367839855994773709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870380911893237329849139 8805571367839855994773709)
            ·
              refine ⟨3302089262939945998040141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8805571367839855994773709 3302089262939945998040141)
              ·
                refine ⟨1238283473602479749265053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3302089262939945998040141 1238283473602479749265053)
                ·
                  refine ⟨464356302600929905974395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238283473602479749265053 464356302600929905974395)
                  ·
                    rfl

theorem cell21_2034744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 3].length) (baseStart_2034744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034744 prefixEnd_2034744 := by exact prefixLift 2034744
  have htrace : WordTrace (prefixWord ++ tailWord_2034744) baseStart_2034744 baseEnd_2034744 := by
    simpa [prefixWord, tailWord_2034744, baseEnd_2034744] using wordTrace_append hprefix tailTrace_2034744
  have hstable : (prefixWord ++ tailWord_2034744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034744).length < 2 ^ (prefixWord ++ tailWord_2034744).sum := by decide
  have hdescent : baseEnd_2034744 < baseStart_2034744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034820 : List Nat := [2, 3, 2, 1, 2, 3, 1, 4, 3]
def baseStart_2034820 : Nat := 118140960795 + 2034820 * 2 ^ 59
def prefixEnd_2034820 : Nat := 4983230072969 + 3 ^ 40 * 2034820 * 2
def baseEnd_2034820 : Nat := 464373646836370662707573

theorem tailTrace_2034820 : CollatzResearch.WordTrace tailWord_2034820 prefixEnd_2034820 464373646836370662707573 := by
  unfold tailWord_2034820
  simp only [CollatzResearch.WordTrace]
  refine ⟨37107991244101067216830957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49477321658801422955774609 37107991244101067216830957)
  ·
    refine ⟨13915496716537900206311609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37107991244101067216830957 13915496716537900206311609)
    ·
      refine ⟨10436622537403425154733707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13915496716537900206311609 10436622537403425154733707)
      ·
        refine ⟨15654933806105137732100561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10436622537403425154733707 15654933806105137732100561)
        ·
          refine ⟨11741200354578853299075421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15654933806105137732100561 11741200354578853299075421)
          ·
            refine ⟨4402950132967069987153283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11741200354578853299075421 4402950132967069987153283)
            ·
              refine ⟨6604425199450604980729925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4402950132967069987153283 6604425199450604980729925)
              ·
                refine ⟨1238329724896988433886861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6604425199450604980729925 1238329724896988433886861)
                ·
                  refine ⟨464373646836370662707573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238329724896988433886861 464373646836370662707573)
                  ·
                    rfl

theorem cell21_2034820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_2034820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034820 prefixEnd_2034820 := by exact prefixLift 2034820
  have htrace : WordTrace (prefixWord ++ tailWord_2034820) baseStart_2034820 baseEnd_2034820 := by
    simpa [prefixWord, tailWord_2034820, baseEnd_2034820] using wordTrace_append hprefix tailTrace_2034820
  have hstable : (prefixWord ++ tailWord_2034820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034820).length < 2 ^ (prefixWord ++ tailWord_2034820).sum := by decide
  have hdescent : baseEnd_2034820 < baseStart_2034820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034834 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2034834 : Nat := 118140960795 + 2034834 * 2 ^ 59
def prefixEnd_2034834 : Nat := 4983230072969 + 3 ^ 40 * 2034834 * 2
def baseEnd_2034834 : Nat := 464376841827109749474211

theorem tailTrace_2034834 : CollatzResearch.WordTrace tailWord_2034834 prefixEnd_2034834 464376841827109749474211 := by
  unfold tailWord_2034834
  simp only [CollatzResearch.WordTrace]
  refine ⟨18554123277537853706167889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49477662073434276549781037 18554123277537853706167889)
  ·
    refine ⟨13915592458153390279625917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18554123277537853706167889 13915592458153390279625917)
    ·
      refine ⟨5218347171807521354859719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13915592458153390279625917 5218347171807521354859719)
      ·
        refine ⟨7827520757711282032289579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5218347171807521354859719 7827520757711282032289579)
        ·
          refine ⟨11741281136566923048434369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7827520757711282032289579 11741281136566923048434369)
          ·
            refine ⟨8805960852425192286325777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11741281136566923048434369 8805960852425192286325777)
            ·
              refine ⟨6604470639318894214744333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8805960852425192286325777 6604470639318894214744333)
              ·
                refine ⟨2476676489744585330529125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6604470639318894214744333 2476676489744585330529125)
                ·
                  refine ⟨464376841827109749474211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476676489744585330529125 464376841827109749474211)
                  ·
                    rfl

theorem cell21_2034834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2034834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034834 prefixEnd_2034834 := by exact prefixLift 2034834
  have htrace : WordTrace (prefixWord ++ tailWord_2034834) baseStart_2034834 baseEnd_2034834 := by
    simpa [prefixWord, tailWord_2034834, baseEnd_2034834] using wordTrace_append hprefix tailTrace_2034834
  have hstable : (prefixWord ++ tailWord_2034834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034834).length < 2 ^ (prefixWord ++ tailWord_2034834).sum := by decide
  have hdescent : baseEnd_2034834 < baseStart_2034834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034848 : List Nat := [2, 1, 1, 4, 2, 1, 5, 5]
def baseStart_2034848 : Nat := 118140960795 + 2034848 * 2 ^ 59
def prefixEnd_2034848 : Nat := 4983230072969 + 3 ^ 40 * 2034848 * 2
def baseEnd_2034848 : Nat := 154793345605949612080283

theorem tailTrace_2034848 : CollatzResearch.WordTrace tailWord_2034848 prefixEnd_2034848 154793345605949612080283 := by
  unfold tailWord_2034848
  simp only [CollatzResearch.WordTrace]
  refine ⟨37108501866050347607840599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49478002488067130143787465 37108501866050347607840599)
  ·
    refine ⟨55662752799075521411760899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37108501866050347607840599 55662752799075521411760899)
    ·
      refine ⟨83494129198613282117641349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55662752799075521411760899 83494129198613282117641349)
      ·
        refine ⟨15655149224739990397057753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83494129198613282117641349 15655149224739990397057753)
        ·
          refine ⟨11741361918554992797793315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15655149224739990397057753 11741361918554992797793315)
          ·
            refine ⟨17612042877832489196689973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11741361918554992797793315 17612042877832489196689973)
            ·
              refine ⟨1651129019796795862189685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17612042877832489196689973 1651129019796795862189685)
              ·
                refine ⟨154793345605949612080283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1651129019796795862189685 154793345605949612080283)
                ·
                  rfl

theorem cell21_2034848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_2034848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034848 prefixEnd_2034848 := by exact prefixLift 2034848
  have htrace : WordTrace (prefixWord ++ tailWord_2034848) baseStart_2034848 baseEnd_2034848 := by
    simpa [prefixWord, tailWord_2034848, baseEnd_2034848] using wordTrace_append hprefix tailTrace_2034848
  have hstable : (prefixWord ++ tailWord_2034848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034848).length < 2 ^ (prefixWord ++ tailWord_2034848).sum := by decide
  have hdescent : baseEnd_2034848 < baseStart_2034848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034879 : List Nat := [1, 1, 2, 2, 2, 2, 4, 4, 3]
def baseStart_2034879 : Nat := 118140960795 + 2034879 * 2 ^ 59
def prefixEnd_2034879 : Nat := 4983230072969 + 3 ^ 40 * 2034879 * 2
def baseEnd_2034879 : Nat := 464387111440199671224119

theorem tailTrace_2034879 : CollatzResearch.WordTrace tailWord_2034879 prefixEnd_2034879 464387111440199671224119 := by
  unfold tailWord_2034879
  simp only [CollatzResearch.WordTrace]
  refine ⟨74218134394988387510059691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49478756263325591673373127 74218134394988387510059691)
  ·
    refine ⟨111327201592482581265089537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74218134394988387510059691 111327201592482581265089537)
    ·
      refine ⟨83495401194361935948817153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111327201592482581265089537 83495401194361935948817153)
      ·
        refine ⟨62621550895771451961612865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83495401194361935948817153 62621550895771451961612865)
        ·
          refine ⟨46966163171828588971209649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62621550895771451961612865 46966163171828588971209649)
          ·
            refine ⟨35224622378871441728407237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46966163171828588971209649 35224622378871441728407237)
            ·
              refine ⟨6604616696038395324076357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35224622378871441728407237 6604616696038395324076357)
              ·
                refine ⟨1238365630507199123264317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6604616696038395324076357 1238365630507199123264317)
                ·
                  refine ⟨464387111440199671224119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238365630507199123264317 464387111440199671224119)
                  ·
                    rfl

theorem cell21_2034879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 3].length) (baseStart_2034879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034879 prefixEnd_2034879 := by exact prefixLift 2034879
  have htrace : WordTrace (prefixWord ++ tailWord_2034879) baseStart_2034879 baseEnd_2034879 := by
    simpa [prefixWord, tailWord_2034879, baseEnd_2034879] using wordTrace_append hprefix tailTrace_2034879
  have hstable : (prefixWord ++ tailWord_2034879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034879).length < 2 ^ (prefixWord ++ tailWord_2034879).sum := by decide
  have hdescent : baseEnd_2034879 < baseStart_2034879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034986 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_2034986 : Nat := 118140960795 + 2034986 * 2 ^ 59
def prefixEnd_2034986 : Nat := 4983230072969 + 3 ^ 40 * 2034986 * 2
def baseEnd_2034986 : Nat := 464411530297991262940567

theorem tailTrace_2034986 : CollatzResearch.WordTrace tailWord_2034986 prefixEnd_2034986 464411530297991262940567 := by
  unfold tailWord_2034986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18555509251400186196051203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49481358003733829856136541 18555509251400186196051203)
  ·
    refine ⟨27833263877100279294076805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18555509251400186196051203 27833263877100279294076805)
    ·
      refine ⟨5218736976956302367639401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27833263877100279294076805 5218736976956302367639401)
      ·
        refine ⟨3914052732717226775729551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5218736976956302367639401 3914052732717226775729551)
        ·
          refine ⟨5871079099075840163594327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914052732717226775729551 5871079099075840163594327)
          ·
            refine ⟨8806618648613760245391491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871079099075840163594327 8806618648613760245391491)
            ·
              refine ⟨13209927972920640368087237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8806618648613760245391491 13209927972920640368087237)
              ·
                refine ⟨2476861494922620069016357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13209927972920640368087237 2476861494922620069016357)
                ·
                  refine ⟨464411530297991262940567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476861494922620069016357 464411530297991262940567)
                  ·
                    rfl

theorem cell21_2034986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_2034986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034986 prefixEnd_2034986 := by exact prefixLift 2034986
  have htrace : WordTrace (prefixWord ++ tailWord_2034986) baseStart_2034986 baseEnd_2034986 := by
    simpa [prefixWord, tailWord_2034986, baseEnd_2034986] using wordTrace_append hprefix tailTrace_2034986
  have hstable : (prefixWord ++ tailWord_2034986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034986).length < 2 ^ (prefixWord ++ tailWord_2034986).sum := by decide
  have hdescent : baseEnd_2034986 < baseStart_2034986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034989 : List Nat := [1, 5, 3, 1, 1, 2, 1, 4, 3]
def baseStart_2034989 : Nat := 118140960795 + 2034989 * 2 ^ 59
def prefixEnd_2034989 : Nat := 4983230072969 + 3 ^ 40 * 2034989 * 2
def baseEnd_2034989 : Nat := 464412214938863924390561

theorem tailTrace_2034989 : CollatzResearch.WordTrace tailWord_2034989 prefixEnd_2034989 464412214938863924390561 := by
  unfold tailWord_2034989
  simp only [CollatzResearch.WordTrace]
  refine ⟨74222146424589876296564021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49481430949726584197709347 74222146424589876296564021)
  ·
    refine ⟨6958326227305300902802877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74222146424589876296564021 6958326227305300902802877)
    ·
      refine ⟨2609372335239487838551079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6958326227305300902802877 2609372335239487838551079)
      ·
        refine ⟨3914058502859231757826619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609372335239487838551079 3914058502859231757826619)
        ·
          refine ⟨5871087754288847636739929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914058502859231757826619 5871087754288847636739929)
          ·
            refine ⟨4403315815716635727554947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5871087754288847636739929 4403315815716635727554947)
            ·
              refine ⟨6604973723574953591332421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4403315815716635727554947 6604973723574953591332421)
              ·
                refine ⟨1238432573170303798374829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6604973723574953591332421 1238432573170303798374829)
                ·
                  refine ⟨464412214938863924390561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238432573170303798374829 464412214938863924390561)
                  ·
                    rfl

theorem cell21_2034989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_2034989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2034989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2034989 prefixEnd_2034989 := by exact prefixLift 2034989
  have htrace : WordTrace (prefixWord ++ tailWord_2034989) baseStart_2034989 baseEnd_2034989 := by
    simpa [prefixWord, tailWord_2034989, baseEnd_2034989] using wordTrace_append hprefix tailTrace_2034989
  have hstable : (prefixWord ++ tailWord_2034989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034989).length < 2 ^ (prefixWord ++ tailWord_2034989).sum := by decide
  have hdescent : baseEnd_2034989 < baseStart_2034989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035031 : List Nat := [1, 1, 3, 2, 3, 2, 1, 5, 3]
def baseStart_2035031 : Nat := 118140960795 + 2035031 * 2 ^ 59
def prefixEnd_2035031 : Nat := 4983230072969 + 3 ^ 40 * 2035031 * 2
def baseEnd_2035031 : Nat := 464421799911081184690475

theorem tailTrace_2035031 : CollatzResearch.WordTrace tailWord_2035031 prefixEnd_2035031 464421799911081184690475 := by
  unfold tailWord_2035031
  simp only [CollatzResearch.WordTrace]
  refine ⟨74223678290437717469592947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49482452193625144979728631 74223678290437717469592947)
  ·
    refine ⟨111335517435656576204389421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74223678290437717469592947 111335517435656576204389421)
    ·
      refine ⟨41750819038371216076646033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111335517435656576204389421 41750819038371216076646033)
      ·
        refine ⟨31313114278778412057484525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41750819038371216076646033 31313114278778412057484525)
        ·
          refine ⟨11742417854541904521556697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31313114278778412057484525 11742417854541904521556697)
          ·
            refine ⟨8806813390906428391167523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11742417854541904521556697 8806813390906428391167523)
            ·
              refine ⟨13210220086359642586751285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8806813390906428391167523 13210220086359642586751285)
              ·
                refine ⟨1238458133096216492507933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13210220086359642586751285 1238458133096216492507933)
                ·
                  refine ⟨464421799911081184690475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238458133096216492507933 464421799911081184690475)
                  ·
                    rfl

theorem cell21_2035031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 3].length) (baseStart_2035031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035031 prefixEnd_2035031 := by exact prefixLift 2035031
  have htrace : WordTrace (prefixWord ++ tailWord_2035031) baseStart_2035031 baseEnd_2035031 := by
    simpa [prefixWord, tailWord_2035031, baseEnd_2035031] using wordTrace_append hprefix tailTrace_2035031
  have hstable : (prefixWord ++ tailWord_2035031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035031).length < 2 ^ (prefixWord ++ tailWord_2035031).sum := by decide
  have hdescent : baseEnd_2035031 < baseStart_2035031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035037 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 4]
def baseStart_2035037 : Nat := 118140960795 + 2035037 * 2 ^ 59
def prefixEnd_2035037 : Nat := 4983230072969 + 3 ^ 40 * 2035037 * 2
def baseEnd_2035037 : Nat := 464423169192826507590463

theorem tailTrace_2035037 : CollatzResearch.WordTrace tailWord_2035037 prefixEnd_2035037 464423169192826507590463 := by
  unfold tailWord_2035037
  simp only [CollatzResearch.WordTrace]
  refine ⟨74223897128415980494311365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49482598085610653662874243 74223897128415980494311365)
  ·
    refine ⟨13916980711577996342683381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74223897128415980494311365 13916980711577996342683381)
    ·
      refine ⟨1304716941710437157126567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13916980711577996342683381 1304716941710437157126567)
      ·
        refine ⟨1957075412565655735689851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304716941710437157126567 1957075412565655735689851)
        ·
          refine ⟨2935613118848483603534777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957075412565655735689851 2935613118848483603534777)
          ·
            refine ⟨2201709839136362702651083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2935613118848483603534777 2201709839136362702651083)
            ·
              refine ⟨3302564758704544053976625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2201709839136362702651083 3302564758704544053976625)
              ·
                refine ⟨2476923569028408040482469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302564758704544053976625 2476923569028408040482469)
                ·
                  refine ⟨464423169192826507590463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476923569028408040482469 464423169192826507590463)
                  ·
                    rfl

theorem cell21_2035037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_2035037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035037 prefixEnd_2035037 := by exact prefixLift 2035037
  have htrace : WordTrace (prefixWord ++ tailWord_2035037) baseStart_2035037 baseEnd_2035037 := by
    simpa [prefixWord, tailWord_2035037, baseEnd_2035037] using wordTrace_append hprefix tailTrace_2035037
  have hstable : (prefixWord ++ tailWord_2035037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035037).length < 2 ^ (prefixWord ++ tailWord_2035037).sum := by decide
  have hdescent : baseEnd_2035037 < baseStart_2035037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035076 : List Nat := [2, 3, 2, 1, 1, 3, 4, 5]
def baseStart_2035076 : Nat := 118140960795 + 2035076 * 2 ^ 59
def prefixEnd_2035076 : Nat := 4983230072969 + 3 ^ 40 * 2035076 * 2
def baseEnd_2035076 : Nat := 154810689841390368813461

theorem tailTrace_2035076 : CollatzResearch.WordTrace tailWord_2035076 prefixEnd_2035076 154810689841390368813461 := by
  unfold tailWord_2035076
  simp only [CollatzResearch.WordTrace]
  refine ⟨37112659787637345077490541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49483546383516460103320721 37112659787637345077490541)
  ·
    refine ⟨13917247420364004404058953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37112659787637345077490541 13917247420364004404058953)
    ·
      refine ⟨10437935565273003303044215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13917247420364004404058953 10437935565273003303044215)
      ·
        refine ⟨15656903347909504954566323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10437935565273003303044215 15656903347909504954566323)
        ·
          refine ⟨23485355021864257431849485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15656903347909504954566323 23485355021864257431849485)
          ·
            refine ⟨8807008133199096536943557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23485355021864257431849485 8807008133199096536943557)
            ·
              refine ⟨1651314024974830600676917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8807008133199096536943557 1651314024974830600676917)
              ·
                refine ⟨154810689841390368813461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1651314024974830600676917 154810689841390368813461)
                ·
                  rfl

theorem cell21_2035076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_2035076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035076 prefixEnd_2035076 := by exact prefixLift 2035076
  have htrace : WordTrace (prefixWord ++ tailWord_2035076) baseStart_2035076 baseEnd_2035076 := by
    simpa [prefixWord, tailWord_2035076, baseEnd_2035076] using wordTrace_append hprefix tailTrace_2035076
  have hstable : (prefixWord ++ tailWord_2035076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035076).length < 2 ^ (prefixWord ++ tailWord_2035076).sum := by decide
  have hdescent : baseEnd_2035076 < baseStart_2035076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035104 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_2035104 : Nat := 118140960795 + 2035104 * 2 ^ 59
def prefixEnd_2035104 : Nat := 4983230072969 + 3 ^ 40 * 2035104 * 2
def baseEnd_2035104 : Nat := 464438459505649279973659

theorem tailTrace_2035104 : CollatzResearch.WordTrace tailWord_2035104 prefixEnd_2035104 464438459505649279973659 := by
  unfold tailWord_2035104
  simp only [CollatzResearch.WordTrace]
  refine ⟨37113170409586625468500183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49484227212782167291333577 37113170409586625468500183)
  ·
    refine ⟨55669755614379938202750275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37113170409586625468500183 55669755614379938202750275)
    ·
      refine ⟨83504633421569907304125413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55669755614379938202750275 83504633421569907304125413)
      ·
        refine ⟨15657118766544357619523515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83504633421569907304125413 15657118766544357619523515)
        ·
          refine ⟨23485678149816536429285273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15657118766544357619523515 23485678149816536429285273)
          ·
            refine ⟨17614258612362402321963955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23485678149816536429285273 17614258612362402321963955)
            ·
              refine ⟨26421387918543603482945933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17614258612362402321963955 26421387918543603482945933)
              ·
                refine ⟨9908020469453851306104725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26421387918543603482945933 9908020469453851306104725)
                ·
                  refine ⟨464438459505649279973659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9908020469453851306104725 464438459505649279973659)
                  ·
                    rfl

theorem cell21_2035104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_2035104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035104 prefixEnd_2035104 := by exact prefixLift 2035104
  have htrace : WordTrace (prefixWord ++ tailWord_2035104) baseStart_2035104 baseEnd_2035104 := by
    simpa [prefixWord, tailWord_2035104, baseEnd_2035104] using wordTrace_append hprefix tailTrace_2035104
  have hstable : (prefixWord ++ tailWord_2035104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035104).length < 2 ^ (prefixWord ++ tailWord_2035104).sum := by decide
  have hdescent : baseEnd_2035104 < baseStart_2035104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035121 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 4]
def baseStart_2035121 : Nat := 118140960795 + 2035121 * 2 ^ 59
def prefixEnd_2035121 : Nat := 4983230072969 + 3 ^ 40 * 2035121 * 2
def baseEnd_2035121 : Nat := 464442339137261028190291

theorem tailTrace_2035121 : CollatzResearch.WordTrace tailWord_2035121 prefixEnd_2035121 464442339137261028190291 := by
  unfold tailWord_2035121
  simp only [CollatzResearch.WordTrace]
  refine ⟨74226960860111662840369217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49484640573407775226912811 74226960860111662840369217)
  ·
    refine ⟨55670220645083747130276913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74226960860111662840369217 55670220645083747130276913)
    ·
      refine ⟨41752665483812810347707685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55670220645083747130276913 41752665483812810347707685)
      ·
        refine ⟨7828624778214901940195191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41752665483812810347707685 7828624778214901940195191)
        ·
          refine ⟨11742937167322352910292787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7828624778214901940195191 11742937167322352910292787)
          ·
            refine ⟨17614405750983529365439181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11742937167322352910292787 17614405750983529365439181)
            ·
              refine ⟨6605402156618823512039693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17614405750983529365439181 6605402156618823512039693)
              ·
                refine ⟨2477025808732058817014885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6605402156618823512039693 2477025808732058817014885)
                ·
                  refine ⟨464442339137261028190291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2477025808732058817014885 464442339137261028190291)
                  ·
                    rfl

theorem cell21_2035121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_2035121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035121 prefixEnd_2035121 := by exact prefixLift 2035121
  have htrace : WordTrace (prefixWord ++ tailWord_2035121) baseStart_2035121 baseEnd_2035121 := by
    simpa [prefixWord, tailWord_2035121, baseEnd_2035121] using wordTrace_append hprefix tailTrace_2035121
  have hstable : (prefixWord ++ tailWord_2035121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035121).length < 2 ^ (prefixWord ++ tailWord_2035121).sum := by decide
  have hdescent : baseEnd_2035121 < baseStart_2035121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035158 : List Nat := [5, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2035158 : Nat := 118140960795 + 2035158 * 2 ^ 59
def prefixEnd_2035158 : Nat := 4983230072969 + 3 ^ 40 * 2035158 * 2
def baseEnd_2035158 : Nat := 464450783041357186073549

theorem tailTrace_2035158 : CollatzResearch.WordTrace tailWord_2035158 prefixEnd_2035158 464450783041357186073549 := by
  unfold tailWord_2035158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4639269397561101134966633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49485540240651745439644085 4639269397561101134966633)
  ·
    refine ⟨3479452048170825851224975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4639269397561101134966633 3479452048170825851224975)
    ·
      refine ⟨5219178072256238776837463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3479452048170825851224975 5219178072256238776837463)
      ·
        refine ⟨7828767108384358165256195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5219178072256238776837463 7828767108384358165256195)
        ·
          refine ⟨11743150662576537247884293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7828767108384358165256195 11743150662576537247884293)
          ·
            refine ⟨2201840749233100733978305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11743150662576537247884293 2201840749233100733978305)
            ·
              refine ⟨1651380561924825550483729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2201840749233100733978305 1651380561924825550483729)
              ·
                refine ⟨1238535421443619162862797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651380561924825550483729 1238535421443619162862797)
                ·
                  refine ⟨464450783041357186073549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238535421443619162862797 464450783041357186073549)
                  ·
                    rfl

theorem cell21_2035158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2035158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035158 prefixEnd_2035158 := by exact prefixLift 2035158
  have htrace : WordTrace (prefixWord ++ tailWord_2035158) baseStart_2035158 baseEnd_2035158 := by
    simpa [prefixWord, tailWord_2035158, baseEnd_2035158] using wordTrace_append hprefix tailTrace_2035158
  have hstable : (prefixWord ++ tailWord_2035158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035158).length < 2 ^ (prefixWord ++ tailWord_2035158).sum := by decide
  have hdescent : baseEnd_2035158 < baseStart_2035158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035206 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2035206 : Nat := 118140960795 + 2035206 * 2 ^ 59
def prefixEnd_2035206 : Nat := 4983230072969 + 3 ^ 40 * 2035206 * 2
def baseEnd_2035206 : Nat := 464461737295319769273451

theorem tailTrace_2035206 : CollatzResearch.WordTrace tailWord_2035206 prefixEnd_2035206 464461737295319769273451 := by
  unfold tailWord_2035206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319689408275116323662921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49486707376535814904808981 2319689408275116323662921)
  ·
    refine ⟨1739767056206337242747191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2319689408275116323662921 1739767056206337242747191)
    ·
      refine ⟨2609650584309505864120787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1739767056206337242747191 2609650584309505864120787)
      ·
        refine ⟨3914475876464258796181181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609650584309505864120787 3914475876464258796181181)
        ·
          refine ⟨1467928453674097048567943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3914475876464258796181181 1467928453674097048567943)
          ·
            refine ⟨2201892680511145572851915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467928453674097048567943 2201892680511145572851915)
            ·
              refine ⟨3302839020766718359277873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2201892680511145572851915 3302839020766718359277873)
              ·
                refine ⟨2477129265575038769458405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302839020766718359277873 2477129265575038769458405)
                ·
                  refine ⟨464461737295319769273451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2477129265575038769458405 464461737295319769273451)
                  ·
                    rfl

theorem cell21_2035206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2035206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035206 prefixEnd_2035206 := by exact prefixLift 2035206
  have htrace : WordTrace (prefixWord ++ tailWord_2035206) baseStart_2035206 baseEnd_2035206 := by
    simpa [prefixWord, tailWord_2035206, baseEnd_2035206] using wordTrace_append hprefix tailTrace_2035206
  have hstable : (prefixWord ++ tailWord_2035206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035206).length < 2 ^ (prefixWord ++ tailWord_2035206).sum := by decide
  have hdescent : baseEnd_2035206 < baseStart_2035206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035211 : List Nat := [1, 1, 1, 1, 8, 1, 8]
def baseStart_2035211 : Nat := 118140960795 + 2035211 * 2 ^ 59
def prefixEnd_2035211 : Nat := 4983230072969 + 3 ^ 40 * 2035211 * 2
def baseEnd_2035211 : Nat := 51606986484826763521123

theorem tailTrace_2035211 : CollatzResearch.WordTrace tailWord_2035211 prefixEnd_2035211 51606986484826763521123 := by
  unfold tailWord_2035211
  simp only [CollatzResearch.WordTrace]
  refine ⟨74230243429785608211145487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49486828953190405474096991 74230243429785608211145487)
  ·
    refine ⟨111345365144678412316718231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74230243429785608211145487 111345365144678412316718231)
    ·
      refine ⟨167018047717017618475077347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111345365144678412316718231 167018047717017618475077347)
      ·
        refine ⟨250527071575526427712616021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167018047717017618475077347 250527071575526427712616021)
        ·
          refine ⟨2935864120025700324757219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 250527071575526427712616021 2935864120025700324757219)
          ·
            refine ⟨4403796180038550487135829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935864120025700324757219 4403796180038550487135829)
            ·
              refine ⟨51606986484826763521123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4403796180038550487135829 51606986484826763521123)
              ·
                rfl

theorem cell21_2035211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 8].length) (baseStart_2035211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035211 prefixEnd_2035211 := by exact prefixLift 2035211
  have htrace : WordTrace (prefixWord ++ tailWord_2035211) baseStart_2035211 baseEnd_2035211 := by
    simpa [prefixWord, tailWord_2035211, baseEnd_2035211] using wordTrace_append hprefix tailTrace_2035211
  have hstable : (prefixWord ++ tailWord_2035211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035211).length < 2 ^ (prefixWord ++ tailWord_2035211).sum := by decide
  have hdescent : baseEnd_2035211 < baseStart_2035211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035242 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_2035242 : Nat := 118140960795 + 2035242 * 2 ^ 59
def prefixEnd_2035242 : Nat := 4983230072969 + 3 ^ 40 * 2035242 * 2
def baseEnd_2035242 : Nat := 464469952985791706673377

theorem tailTrace_2035242 : CollatzResearch.WordTrace tailWord_2035242 prefixEnd_2035242 464469952985791706673377 := by
  unfold tailWord_2035242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18557843523168325126380995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49487582728448867003682653 18557843523168325126380995)
  ·
    refine ⟨27836765284752487689571493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18557843523168325126380995 27836765284752487689571493)
    ·
      refine ⟨5219393490891091441794655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27836765284752487689571493 5219393490891091441794655)
      ·
        refine ⟨7829090236336637162691983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5219393490891091441794655 7829090236336637162691983)
        ·
          refine ⟨11743635354504955744037975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7829090236336637162691983 11743635354504955744037975)
          ·
            refine ⟨17615453031757433616056963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11743635354504955744037975 17615453031757433616056963)
            ·
              refine ⟨26423179547636150424085445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17615453031757433616056963 26423179547636150424085445)
              ·
                refine ⟨4954346165181778204516021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26423179547636150424085445 4954346165181778204516021)
                ·
                  refine ⟨464469952985791706673377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4954346165181778204516021 464469952985791706673377)
                  ·
                    rfl

theorem cell21_2035242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_2035242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035242 prefixEnd_2035242 := by exact prefixLift 2035242
  have htrace : WordTrace (prefixWord ++ tailWord_2035242) baseStart_2035242 baseEnd_2035242 := by
    simpa [prefixWord, tailWord_2035242, baseEnd_2035242] using wordTrace_append hprefix tailTrace_2035242
  have hstable : (prefixWord ++ tailWord_2035242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035242).length < 2 ^ (prefixWord ++ tailWord_2035242).sum := by decide
  have hdescent : baseEnd_2035242 < baseStart_2035242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035256 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_2035256 : Nat := 118140960795 + 2035256 * 2 ^ 59
def prefixEnd_2035256 : Nat := 4983230072969 + 3 ^ 40 * 2035256 * 2
def baseEnd_2035256 : Nat := 464473147976530793440015

theorem tailTrace_2035256 : CollatzResearch.WordTrace tailWord_2035256 prefixEnd_2035256 464473147976530793440015 := by
  unfold tailWord_2035256
  simp only [CollatzResearch.WordTrace]
  refine ⟨37115942357311290448266811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49487923143081720597689081 37115942357311290448266811)
  ·
    refine ⟨55673913535966935672400217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37115942357311290448266811 55673913535966935672400217)
    ·
      refine ⟨41755435151975201754300163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55673913535966935672400217 41755435151975201754300163)
      ·
        refine ⟨62633152727962802631450245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41755435151975201754300163 62633152727962802631450245)
        ·
          refine ⟨11743716136493025493396921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62633152727962802631450245 11743716136493025493396921)
          ·
            refine ⟨8807787102369769120047691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11743716136493025493396921 8807787102369769120047691)
            ·
              refine ⟨13211680653554653680071537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8807787102369769120047691 13211680653554653680071537)
              ·
                refine ⟨9908760490165990260053653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13211680653554653680071537 9908760490165990260053653)
                ·
                  refine ⟨464473147976530793440015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9908760490165990260053653 464473147976530793440015)
                  ·
                    rfl

theorem cell21_2035256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_2035256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035256 prefixEnd_2035256 := by exact prefixLift 2035256
  have htrace : WordTrace (prefixWord ++ tailWord_2035256) baseStart_2035256 baseEnd_2035256 := by
    simpa [prefixWord, tailWord_2035256, baseEnd_2035256] using wordTrace_append hprefix tailTrace_2035256
  have hstable : (prefixWord ++ tailWord_2035256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035256).length < 2 ^ (prefixWord ++ tailWord_2035256).sum := by decide
  have hdescent : baseEnd_2035256 < baseStart_2035256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035276 : List Nat := [2, 2, 1, 3, 1, 4, 3, 2, 3]
def baseStart_2035276 : Nat := 118140960795 + 2035276 * 2 ^ 59
def prefixEnd_2035276 : Nat := 4983230072969 + 3 ^ 40 * 2035276 * 2
def baseEnd_2035276 : Nat := 464477712249015203106641

theorem tailTrace_2035276 : CollatzResearch.WordTrace tailWord_2035276 prefixEnd_2035276 464477712249015203106641 := by
  unfold tailWord_2035276
  simp only [CollatzResearch.WordTrace]
  refine ⟨37116307087275062156130841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49488409449700082874841121 37116307087275062156130841)
  ·
    refine ⟨27837230315456296617098131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37116307087275062156130841 27837230315456296617098131)
    ·
      refine ⟨41755845473184444925647197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27837230315456296617098131 41755845473184444925647197)
      ·
        refine ⟨15658442052444166847117699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41755845473184444925647197 15658442052444166847117699)
        ·
          refine ⟨23487663078666250270676549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15658442052444166847117699 23487663078666250270676549)
          ·
            refine ⟨4403936827249921925751853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23487663078666250270676549 4403936827249921925751853)
            ·
              refine ⟨1651476310218720722156945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4403936827249921925751853 1651476310218720722156945)
              ·
                refine ⟨1238607232664040541617709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651476310218720722156945 1238607232664040541617709)
                ·
                  refine ⟨464477712249015203106641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238607232664040541617709 464477712249015203106641)
                  ·
                    rfl

theorem cell21_2035276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_2035276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035276 prefixEnd_2035276 := by exact prefixLift 2035276
  have htrace : WordTrace (prefixWord ++ tailWord_2035276) baseStart_2035276 baseEnd_2035276 := by
    simpa [prefixWord, tailWord_2035276, baseEnd_2035276] using wordTrace_append hprefix tailTrace_2035276
  have hstable : (prefixWord ++ tailWord_2035276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035276).length < 2 ^ (prefixWord ++ tailWord_2035276).sum := by decide
  have hdescent : baseEnd_2035276 < baseStart_2035276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035287 : List Nat := [1, 1, 3, 2, 2, 4, 2, 6]
def baseStart_2035287 : Nat := 118140960795 + 2035287 * 2 ^ 59
def prefixEnd_2035287 : Nat := 4983230072969 + 3 ^ 40 * 2035287 * 2
def baseEnd_2035287 : Nat := 154826740866293876141095

theorem tailTrace_2035287 : CollatzResearch.WordTrace tailWord_2035287 prefixEnd_2035287 154826740866293876141095 := by
  unfold tailWord_2035287
  simp only [CollatzResearch.WordTrace]
  refine ⟨74233015377510273190912115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49488676918340182127274743 74233015377510273190912115)
  ·
    refine ⟨111349523066265409786368173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74233015377510273190912115 111349523066265409786368173)
    ·
      refine ⟨41756071149849528669888065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111349523066265409786368173 41756071149849528669888065)
      ·
        refine ⟨31317053362387146502416049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41756071149849528669888065 31317053362387146502416049)
        ·
          refine ⟨23487790021790359876812037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31317053362387146502416049 23487790021790359876812037)
          ·
            refine ⟨4403960629085692476902257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23487790021790359876812037 4403960629085692476902257)
            ·
              refine ⟨3302970471814269357676693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4403960629085692476902257 3302970471814269357676693)
              ·
                refine ⟨154826740866293876141095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3302970471814269357676693 154826740866293876141095)
                ·
                  rfl

theorem cell21_2035287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 6].length) (baseStart_2035287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035287 prefixEnd_2035287 := by exact prefixLift 2035287
  have htrace : WordTrace (prefixWord ++ tailWord_2035287) baseStart_2035287 baseEnd_2035287 := by
    simpa [prefixWord, tailWord_2035287, baseEnd_2035287] using wordTrace_append hprefix tailTrace_2035287
  have hstable : (prefixWord ++ tailWord_2035287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035287).length < 2 ^ (prefixWord ++ tailWord_2035287).sum := by decide
  have hdescent : baseEnd_2035287 < baseStart_2035287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035335 : List Nat := [1, 1, 4, 2, 1, 4, 1, 4, 3]
def baseStart_2035335 : Nat := 118140960795 + 2035335 * 2 ^ 59
def prefixEnd_2035335 : Nat := 4983230072969 + 3 ^ 40 * 2035335 * 2
def baseEnd_2035335 : Nat := 464491176852844211623187

theorem tailTrace_2035335 : CollatzResearch.WordTrace tailWord_2035335 prefixEnd_2035335 464491176852844211623187 := by
  unfold tailWord_2035335
  simp only [CollatzResearch.WordTrace]
  refine ⟨74234766081336377388659459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49489844054224251592439639 74234766081336377388659459)
  ·
    refine ⟨111352149122004566082989189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74234766081336377388659459 111352149122004566082989189)
    ·
      refine ⟨20878527960375856140560473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111352149122004566082989189 20878527960375856140560473)
      ·
        refine ⟨15658895970281892105420355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20878527960375856140560473 15658895970281892105420355)
        ·
          refine ⟨23488343955422838158130533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15658895970281892105420355 23488343955422838158130533)
          ·
            refine ⟨4404064491641782154649475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23488343955422838158130533 4404064491641782154649475)
            ·
              refine ⟨6606096737462673231974213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404064491641782154649475 6606096737462673231974213)
              ·
                refine ⟨1238643138274251230995165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6606096737462673231974213 1238643138274251230995165)
                ·
                  refine ⟨464491176852844211623187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238643138274251230995165 464491176852844211623187)
                  ·
                    rfl

theorem cell21_2035335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 3].length) (baseStart_2035335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035335 prefixEnd_2035335 := by exact prefixLift 2035335
  have htrace : WordTrace (prefixWord ++ tailWord_2035335) baseStart_2035335 baseEnd_2035335 := by
    simpa [prefixWord, tailWord_2035335, baseEnd_2035335] using wordTrace_append hprefix tailTrace_2035335
  have hstable : (prefixWord ++ tailWord_2035335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035335).length < 2 ^ (prefixWord ++ tailWord_2035335).sum := by decide
  have hdescent : baseEnd_2035335 < baseStart_2035335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035363 : List Nat := [1, 1, 1, 4, 1, 1, 7, 5]
def baseStart_2035363 : Nat := 118140960795 + 2035363 * 2 ^ 59
def prefixEnd_2035363 : Nat := 4983230072969 + 3 ^ 40 * 2035363 * 2
def baseEnd_2035363 : Nat := 154832522278107461718821

theorem tailTrace_2035363 : CollatzResearch.WordTrace tailWord_2035363 prefixEnd_2035363 154832522278107461718821 := by
  unfold tailWord_2035363
  simp only [CollatzResearch.WordTrace]
  refine ⟨74235787325234938170678743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49490524883489958780452495 74235787325234938170678743)
  ·
    refine ⟨111353680987852407256018115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74235787325234938170678743 111353680987852407256018115)
    ·
      refine ⟨167030521481778610884027173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111353680987852407256018115 167030521481778610884027173)
      ·
        refine ⟨31318222777833489540755095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167030521481778610884027173 31318222777833489540755095)
        ·
          refine ⟨46977334166750234311132643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31318222777833489540755095 46977334166750234311132643)
          ·
            refine ⟨70466001250125351466698965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46977334166750234311132643 70466001250125351466698965)
            ·
              refine ⟨1651546904299812925000757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 70466001250125351466698965 1651546904299812925000757)
              ·
                refine ⟨154832522278107461718821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1651546904299812925000757 154832522278107461718821)
                ·
                  rfl

theorem cell21_2035363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 5].length) (baseStart_2035363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035363 prefixEnd_2035363 := by exact prefixLift 2035363
  have htrace : WordTrace (prefixWord ++ tailWord_2035363) baseStart_2035363 baseEnd_2035363 := by
    simpa [prefixWord, tailWord_2035363, baseEnd_2035363] using wordTrace_append hprefix tailTrace_2035363
  have hstable : (prefixWord ++ tailWord_2035363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035363).length < 2 ^ (prefixWord ++ tailWord_2035363).sum := by decide
  have hdescent : baseEnd_2035363 < baseStart_2035363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035453 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 5]
def baseStart_2035453 : Nat := 118140960795 + 2035453 * 2 ^ 59
def prefixEnd_2035453 : Nat := 4983230072969 + 3 ^ 40 * 2035453 * 2
def baseEnd_2035453 : Nat := 464518106060502228656279

theorem tailTrace_2035453 : CollatzResearch.WordTrace tailWord_2035453 prefixEnd_2035453 464518106060502228656279 := by
  unfold tailWord_2035453
  simp only [CollatzResearch.WordTrace]
  refine ⟨74239069894908883541455013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49492713263272589027636675 74239069894908883541455013)
  ·
    refine ⟨13919825605295415664022815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74239069894908883541455013 13919825605295415664022815)
    ·
      refine ⟨20879738407943123496034223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13919825605295415664022815 20879738407943123496034223)
      ·
        refine ⟨31319607611914685244051335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20879738407943123496034223 31319607611914685244051335)
        ·
          refine ⟨46979411417872027866077003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31319607611914685244051335 46979411417872027866077003)
          ·
            refine ⟨70469117126808041799115505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46979411417872027866077003 70469117126808041799115505)
            ·
              refine ⟨52851837845106031349336629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70469117126808041799115505 52851837845106031349336629)
              ·
                refine ⟨4954859797978690439000309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52851837845106031349336629 4954859797978690439000309)
                ·
                  refine ⟨464518106060502228656279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4954859797978690439000309 464518106060502228656279)
                  ·
                    rfl

theorem cell21_2035453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_2035453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035453 prefixEnd_2035453 := by exact prefixLift 2035453
  have htrace : WordTrace (prefixWord ++ tailWord_2035453) baseStart_2035453 baseEnd_2035453 := by
    simpa [prefixWord, tailWord_2035453, baseEnd_2035453] using wordTrace_append hprefix tailTrace_2035453
  have hstable : (prefixWord ++ tailWord_2035453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035453).length < 2 ^ (prefixWord ++ tailWord_2035453).sum := by decide
  have hdescent : baseEnd_2035453 < baseStart_2035453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035498 : List Nat := [3, 1, 4, 13]
def baseStart_2035498 : Nat := 118140960795 + 2035498 * 2 ^ 59
def prefixEnd_2035498 : Nat := 4983230072969 + 3 ^ 40 * 2035498 * 2
def baseEnd_2035498 : Nat := 1911639406064165228009

theorem tailTrace_2035498 : CollatzResearch.WordTrace tailWord_2035498 prefixEnd_2035498 1911639406064165228009 := by
  unfold tailWord_2035498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560177794936464056710787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49493807453163904151228765 18560177794936464056710787)
  ·
    refine ⟨27840266692404696085066181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18560177794936464056710787 27840266692404696085066181)
    ·
      refine ⟨5220050004825880515949909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27840266692404696085066181 5220050004825880515949909)
      ·
        refine ⟨1911639406064165228009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 5220050004825880515949909 1911639406064165228009)
        ·
          rfl

theorem cell21_2035498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 13].length) (baseStart_2035498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035498 prefixEnd_2035498 := by exact prefixLift 2035498
  have htrace : WordTrace (prefixWord ++ tailWord_2035498) baseStart_2035498 baseEnd_2035498 := by
    simpa [prefixWord, tailWord_2035498, baseEnd_2035498] using wordTrace_append hprefix tailTrace_2035498
  have hstable : (prefixWord ++ tailWord_2035498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035498).length < 2 ^ (prefixWord ++ tailWord_2035498).sum := by decide
  have hdescent : baseEnd_2035498 < baseStart_2035498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
