import V185TrunkScan23Chunk0447

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2649851 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 5, 3, 2]
def baseStart_2649851 : Nat := 118140960795 + 2649851 * 2 ^ 59
def prefixEnd_2649851 : Nat := 4983230072969 + 3 ^ 40 * 2649851 * 2
def baseEnd_2649851 : Nat := 1360647225797217179476063

theorem tailTrace_2649851 : CollatzResearch.WordTrace tailWord_2649851 prefixEnd_2649851 1360647225797217179476063 := by
  unfold tailWord_2649851
  simp only [CollatzResearch.WordTrace]
  refine ⟨96648005923049860365885407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64432003948699906910590271 96648005923049860365885407)
  ·
    refine ⟨144972008884574790548828111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96648005923049860365885407 144972008884574790548828111)
    ·
      refine ⟨217458013326862185823242167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144972008884574790548828111 217458013326862185823242167)
      ·
        refine ⟨326187019990293278734863251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217458013326862185823242167 326187019990293278734863251)
        ·
          refine ⟨489280529985439918102294877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326187019990293278734863251 489280529985439918102294877)
          ·
            refine ⟨183480198744539969288360579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 489280529985439918102294877 183480198744539969288360579)
            ·
              refine ⟨275220298116809953932540869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183480198744539969288360579 275220298116809953932540869)
              ·
                refine ⟨51603805896901866362351413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275220298116809953932540869 51603805896901866362351413)
                ·
                  refine ⟨4837856802834549971470445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51603805896901866362351413 4837856802834549971470445)
                  ·
                    refine ⟨1814196301062956239301417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4837856802834549971470445 1814196301062956239301417)
                    ·
                      refine ⟨1360647225797217179476063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814196301062956239301417 1360647225797217179476063)
                      ·
                        rfl

theorem cell23_2649851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 3, 2].length) (baseStart_2649851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649851 prefixEnd_2649851 := by exact prefixLift 2649851
  have htrace : WordTrace (prefixWord ++ tailWord_2649851) baseStart_2649851 baseEnd_2649851 := by
    simpa [prefixWord, tailWord_2649851, baseEnd_2649851] using wordTrace_append hprefix tailTrace_2649851
  have hstable : (prefixWord ++ tailWord_2649851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649851).length < 2 ^ (prefixWord ++ tailWord_2649851).sum := by decide
  have hdescent : baseEnd_2649851 < baseStart_2649851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649869 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2649869 : Nat := 118140960795 + 2649869 * 2 ^ 59
def prefixEnd_2649869 : Nat := 4983230072969 + 3 ^ 40 * 2649869 * 2
def baseEnd_2649869 : Nat := 453552156149666036350327

theorem tailTrace_2649869 : CollatzResearch.WordTrace tailWord_2649869 prefixEnd_2649869 453552156149666036350327 := by
  unfold tailWord_2649869
  simp only [CollatzResearch.WordTrace]
  refine ⟨96648662436984649440040661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64432441624656432960027107 96648662436984649440040661)
  ·
    refine ⟨2265203025866827721250953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 96648662436984649440040661 2265203025866827721250953)
    ·
      refine ⟨1698902269400120790938215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2265203025866827721250953 1698902269400120790938215)
      ·
        refine ⟨2548353404100181186407323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1698902269400120790938215 2548353404100181186407323)
        ·
          refine ⟨3822530106150271779610985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2548353404100181186407323 3822530106150271779610985)
          ·
            refine ⟨2866897579612703834708239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3822530106150271779610985 2866897579612703834708239)
            ·
              refine ⟨4300346369419055752062359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866897579612703834708239 4300346369419055752062359)
              ·
                refine ⟨6450519554128583628093539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4300346369419055752062359 6450519554128583628093539)
                ·
                  refine ⟨9675779331192875442140309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6450519554128583628093539 9675779331192875442140309)
                  ·
                    refine ⟨453552156149666036350327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9675779331192875442140309 453552156149666036350327)
                    ·
                      rfl

theorem cell23_2649869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2649869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649869 prefixEnd_2649869 := by exact prefixLift 2649869
  have htrace : WordTrace (prefixWord ++ tailWord_2649869) baseStart_2649869 baseEnd_2649869 := by
    simpa [prefixWord, tailWord_2649869, baseEnd_2649869] using wordTrace_append hprefix tailTrace_2649869
  have hstable : (prefixWord ++ tailWord_2649869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649869).length < 2 ^ (prefixWord ++ tailWord_2649869).sum := by decide
  have hdescent : baseEnd_2649869 < baseStart_2649869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649926 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_2649926 : Nat := 118140960795 + 2649926 * 2 ^ 59
def prefixEnd_2649926 : Nat := 4983230072969 + 3 ^ 40 * 2649926 * 2
def baseEnd_2649926 : Nat := 1360685736846304386038219

theorem tailTrace_2649926 : CollatzResearch.WordTrace tailWord_2649926 prefixEnd_2649926 1360685736846304386038219 := by
  unfold tailWord_2649926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3020335668680567130464551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64433827598518765449910421 3020335668680567130464551)
  ·
    refine ⟨4530503503020850695696827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3020335668680567130464551 4530503503020850695696827)
    ·
      refine ⟨6795755254531276043545241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4530503503020850695696827 6795755254531276043545241)
      ·
        refine ⟨5096816440898457032658931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6795755254531276043545241 5096816440898457032658931)
        ·
          refine ⟨7645224661347685548988397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5096816440898457032658931 7645224661347685548988397)
          ·
            refine ⟨2866959248005382080870649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7645224661347685548988397 2866959248005382080870649)
            ·
              refine ⟨2150219436004036560652987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2866959248005382080870649 2150219436004036560652987)
              ·
                refine ⟨3225329154006054840979481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150219436004036560652987 3225329154006054840979481)
                ·
                  refine ⟨2418996865504541130734611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3225329154006054840979481 2418996865504541130734611)
                  ·
                    refine ⟨3628495298256811696101917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2418996865504541130734611 3628495298256811696101917)
                    ·
                      refine ⟨1360685736846304386038219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3628495298256811696101917 1360685736846304386038219)
                      ·
                        rfl

theorem cell23_2649926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_2649926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649926 prefixEnd_2649926 := by exact prefixLift 2649926
  have htrace : WordTrace (prefixWord ++ tailWord_2649926) baseStart_2649926 baseEnd_2649926 := by
    simpa [prefixWord, tailWord_2649926, baseEnd_2649926] using wordTrace_append hprefix tailTrace_2649926
  have hstable : (prefixWord ++ tailWord_2649926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649926).length < 2 ^ (prefixWord ++ tailWord_2649926).sum := by decide
  have hdescent : baseEnd_2649926 < baseStart_2649926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649932 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 2, 2, 2]
def baseStart_2649932 : Nat := 118140960795 + 2649932 * 2 ^ 59
def prefixEnd_2649932 : Nat := 4983230072969 + 3 ^ 40 * 2649932 * 2
def baseEnd_2649932 : Nat := 1360688817730231362563191

theorem tailTrace_2649932 : CollatzResearch.WordTrace tailWord_2649932 prefixEnd_2649932 1360688817730231362563191 := by
  unfold tailWord_2649932
  simp only [CollatzResearch.WordTrace]
  refine ⟨48325480117878205599792025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64433973490504274133056033 48325480117878205599792025)
  ·
    refine ⟨36244110088408654199844019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48325480117878205599792025 36244110088408654199844019)
    ·
      refine ⟨54366165132612981299766029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36244110088408654199844019 54366165132612981299766029)
      ·
        refine ⟨20387311924729867987412261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54366165132612981299766029 20387311924729867987412261)
        ·
          refine ⟨3822620985886850247639799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20387311924729867987412261 3822620985886850247639799)
          ·
            refine ⟨5733931478830275371459699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822620985886850247639799 5733931478830275371459699)
            ·
              refine ⟨8600897218245413057189549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5733931478830275371459699 8600897218245413057189549)
              ·
                refine ⟨3225336456842029896446081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8600897218245413057189549 3225336456842029896446081)
                ·
                  refine ⟨2419002342631522422334561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3225336456842029896446081 2419002342631522422334561)
                  ·
                    refine ⟨1814251756973641816750921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2419002342631522422334561 1814251756973641816750921)
                    ·
                      refine ⟨1360688817730231362563191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814251756973641816750921 1360688817730231362563191)
                      ·
                        rfl

theorem cell23_2649932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_2649932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649932 prefixEnd_2649932 := by exact prefixLift 2649932
  have htrace : WordTrace (prefixWord ++ tailWord_2649932) baseStart_2649932 baseEnd_2649932 := by
    simpa [prefixWord, tailWord_2649932, baseEnd_2649932] using wordTrace_append hprefix tailTrace_2649932
  have hstable : (prefixWord ++ tailWord_2649932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649932).length < 2 ^ (prefixWord ++ tailWord_2649932).sum := by decide
  have hdescent : baseEnd_2649932 < baseStart_2649932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649951 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 2, 5]
def baseStart_2649951 : Nat := 118140960795 + 2649951 * 2 ^ 59
def prefixEnd_2649951 : Nat := 4983230072969 + 3 ^ 40 * 2649951 * 2
def baseEnd_2649951 : Nat := 453566191287555596075201

theorem tailTrace_2649951 : CollatzResearch.WordTrace tailWord_2649951 prefixEnd_2649951 453566191287555596075201 := by
  unfold tailWord_2649951
  simp only [CollatzResearch.WordTrace]
  refine ⟨96651653222687577444525707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64434435481791718296350471 96651653222687577444525707)
  ·
    refine ⟨144977479834031366166788561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96651653222687577444525707 144977479834031366166788561)
    ·
      refine ⟨108733109875523524625091421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144977479834031366166788561 108733109875523524625091421)
      ·
        refine ⟨40774916203321321734409283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108733109875523524625091421 40774916203321321734409283)
        ·
          refine ⟨61162374304981982601613925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40774916203321321734409283 61162374304981982601613925)
          ·
            refine ⟨11467945182184121737802611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61162374304981982601613925 11467945182184121737802611)
            ·
              refine ⟨17201917773276182606703917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11467945182184121737802611 17201917773276182606703917)
              ·
                refine ⟨6450719164978568477513969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17201917773276182606703917 6450719164978568477513969)
                ·
                  refine ⟨4838039373733926358135477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6450719164978568477513969 4838039373733926358135477)
                  ·
                    refine ⟨453566191287555596075201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4838039373733926358135477 453566191287555596075201)
                    ·
                      rfl

theorem cell23_2649951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_2649951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649951 prefixEnd_2649951 := by exact prefixLift 2649951
  have htrace : WordTrace (prefixWord ++ tailWord_2649951) baseStart_2649951 baseEnd_2649951 := by
    simpa [prefixWord, tailWord_2649951, baseEnd_2649951] using wordTrace_append hprefix tailTrace_2649951
  have hstable : (prefixWord ++ tailWord_2649951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649951).length < 2 ^ (prefixWord ++ tailWord_2649951).sum := by decide
  have hdescent : baseEnd_2649951 < baseStart_2649951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649988 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_2649988 : Nat := 118140960795 + 2649988 * 2 ^ 59
def prefixEnd_2649988 : Nat := 4983230072969 + 3 ^ 40 * 2649988 * 2
def baseEnd_2649988 : Nat := 1360717572646883143462933

theorem tailTrace_2649988 : CollatzResearch.WordTrace tailWord_2649988 prefixEnd_2649988 1360717572646883143462933 := by
  unfold tailWord_2649988
  simp only [CollatzResearch.WordTrace]
  refine ⟨48326501361776766381811309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64435335149035688509081745 48326501361776766381811309)
  ·
    refine ⟨18122438010666287393179241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48326501361776766381811309 18122438010666287393179241)
    ·
      refine ⟨13591828507999715544884431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18122438010666287393179241 13591828507999715544884431)
      ·
        refine ⟨20387742761999573317326647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13591828507999715544884431 20387742761999573317326647)
        ·
          refine ⟨30581614142999359975989971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20387742761999573317326647 30581614142999359975989971)
          ·
            refine ⟨45872421214499039963984957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30581614142999359975989971 45872421214499039963984957)
            ·
              refine ⟨17202157955437139986494359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45872421214499039963984957 17202157955437139986494359)
              ·
                refine ⟨25803236933155709979741539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17202157955437139986494359 25803236933155709979741539)
                ·
                  refine ⟨38704855399733564969612309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25803236933155709979741539 38704855399733564969612309)
                  ·
                    refine ⟨1814290096862510857950577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38704855399733564969612309 1814290096862510857950577)
                    ·
                      refine ⟨1360717572646883143462933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814290096862510857950577 1360717572646883143462933)
                      ·
                        rfl

theorem cell23_2649988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_2649988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649988 prefixEnd_2649988 := by exact prefixLift 2649988
  have htrace : WordTrace (prefixWord ++ tailWord_2649988) baseStart_2649988 baseEnd_2649988 := by
    simpa [prefixWord, tailWord_2649988, baseEnd_2649988] using wordTrace_append hprefix tailTrace_2649988
  have hstable : (prefixWord ++ tailWord_2649988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649988).length < 2 ^ (prefixWord ++ tailWord_2649988).sum := by decide
  have hdescent : baseEnd_2649988 < baseStart_2649988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650021 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 1, 7, 3]
def baseStart_2650021 : Nat := 118140960795 + 2650021 * 2 ^ 59
def prefixEnd_2650021 : Nat := 4983230072969 + 3 ^ 40 * 2650021 * 2
def baseEnd_2650021 : Nat := 1360734517508481514350281

theorem tailTrace_2650021 : CollatzResearch.WordTrace tailWord_2650021 prefixEnd_2650021 1360734517508481514350281 := by
  unfold tailWord_2650021
  simp only [CollatzResearch.WordTrace]
  refine ⟨96654206332433979399573917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64436137554955986266382611 96654206332433979399573917)
  ·
    refine ⟨36245327374662742274840219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96654206332433979399573917 36245327374662742274840219)
    ·
      refine ⟨54367991061994113412260329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36245327374662742274840219 54367991061994113412260329)
      ·
        refine ⟨40775993296495585059195247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54367991061994113412260329 40775993296495585059195247)
        ·
          refine ⟨61163989944743377588792871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40775993296495585059195247 61163989944743377588792871)
          ·
            refine ⟨91745984917115066383189307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61163989944743377588792871 91745984917115066383189307)
            ·
              refine ⟨137618977375672599574783961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91745984917115066383189307 137618977375672599574783961)
              ·
                refine ⟨103214233031754449681087971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137618977375672599574783961 103214233031754449681087971)
                ·
                  refine ⟨154821349547631674521631957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103214233031754449681087971 154821349547631674521631957)
                  ·
                    refine ⟨3628625380022617371600749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 154821349547631674521631957 3628625380022617371600749)
                    ·
                      refine ⟨1360734517508481514350281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3628625380022617371600749 1360734517508481514350281)
                      ·
                        rfl

theorem cell23_2650021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_2650021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650021 prefixEnd_2650021 := by exact prefixLift 2650021
  have htrace : WordTrace (prefixWord ++ tailWord_2650021) baseStart_2650021 baseEnd_2650021 := by
    simpa [prefixWord, tailWord_2650021, baseEnd_2650021] using wordTrace_append hprefix tailTrace_2650021
  have hstable : (prefixWord ++ tailWord_2650021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650021).length < 2 ^ (prefixWord ++ tailWord_2650021).sum := by decide
  have hdescent : baseEnd_2650021 < baseStart_2650021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650045 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 6]
def baseStart_2650045 : Nat := 118140960795 + 2650045 * 2 ^ 59
def prefixEnd_2650045 : Nat := 4983230072969 + 3 ^ 40 * 2650045 * 2
def baseEnd_2650045 : Nat := 151194093449354380050019

theorem tailTrace_2650045 : CollatzResearch.WordTrace tailWord_2650045 prefixEnd_2650045 151194093449354380050019 := by
  unfold tailWord_2650045
  simp only [CollatzResearch.WordTrace]
  refine ⟨96655081684347031498447589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64436721122898020998965059 96655081684347031498447589)
  ·
    refine ⟨18122827815815068405958923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96655081684347031498447589 18122827815815068405958923)
    ·
      refine ⟨27184241723722602608938385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18122827815815068405958923 27184241723722602608938385)
      ·
        refine ⟨20388181292791951956703789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27184241723722602608938385 20388181292791951956703789)
        ·
          refine ⟨7645567984796981983763921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20388181292791951956703789 7645567984796981983763921)
          ·
            refine ⟨5734175988597736487822941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7645567984796981983763921 5734175988597736487822941)
            ·
              refine ⟨2150315995724151182933603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5734175988597736487822941 2150315995724151182933603)
              ·
                refine ⟨3225473993586226774400405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150315995724151182933603 3225473993586226774400405)
                ·
                  refine ⟨151194093449354380050019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3225473993586226774400405 151194093449354380050019)
                  ·
                    rfl

theorem cell23_2650045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_2650045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650045 prefixEnd_2650045 := by exact prefixLift 2650045
  have htrace : WordTrace (prefixWord ++ tailWord_2650045) baseStart_2650045 baseEnd_2650045 := by
    simpa [prefixWord, tailWord_2650045, baseEnd_2650045] using wordTrace_append hprefix tailTrace_2650045
  have hstable : (prefixWord ++ tailWord_2650045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650045).length < 2 ^ (prefixWord ++ tailWord_2650045).sum := by decide
  have hdescent : baseEnd_2650045 < baseStart_2650045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650048 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 3, 5, 2]
def baseStart_2650048 : Nat := 118140960795 + 2650048 * 2 ^ 59
def prefixEnd_2650048 : Nat := 4983230072969 + 3 ^ 40 * 2650048 * 2
def baseEnd_2650048 : Nat := 1360748381486152908712657

theorem tailTrace_2650048 : CollatzResearch.WordTrace tailWord_2650048 prefixEnd_2650048 1360748381486152908712657 := by
  unfold tailWord_2650048
  simp only [CollatzResearch.WordTrace]
  refine ⟨48327595551668081505403399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64436794068890775340537865 48327595551668081505403399)
  ·
    refine ⟨72491393327502122258105099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48327595551668081505403399 72491393327502122258105099)
    ·
      refine ⟨108737089991253183387157649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72491393327502122258105099 108737089991253183387157649)
      ·
        refine ⟨81552817493439887540368237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108737089991253183387157649 81552817493439887540368237)
        ·
          refine ⟨30582306560039957827638089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81552817493439887540368237 30582306560039957827638089)
          ·
            refine ⟨22936729920029968370728567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30582306560039957827638089 22936729920029968370728567)
            ·
              refine ⟨34405094880044952556092851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22936729920029968370728567 34405094880044952556092851)
              ·
                refine ⟨51607642320067428834139277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34405094880044952556092851 51607642320067428834139277)
                ·
                  refine ⟨19352865870025285812802229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51607642320067428834139277 19352865870025285812802229)
                  ·
                    refine ⟨1814331175314870544950209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19352865870025285812802229 1814331175314870544950209)
                    ·
                      refine ⟨1360748381486152908712657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814331175314870544950209 1360748381486152908712657)
                      ·
                        rfl

theorem cell23_2650048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 5, 2].length) (baseStart_2650048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650048 prefixEnd_2650048 := by exact prefixLift 2650048
  have htrace : WordTrace (prefixWord ++ tailWord_2650048) baseStart_2650048 baseEnd_2650048 := by
    simpa [prefixWord, tailWord_2650048, baseEnd_2650048] using wordTrace_append hprefix tailTrace_2650048
  have hstable : (prefixWord ++ tailWord_2650048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650048).length < 2 ^ (prefixWord ++ tailWord_2650048).sum := by decide
  have hdescent : baseEnd_2650048 < baseStart_2650048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650058 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 1, 5]
def baseStart_2650058 : Nat := 118140960795 + 2650058 * 2 ^ 59
def prefixEnd_2650058 : Nat := 4983230072969 + 3 ^ 40 * 2650058 * 2
def baseEnd_2650058 : Nat := 453584505430899289862537

theorem tailTrace_2650058 : CollatzResearch.WordTrace tailWord_2650058 prefixEnd_2650058 453584505430899289862537 := by
  unfold tailWord_2650058
  simp only [CollatzResearch.WordTrace]
  refine ⟨24163888958324983679667707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64437037222199956479113885 24163888958324983679667707)
  ·
    refine ⟨36245833437487475519501561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24163888958324983679667707 36245833437487475519501561)
    ·
      refine ⟨27184375078115606639626171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36245833437487475519501561 27184375078115606639626171)
      ·
        refine ⟨40776562617173409959439257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27184375078115606639626171 40776562617173409959439257)
        ·
          refine ⟨30582421962880057469579443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40776562617173409959439257 30582421962880057469579443)
          ·
            refine ⟨45873632944320086204369165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30582421962880057469579443 45873632944320086204369165)
            ·
              refine ⟨17202612354120032326638437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45873632944320086204369165 17202612354120032326638437)
              ·
                refine ⟨3225489816397506061244707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17202612354120032326638437 3225489816397506061244707)
                ·
                  refine ⟨4838234724596259091867061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225489816397506061244707 4838234724596259091867061)
                  ·
                    refine ⟨453584505430899289862537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4838234724596259091867061 453584505430899289862537)
                    ·
                      rfl

theorem cell23_2650058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_2650058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650058 prefixEnd_2650058 := by exact prefixLift 2650058
  have htrace : WordTrace (prefixWord ++ tailWord_2650058) baseStart_2650058 baseEnd_2650058 := by
    simpa [prefixWord, tailWord_2650058, baseEnd_2650058] using wordTrace_append hprefix tailTrace_2650058
  have hstable : (prefixWord ++ tailWord_2650058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650058).length < 2 ^ (prefixWord ++ tailWord_2650058).sum := by decide
  have hdescent : baseEnd_2650058 < baseStart_2650058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650066 : List Nat := [3, 2, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_2650066 : Nat := 118140960795 + 2650066 * 2 ^ 59
def prefixEnd_2650066 : Nat := 4983230072969 + 3 ^ 40 * 2650066 * 2
def baseEnd_2650066 : Nat := 453585874712644612762525

theorem tailTrace_2650066 : CollatzResearch.WordTrace tailWord_2650066 prefixEnd_2650066 453585874712644612762525 := by
  unfold tailWord_2650066
  simp only [CollatzResearch.WordTrace]
  refine ⟨24163961904317738021240513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64437231744847301389974701 24163961904317738021240513)
  ·
    refine ⟨18122971428238303515930385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24163961904317738021240513 18122971428238303515930385)
    ·
      refine ⟨13592228571178727636947789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18122971428238303515930385 13592228571178727636947789)
      ·
        refine ⟨5097085714192022863855421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13592228571178727636947789 5097085714192022863855421)
        ·
          refine ⟨1911407142822008573945783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5097085714192022863855421 1911407142822008573945783)
          ·
            refine ⟨2867110714233012860918675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911407142822008573945783 2867110714233012860918675)
            ·
              refine ⟨4300666071349519291378013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2867110714233012860918675 4300666071349519291378013)
              ·
                refine ⟨1612749776756069734266755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4300666071349519291378013 1612749776756069734266755)
                ·
                  refine ⟨2419124665134104601400133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612749776756069734266755 2419124665134104601400133)
                  ·
                    refine ⟨453585874712644612762525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2419124665134104601400133 453585874712644612762525)
                    ·
                      rfl

theorem cell23_2650066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_2650066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650066 prefixEnd_2650066 := by exact prefixLift 2650066
  have htrace : WordTrace (prefixWord ++ tailWord_2650066) baseStart_2650066 baseEnd_2650066 := by
    simpa [prefixWord, tailWord_2650066, baseEnd_2650066] using wordTrace_append hprefix tailTrace_2650066
  have hstable : (prefixWord ++ tailWord_2650066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650066).length < 2 ^ (prefixWord ++ tailWord_2650066).sum := by decide
  have hdescent : baseEnd_2650066 < baseStart_2650066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650071 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 3, 6]
def baseStart_2650071 : Nat := 118140960795 + 2650071 * 2 ^ 59
def prefixEnd_2650071 : Nat := 4983230072969 + 3 ^ 40 * 2650071 * 2
def baseEnd_2650071 : Nat := 453586730513735439575017

theorem tailTrace_2650071 : CollatzResearch.WordTrace tailWord_2650071 prefixEnd_2650071 453586730513735439575017 := by
  unfold tailWord_2650071
  simp only [CollatzResearch.WordTrace]
  refine ⟨96656029982252837938894067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64437353321501891959262711 96656029982252837938894067)
  ·
    refine ⟨144984044973379256908341101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96656029982252837938894067 144984044973379256908341101)
    ·
      refine ⟨54369016865017221340627913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144984044973379256908341101 54369016865017221340627913)
      ·
        refine ⟨40776762648762916005470935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54369016865017221340627913 40776762648762916005470935)
        ·
          refine ⟨61165143973144374008206403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40776762648762916005470935 61165143973144374008206403)
          ·
            refine ⟨91747715959716561012309605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61165143973144374008206403 91747715959716561012309605)
            ·
              refine ⟨17202696742446855189808051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91747715959716561012309605 17202696742446855189808051)
              ·
                refine ⟨25804045113670282784712077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17202696742446855189808051 25804045113670282784712077)
                ·
                  refine ⟨9676516917626356044267029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25804045113670282784712077 9676516917626356044267029)
                  ·
                    refine ⟨453586730513735439575017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9676516917626356044267029 453586730513735439575017)
                    ·
                      rfl

theorem cell23_2650071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_2650071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650071 prefixEnd_2650071 := by exact prefixLift 2650071
  have htrace : WordTrace (prefixWord ++ tailWord_2650071) baseStart_2650071 baseEnd_2650071 := by
    simpa [prefixWord, tailWord_2650071, baseEnd_2650071] using wordTrace_append hprefix tailTrace_2650071
  have hstable : (prefixWord ++ tailWord_2650071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650071).length < 2 ^ (prefixWord ++ tailWord_2650071).sum := by decide
  have hdescent : baseEnd_2650071 < baseStart_2650071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650105 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 2, 4]
def baseStart_2650105 : Nat := 118140960795 + 2650105 * 2 ^ 59
def prefixEnd_2650105 : Nat := 4983230072969 + 3 ^ 40 * 2650105 * 2
def baseEnd_2650105 : Nat := 453592549961153061899965

theorem tailTrace_2650105 : CollatzResearch.WordTrace tailWord_2650105 prefixEnd_2650105 453592549961153061899965 := by
  unfold tailWord_2650105
  simp only [CollatzResearch.WordTrace]
  refine ⟨96657270064129661745631769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64438180042753107830421179 96657270064129661745631769)
  ·
    refine ⟨72492952548097246309223827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96657270064129661745631769 72492952548097246309223827)
    ·
      refine ⟨108739428822145869463835741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72492952548097246309223827 108739428822145869463835741)
      ·
        refine ⟨40777285808304701048938403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108739428822145869463835741 40777285808304701048938403)
        ·
          refine ⟨61165928712457051573407605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40777285808304701048938403 61165928712457051573407605)
          ·
            refine ⟨5734305816792848585006963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61165928712457051573407605 5734305816792848585006963)
            ·
              refine ⟨8601458725189272877510445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5734305816792848585006963 8601458725189272877510445)
              ·
                refine ⟨3225547021945977329066417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8601458725189272877510445 3225547021945977329066417)
                ·
                  refine ⟨2419160266459482996799813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3225547021945977329066417 2419160266459482996799813)
                  ·
                    refine ⟨453592549961153061899965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2419160266459482996799813 453592549961153061899965)
                    ·
                      rfl

theorem cell23_2650105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 4].length) (baseStart_2650105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650105 prefixEnd_2650105 := by exact prefixLift 2650105
  have htrace : WordTrace (prefixWord ++ tailWord_2650105) baseStart_2650105 baseEnd_2650105 := by
    simpa [prefixWord, tailWord_2650105, baseEnd_2650105] using wordTrace_append hprefix tailTrace_2650105
  have hstable : (prefixWord ++ tailWord_2650105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650105).length < 2 ^ (prefixWord ++ tailWord_2650105).sum := by decide
  have hdescent : baseEnd_2650105 < baseStart_2650105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650108 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_2650108 : Nat := 118140960795 + 2650108 * 2 ^ 59
def prefixEnd_2650108 : Nat := 4983230072969 + 3 ^ 40 * 2650108 * 2
def baseEnd_2650108 : Nat := 1360779190325422673962381

theorem tailTrace_2650108 : CollatzResearch.WordTrace tailWord_2650108 prefixEnd_2650108 1360779190325422673962381 := by
  unfold tailWord_2650108
  simp only [CollatzResearch.WordTrace]
  refine ⟨48328689741559396628995489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64438252988745862171993985 48328689741559396628995489)
  ·
    refine ⟨36246517306169547471746617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48328689741559396628995489 36246517306169547471746617)
    ·
      refine ⟨27184887979627160603809963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36246517306169547471746617 27184887979627160603809963)
      ·
        refine ⟨40777331969440740905714945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27184887979627160603809963 40777331969440740905714945)
        ·
          refine ⟨30582998977080555679286209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40777331969440740905714945 30582998977080555679286209)
          ·
            refine ⟨22937249232810416759464657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30582998977080555679286209 22937249232810416759464657)
            ·
              refine ⟨17202936924607812569598493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22937249232810416759464657 17202936924607812569598493)
              ·
                refine ⟨6451101346727929713599435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17202936924607812569598493 6451101346727929713599435)
                ·
                  refine ⟨9676652020091894570399153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6451101346727929713599435 9676652020091894570399153)
                  ·
                    refine ⟨7257489015068920927799365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9676652020091894570399153 7257489015068920927799365)
                    ·
                      refine ⟨1360779190325422673962381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7257489015068920927799365 1360779190325422673962381)
                      ·
                        rfl

theorem cell23_2650108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_2650108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650108 prefixEnd_2650108 := by exact prefixLift 2650108
  have htrace : WordTrace (prefixWord ++ tailWord_2650108) baseStart_2650108 baseEnd_2650108 := by
    simpa [prefixWord, tailWord_2650108, baseEnd_2650108] using wordTrace_append hprefix tailTrace_2650108
  have hstable : (prefixWord ++ tailWord_2650108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650108).length < 2 ^ (prefixWord ++ tailWord_2650108).sum := by decide
  have hdescent : baseEnd_2650108 < baseStart_2650108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650128 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 3]
def baseStart_2650128 : Nat := 118140960795 + 2650128 * 2 ^ 59
def prefixEnd_2650128 : Nat := 4983230072969 + 3 ^ 40 * 2650128 * 2
def baseEnd_2650128 : Nat := 1360789459938512595712289

theorem tailTrace_2650128 : CollatzResearch.WordTrace tailWord_2650128 prefixEnd_2650128 1360789459938512595712289 := by
  unfold tailWord_2650128
  simp only [CollatzResearch.WordTrace]
  refine ⟨48329054471523168336859519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64438739295364224449146025 48329054471523168336859519)
  ·
    refine ⟨72493581707284752505289279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48329054471523168336859519 72493581707284752505289279)
    ·
      refine ⟨108740372560927128757933919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72493581707284752505289279 108740372560927128757933919)
      ·
        refine ⟨163110558841390693136900879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108740372560927128757933919 163110558841390693136900879)
        ·
          refine ⟨244665838262086039705351319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163110558841390693136900879 244665838262086039705351319)
          ·
            refine ⟨366998757393129059558026979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244665838262086039705351319 366998757393129059558026979)
            ·
              refine ⟨550498136089693589337040469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366998757393129059558026979 550498136089693589337040469)
              ·
                refine ⟨6451150032301096750043443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 550498136089693589337040469 6451150032301096750043443)
                ·
                  refine ⟨9676725048451645125065165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6451150032301096750043443 9676725048451645125065165)
                  ·
                    refine ⟨3628771893169366921899437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9676725048451645125065165 3628771893169366921899437)
                    ·
                      refine ⟨1360789459938512595712289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3628771893169366921899437 1360789459938512595712289)
                      ·
                        rfl

theorem cell23_2650128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 3].length) (baseStart_2650128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650128 prefixEnd_2650128 := by exact prefixLift 2650128
  have htrace : WordTrace (prefixWord ++ tailWord_2650128) baseStart_2650128 baseEnd_2650128 := by
    simpa [prefixWord, tailWord_2650128, baseEnd_2650128] using wordTrace_append hprefix tailTrace_2650128
  have hstable : (prefixWord ++ tailWord_2650128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650128).length < 2 ^ (prefixWord ++ tailWord_2650128).sum := by decide
  have hdescent : baseEnd_2650128 < baseStart_2650128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650152 : List Nat := [2, 1, 5, 3, 1, 2, 1, 8]
def baseStart_2650152 : Nat := 118140960795 + 2650152 * 2 ^ 59
def prefixEnd_2650152 : Nat := 4983230072969 + 3 ^ 40 * 2650152 * 2
def baseEnd_2650152 : Nat := 50400066054600759326377

theorem tailTrace_2650152 : CollatzResearch.WordTrace tailWord_2650152 prefixEnd_2650152 50400066054600759326377 := by
  unfold tailWord_2650152
  simp only [CollatzResearch.WordTrace]
  refine ⟨48329492147479694386296355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64439322863306259181728473 48329492147479694386296355)
  ·
    refine ⟨72494238221219541579444533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48329492147479694386296355 72494238221219541579444533)
    ·
      refine ⟨6796334833239332023072925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72494238221219541579444533 6796334833239332023072925)
      ·
        refine ⟨2548625562464749508652347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6796334833239332023072925 2548625562464749508652347)
        ·
          refine ⟨3822938343697124262978521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2548625562464749508652347 3822938343697124262978521)
          ·
            refine ⟨2867203757772843197233891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3822938343697124262978521 2867203757772843197233891)
            ·
              refine ⟨4300805636659264795850837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2867203757772843197233891 4300805636659264795850837)
              ·
                refine ⟨50400066054600759326377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4300805636659264795850837 50400066054600759326377)
                ·
                  rfl

theorem cell23_2650152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 8].length) (baseStart_2650152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650152 prefixEnd_2650152 := by exact prefixLift 2650152
  have htrace : WordTrace (prefixWord ++ tailWord_2650152) baseStart_2650152 baseEnd_2650152 := by
    simpa [prefixWord, tailWord_2650152, baseEnd_2650152] using wordTrace_append hprefix tailTrace_2650152
  have hstable : (prefixWord ++ tailWord_2650152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650152).length < 2 ^ (prefixWord ++ tailWord_2650152).sum := by decide
  have hdescent : baseEnd_2650152 < baseStart_2650152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650162 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_2650162 : Nat := 118140960795 + 2650162 * 2 ^ 59
def prefixEnd_2650162 : Nat := 4983230072969 + 3 ^ 40 * 2650162 * 2
def baseEnd_2650162 : Nat := 1360806918280765462687133

theorem tailTrace_2650162 : CollatzResearch.WordTrace tailWord_2650162 prefixEnd_2650162 1360806918280765462687133 := by
  unfold tailWord_2650162
  simp only [CollatzResearch.WordTrace]
  refine ⟨24164837256230790120114185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64439566016615440320304493 24164837256230790120114185)
  ·
    refine ⟨18123627942173092590085639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24164837256230790120114185 18123627942173092590085639)
    ·
      refine ⟨27185441913259638885128459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18123627942173092590085639 27185441913259638885128459)
      ·
        refine ⟨40778162869889458327692689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27185441913259638885128459 40778162869889458327692689)
        ·
          refine ⟨30583622152417093745769517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40778162869889458327692689 30583622152417093745769517)
          ·
            refine ⟨11468858307156410154663569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30583622152417093745769517 11468858307156410154663569)
            ·
              refine ⟨8601643730367307615997677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11468858307156410154663569 8601643730367307615997677)
              ·
                refine ⟨3225616398887740355999129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8601643730367307615997677 3225616398887740355999129)
                ·
                  refine ⟨2419212299165805266999347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3225616398887740355999129 2419212299165805266999347)
                  ·
                    refine ⟨3628818448748707900499021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2419212299165805266999347 3628818448748707900499021)
                    ·
                      refine ⟨1360806918280765462687133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3628818448748707900499021 1360806918280765462687133)
                      ·
                        rfl

theorem cell23_2650162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_2650162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650162 prefixEnd_2650162 := by exact prefixLift 2650162
  have htrace : WordTrace (prefixWord ++ tailWord_2650162) baseStart_2650162 baseEnd_2650162 := by
    simpa [prefixWord, tailWord_2650162, baseEnd_2650162] using wordTrace_append hprefix tailTrace_2650162
  have hstable : (prefixWord ++ tailWord_2650162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650162).length < 2 ^ (prefixWord ++ tailWord_2650162).sum := by decide
  have hdescent : baseEnd_2650162 < baseStart_2650162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650172 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 1, 3, 2]
def baseStart_2650172 : Nat := 118140960795 + 2650172 * 2 ^ 59
def prefixEnd_2650172 : Nat := 4983230072969 + 3 ^ 40 * 2650172 * 2
def baseEnd_2650172 : Nat := 1360812053087310423562087

theorem tailTrace_2650172 : CollatzResearch.WordTrace tailWord_2650172 prefixEnd_2650172 1360812053087310423562087 := by
  unfold tailWord_2650172
  simp only [CollatzResearch.WordTrace]
  refine ⟨48329856877443466094160385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64439809169924621458880513 48329856877443466094160385)
  ·
    refine ⟨36247392658082599570620289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48329856877443466094160385 36247392658082599570620289)
    ·
      refine ⟨27185544493561949677965217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36247392658082599570620289 27185544493561949677965217)
      ·
        refine ⟨20389158370171462258473913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27185544493561949677965217 20389158370171462258473913)
        ·
          refine ⟨15291868777628596693855435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20389158370171462258473913 15291868777628596693855435)
          ·
            refine ⟨22937803166442895040783153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15291868777628596693855435 22937803166442895040783153)
            ·
              refine ⟨17203352374832171280587365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22937803166442895040783153 17203352374832171280587365)
              ·
                refine ⟨3225628570281032115110131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17203352374832171280587365 3225628570281032115110131)
                ·
                  refine ⟨4838442855421548172665197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225628570281032115110131 4838442855421548172665197)
                  ·
                    refine ⟨1814416070783080564749449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4838442855421548172665197 1814416070783080564749449)
                    ·
                      refine ⟨1360812053087310423562087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814416070783080564749449 1360812053087310423562087)
                      ·
                        rfl

theorem cell23_2650172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_2650172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650172 prefixEnd_2650172 := by exact prefixLift 2650172
  have htrace : WordTrace (prefixWord ++ tailWord_2650172) baseStart_2650172 baseEnd_2650172 := by
    simpa [prefixWord, tailWord_2650172, baseEnd_2650172] using wordTrace_append hprefix tailTrace_2650172
  have hstable : (prefixWord ++ tailWord_2650172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650172).length < 2 ^ (prefixWord ++ tailWord_2650172).sum := by decide
  have hdescent : baseEnd_2650172 < baseStart_2650172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650185 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 1, 4, 2]
def baseStart_2650185 : Nat := 118140960795 + 2650185 * 2 ^ 59
def prefixEnd_2650185 : Nat := 4983230072969 + 3 ^ 40 * 2650185 * 2
def baseEnd_2650185 : Nat := 1360818728335818872699527

theorem tailTrace_2650185 : CollatzResearch.WordTrace tailWord_2650185 prefixEnd_2650185 1360818728335818872699527 := by
  unfold tailWord_2650185
  simp only [CollatzResearch.WordTrace]
  refine ⟨96660187903839835408544009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64440125269226556939029339 96660187903839835408544009)
  ·
    refine ⟨72495140927879876556408007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96660187903839835408544009 72495140927879876556408007)
    ·
      refine ⟨108742711391819814834612011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72495140927879876556408007 108742711391819814834612011)
      ·
        refine ⟨163114067087729722251918017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108742711391819814834612011 163114067087729722251918017)
        ·
          refine ⟨122335550315797291688938513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163114067087729722251918017 122335550315797291688938513)
          ·
            refine ⟨91751662736847968766703885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122335550315797291688938513 91751662736847968766703885)
            ·
              refine ⟨34406873526317988287513957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91751662736847968766703885 34406873526317988287513957)
              ·
                refine ⟨6451288786184622803908867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34406873526317988287513957 6451288786184622803908867)
                ·
                  refine ⟨9676933179276934205863301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6451288786184622803908867 9676933179276934205863301)
                  ·
                    refine ⟨1814424971114425163599369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9676933179276934205863301 1814424971114425163599369)
                    ·
                      refine ⟨1360818728335818872699527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814424971114425163599369 1360818728335818872699527)
                      ·
                        rfl

theorem cell23_2650185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 4, 2].length) (baseStart_2650185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650185 prefixEnd_2650185 := by exact prefixLift 2650185
  have htrace : WordTrace (prefixWord ++ tailWord_2650185) baseStart_2650185 baseEnd_2650185 := by
    simpa [prefixWord, tailWord_2650185, baseEnd_2650185] using wordTrace_append hprefix tailTrace_2650185
  have hstable : (prefixWord ++ tailWord_2650185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650185).length < 2 ^ (prefixWord ++ tailWord_2650185).sum := by decide
  have hdescent : baseEnd_2650185 < baseStart_2650185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650188 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2650188 : Nat := 118140960795 + 2650188 * 2 ^ 59
def prefixEnd_2650188 : Nat := 4983230072969 + 3 ^ 40 * 2650188 * 2
def baseEnd_2650188 : Nat := 1360820268777782360962013

theorem tailTrace_2650188 : CollatzResearch.WordTrace tailWord_2650188 prefixEnd_2650188 1360820268777782360962013 := by
  unfold tailWord_2650188
  simp only [CollatzResearch.WordTrace]
  refine ⟨48330148661414483460451609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64440198215219311280602145 48330148661414483460451609)
  ·
    refine ⟨36247611496060862595338707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48330148661414483460451609 36247611496060862595338707)
    ·
      refine ⟨54371417244091293893008061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36247611496060862595338707 54371417244091293893008061)
      ·
        refine ⟨20389281466534235209878023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54371417244091293893008061 20389281466534235209878023)
        ·
          refine ⟨30583922199801352814817035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20389281466534235209878023 30583922199801352814817035)
          ·
            refine ⟨45875883299702029222225553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30583922199801352814817035 45875883299702029222225553)
            ·
              refine ⟨34406912474776521916669165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45875883299702029222225553 34406912474776521916669165)
              ·
                refine ⟨12902592178041195718750937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34406912474776521916669165 12902592178041195718750937)
                ·
                  refine ⟨9676944133530896789063203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12902592178041195718750937 9676944133530896789063203)
                  ·
                    refine ⟨14515416200296345183594805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9676944133530896789063203 14515416200296345183594805)
                    ·
                      refine ⟨1360820268777782360962013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14515416200296345183594805 1360820268777782360962013)
                      ·
                        rfl

theorem cell23_2650188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2650188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650188 prefixEnd_2650188 := by exact prefixLift 2650188
  have htrace : WordTrace (prefixWord ++ tailWord_2650188) baseStart_2650188 baseEnd_2650188 := by
    simpa [prefixWord, tailWord_2650188, baseEnd_2650188] using wordTrace_append hprefix tailTrace_2650188
  have hstable : (prefixWord ++ tailWord_2650188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650188).length < 2 ^ (prefixWord ++ tailWord_2650188).sum := by decide
  have hdescent : baseEnd_2650188 < baseStart_2650188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650189 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_2650189 : Nat := 118140960795 + 2650189 * 2 ^ 59
def prefixEnd_2650189 : Nat := 4983230072969 + 3 ^ 40 * 2650189 * 2
def baseEnd_2650189 : Nat := 1360820782258436857049509

theorem tailTrace_2650189 : CollatzResearch.WordTrace tailWord_2650189 prefixEnd_2650189 1360820782258436857049509 := by
  unfold tailWord_2650189
  simp only [CollatzResearch.WordTrace]
  refine ⟨96660333795825344091689621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64440222530550229394459747 96660333795825344091689621)
  ·
    refine ⟨4530953146679313004297951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96660333795825344091689621 4530953146679313004297951)
    ·
      refine ⟨6796429720018969506446927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4530953146679313004297951 6796429720018969506446927)
      ·
        refine ⟨10194644580028454259670391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6796429720018969506446927 10194644580028454259670391)
        ·
          refine ⟨15291966870042681389505587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10194644580028454259670391 15291966870042681389505587)
          ·
            refine ⟨22937950305064022084258381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15291966870042681389505587 22937950305064022084258381)
            ·
              refine ⟨8601731364399008281596893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22937950305064022084258381 8601731364399008281596893)
              ·
                refine ⟨3225649261649628105598835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8601731364399008281596893 3225649261649628105598835)
                ·
                  refine ⟨4838473892474442158398253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225649261649628105598835 4838473892474442158398253)
                  ·
                    refine ⟨1814427709677915809399345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4838473892474442158398253 1814427709677915809399345)
                    ·
                      refine ⟨1360820782258436857049509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814427709677915809399345 1360820782258436857049509)
                      ·
                        rfl

theorem cell23_2650189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_2650189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650189 prefixEnd_2650189 := by exact prefixLift 2650189
  have htrace : WordTrace (prefixWord ++ tailWord_2650189) baseStart_2650189 baseEnd_2650189 := by
    simpa [prefixWord, tailWord_2650189, baseEnd_2650189] using wordTrace_append hprefix tailTrace_2650189
  have hstable : (prefixWord ++ tailWord_2650189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650189).length < 2 ^ (prefixWord ++ tailWord_2650189).sum := by decide
  have hdescent : baseEnd_2650189 < baseStart_2650189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650202 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2]
def baseStart_2650202 : Nat := 118140960795 + 2650202 * 2 ^ 59
def prefixEnd_2650202 : Nat := 4983230072969 + 3 ^ 40 * 2650202 * 2
def baseEnd_2650202 : Nat := 1360827457506945306186949

theorem tailTrace_2650202 : CollatzResearch.WordTrace tailWord_2650202 prefixEnd_2650202 1360827457506945306186949 := by
  unfold tailWord_2650202
  simp only [CollatzResearch.WordTrace]
  refine ⟨24165201986194561827978215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64440538629852164874608573 24165201986194561827978215)
  ·
    refine ⟨36247802979291842741967323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24165201986194561827978215 36247802979291842741967323)
    ·
      refine ⟨54371704468937764112950985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36247802979291842741967323 54371704468937764112950985)
      ·
        refine ⟨40778778351703323084713239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54371704468937764112950985 40778778351703323084713239)
        ·
          refine ⟨61168167527554984627069859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40778778351703323084713239 61168167527554984627069859)
          ·
            refine ⟨91752251291332476940604789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61168167527554984627069859 91752251291332476940604789)
            ·
              refine ⟨8601773558562419713181699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91752251291332476940604789 8601773558562419713181699)
              ·
                refine ⟨12902660337843629569772549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8601773558562419713181699 12902660337843629569772549)
                ·
                  refine ⟨2419248813345680544332353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12902660337843629569772549 2419248813345680544332353)
                  ·
                    refine ⟨1814436610009260408249265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2419248813345680544332353 1814436610009260408249265)
                    ·
                      refine ⟨1360827457506945306186949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814436610009260408249265 1360827457506945306186949)
                      ·
                        rfl

theorem cell23_2650202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_2650202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650202 prefixEnd_2650202 := by exact prefixLift 2650202
  have htrace : WordTrace (prefixWord ++ tailWord_2650202) baseStart_2650202 baseEnd_2650202 := by
    simpa [prefixWord, tailWord_2650202, baseEnd_2650202] using wordTrace_append hprefix tailTrace_2650202
  have hstable : (prefixWord ++ tailWord_2650202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650202).length < 2 ^ (prefixWord ++ tailWord_2650202).sum := by decide
  have hdescent : baseEnd_2650202 < baseStart_2650202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650208 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 7]
def baseStart_2650208 : Nat := 118140960795 + 2650208 * 2 ^ 59
def prefixEnd_2650208 : Nat := 4983230072969 + 3 ^ 40 * 2650208 * 2
def baseEnd_2650208 : Nat := 151203393154541364745769

theorem tailTrace_2650208 : CollatzResearch.WordTrace tailWord_2650208 prefixEnd_2650208 151203393154541364745769 := by
  unfold tailWord_2650208
  simp only [CollatzResearch.WordTrace]
  refine ⟨48330513391378255168315639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64440684521837673557754185 48330513391378255168315639)
  ·
    refine ⟨72495770087067382752473459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48330513391378255168315639 72495770087067382752473459)
    ·
      refine ⟨108743655130601074128710189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72495770087067382752473459 108743655130601074128710189)
      ·
        refine ⟨40778870673975402798266321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108743655130601074128710189 40778870673975402798266321)
        ·
          refine ⟨30584153005481552098699741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40778870673975402798266321 30584153005481552098699741)
          ·
            refine ⟨11469057377055582037012403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30584153005481552098699741 11469057377055582037012403)
            ·
              refine ⟨17203586065583373055518605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11469057377055582037012403 17203586065583373055518605)
              ·
                refine ⟨6451344774593764895819477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17203586065583373055518605 6451344774593764895819477)
                ·
                  refine ⟨151203393154541364745769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6451344774593764895819477 151203393154541364745769)
                  ·
                    rfl

theorem cell23_2650208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 7].length) (baseStart_2650208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650208 prefixEnd_2650208 := by exact prefixLift 2650208
  have htrace : WordTrace (prefixWord ++ tailWord_2650208) baseStart_2650208 baseEnd_2650208 := by
    simpa [prefixWord, tailWord_2650208, baseEnd_2650208] using wordTrace_append hprefix tailTrace_2650208
  have hstable : (prefixWord ++ tailWord_2650208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650208).length < 2 ^ (prefixWord ++ tailWord_2650208).sum := by decide
  have hdescent : baseEnd_2650208 < baseStart_2650208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650270 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_2650270 : Nat := 118140960795 + 2650270 * 2 ^ 59
def prefixEnd_2650270 : Nat := 4983230072969 + 3 ^ 40 * 2650270 * 2
def baseEnd_2650270 : Nat := 1360862374191451040136637

theorem tailTrace_2650270 : CollatzResearch.WordTrace tailWord_2650270 prefixEnd_2650270 1360862374191451040136637 := by
  unfold tailWord_2650270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12082911013566486865673533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64442192072354596616925509 12082911013566486865673533)
  ·
    refine ⟨4531091630087432574627575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12082911013566486865673533 4531091630087432574627575)
    ·
      refine ⟨6796637445131148861941363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4531091630087432574627575 6796637445131148861941363)
      ·
        refine ⟨10194956167696723292912045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6796637445131148861941363 10194956167696723292912045)
        ·
          refine ⟨3823108562886271234842017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10194956167696723292912045 3823108562886271234842017)
          ·
            refine ⟨2867331422164703426131513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3823108562886271234842017 2867331422164703426131513)
            ·
              refine ⟨2150498566623527569598635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2867331422164703426131513 2150498566623527569598635)
              ·
                refine ⟨3225747849935291354397953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150498566623527569598635 3225747849935291354397953)
                ·
                  refine ⟨2419310887451468515798465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3225747849935291354397953 2419310887451468515798465)
                  ·
                    refine ⟨1814483165588601386848849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2419310887451468515798465 1814483165588601386848849)
                    ·
                      refine ⟨1360862374191451040136637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814483165588601386848849 1360862374191451040136637)
                      ·
                        rfl

theorem cell23_2650270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_2650270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650270 prefixEnd_2650270 := by exact prefixLift 2650270
  have htrace : WordTrace (prefixWord ++ tailWord_2650270) baseStart_2650270 baseEnd_2650270 := by
    simpa [prefixWord, tailWord_2650270, baseEnd_2650270] using wordTrace_append hprefix tailTrace_2650270
  have hstable : (prefixWord ++ tailWord_2650270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650270).length < 2 ^ (prefixWord ++ tailWord_2650270).sum := by decide
  have hdescent : baseEnd_2650270 < baseStart_2650270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650298 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 10]
def baseStart_2650298 : Nat := 118140960795 + 2650298 * 2 ^ 59
def prefixEnd_2650298 : Nat := 4983230072969 + 3 ^ 40 * 2650298 * 2
def baseEnd_2650298 : Nat := 151208527961086325620723

theorem tailTrace_2650298 : CollatzResearch.WordTrace tailWord_2650298 prefixEnd_2650298 151208527961086325620723 := by
  unfold tailWord_2650298
  simp only [CollatzResearch.WordTrace]
  refine ⟨24166077338107613926851887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64442872901620303804938365 24166077338107613926851887)
  ·
    refine ⟨36249116007161420890277831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24166077338107613926851887 36249116007161420890277831)
    ·
      refine ⟨54373674010742131335416747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36249116007161420890277831 54373674010742131335416747)
      ·
        refine ⟨81560511016113197003125121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54373674010742131335416747 81560511016113197003125121)
        ·
          refine ⟨61170383262084897752343841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81560511016113197003125121 61170383262084897752343841)
          ·
            refine ⟨45877787446563673314257881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61170383262084897752343841 45877787446563673314257881)
            ·
              refine ⟨34408340584922754985693411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45877787446563673314257881 34408340584922754985693411)
              ·
                refine ⟨51612510877384132478540117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34408340584922754985693411 51612510877384132478540117)
                ·
                  refine ⟨151208527961086325620723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 51612510877384132478540117 151208527961086325620723)
                  ·
                    rfl

theorem cell23_2650298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_2650298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650298 prefixEnd_2650298 := by exact prefixLift 2650298
  have htrace : WordTrace (prefixWord ++ tailWord_2650298) baseStart_2650298 baseEnd_2650298 := by
    simpa [prefixWord, tailWord_2650298, baseEnd_2650298] using wordTrace_append hprefix tailTrace_2650298
  have hstable : (prefixWord ++ tailWord_2650298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650298).length < 2 ^ (prefixWord ++ tailWord_2650298).sum := by decide
  have hdescent : baseEnd_2650298 < baseStart_2650298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650315 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 6]
def baseStart_2650315 : Nat := 118140960795 + 2650315 * 2 ^ 59
def prefixEnd_2650315 : Nat := 4983230072969 + 3 ^ 40 * 2650315 * 2
def baseEnd_2650315 : Nat := 151209497868989262674881

theorem tailTrace_2650315 : CollatzResearch.WordTrace tailWord_2650315 prefixEnd_2650315 151209497868989262674881 := by
  unfold tailWord_2650315
  simp only [CollatzResearch.WordTrace]
  refine ⟨96664929393368867610776399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64443286262245911740517599 96664929393368867610776399)
  ·
    refine ⟨144997394090053301416164599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96664929393368867610776399 144997394090053301416164599)
    ·
      refine ⟨217496091135079952124246899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144997394090053301416164599 217496091135079952124246899)
      ·
        refine ⟨326244136702619928186370349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217496091135079952124246899 326244136702619928186370349)
        ·
          refine ⟨122341551263482473069888881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326244136702619928186370349 122341551263482473069888881)
          ·
            refine ⟨91756163447611854802416661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122341551263482473069888881 91756163447611854802416661)
            ·
              refine ⟨4301070161606805693863281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91756163447611854802416661 4301070161606805693863281)
              ·
                refine ⟨3225802621205104270397461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4301070161606805693863281 3225802621205104270397461)
                ·
                  refine ⟨151209497868989262674881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3225802621205104270397461 151209497868989262674881)
                  ·
                    rfl

theorem cell23_2650315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 6].length) (baseStart_2650315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650315 prefixEnd_2650315 := by exact prefixLift 2650315
  have htrace : WordTrace (prefixWord ++ tailWord_2650315) baseStart_2650315 baseEnd_2650315 := by
    simpa [prefixWord, tailWord_2650315, baseEnd_2650315] using wordTrace_append hprefix tailTrace_2650315
  have hstable : (prefixWord ++ tailWord_2650315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650315).length < 2 ^ (prefixWord ++ tailWord_2650315).sum := by decide
  have hdescent : baseEnd_2650315 < baseStart_2650315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650326 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_2650326 : Nat := 118140960795 + 2650326 * 2 ^ 59
def prefixEnd_2650326 : Nat := 4983230072969 + 3 ^ 40 * 2650326 * 2
def baseEnd_2650326 : Nat := 1360891129108102821036379

theorem tailTrace_2650326 : CollatzResearch.WordTrace tailWord_2650326 prefixEnd_2650326 1360891129108102821036379 := by
  unfold tailWord_2650326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6041583162270563530589177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64443553730886010992951221 6041583162270563530589177)
  ·
    refine ⟨4531187371702922647941883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6041583162270563530589177 4531187371702922647941883)
    ·
      refine ⟨6796781057554383971912825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4531187371702922647941883 6796781057554383971912825)
      ·
        refine ⟨5097585793165787978934619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6796781057554383971912825 5097585793165787978934619)
        ·
          refine ⟨7646378689748681968401929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5097585793165787978934619 7646378689748681968401929)
          ·
            refine ⟨5734784017311511476301447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7646378689748681968401929 5734784017311511476301447)
            ·
              refine ⟨8602176025967267214452171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5734784017311511476301447 8602176025967267214452171)
              ·
                refine ⟨12903264038950900821678257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8602176025967267214452171 12903264038950900821678257)
                ·
                  refine ⟨9677448029213175616258693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12903264038950900821678257 9677448029213175616258693)
                  ·
                    refine ⟨1814521505477470428048505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9677448029213175616258693 1814521505477470428048505)
                    ·
                      refine ⟨1360891129108102821036379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814521505477470428048505 1360891129108102821036379)
                      ·
                        rfl

theorem cell23_2650326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_2650326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650326 prefixEnd_2650326 := by exact prefixLift 2650326
  have htrace : WordTrace (prefixWord ++ tailWord_2650326) baseStart_2650326 baseEnd_2650326 := by
    simpa [prefixWord, tailWord_2650326, baseEnd_2650326] using wordTrace_append hprefix tailTrace_2650326
  have hstable : (prefixWord ++ tailWord_2650326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650326).length < 2 ^ (prefixWord ++ tailWord_2650326).sum := by decide
  have hdescent : baseEnd_2650326 < baseStart_2650326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650362 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 1, 5]
def baseStart_2650362 : Nat := 118140960795 + 2650362 * 2 ^ 59
def prefixEnd_2650362 : Nat := 4983230072969 + 3 ^ 40 * 2650362 * 2
def baseEnd_2650362 : Nat := 453636538137221560062071

theorem tailTrace_2650362 : CollatzResearch.WordTrace tailWord_2650362 prefixEnd_2650362 453636538137221560062071 := by
  unfold tailWord_2650362
  simp only [CollatzResearch.WordTrace]
  refine ⟨24166660906049648659434335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64444429082799063091824893 24166660906049648659434335)
  ·
    refine ⟨36249991359074472989151503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24166660906049648659434335 36249991359074472989151503)
    ·
      refine ⟨54374987038611709483727255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36249991359074472989151503 54374987038611709483727255)
      ·
        refine ⟨81562480557917564225590883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54374987038611709483727255 81562480557917564225590883)
        ·
          refine ⟨122343720836876346338386325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81562480557917564225590883 122343720836876346338386325)
          ·
            refine ⟨5734861914228578734611859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122343720836876346338386325 5734861914228578734611859)
            ·
              refine ⟨8602292871342868101917789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5734861914228578734611859 8602292871342868101917789)
              ·
                refine ⟨3225859826753575538219171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8602292871342868101917789 3225859826753575538219171)
                ·
                  refine ⟨4838789740130363307328757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225859826753575538219171 4838789740130363307328757)
                  ·
                    refine ⟨453636538137221560062071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4838789740130363307328757 453636538137221560062071)
                    ·
                      rfl

theorem cell23_2650362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_2650362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650362 prefixEnd_2650362 := by exact prefixLift 2650362
  have htrace : WordTrace (prefixWord ++ tailWord_2650362) baseStart_2650362 baseEnd_2650362 := by
    simpa [prefixWord, tailWord_2650362, baseEnd_2650362] using wordTrace_append hprefix tailTrace_2650362
  have hstable : (prefixWord ++ tailWord_2650362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650362).length < 2 ^ (prefixWord ++ tailWord_2650362).sum := by decide
  have hdescent : baseEnd_2650362 < baseStart_2650362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650376 : List Nat := [2, 1, 3, 2, 3, 1, 2, 4, 1, 1, 3]
def baseStart_2650376 : Nat := 118140960795 + 2650376 * 2 ^ 59
def prefixEnd_2650376 : Nat := 4983230072969 + 3 ^ 40 * 2650376 * 2
def baseEnd_2650376 : Nat := 1360916803140827625411149

theorem tailTrace_2650376 : CollatzResearch.WordTrace tailWord_2650376 prefixEnd_2650376 1360916803140827625411149 := by
  unfold tailWord_2650376
  simp only [CollatzResearch.WordTrace]
  refine ⟨48333577123073937514373491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64444769497431916685831321 48333577123073937514373491)
  ·
    refine ⟨72500365684610906271560237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48333577123073937514373491 72500365684610906271560237)
    ·
      refine ⟨27187637131729089851835089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72500365684610906271560237 27187637131729089851835089)
      ·
        refine ⟨20390727848796817388876317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27187637131729089851835089 20390727848796817388876317)
        ·
          refine ⟨7646522943298806520828619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20390727848796817388876317 7646522943298806520828619)
          ·
            refine ⟨11469784414948209781242929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7646522943298806520828619 11469784414948209781242929)
            ·
              refine ⟨8602338311211157335932197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11469784414948209781242929 8602338311211157335932197)
              ·
                refine ⟨1612938433352092000487287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8602338311211157335932197 1612938433352092000487287)
                ·
                  refine ⟨2419407650028138000730931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612938433352092000487287 2419407650028138000730931)
                  ·
                    refine ⟨3629111475042207001096397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2419407650028138000730931 3629111475042207001096397)
                    ·
                      refine ⟨1360916803140827625411149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3629111475042207001096397 1360916803140827625411149)
                      ·
                        rfl

theorem cell23_2650376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_2650376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650376 prefixEnd_2650376 := by exact prefixLift 2650376
  have htrace : WordTrace (prefixWord ++ tailWord_2650376) baseStart_2650376 baseEnd_2650376 := by
    simpa [prefixWord, tailWord_2650376, baseEnd_2650376] using wordTrace_append hprefix tailTrace_2650376
  have hstable : (prefixWord ++ tailWord_2650376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650376).length < 2 ^ (prefixWord ++ tailWord_2650376).sum := by decide
  have hdescent : baseEnd_2650376 < baseStart_2650376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650385 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_2650385 : Nat := 118140960795 + 2650385 * 2 ^ 59
def prefixEnd_2650385 : Nat := 4983230072969 + 3 ^ 40 * 2650385 * 2
def baseEnd_2650385 : Nat := 1360921424466718090198607

theorem tailTrace_2650385 : CollatzResearch.WordTrace tailWord_2650385 prefixEnd_2650385 1360921424466718090198607 := by
  unfold tailWord_2650385
  simp only [CollatzResearch.WordTrace]
  refine ⟨96667482503115269565824609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64444988335410179710549739 96667482503115269565824609)
  ·
    refine ⟨72500611877336452174368457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96667482503115269565824609 72500611877336452174368457)
    ·
      refine ⟨54375458908002339130776343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72500611877336452174368457 54375458908002339130776343)
      ·
        refine ⟨81563188362003508696164515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54375458908002339130776343 81563188362003508696164515)
        ·
          refine ⟨122344782543005263044246773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81563188362003508696164515 122344782543005263044246773)
          ·
            refine ⟨11469823363406743410398135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122344782543005263044246773 11469823363406743410398135)
            ·
              refine ⟨17204735045110115115597203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11469823363406743410398135 17204735045110115115597203)
              ·
                refine ⟨25807102567665172673395805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17204735045110115115597203 25807102567665172673395805)
                ·
                  refine ⟨9677663462874439752523427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25807102567665172673395805 9677663462874439752523427)
                  ·
                    refine ⟨14516495194311659628785141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9677663462874439752523427 14516495194311659628785141)
                    ·
                      refine ⟨1360921424466718090198607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14516495194311659628785141 1360921424466718090198607)
                      ·
                        rfl

theorem cell23_2650385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_2650385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650385 prefixEnd_2650385 := by exact prefixLift 2650385
  have htrace : WordTrace (prefixWord ++ tailWord_2650385) baseStart_2650385 baseEnd_2650385 := by
    simpa [prefixWord, tailWord_2650385, baseEnd_2650385] using wordTrace_append hprefix tailTrace_2650385
  have hstable : (prefixWord ++ tailWord_2650385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650385).length < 2 ^ (prefixWord ++ tailWord_2650385).sum := by decide
  have hdescent : baseEnd_2650385 < baseStart_2650385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650399 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 4]
def baseStart_2650399 : Nat := 118140960795 + 2650399 * 2 ^ 59
def prefixEnd_2650399 : Nat := 4983230072969 + 3 ^ 40 * 2650399 * 2
def baseEnd_2650399 : Nat := 1360928613195881035423543

theorem tailTrace_2650399 : CollatzResearch.WordTrace tailWord_2650399 prefixEnd_2650399 1360928613195881035423543 := by
  unfold tailWord_2650399
  simp only [CollatzResearch.WordTrace]
  refine ⟨96667993125064549956834251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64445328750043033304556167 96667993125064549956834251)
  ·
    refine ⟨145001989687596824935251377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96667993125064549956834251 145001989687596824935251377)
    ·
      refine ⟨108751492265697618701438533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145001989687596824935251377 108751492265697618701438533)
      ·
        refine ⟨20390904799818303506519725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108751492265697618701438533 20390904799818303506519725)
        ·
          refine ⟨7646589299931863814944897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20390904799818303506519725 7646589299931863814944897)
          ·
            refine ⟨5734941974948897861208673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7646589299931863814944897 5734941974948897861208673)
            ·
              refine ⟨4301206481211673395906505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5734941974948897861208673 4301206481211673395906505)
              ·
                refine ⟨3225904860908755046929879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4301206481211673395906505 3225904860908755046929879)
                ·
                  refine ⟨4838857291363132570394819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225904860908755046929879 4838857291363132570394819)
                  ·
                    refine ⟨7258285937044698855592229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4838857291363132570394819 7258285937044698855592229)
                    ·
                      refine ⟨1360928613195881035423543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7258285937044698855592229 1360928613195881035423543)
                      ·
                        rfl

theorem cell23_2650399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_2650399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650399 prefixEnd_2650399 := by exact prefixLift 2650399
  have htrace : WordTrace (prefixWord ++ tailWord_2650399) baseStart_2650399 baseEnd_2650399 := by
    simpa [prefixWord, tailWord_2650399, baseEnd_2650399] using wordTrace_append hprefix tailTrace_2650399
  have hstable : (prefixWord ++ tailWord_2650399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650399).length < 2 ^ (prefixWord ++ tailWord_2650399).sum := by decide
  have hdescent : baseEnd_2650399 < baseStart_2650399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650410 : List Nat := [3, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_2650410 : Nat := 118140960795 + 2650410 * 2 ^ 59
def prefixEnd_2650410 : Nat := 4983230072969 + 3 ^ 40 * 2650410 * 2
def baseEnd_2650410 : Nat := 1360934261483080492385993

theorem tailTrace_2650410 : CollatzResearch.WordTrace tailWord_2650410 prefixEnd_2650410 1360934261483080492385993 := by
  unfold tailWord_2650410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24167098582006174708871171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64445596218683132556989789 24167098582006174708871171)
  ·
    refine ⟨36250647873009262063306757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24167098582006174708871171 36250647873009262063306757)
    ·
      refine ⟨6796996476189236636870017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36250647873009262063306757 6796996476189236636870017)
      ·
        refine ⟨5097747357141927477652513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6796996476189236636870017 5097747357141927477652513)
        ·
          refine ⟨3823310517856445608239385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5097747357141927477652513 3823310517856445608239385)
          ·
            refine ⟨2867482888392334206179539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3823310517856445608239385 2867482888392334206179539)
            ·
              refine ⟨4301224332588501309269309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2867482888392334206179539 4301224332588501309269309)
              ·
                refine ⟨1612959124720687990975991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4301224332588501309269309 1612959124720687990975991)
                ·
                  refine ⟨2419438687081031986463987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612959124720687990975991 2419438687081031986463987)
                  ·
                    refine ⟨3629158030621547979695981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2419438687081031986463987 3629158030621547979695981)
                    ·
                      refine ⟨1360934261483080492385993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3629158030621547979695981 1360934261483080492385993)
                      ·
                        rfl

theorem cell23_2650410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_2650410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650410 prefixEnd_2650410 := by exact prefixLift 2650410
  have htrace : WordTrace (prefixWord ++ tailWord_2650410) baseStart_2650410 baseEnd_2650410 := by
    simpa [prefixWord, tailWord_2650410, baseEnd_2650410] using wordTrace_append hprefix tailTrace_2650410
  have hstable : (prefixWord ++ tailWord_2650410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650410).length < 2 ^ (prefixWord ++ tailWord_2650410).sum := by decide
  have hdescent : baseEnd_2650410 < baseStart_2650410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650416 : List Nat := [2, 1, 1, 1, 2, 2, 2, 7, 1, 2, 2]
def baseStart_2650416 : Nat := 118140960795 + 2650416 * 2 ^ 59
def prefixEnd_2650416 : Nat := 4983230072969 + 3 ^ 40 * 2650416 * 2
def baseEnd_2650416 : Nat := 1360937342367007468910965

theorem tailTrace_2650416 : CollatzResearch.WordTrace tailWord_2650416 prefixEnd_2650416 1360937342367007468910965 := by
  unfold tailWord_2650416
  simp only [CollatzResearch.WordTrace]
  refine ⟨48334306583001480930101551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64445742110668641240135401 48334306583001480930101551)
  ·
    refine ⟨72501459874502221395152327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48334306583001480930101551 72501459874502221395152327)
    ·
      refine ⟨108752189811753332092728491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72501459874502221395152327 108752189811753332092728491)
      ·
        refine ⟨163128284717629998139092737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108752189811753332092728491 163128284717629998139092737)
        ·
          refine ⟨122346213538222498604319553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163128284717629998139092737 122346213538222498604319553)
          ·
            refine ⟨91759660153666873953239665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122346213538222498604319553 91759660153666873953239665)
            ·
              refine ⟨68819745115250155464929749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91759660153666873953239665 68819745115250155464929749)
              ·
                refine ⟨1612962776138675518709291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68819745115250155464929749 1612962776138675518709291)
                ·
                  refine ⟨2419444164208013278063937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612962776138675518709291 2419444164208013278063937)
                  ·
                    refine ⟨1814583123156009958547953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2419444164208013278063937 1814583123156009958547953)
                    ·
                      refine ⟨1360937342367007468910965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814583123156009958547953 1360937342367007468910965)
                      ·
                        rfl

theorem cell23_2650416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 1, 2, 2].length) (baseStart_2650416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650416 prefixEnd_2650416 := by exact prefixLift 2650416
  have htrace : WordTrace (prefixWord ++ tailWord_2650416) baseStart_2650416 baseEnd_2650416 := by
    simpa [prefixWord, tailWord_2650416, baseEnd_2650416] using wordTrace_append hprefix tailTrace_2650416
  have hstable : (prefixWord ++ tailWord_2650416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650416).length < 2 ^ (prefixWord ++ tailWord_2650416).sum := by decide
  have hdescent : baseEnd_2650416 < baseStart_2650416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650442 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2]
def baseStart_2650442 : Nat := 118140960795 + 2650442 * 2 ^ 59
def prefixEnd_2650442 : Nat := 4983230072969 + 3 ^ 40 * 2650442 * 2
def baseEnd_2650442 : Nat := 1360950692864024367185845

theorem tailTrace_2650442 : CollatzResearch.WordTrace tailWord_2650442 prefixEnd_2650442 1360950692864024367185845 := by
  unfold tailWord_2650442
  simp only [CollatzResearch.WordTrace]
  refine ⟨24167390365977192075162395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64446374309272512200433053 24167390365977192075162395)
  ·
    refine ⟨36251085548965788112743593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24167390365977192075162395 36251085548965788112743593)
    ·
      refine ⟨27188314161724341084557695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36251085548965788112743593 27188314161724341084557695)
      ·
        refine ⟨40782471242586511626836543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27188314161724341084557695 40782471242586511626836543)
        ·
          refine ⟨61173706863879767440254815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40782471242586511626836543 61173706863879767440254815)
          ·
            refine ⟨91760560295819651160382223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61173706863879767440254815 91760560295819651160382223)
            ·
              refine ⟨137640840443729476740573335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91760560295819651160382223 137640840443729476740573335)
              ·
                refine ⟨206461260665594215110860003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137640840443729476740573335 206461260665594215110860003)
                ·
                  refine ⟨309691890998391322666290005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206461260665594215110860003 309691890998391322666290005)
                  ·
                    refine ⟨1814600923818699156247793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 309691890998391322666290005 1814600923818699156247793)
                    ·
                      refine ⟨1360950692864024367185845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814600923818699156247793 1360950692864024367185845)
                      ·
                        rfl

theorem cell23_2650442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_2650442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650442 prefixEnd_2650442 := by exact prefixLift 2650442
  have htrace : WordTrace (prefixWord ++ tailWord_2650442) baseStart_2650442 baseEnd_2650442 := by
    simpa [prefixWord, tailWord_2650442, baseEnd_2650442] using wordTrace_append hprefix tailTrace_2650442
  have hstable : (prefixWord ++ tailWord_2650442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650442).length < 2 ^ (prefixWord ++ tailWord_2650442).sum := by decide
  have hdescent : baseEnd_2650442 < baseStart_2650442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650453 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 1, 2, 3]
def baseStart_2650453 : Nat := 118140960795 + 2650453 * 2 ^ 59
def prefixEnd_2650453 : Nat := 4983230072969 + 3 ^ 40 * 2650453 * 2
def baseEnd_2650453 : Nat := 1360956341151223824148295

theorem tailTrace_2650453 : CollatzResearch.WordTrace tailWord_2650453 prefixEnd_2650453 1360956341151223824148295 := by
  unfold tailWord_2650453
  simp only [CollatzResearch.WordTrace]
  refine ⟨96669962666868917179300013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64446641777912611452866675 96669962666868917179300013)
  ·
    refine ⟨36251236000075843942237505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96669962666868917179300013 36251236000075843942237505)
    ·
      refine ⟨27188427000056882956678129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36251236000075843942237505 27188427000056882956678129)
      ·
        refine ⟨20391320250042662217508597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27188427000056882956678129 20391320250042662217508597)
        ·
          refine ⟨1911686273441499582891431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20391320250042662217508597 1911686273441499582891431)
          ·
            refine ⟨2867529410162249374337147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911686273441499582891431 2867529410162249374337147)
            ·
              refine ⟨4301294115243374061505721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2867529410162249374337147 4301294115243374061505721)
              ·
                refine ⟨3225970586432530546129291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4301294115243374061505721 3225970586432530546129291)
                ·
                  refine ⟨4838955879648795819193937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225970586432530546129291 4838955879648795819193937)
                  ·
                    refine ⟨3629216909736596864395453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4838955879648795819193937 3629216909736596864395453)
                    ·
                      refine ⟨1360956341151223824148295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3629216909736596864395453 1360956341151223824148295)
                      ·
                        rfl

theorem cell23_2650453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_2650453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650453 prefixEnd_2650453 := by exact prefixLift 2650453
  have htrace : WordTrace (prefixWord ++ tailWord_2650453) baseStart_2650453 baseEnd_2650453 := by
    simpa [prefixWord, tailWord_2650453, baseEnd_2650453] using wordTrace_append hprefix tailTrace_2650453
  have hstable : (prefixWord ++ tailWord_2650453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650453).length < 2 ^ (prefixWord ++ tailWord_2650453).sum := by decide
  have hdescent : baseEnd_2650453 < baseStart_2650453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650465 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 6, 6]
def baseStart_2650465 : Nat := 118140960795 + 2650465 * 2 ^ 59
def prefixEnd_2650465 : Nat := 4983230072969 + 3 ^ 40 * 2650465 * 2
def baseEnd_2650465 : Nat := 453654167639692592399413

theorem tailTrace_2650465 : CollatzResearch.WordTrace tailWord_2650465 prefixEnd_2650465 453654167639692592399413 := by
  unfold tailWord_2650465
  simp only [CollatzResearch.WordTrace]
  refine ⟨96670400342825443228736849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64446933561883628819157899 96670400342825443228736849)
  ·
    refine ⟨72502800257119082421552637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96670400342825443228736849 72502800257119082421552637)
    ·
      refine ⟨27188550096419655908082239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72502800257119082421552637 27188550096419655908082239)
      ·
        refine ⟨40782825144629483862123359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27188550096419655908082239 40782825144629483862123359)
        ·
          refine ⟨61174237716944225793185039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40782825144629483862123359 61174237716944225793185039)
          ·
            refine ⟨91761356575416338689777559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61174237716944225793185039 91761356575416338689777559)
            ·
              refine ⟨137642034863124508034666339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91761356575416338689777559 137642034863124508034666339)
              ·
                refine ⟨206463052294686762051999509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137642034863124508034666339 206463052294686762051999509)
                ·
                  refine ⟨9677955576313441971187477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 206463052294686762051999509 9677955576313441971187477)
                  ·
                    refine ⟨453654167639692592399413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9677955576313441971187477 453654167639692592399413)
                    ·
                      rfl

theorem cell23_2650465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_2650465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650465 prefixEnd_2650465 := by exact prefixLift 2650465
  have htrace : WordTrace (prefixWord ++ tailWord_2650465) baseStart_2650465 baseEnd_2650465 := by
    simpa [prefixWord, tailWord_2650465, baseEnd_2650465] using wordTrace_append hprefix tailTrace_2650465
  have hstable : (prefixWord ++ tailWord_2650465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650465).length < 2 ^ (prefixWord ++ tailWord_2650465).sum := by decide
  have hdescent : baseEnd_2650465 < baseStart_2650465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650606 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_2650606 : Nat := 118140960795 + 2650606 * 2 ^ 59
def prefixEnd_2650606 : Nat := 4983230072969 + 3 ^ 40 * 2650606 * 2
def baseEnd_2650606 : Nat := 453678301230453908511697

theorem tailTrace_2650606 : CollatzResearch.WordTrace tailWord_2650606 prefixEnd_2650606 453678301230453908511697 := by
  unfold tailWord_2650606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12084442879414328038702459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64450362023543082873079781 12084442879414328038702459)
  ·
    refine ⟨18126664319121492058053689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12084442879414328038702459 18126664319121492058053689)
    ·
      refine ⟨13594998239341119043540267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18126664319121492058053689 13594998239341119043540267)
      ·
        refine ⟨20392497359011678565310401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13594998239341119043540267 20392497359011678565310401)
        ·
          refine ⟨15294373019258758923982801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20392497359011678565310401 15294373019258758923982801)
          ·
            refine ⟨11470779764444069192987101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15294373019258758923982801 11470779764444069192987101)
            ·
              refine ⟨4301542411666525947370163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11470779764444069192987101 4301542411666525947370163)
              ·
                refine ⟨6452313617499788921055245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4301542411666525947370163 6452313617499788921055245)
                ·
                  refine ⟨2419617606562420845395717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6452313617499788921055245 2419617606562420845395717)
                  ·
                    refine ⟨453678301230453908511697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2419617606562420845395717 453678301230453908511697)
                    ·
                      rfl

theorem cell23_2650606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_2650606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650606 prefixEnd_2650606 := by exact prefixLift 2650606
  have htrace : WordTrace (prefixWord ++ tailWord_2650606) baseStart_2650606 baseEnd_2650606 := by
    simpa [prefixWord, tailWord_2650606, baseEnd_2650606] using wordTrace_append hprefix tailTrace_2650606
  have hstable : (prefixWord ++ tailWord_2650606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650606).length < 2 ^ (prefixWord ++ tailWord_2650606).sum := by decide
  have hdescent : baseEnd_2650606 < baseStart_2650606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650630 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2650630 : Nat := 118140960795 + 2650630 * 2 ^ 59
def prefixEnd_2650630 : Nat := 4983230072969 + 3 ^ 40 * 2650630 * 2
def baseEnd_2650630 : Nat := 1361047227227069631634981

theorem tailTrace_2650630 : CollatzResearch.WordTrace tailWord_2650630 prefixEnd_2650630 1361047227227069631634981 := by
  unfold tailWord_2650630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3021138074600864887765417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64450945591485117605662229 3021138074600864887765417)
  ·
    refine ⟨2265853555950648665824063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3021138074600864887765417 2265853555950648665824063)
    ·
      refine ⟨3398780333925972998736095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2265853555950648665824063 3398780333925972998736095)
      ·
        refine ⟨5098170500888959498104143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3398780333925972998736095 5098170500888959498104143)
        ·
          refine ⟨7647255751333439247156215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5098170500888959498104143 7647255751333439247156215)
          ·
            refine ⟨11470883627000158870734323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7647255751333439247156215 11470883627000158870734323)
            ·
              refine ⟨17206325440500238306101485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11470883627000158870734323 17206325440500238306101485)
              ·
                refine ⟨6452372040187589364788057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17206325440500238306101485 6452372040187589364788057)
                ·
                  refine ⟨4839279030140692023591043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6452372040187589364788057 4839279030140692023591043)
                  ·
                    refine ⟨7258918545211038035386565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4839279030140692023591043 7258918545211038035386565)
                    ·
                      refine ⟨1361047227227069631634981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7258918545211038035386565 1361047227227069631634981)
                      ·
                        rfl

theorem cell23_2650630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2650630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650630 prefixEnd_2650630 := by exact prefixLift 2650630
  have htrace : WordTrace (prefixWord ++ tailWord_2650630) baseStart_2650630 baseEnd_2650630 := by
    simpa [prefixWord, tailWord_2650630, baseEnd_2650630] using wordTrace_append hprefix tailTrace_2650630
  have hstable : (prefixWord ++ tailWord_2650630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650630).length < 2 ^ (prefixWord ++ tailWord_2650630).sum := by decide
  have hdescent : baseEnd_2650630 < baseStart_2650630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650679 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 1, 6]
def baseStart_2650679 : Nat := 118140960795 + 2650679 * 2 ^ 59
def prefixEnd_2650679 : Nat := 4983230072969 + 3 ^ 40 * 2650679 * 2
def baseEnd_2650679 : Nat := 453690795926379979974085

theorem tailTrace_2650679 : CollatzResearch.WordTrace tailWord_2650679 prefixEnd_2650679 453690795926379979974085 := by
  unfold tailWord_2650679
  simp only [CollatzResearch.WordTrace]
  refine ⟨96678205564050157777027091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64452137042700105184684727 96678205564050157777027091)
  ·
    refine ⟨145017308346075236665540637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96678205564050157777027091 145017308346075236665540637)
    ·
      refine ⟨54381490629778213749577739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145017308346075236665540637 54381490629778213749577739)
      ·
        refine ⟨81572235944667320624366609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54381490629778213749577739 81572235944667320624366609)
        ·
          refine ⟨61179176958500490468274957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81572235944667320624366609 61179176958500490468274957)
          ·
            refine ⟨22942191359437683925603109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61179176958500490468274957 22942191359437683925603109)
            ·
              refine ⟨4301660879894565736050583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22942191359437683925603109 4301660879894565736050583)
              ·
                refine ⟨6452491319841848604075875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4301660879894565736050583 6452491319841848604075875)
                ·
                  refine ⟨9678736979762772906113813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6452491319841848604075875 9678736979762772906113813)
                  ·
                    refine ⟨453690795926379979974085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9678736979762772906113813 453690795926379979974085)
                    ·
                      rfl

theorem cell23_2650679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_2650679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650679 prefixEnd_2650679 := by exact prefixLift 2650679
  have htrace : WordTrace (prefixWord ++ tailWord_2650679) baseStart_2650679 baseEnd_2650679 := by
    simpa [prefixWord, tailWord_2650679, baseEnd_2650679] using wordTrace_append hprefix tailTrace_2650679
  have hstable : (prefixWord ++ tailWord_2650679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650679).length < 2 ^ (prefixWord ++ tailWord_2650679).sum := by decide
  have hdescent : baseEnd_2650679 < baseStart_2650679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650699 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 4]
def baseStart_2650699 : Nat := 118140960795 + 2650699 * 2 ^ 59
def prefixEnd_2650699 : Nat := 4983230072969 + 3 ^ 40 * 2650699 * 2
def baseEnd_2650699 : Nat := 1361082657392229861672163

theorem tailTrace_2650699 : CollatzResearch.WordTrace tailWord_2650699 prefixEnd_2650699 1361082657392229861672163 := by
  unfold tailWord_2650699
  simp only [CollatzResearch.WordTrace]
  refine ⟨96678935023977701192755151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64452623349318467461836767 96678935023977701192755151)
  ·
    refine ⟨145018402535966551789132727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96678935023977701192755151 145018402535966551789132727)
    ·
      refine ⟨217527603803949827683699091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145018402535966551789132727 217527603803949827683699091)
      ·
        refine ⟨326291405705924741525548637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217527603803949827683699091 326291405705924741525548637)
        ·
          refine ⟨122359277139721778072080739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326291405705924741525548637 122359277139721778072080739)
          ·
            refine ⟨183538915709582667108121109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122359277139721778072080739 183538915709582667108121109)
            ·
              refine ⟨8603386673886687520693177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 183538915709582667108121109 8603386673886687520693177)
              ·
                refine ⟨6452540005415015640519883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8603386673886687520693177 6452540005415015640519883)
                ·
                  refine ⟨9678810008122523460779825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6452540005415015640519883 9678810008122523460779825)
                  ·
                    refine ⟨7259107506091892595584869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9678810008122523460779825 7259107506091892595584869)
                    ·
                      refine ⟨1361082657392229861672163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7259107506091892595584869 1361082657392229861672163)
                      ·
                        rfl

theorem cell23_2650699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 4].length) (baseStart_2650699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650699 prefixEnd_2650699 := by exact prefixLift 2650699
  have htrace : WordTrace (prefixWord ++ tailWord_2650699) baseStart_2650699 baseEnd_2650699 := by
    simpa [prefixWord, tailWord_2650699, baseEnd_2650699] using wordTrace_append hprefix tailTrace_2650699
  have hstable : (prefixWord ++ tailWord_2650699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650699).length < 2 ^ (prefixWord ++ tailWord_2650699).sum := by decide
  have hdescent : baseEnd_2650699 < baseStart_2650699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650719 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 3]
def baseStart_2650719 : Nat := 118140960795 + 2650719 * 2 ^ 59
def prefixEnd_2650719 : Nat := 4983230072969 + 3 ^ 40 * 2650719 * 2
def baseEnd_2650719 : Nat := 1361092927005319783422071

theorem tailTrace_2650719 : CollatzResearch.WordTrace tailWord_2650719 prefixEnd_2650719 1361092927005319783422071 := by
  unfold tailWord_2650719
  simp only [CollatzResearch.WordTrace]
  refine ⟨96679664483905244608483211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64453109655936829738988807 96679664483905244608483211)
  ·
    refine ⟨145019496725857866912724817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96679664483905244608483211 145019496725857866912724817)
    ·
      refine ⟨108764622544393400184543613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145019496725857866912724817 108764622544393400184543613)
      ·
        refine ⟨40786733454147525069203855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108764622544393400184543613 40786733454147525069203855)
        ·
          refine ⟨61180100181221287603805783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40786733454147525069203855 61180100181221287603805783)
          ·
            refine ⟨91770150271831931405708675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61180100181221287603805783 91770150271831931405708675)
            ·
              refine ⟨137655225407747897108563013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91770150271831931405708675 137655225407747897108563013)
              ·
                refine ⟨25810354763952730707855565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137655225407747897108563013 25810354763952730707855565)
                ·
                  refine ⟨9678883036482274015445837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25810354763952730707855565 9678883036482274015445837)
                  ·
                    refine ⟨3629581138680852755792189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9678883036482274015445837 3629581138680852755792189)
                    ·
                      refine ⟨1361092927005319783422071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3629581138680852755792189 1361092927005319783422071)
                      ·
                        rfl

theorem cell23_2650719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_2650719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650719 prefixEnd_2650719 := by exact prefixLift 2650719
  have htrace : WordTrace (prefixWord ++ tailWord_2650719) baseStart_2650719 baseEnd_2650719 := by
    simpa [prefixWord, tailWord_2650719, baseEnd_2650719] using wordTrace_append hprefix tailTrace_2650719
  have hstable : (prefixWord ++ tailWord_2650719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650719).length < 2 ^ (prefixWord ++ tailWord_2650719).sum := by decide
  have hdescent : baseEnd_2650719 < baseStart_2650719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650720 : List Nat := [2, 1, 1, 3, 2, 1, 4, 4, 1, 2, 2]
def baseStart_2650720 : Nat := 118140960795 + 2650720 * 2 ^ 59
def prefixEnd_2650720 : Nat := 4983230072969 + 3 ^ 40 * 2650720 * 2
def baseEnd_2650720 : Nat := 1361093440485974279509567

theorem tailTrace_2650720 : CollatzResearch.WordTrace tailWord_2650720 prefixEnd_2650720 1361093440485974279509567 := by
  unfold tailWord_2650720
  simp only [CollatzResearch.WordTrace]
  refine ⟨48339850478450810889634807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64453133971267747852846409 48339850478450810889634807)
  ·
    refine ⟨72509775717676216334452211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48339850478450810889634807 72509775717676216334452211)
    ·
      refine ⟨108764663576514324501678317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72509775717676216334452211 108764663576514324501678317)
      ·
        refine ⟨40786748841192871688129369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108764663576514324501678317 40786748841192871688129369)
        ·
          refine ⟨30590061630894653766097027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40786748841192871688129369 30590061630894653766097027)
          ·
            refine ⟨45885092446341980649145541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30590061630894653766097027 45885092446341980649145541)
            ·
              refine ⟨8603454833689121371714789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45885092446341980649145541 8603454833689121371714789)
              ·
                refine ⟨1613147781316710257196523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8603454833689121371714789 1613147781316710257196523)
                ·
                  refine ⟨2419721671975065385794785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613147781316710257196523 2419721671975065385794785)
                  ·
                    refine ⟨1814791253981299039346089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2419721671975065385794785 1814791253981299039346089)
                    ·
                      refine ⟨1361093440485974279509567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814791253981299039346089 1361093440485974279509567)
                      ·
                        rfl

theorem cell23_2650720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_2650720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650720 prefixEnd_2650720 := by exact prefixLift 2650720
  have htrace : WordTrace (prefixWord ++ tailWord_2650720) baseStart_2650720 baseEnd_2650720 := by
    simpa [prefixWord, tailWord_2650720, baseEnd_2650720] using wordTrace_append hprefix tailTrace_2650720
  have hstable : (prefixWord ++ tailWord_2650720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650720).length < 2 ^ (prefixWord ++ tailWord_2650720).sum := by decide
  have hdescent : baseEnd_2650720 < baseStart_2650720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650733 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_2650733 : Nat := 118140960795 + 2650733 * 2 ^ 59
def prefixEnd_2650733 : Nat := 4983230072969 + 3 ^ 40 * 2650733 * 2
def baseEnd_2650733 : Nat := 1361100115734482728647007

theorem tailTrace_2650733 : CollatzResearch.WordTrace tailWord_2650733 prefixEnd_2650733 1361100115734482728647007 := by
  unfold tailWord_2650733
  simp only [CollatzResearch.WordTrace]
  refine ⟨96680175105854524999492853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64453450070569683332995235 96680175105854524999492853)
  ·
    refine ⟨9063766416173861718702455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96680175105854524999492853 9063766416173861718702455)
    ·
      refine ⟨13595649624260792578053683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9063766416173861718702455 13595649624260792578053683)
      ·
        refine ⟨20393474436391188867080525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13595649624260792578053683 20393474436391188867080525)
        ·
          refine ⟨7647552913646695825155197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20393474436391188867080525 7647552913646695825155197)
          ·
            refine ⟨2867832342617510934433199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7647552913646695825155197 2867832342617510934433199)
            ·
              refine ⟨4301748513926266401649799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2867832342617510934433199 4301748513926266401649799)
              ·
                refine ⟨6452622770889399602474699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4301748513926266401649799 6452622770889399602474699)
                ·
                  refine ⟨9678934156334099403712049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6452622770889399602474699 9678934156334099403712049)
                  ·
                    refine ⟨7259200617250574552784037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9678934156334099403712049 7259200617250574552784037)
                    ·
                      refine ⟨1361100115734482728647007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7259200617250574552784037 1361100115734482728647007)
                      ·
                        rfl

theorem cell23_2650733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_2650733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650733 prefixEnd_2650733 := by exact prefixLift 2650733
  have htrace : WordTrace (prefixWord ++ tailWord_2650733) baseStart_2650733 baseEnd_2650733 := by
    simpa [prefixWord, tailWord_2650733, baseEnd_2650733] using wordTrace_append hprefix tailTrace_2650733
  have hstable : (prefixWord ++ tailWord_2650733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650733).length < 2 ^ (prefixWord ++ tailWord_2650733).sum := by decide
  have hdescent : baseEnd_2650733 < baseStart_2650733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650746 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2]
def baseStart_2650746 : Nat := 118140960795 + 2650746 * 2 ^ 59
def prefixEnd_2650746 : Nat := 4983230072969 + 3 ^ 40 * 2650746 * 2
def baseEnd_2650746 : Nat := 1361106790982991177784447

theorem tailTrace_2650746 : CollatzResearch.WordTrace tailWord_2650746 prefixEnd_2650746 1361106790982991177784447 := by
  unfold tailWord_2650746
  simp only [CollatzResearch.WordTrace]
  refine ⟨24170162313701857054929023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64453766169871618813144061 24170162313701857054929023)
  ·
    refine ⟨36255243470552785582393535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24170162313701857054929023 36255243470552785582393535)
    ·
      refine ⟨54382865205829178373590303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36255243470552785582393535 54382865205829178373590303)
      ·
        refine ⟨81574297808743767560385455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54382865205829178373590303 81574297808743767560385455)
        ·
          refine ⟨122361446713115651340578183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81574297808743767560385455 122361446713115651340578183)
          ·
            refine ⟨183542170069673477010867275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122361446713115651340578183 183542170069673477010867275)
            ·
              refine ⟨275313255104510215516300913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183542170069673477010867275 275313255104510215516300913)
              ·
                refine ⟨206484941328382661637225685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275313255104510215516300913 206484941328382661637225685)
                ·
                  refine ⟨4839490812383968632122477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 206484941328382661637225685 4839490812383968632122477)
                  ·
                    refine ⟨1814809054643988237045929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4839490812383968632122477 1814809054643988237045929)
                    ·
                      refine ⟨1361106790982991177784447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814809054643988237045929 1361106790982991177784447)
                      ·
                        rfl

theorem cell23_2650746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2].length) (baseStart_2650746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650746 prefixEnd_2650746 := by exact prefixLift 2650746
  have htrace : WordTrace (prefixWord ++ tailWord_2650746) baseStart_2650746 baseEnd_2650746 := by
    simpa [prefixWord, tailWord_2650746, baseEnd_2650746] using wordTrace_append hprefix tailTrace_2650746
  have hstable : (prefixWord ++ tailWord_2650746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650746).length < 2 ^ (prefixWord ++ tailWord_2650746).sum := by decide
  have hdescent : baseEnd_2650746 < baseStart_2650746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650779 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 3]
def baseStart_2650779 : Nat := 118140960795 + 2650779 * 2 ^ 59
def prefixEnd_2650779 : Nat := 4983230072969 + 3 ^ 40 * 2650779 * 2
def baseEnd_2650779 : Nat := 1361123735844589548671795

theorem tailTrace_2650779 : CollatzResearch.WordTrace tailWord_2650779 prefixEnd_2650779 1361123735844589548671795 := by
  unfold tailWord_2650779
  simp only [CollatzResearch.WordTrace]
  refine ⟨96681852863687874855667391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64454568575791916570444927 96681852863687874855667391)
  ·
    refine ⟨145022779295531812283501087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96681852863687874855667391 145022779295531812283501087)
    ·
      refine ⟨217534168943297718425251631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145022779295531812283501087 217534168943297718425251631)
      ·
        refine ⟨326301253414946577637877447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217534168943297718425251631 326301253414946577637877447)
        ·
          refine ⟨489451880122419866456816171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326301253414946577637877447 489451880122419866456816171)
          ·
            refine ⟨734177820183629799685224257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489451880122419866456816171 734177820183629799685224257)
            ·
              refine ⟨550633365137722349763918193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734177820183629799685224257 550633365137722349763918193)
              ·
                refine ⟨412975023853291762322938645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550633365137722349763918193 412975023853291762322938645)
                ·
                  refine ⟨19358204243123051358887749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 412975023853291762322938645 19358204243123051358887749)
                  ·
                    refine ⟨3629663295585572129791453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19358204243123051358887749 3629663295585572129791453)
                    ·
                      refine ⟨1361123735844589548671795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3629663295585572129791453 1361123735844589548671795)
                      ·
                        rfl

theorem cell23_2650779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 3].length) (baseStart_2650779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650779 prefixEnd_2650779 := by exact prefixLift 2650779
  have htrace : WordTrace (prefixWord ++ tailWord_2650779) baseStart_2650779 baseEnd_2650779 := by
    simpa [prefixWord, tailWord_2650779, baseEnd_2650779] using wordTrace_append hprefix tailTrace_2650779
  have hstable : (prefixWord ++ tailWord_2650779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650779).length < 2 ^ (prefixWord ++ tailWord_2650779).sum := by decide
  have hdescent : baseEnd_2650779 < baseStart_2650779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650789 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_2650789 : Nat := 118140960795 + 2650789 * 2 ^ 59
def prefixEnd_2650789 : Nat := 4983230072969 + 3 ^ 40 * 2650789 * 2
def baseEnd_2650789 : Nat := 1361128870651134509546749

theorem tailTrace_2650789 : CollatzResearch.WordTrace tailWord_2650789 prefixEnd_2650789 1361128870651134509546749 := by
  unfold tailWord_2650789
  simp only [CollatzResearch.WordTrace]
  refine ⟨96682217593651646563531421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64454811729101097709020947 96682217593651646563531421)
  ·
    refine ⟨36255831597619367461324283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96682217593651646563531421 36255831597619367461324283)
    ·
      refine ⟨54383747396429051191986425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36255831597619367461324283 54383747396429051191986425)
      ·
        refine ⟨40787810547321788393989819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54383747396429051191986425 40787810547321788393989819)
        ·
          refine ⟨61181715820982682590984729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40787810547321788393989819 61181715820982682590984729)
          ·
            refine ⟨45886286865737011943238547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61181715820982682590984729 45886286865737011943238547)
            ·
              refine ⟨68829430298605517914857821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45886286865737011943238547 68829430298605517914857821)
              ·
                refine ⟨25811036361977069218071683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68829430298605517914857821 25811036361977069218071683)
                ·
                  refine ⟨38716554542965603827107525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25811036361977069218071683 38716554542965603827107525)
                  ·
                    refine ⟨7259353976806050717582661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38716554542965603827107525 7259353976806050717582661)
                    ·
                      refine ⟨1361128870651134509546749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7259353976806050717582661 1361128870651134509546749)
                      ·
                        rfl

theorem cell23_2650789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_2650789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650789 prefixEnd_2650789 := by exact prefixLift 2650789
  have htrace : WordTrace (prefixWord ++ tailWord_2650789) baseStart_2650789 baseEnd_2650789 := by
    simpa [prefixWord, tailWord_2650789, baseEnd_2650789] using wordTrace_append hprefix tailTrace_2650789
  have hstable : (prefixWord ++ tailWord_2650789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650789).length < 2 ^ (prefixWord ++ tailWord_2650789).sum := by decide
  have hdescent : baseEnd_2650789 < baseStart_2650789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650797 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_2650797 : Nat := 118140960795 + 2650797 * 2 ^ 59
def prefixEnd_2650797 : Nat := 4983230072969 + 3 ^ 40 * 2650797 * 2
def baseEnd_2650797 : Nat := 1361132978496370478246713

theorem tailTrace_2650797 : CollatzResearch.WordTrace tailWord_2650797 prefixEnd_2650797 1361132978496370478246713 := by
  unfold tailWord_2650797
  simp only [CollatzResearch.WordTrace]
  refine ⟨96682509377622663929822645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64455006251748442619881763 96682509377622663929822645)
  ·
    refine ⟨9063985254152124743420873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96682509377622663929822645 9063985254152124743420873)
    ·
      refine ⟨6797988940614093557565655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9063985254152124743420873 6797988940614093557565655)
      ·
        refine ⟨10196983410921140336348483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6797988940614093557565655 10196983410921140336348483)
        ·
          refine ⟨15295475116381710504522725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10196983410921140336348483 15295475116381710504522725)
          ·
            refine ⟨2867901584321570719598011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15295475116381710504522725 2867901584321570719598011)
            ·
              refine ⟨4301852376482356079397017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2867901584321570719598011 4301852376482356079397017)
              ·
                refine ⟨3226389282361767059547763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4301852376482356079397017 3226389282361767059547763)
                ·
                  refine ⟨4839583923542650589321645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3226389282361767059547763 4839583923542650589321645)
                  ·
                    refine ⟨1814843971328493970995617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4839583923542650589321645 1814843971328493970995617)
                    ·
                      refine ⟨1361132978496370478246713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814843971328493970995617 1361132978496370478246713)
                      ·
                        rfl

theorem cell23_2650797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_2650797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650797 prefixEnd_2650797 := by exact prefixLift 2650797
  have htrace : WordTrace (prefixWord ++ tailWord_2650797) baseStart_2650797 baseEnd_2650797 := by
    simpa [prefixWord, tailWord_2650797, baseEnd_2650797] using wordTrace_append hprefix tailTrace_2650797
  have hstable : (prefixWord ++ tailWord_2650797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650797).length < 2 ^ (prefixWord ++ tailWord_2650797).sum := by decide
  have hdescent : baseEnd_2650797 < baseStart_2650797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650863 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 2, 5]
def baseStart_2650863 : Nat := 118140960795 + 2650863 * 2 ^ 59
def prefixEnd_2650863 : Nat := 4983230072969 + 3 ^ 40 * 2650863 * 2
def baseEnd_2650863 : Nat := 453722289406522406673803

theorem tailTrace_2650863 : CollatzResearch.WordTrace tailWord_2650863 prefixEnd_2650863 453722289406522406673803 := by
  unfold tailWord_2650863
  simp only [CollatzResearch.WordTrace]
  refine ⟨96684916595383557201725243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64456611063589038134483495 96684916595383557201725243)
  ·
    refine ⟨145027374893075335802587865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96684916595383557201725243 145027374893075335802587865)
    ·
      refine ⟨108770531169806501851940899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145027374893075335802587865 108770531169806501851940899)
      ·
        refine ⟨163155796754709752777911349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108770531169806501851940899 163155796754709752777911349)
        ·
          refine ⟨15295855945754039322929189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163155796754709752777911349 15295855945754039322929189)
          ·
            refine ⟨2867972989828882373049223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15295855945754039322929189 2867972989828882373049223)
            ·
              refine ⟨4301959484743323559573835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2867972989828882373049223 4301959484743323559573835)
              ·
                refine ⟨6452939227114985339360753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4301959484743323559573835 6452939227114985339360753)
                ·
                  refine ⟨4839704420336239004520565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6452939227114985339360753 4839704420336239004520565)
                  ·
                    refine ⟨453722289406522406673803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4839704420336239004520565 453722289406522406673803)
                    ·
                      rfl

theorem cell23_2650863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 5].length) (baseStart_2650863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650863 prefixEnd_2650863 := by exact prefixLift 2650863
  have htrace : WordTrace (prefixWord ++ tailWord_2650863) baseStart_2650863 baseEnd_2650863 := by
    simpa [prefixWord, tailWord_2650863, baseEnd_2650863] using wordTrace_append hprefix tailTrace_2650863
  have hstable : (prefixWord ++ tailWord_2650863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650863).length < 2 ^ (prefixWord ++ tailWord_2650863).sum := by decide
  have hdescent : baseEnd_2650863 < baseStart_2650863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650970 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 1, 5]
def baseStart_2650970 : Nat := 118140960795 + 2650970 * 2 ^ 59
def prefixEnd_2650970 : Nat := 4983230072969 + 3 ^ 40 * 2650970 * 2
def baseEnd_2650970 : Nat := 453740603549866100461139

theorem tailTrace_2650970 : CollatzResearch.WordTrace tailWord_2650970 prefixEnd_2650970 453740603549866100461139 := by
  unfold tailWord_2650970
  simp only [CollatzResearch.WordTrace]
  refine ⟨24172204801498978618967591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64459212803997276317246909 24172204801498978618967591)
  ·
    refine ⟨36258307202248467928451387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24172204801498978618967591 36258307202248467928451387)
    ·
      refine ⟨54387460803372701892677081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36258307202248467928451387 54387460803372701892677081)
      ·
        refine ⟨40790595602529526419507811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54387460803372701892677081 40790595602529526419507811)
        ·
          refine ⟨61185893403794289629261717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40790595602529526419507811 61185893403794289629261717)
          ·
            refine ⟨2868088753302857326371643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61185893403794289629261717 2868088753302857326371643)
            ·
              refine ⟨4302133129954285989557465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868088753302857326371643 4302133129954285989557465)
              ·
                refine ⟨3226599847465714492168099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4302133129954285989557465 3226599847465714492168099)
                ·
                  refine ⟨4839899771198571738252149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3226599847465714492168099 4839899771198571738252149)
                  ·
                    refine ⟨453740603549866100461139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4839899771198571738252149 453740603549866100461139)
                    ·
                      rfl

theorem cell23_2650970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_2650970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650970 prefixEnd_2650970 := by exact prefixLift 2650970
  have htrace : WordTrace (prefixWord ++ tailWord_2650970) baseStart_2650970 baseEnd_2650970 := by
    simpa [prefixWord, tailWord_2650970, baseEnd_2650970] using wordTrace_append hprefix tailTrace_2650970
  have hstable : (prefixWord ++ tailWord_2650970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650970).length < 2 ^ (prefixWord ++ tailWord_2650970).sum := by decide
  have hdescent : baseEnd_2650970 < baseStart_2650970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650983 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 1, 6]
def baseStart_2650983 : Nat := 118140960795 + 2650983 * 2 ^ 59
def prefixEnd_2650983 : Nat := 4983230072969 + 3 ^ 40 * 2650983 * 2
def baseEnd_2650983 : Nat := 453742828632702250173619

theorem tailTrace_2650983 : CollatzResearch.WordTrace tailWord_2650983 prefixEnd_2650983 453742828632702250173619 := by
  unfold tailWord_2650983
  simp only [CollatzResearch.WordTrace]
  refine ⟨96689293354948817696093603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64459528903299211797395735 96689293354948817696093603)
  ·
    refine ⟨145033940032423226544140405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96689293354948817696093603 145033940032423226544140405)
    ·
      refine ⟨13596931878039677488513163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145033940032423226544140405 13596931878039677488513163)
      ·
        refine ⟨20395397817059516232769745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13596931878039677488513163 20395397817059516232769745)
        ·
          refine ⟨15296548362794637174577309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20395397817059516232769745 15296548362794637174577309)
          ·
            refine ⟨5736205636047988940466491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15296548362794637174577309 5736205636047988940466491)
            ·
              refine ⟨8604308454071983410699737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5736205636047988940466491 8604308454071983410699737)
              ·
                refine ⟨6453231340553987558024803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8604308454071983410699737 6453231340553987558024803)
                ·
                  refine ⟨9679847010830981337037205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6453231340553987558024803 9679847010830981337037205)
                  ·
                    refine ⟨453742828632702250173619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9679847010830981337037205 453742828632702250173619)
                    ·
                      rfl

theorem cell23_2650983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_2650983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650983 prefixEnd_2650983 := by exact prefixLift 2650983
  have htrace : WordTrace (prefixWord ++ tailWord_2650983) baseStart_2650983 baseEnd_2650983 := by
    simpa [prefixWord, tailWord_2650983, baseEnd_2650983] using wordTrace_append hprefix tailTrace_2650983
  have hstable : (prefixWord ++ tailWord_2650983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650983).length < 2 ^ (prefixWord ++ tailWord_2650983).sum := by decide
  have hdescent : baseEnd_2650983 < baseStart_2650983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650993 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 5]
def baseStart_2650993 : Nat := 118140960795 + 2650993 * 2 ^ 59
def prefixEnd_2650993 : Nat := 4983230072969 + 3 ^ 40 * 2650993 * 2
def baseEnd_2650993 : Nat := 1361233620704651711395811

theorem tailTrace_2650993 : CollatzResearch.WordTrace tailWord_2650993 prefixEnd_2650993 1361233620704651711395811 := by
  unfold tailWord_2650993
  simp only [CollatzResearch.WordTrace]
  refine ⟨96689658084912589403957633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64459772056608392935971755 96689658084912589403957633)
  ·
    refine ⟨72517243563684442052968225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96689658084912589403957633 72517243563684442052968225)
    ·
      refine ⟨54387932672763331539726169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72517243563684442052968225 54387932672763331539726169)
      ·
        refine ⟨40790949504572498654794627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54387932672763331539726169 40790949504572498654794627)
        ·
          refine ⟨61186424256858747982191941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40790949504572498654794627 61186424256858747982191941)
          ·
            refine ⟨11472454548161015246660989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61186424256858747982191941 11472454548161015246660989)
            ·
              refine ⟨4302170455560380717497871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11472454548161015246660989 4302170455560380717497871)
              ·
                refine ⟨6453255683340571076246807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4302170455560380717497871 6453255683340571076246807)
                ·
                  refine ⟨9679883525010856614370211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6453255683340571076246807 9679883525010856614370211)
                  ·
                    refine ⟨14519825287516284921555317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9679883525010856614370211 14519825287516284921555317)
                    ·
                      refine ⟨1361233620704651711395811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14519825287516284921555317 1361233620704651711395811)
                      ·
                        rfl

theorem cell23_2650993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_2650993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2650993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2650993 prefixEnd_2650993 := by exact prefixLift 2650993
  have htrace : WordTrace (prefixWord ++ tailWord_2650993) baseStart_2650993 baseEnd_2650993 := by
    simpa [prefixWord, tailWord_2650993, baseEnd_2650993] using wordTrace_append hprefix tailTrace_2650993
  have hstable : (prefixWord ++ tailWord_2650993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650993).length < 2 ^ (prefixWord ++ tailWord_2650993).sum := by decide
  have hdescent : baseEnd_2650993 < baseStart_2650993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651013 : List Nat := [1, 3, 1, 1, 3, 5, 1, 8]
def baseStart_2651013 : Nat := 118140960795 + 2651013 * 2 ^ 59
def prefixEnd_2651013 : Nat := 4983230072969 + 3 ^ 40 * 2651013 * 2
def baseEnd_2651013 : Nat := 50416440382138579005397

theorem tailTrace_2651013 : CollatzResearch.WordTrace tailWord_2651013 prefixEnd_2651013 50416440382138579005397 := by
  unfold tailWord_2651013
  simp only [CollatzResearch.WordTrace]
  refine ⟨96690387544840132819685693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64460258363226755213123795 96690387544840132819685693)
  ·
    refine ⟨36258895329315049807382135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96690387544840132819685693 36258895329315049807382135)
    ·
      refine ⟨54388342993972574711073203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36258895329315049807382135 54388342993972574711073203)
      ·
        refine ⟨81582514490958862066609805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54388342993972574711073203 81582514490958862066609805)
        ·
          refine ⟨30593442934109573274978677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81582514490958862066609805 30593442934109573274978677)
          ·
            refine ⟨2868135275072772494529251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30593442934109573274978677 2868135275072772494529251)
            ·
              refine ⟨4302202912609158741793877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868135275072772494529251 4302202912609158741793877)
              ·
                refine ⟨50416440382138579005397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4302202912609158741793877 50416440382138579005397)
                ·
                  rfl

theorem cell23_2651013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 8].length) (baseStart_2651013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651013 prefixEnd_2651013 := by exact prefixLift 2651013
  have htrace : WordTrace (prefixWord ++ tailWord_2651013) baseStart_2651013 baseEnd_2651013 := by
    simpa [prefixWord, tailWord_2651013, baseEnd_2651013] using wordTrace_append hprefix tailTrace_2651013
  have hstable : (prefixWord ++ tailWord_2651013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651013).length < 2 ^ (prefixWord ++ tailWord_2651013).sum := by decide
  have hdescent : baseEnd_2651013 < baseStart_2651013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651041 : List Nat := [1, 2, 3, 4, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2651041 : Nat := 118140960795 + 2651041 * 2 ^ 59
def prefixEnd_2651041 : Nat := 4983230072969 + 3 ^ 40 * 2651041 * 2
def baseEnd_2651041 : Nat := 1361258267776067523595591

theorem tailTrace_2651041 : CollatzResearch.WordTrace tailWord_2651041 prefixEnd_2651041 1361258267776067523595591 := by
  unfold tailWord_2651041
  simp only [CollatzResearch.WordTrace]
  refine ⟨96691408788738693601704977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64460939192492462401136651 96691408788738693601704977)
  ·
    refine ⟨72518556591554020201278733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96691408788738693601704977 72518556591554020201278733)
    ·
      refine ⟨27194458721832757575479525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72518556591554020201278733 27194458721832757575479525)
      ·
        refine ⟨5098961010343642045402411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27194458721832757575479525 5098961010343642045402411)
        ·
          refine ⟨7648441515515463068103617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5098961010343642045402411 7648441515515463068103617)
          ·
            refine ⟨5736331136636597301077713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7648441515515463068103617 5736331136636597301077713)
            ·
              refine ⟨4302248352477447975808285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5736331136636597301077713 4302248352477447975808285)
              ·
                refine ⟨1613343132179042990928107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4302248352477447975808285 1613343132179042990928107)
                ·
                  refine ⟨2420014698268564486392161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613343132179042990928107 2420014698268564486392161)
                  ·
                    refine ⟨1815011023701423364794121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2420014698268564486392161 1815011023701423364794121)
                    ·
                      refine ⟨1361258267776067523595591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815011023701423364794121 1361258267776067523595591)
                      ·
                        rfl

theorem cell23_2651041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2651041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651041 prefixEnd_2651041 := by exact prefixLift 2651041
  have htrace : WordTrace (prefixWord ++ tailWord_2651041) baseStart_2651041 baseEnd_2651041 := by
    simpa [prefixWord, tailWord_2651041, baseEnd_2651041] using wordTrace_append hprefix tailTrace_2651041
  have hstable : (prefixWord ++ tailWord_2651041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651041).length < 2 ^ (prefixWord ++ tailWord_2651041).sum := by decide
  have hdescent : baseEnd_2651041 < baseStart_2651041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651057 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2651057 : Nat := 118140960795 + 2651057 * 2 ^ 59
def prefixEnd_2651057 : Nat := 4983230072969 + 3 ^ 40 * 2651057 * 2
def baseEnd_2651057 : Nat := 1361266483466539460995517

theorem tailTrace_2651057 : CollatzResearch.WordTrace tailWord_2651057 prefixEnd_2651057 1361266483466539460995517 := by
  unfold tailWord_2651057
  simp only [CollatzResearch.WordTrace]
  refine ⟨96691992356680728334287425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64461328237787152222858283 96691992356680728334287425)
  ·
    refine ⟨72518994267510546250715569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96691992356680728334287425 72518994267510546250715569)
    ·
      refine ⟨54389245700632909688036677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72518994267510546250715569 54389245700632909688036677)
      ·
        refine ⟨10197983568868670566506877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54389245700632909688036677 10197983568868670566506877)
        ·
          refine ⟨3824243838325751462440079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10197983568868670566506877 3824243838325751462440079)
          ·
            refine ⟨5736365757488627193660119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3824243838325751462440079 5736365757488627193660119)
            ·
              refine ⟨8604548636232940790490179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5736365757488627193660119 8604548636232940790490179)
              ·
                refine ⟨12906822954349411185735269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8604548636232940790490179 12906822954349411185735269)
                ·
                  refine ⟨2420029303940514597325363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12906822954349411185735269 2420029303940514597325363)
                  ·
                    refine ⟨3630043955910771895988045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2420029303940514597325363 3630043955910771895988045)
                    ·
                      refine ⟨1361266483466539460995517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3630043955910771895988045 1361266483466539460995517)
                      ·
                        rfl

theorem cell23_2651057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2651057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651057 prefixEnd_2651057 := by exact prefixLift 2651057
  have htrace : WordTrace (prefixWord ++ tailWord_2651057) baseStart_2651057 baseEnd_2651057 := by
    simpa [prefixWord, tailWord_2651057, baseEnd_2651057] using wordTrace_append hprefix tailTrace_2651057
  have hstable : (prefixWord ++ tailWord_2651057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651057).length < 2 ^ (prefixWord ++ tailWord_2651057).sum := by decide
  have hdescent : baseEnd_2651057 < baseStart_2651057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651097 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 4, 2, 2]
def baseStart_2651097 : Nat := 118140960795 + 2651097 * 2 ^ 59
def prefixEnd_2651097 : Nat := 4983230072969 + 3 ^ 40 * 2651097 * 2
def baseEnd_2651097 : Nat := 1361287022692719304495333

theorem tailTrace_2651097 : CollatzResearch.WordTrace tailWord_2651097 prefixEnd_2651097 1361287022692719304495333 := by
  unfold tailWord_2651097
  simp only [CollatzResearch.WordTrace]
  refine ⟨96693451276535815165743545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64462300851023876777162363 96693451276535815165743545)
  ·
    refine ⟨72520088457401861374307659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96693451276535815165743545 72520088457401861374307659)
    ·
      refine ⟨108780132686102792061461489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72520088457401861374307659 108780132686102792061461489)
      ·
        refine ⟨81585099514577094046096117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108780132686102792061461489 81585099514577094046096117)
        ·
          refine ⟨7648603079491602566821511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81585099514577094046096117 7648603079491602566821511)
          ·
            refine ⟨11472904619237403850232267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7648603079491602566821511 11472904619237403850232267)
            ·
              refine ⟨17209356928856105775348401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11472904619237403850232267 17209356928856105775348401)
              ·
                refine ⟨12907017696642079331511301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17209356928856105775348401 12907017696642079331511301)
                ·
                  refine ⟨2420065818120389874658369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12907017696642079331511301 2420065818120389874658369)
                  ·
                    refine ⟨1815049363590292405993777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2420065818120389874658369 1815049363590292405993777)
                    ·
                      refine ⟨1361287022692719304495333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815049363590292405993777 1361287022692719304495333)
                      ·
                        rfl

theorem cell23_2651097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 2, 2].length) (baseStart_2651097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651097 prefixEnd_2651097 := by exact prefixLift 2651097
  have htrace : WordTrace (prefixWord ++ tailWord_2651097) baseStart_2651097 baseEnd_2651097 := by
    simpa [prefixWord, tailWord_2651097, baseEnd_2651097] using wordTrace_append hprefix tailTrace_2651097
  have hstable : (prefixWord ++ tailWord_2651097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651097).length < 2 ^ (prefixWord ++ tailWord_2651097).sum := by decide
  have hdescent : baseEnd_2651097 < baseStart_2651097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651125 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2651125 : Nat := 118140960795 + 2651125 * 2 ^ 59
def prefixEnd_2651125 : Nat := 4983230072969 + 3 ^ 40 * 2651125 * 2
def baseEnd_2651125 : Nat := 1361301400151045194945205

theorem tailTrace_2651125 : CollatzResearch.WordTrace tailWord_2651125 prefixEnd_2651125 1361301400151045194945205 := by
  unfold tailWord_2651125
  simp only [CollatzResearch.WordTrace]
  refine ⟨96694472520434375947762829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64462981680289583965175219 96694472520434375947762829)
  ·
    refine ⟨36260427195162890980411061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96694472520434375947762829 36260427195162890980411061)
    ·
      refine ⟨3399415049546521029413537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36260427195162890980411061 3399415049546521029413537)
      ·
        refine ⟨2549561287159890772060153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3399415049546521029413537 2549561287159890772060153)
        ·
          refine ⟨1912170965369918079045115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2549561287159890772060153 1912170965369918079045115)
          ·
            refine ⟨2868256448054877118567673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912170965369918079045115 2868256448054877118567673)
            ·
              refine ⟨2151192336041157838925755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2868256448054877118567673 2151192336041157838925755)
              ·
                refine ⟨3226788504061736758388633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151192336041157838925755 3226788504061736758388633)
                ·
                  refine ⟨2420091378046302568791475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3226788504061736758388633 2420091378046302568791475)
                  ·
                    refine ⟨3630137067069453853187213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2420091378046302568791475 3630137067069453853187213)
                    ·
                      refine ⟨1361301400151045194945205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3630137067069453853187213 1361301400151045194945205)
                      ·
                        rfl

theorem cell23_2651125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2651125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651125 prefixEnd_2651125 := by exact prefixLift 2651125
  have htrace : WordTrace (prefixWord ++ tailWord_2651125) baseStart_2651125 baseEnd_2651125 := by
    simpa [prefixWord, tailWord_2651125, baseEnd_2651125] using wordTrace_append hprefix tailTrace_2651125
  have hstable : (prefixWord ++ tailWord_2651125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651125).length < 2 ^ (prefixWord ++ tailWord_2651125).sum := by decide
  have hdescent : baseEnd_2651125 < baseStart_2651125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651133 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_2651133 : Nat := 118140960795 + 2651133 * 2 ^ 59
def prefixEnd_2651133 : Nat := 4983230072969 + 3 ^ 40 * 2651133 * 2
def baseEnd_2651133 : Nat := 453768502665427054548389

theorem tailTrace_2651133 : CollatzResearch.WordTrace tailWord_2651133 prefixEnd_2651133 453768502665427054548389 := by
  unfold tailWord_2651133
  simp only [CollatzResearch.WordTrace]
  refine ⟨96694764304405393314054053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64463176202936928876036035 96694764304405393314054053)
  ·
    refine ⟨18130268307076011246385135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96694764304405393314054053 18130268307076011246385135)
    ·
      refine ⟨27195402460614016869577703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18130268307076011246385135 27195402460614016869577703)
      ·
        refine ⟨40793103690921025304366555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27195402460614016869577703 40793103690921025304366555)
        ·
          refine ⟨61189655536381537956549833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40793103690921025304366555 61189655536381537956549833)
          ·
            refine ⟨45892241652286153467412375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61189655536381537956549833 45892241652286153467412375)
            ·
              refine ⟨68838362478429230201118563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45892241652286153467412375 68838362478429230201118563)
              ·
                refine ⟨103257543717643845301677845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68838362478429230201118563 103257543717643845301677845)
                ·
                  refine ⟨4840197361764555248516149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103257543717643845301677845 4840197361764555248516149)
                  ·
                    refine ⟨453768502665427054548389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4840197361764555248516149 453768502665427054548389)
                    ·
                      rfl

theorem cell23_2651133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_2651133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651133 prefixEnd_2651133 := by exact prefixLift 2651133
  have htrace : WordTrace (prefixWord ++ tailWord_2651133) baseStart_2651133 baseEnd_2651133 := by
    simpa [prefixWord, tailWord_2651133, baseEnd_2651133] using wordTrace_append hprefix tailTrace_2651133
  have hstable : (prefixWord ++ tailWord_2651133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651133).length < 2 ^ (prefixWord ++ tailWord_2651133).sum := by decide
  have hdescent : baseEnd_2651133 < baseStart_2651133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651143 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2651143 : Nat := 118140960795 + 2651143 * 2 ^ 59
def prefixEnd_2651143 : Nat := 4983230072969 + 3 ^ 40 * 2651143 * 2
def baseEnd_2651143 : Nat := 1361310642802826124520121

theorem tailTrace_2651143 : CollatzResearch.WordTrace tailWord_2651143 prefixEnd_2651143 1361310642802826124520121 := by
  unfold tailWord_2651143
  simp only [CollatzResearch.WordTrace]
  refine ⟨96695129034369165021918083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64463419356246110014612055 96695129034369165021918083)
  ·
    refine ⟨145042693551553747532877125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96695129034369165021918083 145042693551553747532877125)
    ·
      refine ⟨27195505040916327662414461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145042693551553747532877125 27195505040916327662414461)
      ·
        refine ⟨10198314390343622873405423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27195505040916327662414461 10198314390343622873405423)
        ·
          refine ⟨15297471585515434310108135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10198314390343622873405423 15297471585515434310108135)
          ·
            refine ⟨22946207378273151465162203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15297471585515434310108135 22946207378273151465162203)
            ·
              refine ⟨34419311067409727197743305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22946207378273151465162203 34419311067409727197743305)
              ·
                refine ⟨25814483300557295398307479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34419311067409727197743305 25814483300557295398307479)
                ·
                  refine ⟨38721724950835943097461219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25814483300557295398307479 38721724950835943097461219)
                  ·
                    refine ⟨58082587426253914646191829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38721724950835943097461219 58082587426253914646191829)
                    ·
                      refine ⟨1361310642802826124520121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58082587426253914646191829 1361310642802826124520121)
                      ·
                        rfl

theorem cell23_2651143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2651143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651143 prefixEnd_2651143 := by exact prefixLift 2651143
  have htrace : WordTrace (prefixWord ++ tailWord_2651143) baseStart_2651143 baseEnd_2651143 := by
    simpa [prefixWord, tailWord_2651143, baseEnd_2651143] using wordTrace_append hprefix tailTrace_2651143
  have hstable : (prefixWord ++ tailWord_2651143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651143).length < 2 ^ (prefixWord ++ tailWord_2651143).sum := by decide
  have hdescent : baseEnd_2651143 < baseStart_2651143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651150 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_2651150 : Nat := 118140960795 + 2651150 * 2 ^ 59
def prefixEnd_2651150 : Nat := 4983230072969 + 3 ^ 40 * 2651150 * 2
def baseEnd_2651150 : Nat := 453771412389135865710863

theorem tailTrace_2651150 : CollatzResearch.WordTrace tailWord_2651150 prefixEnd_2651150 453771412389135865710863 := by
  unfold tailWord_2651150
  simp only [CollatzResearch.WordTrace]
  refine ⟨12086923043167975652177863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64463589563562536811615269 12086923043167975652177863)
  ·
    refine ⟨18130384564751963478266795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12086923043167975652177863 18130384564751963478266795)
    ·
      refine ⟨27195576847127945217400193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18130384564751963478266795 27195576847127945217400193)
      ·
        refine ⟨20396682635345958913050145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27195576847127945217400193 20396682635345958913050145)
        ·
          refine ⟨15297511976509469184787609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20396682635345958913050145 15297511976509469184787609)
          ·
            refine ⟨11473133982382101888590707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15297511976509469184787609 11473133982382101888590707)
            ·
              refine ⟨17209700973573152832886061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11473133982382101888590707 17209700973573152832886061)
              ·
                refine ⟨6453637865089932312332273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17209700973573152832886061 6453637865089932312332273)
                ·
                  refine ⟨4840228398817449234249205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6453637865089932312332273 4840228398817449234249205)
                  ·
                    refine ⟨453771412389135865710863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4840228398817449234249205 453771412389135865710863)
                    ·
                      rfl

theorem cell23_2651150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_2651150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651150 prefixEnd_2651150 := by exact prefixLift 2651150
  have htrace : WordTrace (prefixWord ++ tailWord_2651150) baseStart_2651150 baseEnd_2651150 := by
    simpa [prefixWord, tailWord_2651150, baseEnd_2651150] using wordTrace_append hprefix tailTrace_2651150
  have hstable : (prefixWord ++ tailWord_2651150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651150).length < 2 ^ (prefixWord ++ tailWord_2651150).sum := by decide
  have hdescent : baseEnd_2651150 < baseStart_2651150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651153 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_2651153 : Nat := 118140960795 + 2651153 * 2 ^ 59
def prefixEnd_2651153 : Nat := 4983230072969 + 3 ^ 40 * 2651153 * 2
def baseEnd_2651153 : Nat := 1361315777609371085395075

theorem tailTrace_2651153 : CollatzResearch.WordTrace tailWord_2651153 prefixEnd_2651153 1361315777609371085395075 := by
  unfold tailWord_2651153
  simp only [CollatzResearch.WordTrace]
  refine ⟨96695493764332936729782113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64463662509555291153188075 96695493764332936729782113)
  ·
    refine ⟨72521620323249702547336585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96695493764332936729782113 72521620323249702547336585)
    ·
      refine ⟨54391215242437276910502439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72521620323249702547336585 54391215242437276910502439)
      ·
        refine ⟨81586822863655915365753659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54391215242437276910502439 81586822863655915365753659)
        ·
          refine ⟨122380234295483873048630489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81586822863655915365753659 122380234295483873048630489)
          ·
            refine ⟨91785175721612904786472867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122380234295483873048630489 91785175721612904786472867)
            ·
              refine ⟨137677763582419357179709301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91785175721612904786472867 137677763582419357179709301)
              ·
                refine ⟨12907290335851814735597747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137677763582419357179709301 12907290335851814735597747)
                ·
                  refine ⟨19360935503777722103396621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12907290335851814735597747 19360935503777722103396621)
                  ·
                    refine ⟨7260350813916645788773733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19360935503777722103396621 7260350813916645788773733)
                    ·
                      refine ⟨1361315777609371085395075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7260350813916645788773733 1361315777609371085395075)
                      ·
                        rfl

theorem cell23_2651153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_2651153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651153 prefixEnd_2651153 := by exact prefixLift 2651153
  have htrace : WordTrace (prefixWord ++ tailWord_2651153) baseStart_2651153 baseEnd_2651153 := by
    simpa [prefixWord, tailWord_2651153, baseEnd_2651153] using wordTrace_append hprefix tailTrace_2651153
  have hstable : (prefixWord ++ tailWord_2651153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651153).length < 2 ^ (prefixWord ++ tailWord_2651153).sum := by decide
  have hdescent : baseEnd_2651153 < baseStart_2651153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651173 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_2651173 : Nat := 118140960795 + 2651173 * 2 ^ 59
def prefixEnd_2651173 : Nat := 4983230072969 + 3 ^ 40 * 2651173 * 2
def baseEnd_2651173 : Nat := 1361326047222461007144983

theorem tailTrace_2651173 : CollatzResearch.WordTrace tailWord_2651173 prefixEnd_2651173 1361326047222461007144983 := by
  unfold tailWord_2651173
  simp only [CollatzResearch.WordTrace]
  refine ⟨96696223224260480145510173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64464148816173653430340115 96696223224260480145510173)
  ·
    refine ⟨36261083709097680054566315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96696223224260480145510173 36261083709097680054566315)
    ·
      refine ⟨54391625563646520081849473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36261083709097680054566315 54391625563646520081849473)
      ·
        refine ⟨40793719172734890061387105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54391625563646520081849473 40793719172734890061387105)
        ·
          refine ⟨30595289379551167546040329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40793719172734890061387105 30595289379551167546040329)
          ·
            refine ⟨22946467034663375659530247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30595289379551167546040329 22946467034663375659530247)
            ·
              refine ⟨34419700551995063489295371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22946467034663375659530247 34419700551995063489295371)
              ·
                refine ⟨51629550827992595233943057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34419700551995063489295371 51629550827992595233943057)
                ·
                  refine ⟨38722163120994446425457293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51629550827992595233943057 38722163120994446425457293)
                  ·
                    refine ⟨14520811170372917409546485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38722163120994446425457293 14520811170372917409546485)
                    ·
                      refine ⟨1361326047222461007144983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14520811170372917409546485 1361326047222461007144983)
                      ·
                        rfl

theorem cell23_2651173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_2651173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651173 prefixEnd_2651173 := by exact prefixLift 2651173
  have htrace : WordTrace (prefixWord ++ tailWord_2651173) baseStart_2651173 baseEnd_2651173 := by
    simpa [prefixWord, tailWord_2651173, baseEnd_2651173] using wordTrace_append hprefix tailTrace_2651173
  have hstable : (prefixWord ++ tailWord_2651173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651173).length < 2 ^ (prefixWord ++ tailWord_2651173).sum := by decide
  have hdescent : baseEnd_2651173 < baseStart_2651173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651180 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 3, 4]
def baseStart_2651180 : Nat := 118140960795 + 2651180 * 2 ^ 59
def prefixEnd_2651180 : Nat := 4983230072969 + 3 ^ 40 * 2651180 * 2
def baseEnd_2651180 : Nat := 453776547195680826585817

theorem tailTrace_2651180 : CollatzResearch.WordTrace tailWord_2651180 prefixEnd_2651180 453776547195680826585817 := by
  unfold tailWord_2651180
  simp only [CollatzResearch.WordTrace]
  refine ⟨48348239267617560170507497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64464319023490080227343329 48348239267617560170507497)
  ·
    refine ⟨36261179450713170127880623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48348239267617560170507497 36261179450713170127880623)
    ·
      refine ⟨54391769176069755191820935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36261179450713170127880623 54391769176069755191820935)
      ·
        refine ⟨81587653764104632787731403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54391769176069755191820935 81587653764104632787731403)
        ·
          refine ⟨122381480646156949181597105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81587653764104632787731403 122381480646156949181597105)
          ·
            refine ⟨91786110484617711886197829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122381480646156949181597105 91786110484617711886197829)
            ·
              refine ⟨17209895715865820978662093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91786110484617711886197829 17209895715865820978662093)
              ·
                refine ⟨6453710893449682866998285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17209895715865820978662093 6453710893449682866998285)
                ·
                  refine ⟨2420141585043631075124357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6453710893449682866998285 2420141585043631075124357)
                  ·
                    refine ⟨453776547195680826585817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2420141585043631075124357 453776547195680826585817)
                    ·
                      rfl

theorem cell23_2651180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_2651180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651180 prefixEnd_2651180 := by exact prefixLift 2651180
  have htrace : WordTrace (prefixWord ++ tailWord_2651180) baseStart_2651180 baseEnd_2651180 := by
    simpa [prefixWord, tailWord_2651180, baseEnd_2651180] using wordTrace_append hprefix tailTrace_2651180
  have hstable : (prefixWord ++ tailWord_2651180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651180).length < 2 ^ (prefixWord ++ tailWord_2651180).sum := by decide
  have hdescent : baseEnd_2651180 < baseStart_2651180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651197 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_2651197 : Nat := 118140960795 + 2651197 * 2 ^ 59
def prefixEnd_2651197 : Nat := 4983230072969 + 3 ^ 40 * 2651197 * 2
def baseEnd_2651197 : Nat := 453779456919389637748291

theorem tailTrace_2651197 : CollatzResearch.WordTrace tailWord_2651197 prefixEnd_2651197 453779456919389637748291 := by
  unfold tailWord_2651197
  simp only [CollatzResearch.WordTrace]
  refine ⟨96697098576173532244383845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64464732384115688162922563 96697098576173532244383845)
  ·
    refine ⟨18130705983032537295821971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96697098576173532244383845 18130705983032537295821971)
    ·
      refine ⟨27196058974548805943732957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18130705983032537295821971 27196058974548805943732957)
      ·
        refine ⟨10198522115455802228899859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27196058974548805943732957 10198522115455802228899859)
        ·
          refine ⟨15297783173183703343349789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10198522115455802228899859 15297783173183703343349789)
          ·
            refine ⟨5736668689943888753756171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15297783173183703343349789 5736668689943888753756171)
            ·
              refine ⟨8605003034915833130634257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5736668689943888753756171 8605003034915833130634257)
              ·
                refine ⟨6453752276186874847975693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8605003034915833130634257 6453752276186874847975693)
                ·
                  refine ⟨2420157103570078067990885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6453752276186874847975693 2420157103570078067990885)
                  ·
                    refine ⟨453779456919389637748291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2420157103570078067990885 453779456919389637748291)
                    ·
                      rfl

theorem cell23_2651197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_2651197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651197 prefixEnd_2651197 := by exact prefixLift 2651197
  have htrace : WordTrace (prefixWord ++ tailWord_2651197) baseStart_2651197 baseEnd_2651197 := by
    simpa [prefixWord, tailWord_2651197, baseEnd_2651197] using wordTrace_append hprefix tailTrace_2651197
  have hstable : (prefixWord ++ tailWord_2651197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651197).length < 2 ^ (prefixWord ++ tailWord_2651197).sum := by decide
  have hdescent : baseEnd_2651197 < baseStart_2651197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651207 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_2651207 : Nat := 118140960795 + 2651207 * 2 ^ 59
def prefixEnd_2651207 : Nat := 4983230072969 + 3 ^ 40 * 2651207 * 2
def baseEnd_2651207 : Nat := 1361343505564713874119827

theorem tailTrace_2651207 : CollatzResearch.WordTrace tailWord_2651207 prefixEnd_2651207 1361343505564713874119827 := by
  unfold tailWord_2651207
  simp only [CollatzResearch.WordTrace]
  refine ⟨96697463306137303952247875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64464975537424869301498583 96697463306137303952247875)
  ·
    refine ⟨145046194959205955928371813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96697463306137303952247875 145046194959205955928371813)
    ·
      refine ⟨27196161554851116736569715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145046194959205955928371813 27196161554851116736569715)
      ·
        refine ⟨40794242332276675104854573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27196161554851116736569715 40794242332276675104854573)
        ·
          refine ⟨15297840874603753164320465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40794242332276675104854573 15297840874603753164320465)
          ·
            refine ⟨11473380655952814873240349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15297840874603753164320465 11473380655952814873240349)
            ·
              refine ⟨4302517745982305577465131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11473380655952814873240349 4302517745982305577465131)
              ·
                refine ⟨6453776618973458366197697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4302517745982305577465131 6453776618973458366197697)
                ·
                  refine ⟨4840332464230093774648273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6453776618973458366197697 4840332464230093774648273)
                  ·
                    refine ⟨3630249348172570330986205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4840332464230093774648273 3630249348172570330986205)
                    ·
                      refine ⟨1361343505564713874119827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3630249348172570330986205 1361343505564713874119827)
                      ·
                        rfl

theorem cell23_2651207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_2651207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651207 prefixEnd_2651207 := by exact prefixLift 2651207
  have htrace : WordTrace (prefixWord ++ tailWord_2651207) baseStart_2651207 baseEnd_2651207 := by
    simpa [prefixWord, tailWord_2651207, baseEnd_2651207] using wordTrace_append hprefix tailTrace_2651207
  have hstable : (prefixWord ++ tailWord_2651207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651207).length < 2 ^ (prefixWord ++ tailWord_2651207).sum := by decide
  have hdescent : baseEnd_2651207 < baseStart_2651207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651214 : List Nat := [4, 1, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_2651214 : Nat := 118140960795 + 2651214 * 2 ^ 59
def prefixEnd_2651214 : Nat := 4983230072969 + 3 ^ 40 * 2651214 * 2
def baseEnd_2651214 : Nat := 453782366643098448910765

theorem tailTrace_2651214 : CollatzResearch.WordTrace tailWord_2651214 prefixEnd_2651214 453782366643098448910765 := by
  unfold tailWord_2651214
  simp only [CollatzResearch.WordTrace]
  refine ⟨12087214827138993018469087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64465145744741296098501797 12087214827138993018469087)
  ·
    refine ⟨18130822240708489527703631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12087214827138993018469087 18130822240708489527703631)
    ·
      refine ⟨27196233361062734291555447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18130822240708489527703631 27196233361062734291555447)
      ·
        refine ⟨40794350041594101437333171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27196233361062734291555447 40794350041594101437333171)
        ·
          refine ⟨61191525062391152155999757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40794350041594101437333171 61191525062391152155999757)
          ·
            refine ⟨22946821898396682058499909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61191525062391152155999757 22946821898396682058499909)
            ·
              refine ⟨4302529105949377885968733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22946821898396682058499909 4302529105949377885968733)
              ·
                refine ⟨1613448414731016707238275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4302529105949377885968733 1613448414731016707238275)
                ·
                  refine ⟨2420172622096525060857413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613448414731016707238275 2420172622096525060857413)
                  ·
                    refine ⟨453782366643098448910765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2420172622096525060857413 453782366643098448910765)
                    ·
                      rfl

theorem cell23_2651214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_2651214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651214 prefixEnd_2651214 := by exact prefixLift 2651214
  have htrace : WordTrace (prefixWord ++ tailWord_2651214) baseStart_2651214 baseEnd_2651214 := by
    simpa [prefixWord, tailWord_2651214, baseEnd_2651214] using wordTrace_append hprefix tailTrace_2651214
  have hstable : (prefixWord ++ tailWord_2651214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651214).length < 2 ^ (prefixWord ++ tailWord_2651214).sum := by decide
  have hdescent : baseEnd_2651214 < baseStart_2651214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651254 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2651254 : Nat := 118140960795 + 2651254 * 2 ^ 59
def prefixEnd_2651254 : Nat := 4983230072969 + 3 ^ 40 * 2651254 * 2
def baseEnd_2651254 : Nat := 1361367639155475190232111

theorem tailTrace_2651254 : CollatzResearch.WordTrace tailWord_2651254 prefixEnd_2651254 1361367639155475190232111 := by
  unfold tailWord_2651254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6043698596060439436200551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64466118357978020652805877 6043698596060439436200551)
  ·
    refine ⟨9065547894090659154300827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6043698596060439436200551 9065547894090659154300827)
    ·
      refine ⟨13598321841135988731451241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9065547894090659154300827 13598321841135988731451241)
      ·
        refine ⟨10198741380851991548588431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13598321841135988731451241 10198741380851991548588431)
        ·
          refine ⟨15298112071277987322882647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10198741380851991548588431 15298112071277987322882647)
          ·
            refine ⟨22947168106916980984323971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15298112071277987322882647 22947168106916980984323971)
            ·
              refine ⟨34420752160375471476485957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22947168106916980984323971 34420752160375471476485957)
              ·
                refine ⟨6453891030070400901841117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34420752160375471476485957 6453891030070400901841117)
                ·
                  refine ⟨2420209136276400338190419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6453891030070400901841117 2420209136276400338190419)
                  ·
                    refine ⟨3630313704414600507285629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2420209136276400338190419 3630313704414600507285629)
                    ·
                      refine ⟨1361367639155475190232111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3630313704414600507285629 1361367639155475190232111)
                      ·
                        rfl

theorem cell23_2651254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2651254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651254 prefixEnd_2651254 := by exact prefixLift 2651254
  have htrace : WordTrace (prefixWord ++ tailWord_2651254) baseStart_2651254 baseEnd_2651254 := by
    simpa [prefixWord, tailWord_2651254, baseEnd_2651254] using wordTrace_append hprefix tailTrace_2651254
  have hstable : (prefixWord ++ tailWord_2651254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651254).length < 2 ^ (prefixWord ++ tailWord_2651254).sum := by decide
  have hdescent : baseEnd_2651254 < baseStart_2651254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651283 : List Nat := [1, 1, 1, 2, 1, 2, 15]
def baseStart_2651283 : Nat := 118140960795 + 2651283 * 2 ^ 59
def prefixEnd_2651283 : Nat := 4983230072969 + 3 ^ 40 * 2651283 * 2
def baseEnd_2651283 : Nat := 16807191729561179960117

theorem tailTrace_2651283 : CollatzResearch.WordTrace tailWord_2651283 prefixEnd_2651283 16807191729561179960117 := by
  unfold tailWord_2651283
  simp only [CollatzResearch.WordTrace]
  refine ⟨96700235253861968932014503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64466823502574645954676335 96700235253861968932014503)
  ·
    refine ⟨145050352880792953398021755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96700235253861968932014503 145050352880792953398021755)
    ·
      refine ⟨217575529321189430097032633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145050352880792953398021755 217575529321189430097032633)
      ·
        refine ⟨163181646990892072572774475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217575529321189430097032633 163181646990892072572774475)
        ·
          refine ⟨244772470486338108859161713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163181646990892072572774475 244772470486338108859161713)
          ·
            refine ⟨183579352864753581644371285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244772470486338108859161713 183579352864753581644371285)
            ·
              refine ⟨16807191729561179960117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 183579352864753581644371285 16807191729561179960117)
              ·
                rfl

theorem cell23_2651283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 15].length) (baseStart_2651283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651283 prefixEnd_2651283 := by exact prefixLift 2651283
  have htrace : WordTrace (prefixWord ++ tailWord_2651283) baseStart_2651283 baseEnd_2651283 := by
    simpa [prefixWord, tailWord_2651283, baseEnd_2651283] using wordTrace_append hprefix tailTrace_2651283
  have hstable : (prefixWord ++ tailWord_2651283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651283).length < 2 ^ (prefixWord ++ tailWord_2651283).sum := by decide
  have hdescent : baseEnd_2651283 < baseStart_2651283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651287 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 4, 4]
def baseStart_2651287 : Nat := 118140960795 + 2651287 * 2 ^ 59
def prefixEnd_2651287 : Nat := 4983230072969 + 3 ^ 40 * 2651287 * 2
def baseEnd_2651287 : Nat := 453794861339024520373153

theorem tailTrace_2651287 : CollatzResearch.WordTrace tailWord_2651287 prefixEnd_2651287 453794861339024520373153 := by
  unfold tailWord_2651287
  simp only [CollatzResearch.WordTrace]
  refine ⟨96700381145847477615160115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64466920763898318410106743 96700381145847477615160115)
  ·
    refine ⟨145050571718771216422740173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96700381145847477615160115 145050571718771216422740173)
    ·
      refine ⟨54393964394539206158527565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145050571718771216422740173 54393964394539206158527565)
      ·
        refine ⟨20397736647952202309447837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54393964394539206158527565 20397736647952202309447837)
        ·
          refine ⟨7649151242982075866042939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20397736647952202309447837 7649151242982075866042939)
          ·
            refine ⟨11473726864473113799064409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7649151242982075866042939 11473726864473113799064409)
            ·
              refine ⟨8605295148354835349298307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11473726864473113799064409 8605295148354835349298307)
              ·
                refine ⟨12907942722532253023947461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8605295148354835349298307 12907942722532253023947461)
                ·
                  refine ⟨2420239260474797441990149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12907942722532253023947461 2420239260474797441990149)
                  ·
                    refine ⟨453794861339024520373153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2420239260474797441990149 453794861339024520373153)
                    ·
                      rfl

theorem cell23_2651287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_2651287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651287 prefixEnd_2651287 := by exact prefixLift 2651287
  have htrace : WordTrace (prefixWord ++ tailWord_2651287) baseStart_2651287 baseEnd_2651287 := by
    simpa [prefixWord, tailWord_2651287, baseEnd_2651287] using wordTrace_append hprefix tailTrace_2651287
  have hstable : (prefixWord ++ tailWord_2651287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651287).length < 2 ^ (prefixWord ++ tailWord_2651287).sum := by decide
  have hdescent : baseEnd_2651287 < baseStart_2651287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651288 : List Nat := [2, 1, 2, 4, 2, 2, 3, 2, 1, 1, 3]
def baseStart_2651288 : Nat := 118140960795 + 2651288 * 2 ^ 59
def prefixEnd_2651288 : Nat := 4983230072969 + 3 ^ 40 * 2651288 * 2
def baseEnd_2651288 : Nat := 1361385097497728057206955

theorem tailTrace_2651288 : CollatzResearch.WordTrace tailWord_2651288 prefixEnd_2651288 1361385097497728057206955 := by
  unfold tailWord_2651288
  simp only [CollatzResearch.WordTrace]
  refine ⟨48350208809421927392973259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64466945079229236523964345 48350208809421927392973259)
  ·
    refine ⟨72525313214132891089459889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48350208809421927392973259 72525313214132891089459889)
    ·
      refine ⟨54393984910599668317094917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72525313214132891089459889 54393984910599668317094917)
      ·
        refine ⟨10198872170737437809455297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54393984910599668317094917 10198872170737437809455297)
        ·
          refine ⟨7649154128053078357091473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10198872170737437809455297 7649154128053078357091473)
          ·
            refine ⟨5736865596039808767818605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7649154128053078357091473 5736865596039808767818605)
            ·
              refine ⟨2151324598514928287931977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5736865596039808767818605 2151324598514928287931977)
              ·
                refine ⟨1613493448886196215948983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151324598514928287931977 1613493448886196215948983)
                ·
                  refine ⟨2420240173329294323923475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613493448886196215948983 2420240173329294323923475)
                  ·
                    refine ⟨3630360259993941485885213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2420240173329294323923475 3630360259993941485885213)
                    ·
                      refine ⟨1361385097497728057206955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3630360259993941485885213 1361385097497728057206955)
                      ·
                        rfl

theorem cell23_2651288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_2651288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651288 prefixEnd_2651288 := by exact prefixLift 2651288
  have htrace : WordTrace (prefixWord ++ tailWord_2651288) baseStart_2651288 baseEnd_2651288 := by
    simpa [prefixWord, tailWord_2651288, baseEnd_2651288] using wordTrace_append hprefix tailTrace_2651288
  have hstable : (prefixWord ++ tailWord_2651288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651288).length < 2 ^ (prefixWord ++ tailWord_2651288).sum := by decide
  have hdescent : baseEnd_2651288 < baseStart_2651288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651297 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2651297 : Nat := 118140960795 + 2651297 * 2 ^ 59
def prefixEnd_2651297 : Nat := 4983230072969 + 3 ^ 40 * 2651297 * 2
def baseEnd_2651297 : Nat := 1361389718823618521994413

theorem tailTrace_2651297 : CollatzResearch.WordTrace tailWord_2651297 prefixEnd_2651297 1361389718823618521994413 := by
  unfold tailWord_2651297
  simp only [CollatzResearch.WordTrace]
  refine ⟨96700745875811249323024145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64467163917207499548682763 96700745875811249323024145)
  ·
    refine ⟨72525559406858436992268109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96700745875811249323024145 72525559406858436992268109)
    ·
      refine ⟨27197084777571913872100541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72525559406858436992268109 27197084777571913872100541)
      ·
        refine ⟨10198906791589467702037703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27197084777571913872100541 10198906791589467702037703)
        ·
          refine ⟨15298360187384201553056555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10198906791589467702037703 15298360187384201553056555)
          ·
            refine ⟨22947540281076302329584833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15298360187384201553056555 22947540281076302329584833)
            ·
              refine ⟨17210655210807226747188625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22947540281076302329584833 17210655210807226747188625)
              ·
                refine ⟨12907991408105420060391469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17210655210807226747188625 12907991408105420060391469)
                ·
                  refine ⟨4840496778039532522646801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12907991408105420060391469 4840496778039532522646801)
                  ·
                    refine ⟨3630372583529649391985101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4840496778039532522646801 3630372583529649391985101)
                    ·
                      refine ⟨1361389718823618521994413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3630372583529649391985101 1361389718823618521994413)
                      ·
                        rfl

theorem cell23_2651297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2651297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651297 prefixEnd_2651297 := by exact prefixLift 2651297
  have htrace : WordTrace (prefixWord ++ tailWord_2651297) baseStart_2651297 baseEnd_2651297 := by
    simpa [prefixWord, tailWord_2651297, baseEnd_2651297] using wordTrace_append hprefix tailTrace_2651297
  have hstable : (prefixWord ++ tailWord_2651297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651297).length < 2 ^ (prefixWord ++ tailWord_2651297).sum := by decide
  have hdescent : baseEnd_2651297 < baseStart_2651297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651300 : List Nat := [2, 3, 1, 2, 3, 1, 1, 10]
def baseStart_2651300 : Nat := 118140960795 + 2651300 * 2 ^ 59
def prefixEnd_2651300 : Nat := 4983230072969 + 3 ^ 40 * 2651300 * 2
def baseEnd_2651300 : Nat := 50421898491317852231737

theorem tailTrace_2651300 : CollatzResearch.WordTrace tailWord_2651300 prefixEnd_2651300 50421898491317852231737 := by
  unfold tailWord_2651300
  simp only [CollatzResearch.WordTrace]
  refine ⟨48350427647400190417691677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64467236863200253890255569 48350427647400190417691677)
  ·
    refine ⟨18131410367775071406634379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48350427647400190417691677 18131410367775071406634379)
    ·
      refine ⟨27197115551662607109951569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18131410367775071406634379 27197115551662607109951569)
      ·
        refine ⟨20397836663746955332463677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27197115551662607109951569 20397836663746955332463677)
        ·
          refine ⟨7649188748905108249673879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20397836663746955332463677 7649188748905108249673879)
          ·
            refine ⟨11473783123357662374510819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7649188748905108249673879 11473783123357662374510819)
            ·
              refine ⟨17210674685036493561766229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11473783123357662374510819 17210674685036493561766229)
              ·
                refine ⟨50421898491317852231737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17210674685036493561766229 50421898491317852231737)
                ·
                  rfl

theorem cell23_2651300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 10].length) (baseStart_2651300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651300 prefixEnd_2651300 := by exact prefixLift 2651300
  have htrace : WordTrace (prefixWord ++ tailWord_2651300) baseStart_2651300 baseEnd_2651300 := by
    simpa [prefixWord, tailWord_2651300, baseEnd_2651300] using wordTrace_append hprefix tailTrace_2651300
  have hstable : (prefixWord ++ tailWord_2651300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651300).length < 2 ^ (prefixWord ++ tailWord_2651300).sum := by decide
  have hdescent : baseEnd_2651300 < baseStart_2651300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651314 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_2651314 : Nat := 118140960795 + 2651314 * 2 ^ 59
def prefixEnd_2651314 : Nat := 4983230072969 + 3 ^ 40 * 2651314 * 2
def baseEnd_2651314 : Nat := 1361398447994744955481835

theorem tailTrace_2651314 : CollatzResearch.WordTrace tailWord_2651314 prefixEnd_2651314 1361398447994744955481835 := by
  unfold tailWord_2651314
  simp only [CollatzResearch.WordTrace]
  refine ⟨24175341479187415306598249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64467577277833107484261997 24175341479187415306598249)
  ·
    refine ⟨18131506109390561479948687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24175341479187415306598249 18131506109390561479948687)
    ·
      refine ⟨27197259164085842219923031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18131506109390561479948687 27197259164085842219923031)
      ·
        refine ⟨40795888746128763329884547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27197259164085842219923031 40795888746128763329884547)
        ·
          refine ⟨61193833119193144994826821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40795888746128763329884547 61193833119193144994826821)
          ·
            refine ⟨11473843709848714686530029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61193833119193144994826821 11473843709848714686530029)
            ·
              refine ⟨4302691391193268007448761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11473843709848714686530029 4302691391193268007448761)
              ·
                refine ⟨3227018543394951005586571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4302691391193268007448761 3227018543394951005586571)
                ·
                  refine ⟨4840527815092426508379857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3227018543394951005586571 4840527815092426508379857)
                  ·
                    refine ⟨3630395861319319881284893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4840527815092426508379857 3630395861319319881284893)
                    ·
                      refine ⟨1361398447994744955481835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3630395861319319881284893 1361398447994744955481835)
                      ·
                        rfl

theorem cell23_2651314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_2651314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651314 prefixEnd_2651314 := by exact prefixLift 2651314
  have htrace : WordTrace (prefixWord ++ tailWord_2651314) baseStart_2651314 baseEnd_2651314 := by
    simpa [prefixWord, tailWord_2651314, baseEnd_2651314] using wordTrace_append hprefix tailTrace_2651314
  have hstable : (prefixWord ++ tailWord_2651314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651314).length < 2 ^ (prefixWord ++ tailWord_2651314).sum := by decide
  have hdescent : baseEnd_2651314 < baseStart_2651314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651327 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 6, 1, 3]
def baseStart_2651327 : Nat := 118140960795 + 2651327 * 2 ^ 59
def prefixEnd_2651327 : Nat := 4983230072969 + 3 ^ 40 * 2651327 * 2
def baseEnd_2651327 : Nat := 1361405123243253404619275

theorem tailTrace_2651327 : CollatzResearch.WordTrace tailWord_2651327 prefixEnd_2651327 1361405123243253404619275 := by
  unfold tailWord_2651327
  simp only [CollatzResearch.WordTrace]
  refine ⟨96701840065702564446616235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64467893377135042964410823 96701840065702564446616235)
  ·
    refine ⟨145052760098553846669924353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96701840065702564446616235 145052760098553846669924353)
    ·
      refine ⟨108789570073915385002443265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145052760098553846669924353 108789570073915385002443265)
      ·
        refine ⟨81592177555436538751832449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108789570073915385002443265 81592177555436538751832449)
        ·
          refine ⟨61194133166577404063874337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81592177555436538751832449 61194133166577404063874337)
          ·
            refine ⟨45895599874933053047905753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61194133166577404063874337 45895599874933053047905753)
            ·
              refine ⟨34421699906199789785929315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45895599874933053047905753 34421699906199789785929315)
              ·
                refine ⟨51632549859299684678893973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34421699906199789785929315 51632549859299684678893973)
                ·
                  refine ⟨2420275774654672719323155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51632549859299684678893973 2420275774654672719323155)
                  ·
                    refine ⟨3630413661982009078984733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2420275774654672719323155 3630413661982009078984733)
                    ·
                      refine ⟨1361405123243253404619275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3630413661982009078984733 1361405123243253404619275)
                      ·
                        rfl

theorem cell23_2651327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_2651327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651327 prefixEnd_2651327 := by exact prefixLift 2651327
  have htrace : WordTrace (prefixWord ++ tailWord_2651327) baseStart_2651327 baseEnd_2651327 := by
    simpa [prefixWord, tailWord_2651327, baseEnd_2651327] using wordTrace_append hprefix tailTrace_2651327
  have hstable : (prefixWord ++ tailWord_2651327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651327).length < 2 ^ (prefixWord ++ tailWord_2651327).sum := by decide
  have hdescent : baseEnd_2651327 < baseStart_2651327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651334 : List Nat := [6, 1, 2, 2, 12]
def baseStart_2651334 : Nat := 118140960795 + 2651334 * 2 ^ 59
def prefixEnd_2651334 : Nat := 4983230072969 + 3 ^ 40 * 2651334 * 2
def baseEnd_2651334 : Nat := 1867501670243943590167

theorem tailTrace_2651334 : CollatzResearch.WordTrace tailWord_2651334 prefixEnd_2651334 1867501670243943590167 := by
  unfold tailWord_2651334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3021940480521162645066283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64468063584451469761414037 3021940480521162645066283)
  ·
    refine ⟨4532910720781743967599425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3021940480521162645066283 4532910720781743967599425)
    ·
      refine ⟨3399683040586307975699569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4532910720781743967599425 3399683040586307975699569)
      ·
        refine ⟨2549762280439730981774677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3399683040586307975699569 2549762280439730981774677)
        ·
          refine ⟨1867501670243943590167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2549762280439730981774677 1867501670243943590167)
          ·
            rfl

theorem cell23_2651334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 12].length) (baseStart_2651334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651334 prefixEnd_2651334 := by exact prefixLift 2651334
  have htrace : WordTrace (prefixWord ++ tailWord_2651334) baseStart_2651334 baseEnd_2651334 := by
    simpa [prefixWord, tailWord_2651334, baseEnd_2651334] using wordTrace_append hprefix tailTrace_2651334
  have hstable : (prefixWord ++ tailWord_2651334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651334).length < 2 ^ (prefixWord ++ tailWord_2651334).sum := by decide
  have hdescent : baseEnd_2651334 < baseStart_2651334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651360 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 1, 8]
def baseStart_2651360 : Nat := 118140960795 + 2651360 * 2 ^ 59
def prefixEnd_2651360 : Nat := 4983230072969 + 3 ^ 40 * 2651360 * 2
def baseEnd_2651360 : Nat := 453807356034950591835541

theorem tailTrace_2651360 : CollatzResearch.WordTrace tailWord_2651360 prefixEnd_2651360 453807356034950591835541 := by
  unfold tailWord_2651360
  simp only [CollatzResearch.WordTrace]
  refine ⟨48351521837291505541283767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64468695783055340721711689 48351521837291505541283767)
  ·
    refine ⟨72527282755937258311925651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48351521837291505541283767 72527282755937258311925651)
    ·
      refine ⟨108790924133905887467888477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72527282755937258311925651 108790924133905887467888477)
      ·
        refine ⟨40796596550214707800458179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108790924133905887467888477 40796596550214707800458179)
        ·
          refine ⟨61194894825322061700687269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40796596550214707800458179 61194894825322061700687269)
          ·
            refine ⟨11474042779747886568878863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61194894825322061700687269 11474042779747886568878863)
            ·
              refine ⟨17211064169621829853318295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11474042779747886568878863 17211064169621829853318295)
              ·
                refine ⟨25816596254432744779977443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17211064169621829853318295 25816596254432744779977443)
                ·
                  refine ⟨38724894381649117169966165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25816596254432744779977443 38724894381649117169966165)
                  ·
                    refine ⟨453807356034950591835541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38724894381649117169966165 453807356034950591835541)
                    ·
                      rfl

theorem cell23_2651360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_2651360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651360 prefixEnd_2651360 := by exact prefixLift 2651360
  have htrace : WordTrace (prefixWord ++ tailWord_2651360) baseStart_2651360 baseEnd_2651360 := by
    simpa [prefixWord, tailWord_2651360, baseEnd_2651360] using wordTrace_append hprefix tailTrace_2651360
  have hstable : (prefixWord ++ tailWord_2651360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651360).length < 2 ^ (prefixWord ++ tailWord_2651360).sum := by decide
  have hdescent : baseEnd_2651360 < baseStart_2651360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651441 : List Nat := [1, 2, 2, 3, 3, 3, 1, 3, 5]
def baseStart_2651441 : Nat := 118140960795 + 2651441 * 2 ^ 59
def prefixEnd_2651441 : Nat := 4983230072969 + 3 ^ 40 * 2651441 * 2
def baseEnd_2651441 : Nat := 151273740004207328732639

theorem tailTrace_2651441 : CollatzResearch.WordTrace tailWord_2651441 prefixEnd_2651441 151273740004207328732639 := by
  unfold tailWord_2651441
  simp only [CollatzResearch.WordTrace]
  refine ⟨96705997987289561916266177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64470665324859707944177451 96705997987289561916266177)
  ·
    refine ⟨72529498490467171437199633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96705997987289561916266177 72529498490467171437199633)
    ·
      refine ⟨54397123867850378577899725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72529498490467171437199633 54397123867850378577899725)
      ·
        refine ⟨20398921450443891966712397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54397123867850378577899725 20398921450443891966712397)
        ·
          refine ⟨7649595543916459487517149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20398921450443891966712397 7649595543916459487517149)
          ·
            refine ⟨2868598328968672307818931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7649595543916459487517149 2868598328968672307818931)
            ·
              refine ⟨4302897493453008461728397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868598328968672307818931 4302897493453008461728397)
              ·
                refine ⟨1613586560044878173148149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4302897493453008461728397 1613586560044878173148149)
                ·
                  refine ⟨151273740004207328732639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1613586560044878173148149 151273740004207328732639)
                  ·
                    rfl

theorem cell23_2651441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 5].length) (baseStart_2651441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651441 prefixEnd_2651441 := by exact prefixLift 2651441
  have htrace : WordTrace (prefixWord ++ tailWord_2651441) baseStart_2651441 baseEnd_2651441 := by
    simpa [prefixWord, tailWord_2651441, baseEnd_2651441] using wordTrace_append hprefix tailTrace_2651441
  have hstable : (prefixWord ++ tailWord_2651441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651441).length < 2 ^ (prefixWord ++ tailWord_2651441).sum := by decide
  have hdescent : baseEnd_2651441 < baseStart_2651441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651454 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2651454 : Nat := 118140960795 + 2651454 * 2 ^ 59
def prefixEnd_2651454 : Nat := 4983230072969 + 3 ^ 40 * 2651454 * 2
def baseEnd_2651454 : Nat := 453823445095458135910397

theorem tailTrace_2651454 : CollatzResearch.WordTrace tailWord_2651454 prefixEnd_2651454 453823445095458135910397 := by
  unfold tailWord_2651454
  simp only [CollatzResearch.WordTrace]
  refine ⟨12088309017030308142061177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64470981424161643424326277 12088309017030308142061177)
  ·
    refine ⟨9066231762772731106545883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12088309017030308142061177 9066231762772731106545883)
    ·
      refine ⟨13599347644159096659818825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9066231762772731106545883 13599347644159096659818825)
      ·
        refine ⟨10199510733119322494864119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13599347644159096659818825 10199510733119322494864119)
        ·
          refine ⟨15299266099678983742296179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10199510733119322494864119 15299266099678983742296179)
          ·
            refine ⟨22948899149518475613444269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15299266099678983742296179 22948899149518475613444269)
            ·
              refine ⟨8605837181069428355041601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22948899149518475613444269 8605837181069428355041601)
              ·
                refine ⟨6454377885802071266281201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8605837181069428355041601 6454377885802071266281201)
                ·
                  refine ⟨4840783414351553449710901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6454377885802071266281201 4840783414351553449710901)
                  ·
                    refine ⟨453823445095458135910397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4840783414351553449710901 453823445095458135910397)
                    ·
                      rfl

theorem cell23_2651454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2651454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651454 prefixEnd_2651454 := by exact prefixLift 2651454
  have htrace : WordTrace (prefixWord ++ tailWord_2651454) baseStart_2651454 baseEnd_2651454 := by
    simpa [prefixWord, tailWord_2651454, baseEnd_2651454] using wordTrace_append hprefix tailTrace_2651454
  have hstable : (prefixWord ++ tailWord_2651454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651454).length < 2 ^ (prefixWord ++ tailWord_2651454).sum := by decide
  have hdescent : baseEnd_2651454 < baseStart_2651454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651469 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_2651469 : Nat := 118140960795 + 2651469 * 2 ^ 59
def prefixEnd_2651469 : Nat := 4983230072969 + 3 ^ 40 * 2651469 * 2
def baseEnd_2651469 : Nat := 1361478037496191849043623

theorem tailTrace_2651469 : CollatzResearch.WordTrace tailWord_2651469 prefixEnd_2651469 1361478037496191849043623 := by
  unfold tailWord_2651469
  simp only [CollatzResearch.WordTrace]
  refine ⟨96707019231188122698285461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64471346154125415132190307 96707019231188122698285461)
  ·
    refine ⟨4533141526461943251482131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96707019231188122698285461 4533141526461943251482131)
    ·
      refine ⟨6799712289692914877223197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4533141526461943251482131 6799712289692914877223197)
      ·
        refine ⟨2549892108634843078958699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6799712289692914877223197 2549892108634843078958699)
        ·
          refine ⟨3824838162952264618438049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2549892108634843078958699 3824838162952264618438049)
          ·
            refine ⟨2868628622214198463828537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3824838162952264618438049 2868628622214198463828537)
            ·
              refine ⟨2151471466660648847871403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2868628622214198463828537 2151471466660648847871403)
              ·
                refine ⟨3227207199990973271807105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151471466660648847871403 3227207199990973271807105)
                ·
                  refine ⟨2420405399993229953855329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3227207199990973271807105 2420405399993229953855329)
                  ·
                    refine ⟨1815304049994922465391497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2420405399993229953855329 1815304049994922465391497)
                    ·
                      refine ⟨1361478037496191849043623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815304049994922465391497 1361478037496191849043623)
                      ·
                        rfl

theorem cell23_2651469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_2651469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651469 prefixEnd_2651469 := by exact prefixLift 2651469
  have htrace : WordTrace (prefixWord ++ tailWord_2651469) baseStart_2651469 baseEnd_2651469 := by
    simpa [prefixWord, tailWord_2651469, baseEnd_2651469] using wordTrace_append hprefix tailTrace_2651469
  have hstable : (prefixWord ++ tailWord_2651469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651469).length < 2 ^ (prefixWord ++ tailWord_2651469).sum := by decide
  have hdescent : baseEnd_2651469 < baseStart_2651469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651474 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_2651474 : Nat := 118140960795 + 2651474 * 2 ^ 59
def prefixEnd_2651474 : Nat := 4983230072969 + 3 ^ 40 * 2651474 * 2
def baseEnd_2651474 : Nat := 1361480604899464329481099

theorem tailTrace_2651474 : CollatzResearch.WordTrace tailWord_2651474 prefixEnd_2651474 1361480604899464329481099 := by
  unfold tailWord_2651474
  simp only [CollatzResearch.WordTrace]
  refine ⟨24176800399042502138054369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64471467730780005701478317 24176800399042502138054369)
  ·
    refine ⟨18132600299281876603540777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24176800399042502138054369 18132600299281876603540777)
    ·
      refine ⟨13599450224461407452655583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18132600299281876603540777 13599450224461407452655583)
      ·
        refine ⟨20399175336692111178983375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13599450224461407452655583 20399175336692111178983375)
        ·
          refine ⟨30598763005038166768475063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20399175336692111178983375 30598763005038166768475063)
          ·
            refine ⟨45898144507557250152712595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30598763005038166768475063 45898144507557250152712595)
            ·
              refine ⟨68847216761335875229068893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45898144507557250152712595 68847216761335875229068893)
              ·
                refine ⟨25817706285500953210900835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68847216761335875229068893 25817706285500953210900835)
                ·
                  refine ⟨38726559428251429816351253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25817706285500953210900835 38726559428251429816351253)
                  ·
                    refine ⟨1815307473199285772641465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38726559428251429816351253 1815307473199285772641465)
                    ·
                      refine ⟨1361480604899464329481099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815307473199285772641465 1361480604899464329481099)
                      ·
                        rfl

theorem cell23_2651474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_2651474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651474 prefixEnd_2651474 := by exact prefixLift 2651474
  have htrace : WordTrace (prefixWord ++ tailWord_2651474) baseStart_2651474 baseEnd_2651474 := by
    simpa [prefixWord, tailWord_2651474, baseEnd_2651474] using wordTrace_append hprefix tailTrace_2651474
  have hstable : (prefixWord ++ tailWord_2651474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651474).length < 2 ^ (prefixWord ++ tailWord_2651474).sum := by decide
  have hdescent : baseEnd_2651474 < baseStart_2651474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651517 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_2651517 : Nat := 118140960795 + 2651517 * 2 ^ 59
def prefixEnd_2651517 : Nat := 4983230072969 + 3 ^ 40 * 2651517 * 2
def baseEnd_2651517 : Nat := 1361502684567607661243401

theorem tailTrace_2651517 : CollatzResearch.WordTrace tailWord_2651517 prefixEnd_2651517 1361502684567607661243401 := by
  unfold tailWord_2651517
  simp only [CollatzResearch.WordTrace]
  refine ⟨96708769935014226896032805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64472513290009484597355203 96708769935014226896032805)
  ·
    refine ⟨18132894362815167543006151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96708769935014226896032805 18132894362815167543006151)
    ·
      refine ⟨27199341544222751314509227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18132894362815167543006151 27199341544222751314509227)
      ·
        refine ⟨40799012316334126971763841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27199341544222751314509227 40799012316334126971763841)
        ·
          refine ⟨30599259237250595228822881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40799012316334126971763841 30599259237250595228822881)
          ·
            refine ⟨22949444427937946421617161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30599259237250595228822881 22949444427937946421617161)
            ·
              refine ⟨17212083320953459816212871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22949444427937946421617161 17212083320953459816212871)
              ·
                refine ⟨25818124981430189724319307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17212083320953459816212871 25818124981430189724319307)
                ·
                  refine ⟨38727187472145284586478961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25818124981430189724319307 38727187472145284586478961)
                  ·
                    refine ⟨29045390604108963439859221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38727187472145284586478961 29045390604108963439859221)
                    ·
                      refine ⟨1361502684567607661243401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29045390604108963439859221 1361502684567607661243401)
                      ·
                        rfl

theorem cell23_2651517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_2651517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651517 prefixEnd_2651517 := by exact prefixLift 2651517
  have htrace : WordTrace (prefixWord ++ tailWord_2651517) baseStart_2651517 baseEnd_2651517 := by
    simpa [prefixWord, tailWord_2651517, baseEnd_2651517] using wordTrace_append hprefix tailTrace_2651517
  have hstable : (prefixWord ++ tailWord_2651517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651517).length < 2 ^ (prefixWord ++ tailWord_2651517).sum := by decide
  have hdescent : baseEnd_2651517 < baseStart_2651517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651551 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 1, 5, 2]
def baseStart_2651551 : Nat := 118140960795 + 2651551 * 2 ^ 59
def prefixEnd_2651551 : Nat := 4983230072969 + 3 ^ 40 * 2651551 * 2
def baseEnd_2651551 : Nat := 1361520142909860528218245

theorem tailTrace_2651551 : CollatzResearch.WordTrace tailWord_2651551 prefixEnd_2651551 1361520142909860528218245 := by
  unfold tailWord_2651551
  simp only [CollatzResearch.WordTrace]
  refine ⟨96710010016891050702770507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64473340011260700468513671 96710010016891050702770507)
  ·
    refine ⟨145065015025336576054155761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96710010016891050702770507 145065015025336576054155761)
    ·
      refine ⟨108798761269002432040616821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145065015025336576054155761 108798761269002432040616821)
      ·
        refine ⟨10199883868968978003807827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108798761269002432040616821 10199883868968978003807827)
        ·
          refine ⟨15299825803453467005711741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10199883868968978003807827 15299825803453467005711741)
          ·
            refine ⟨5737434676295050127141903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15299825803453467005711741 5737434676295050127141903)
            ·
              refine ⟨8606152014442575190712855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737434676295050127141903 8606152014442575190712855)
              ·
                refine ⟨12909228021663862786069283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8606152014442575190712855 12909228021663862786069283)
                ·
                  refine ⟨19363842032495794179103925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12909228021663862786069283 19363842032495794179103925)
                  ·
                    refine ⟨1815360190546480704290993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19363842032495794179103925 1815360190546480704290993)
                    ·
                      refine ⟨1361520142909860528218245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815360190546480704290993 1361520142909860528218245)
                      ·
                        rfl

theorem cell23_2651551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_2651551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651551 prefixEnd_2651551 := by exact prefixLift 2651551
  have htrace : WordTrace (prefixWord ++ tailWord_2651551) baseStart_2651551 baseEnd_2651551 := by
    simpa [prefixWord, tailWord_2651551, baseEnd_2651551] using wordTrace_append hprefix tailTrace_2651551
  have hstable : (prefixWord ++ tailWord_2651551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651551).length < 2 ^ (prefixWord ++ tailWord_2651551).sum := by decide
  have hdescent : baseEnd_2651551 < baseStart_2651551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651557 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_2651557 : Nat := 118140960795 + 2651557 * 2 ^ 59
def prefixEnd_2651557 : Nat := 4983230072969 + 3 ^ 40 * 2651557 * 2
def baseEnd_2651557 : Nat := 453841074597929168247739

theorem tailTrace_2651557 : CollatzResearch.WordTrace tailWord_2651557 prefixEnd_2651557 453841074597929168247739 := by
  unfold tailWord_2651557
  simp only [CollatzResearch.WordTrace]
  refine ⟨96710228854869313727488925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64473485903246209151659283 96710228854869313727488925)
  ·
    refine ⟨36266335820575992647808347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96710228854869313727488925 36266335820575992647808347)
    ·
      refine ⟨54399503730863988971712521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36266335820575992647808347 54399503730863988971712521)
      ·
        refine ⟨40799627798147991728784391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54399503730863988971712521 40799627798147991728784391)
        ·
          refine ⟨61199441697221987593176587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40799627798147991728784391 61199441697221987593176587)
          ·
            refine ⟨91799162545832981389764881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61199441697221987593176587 91799162545832981389764881)
            ·
              refine ⟨68849371909374736042323661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91799162545832981389764881 68849371909374736042323661)
              ·
                refine ⟨25818514466015526015871373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68849371909374736042323661 25818514466015526015871373)
                ·
                  refine ⟨9681942924755822255951765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25818514466015526015871373 9681942924755822255951765)
                  ·
                    refine ⟨453841074597929168247739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9681942924755822255951765 453841074597929168247739)
                    ·
                      rfl

theorem cell23_2651557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_2651557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651557 prefixEnd_2651557 := by exact prefixLift 2651557
  have htrace : WordTrace (prefixWord ++ tailWord_2651557) baseStart_2651557 baseEnd_2651557 := by
    simpa [prefixWord, tailWord_2651557, baseEnd_2651557] using wordTrace_append hprefix tailTrace_2651557
  have hstable : (prefixWord ++ tailWord_2651557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651557).length < 2 ^ (prefixWord ++ tailWord_2651557).sum := by decide
  have hdescent : baseEnd_2651557 < baseStart_2651557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651567 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 5]
def baseStart_2651567 : Nat := 118140960795 + 2651567 * 2 ^ 59
def prefixEnd_2651567 : Nat := 4983230072969 + 3 ^ 40 * 2651567 * 2
def baseEnd_2651567 : Nat := 1361528358600332465618171

theorem tailTrace_2651567 : CollatzResearch.WordTrace tailWord_2651567 prefixEnd_2651567 1361528358600332465618171 := by
  unfold tailWord_2651567
  simp only [CollatzResearch.WordTrace]
  refine ⟨96710593584833085435352955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64473729056555390290235303 96710593584833085435352955)
  ·
    refine ⟨145065890377249628153029433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96710593584833085435352955 145065890377249628153029433)
    ·
      refine ⟨108799417782937221114772075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145065890377249628153029433 108799417782937221114772075)
      ·
        refine ⟨163199126674405831672158113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108799417782937221114772075 163199126674405831672158113)
        ·
          refine ⟨122399345005804373754118585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163199126674405831672158113 122399345005804373754118585)
          ·
            refine ⟨91799508754353280315588939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122399345005804373754118585 91799508754353280315588939)
            ·
              refine ⟨137699263131529920473383409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91799508754353280315588939 137699263131529920473383409)
              ·
                refine ⟨103274447348647440355037557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137699263131529920473383409 103274447348647440355037557)
                ·
                  refine ⟨9681979438935697533284771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103274447348647440355037557 9681979438935697533284771)
                  ·
                    refine ⟨14522969158403546299927157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9681979438935697533284771 14522969158403546299927157)
                    ·
                      refine ⟨1361528358600332465618171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14522969158403546299927157 1361528358600332465618171)
                      ·
                        rfl

theorem cell23_2651567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_2651567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651567 prefixEnd_2651567 := by exact prefixLift 2651567
  have htrace : WordTrace (prefixWord ++ tailWord_2651567) baseStart_2651567 baseEnd_2651567 := by
    simpa [prefixWord, tailWord_2651567, baseEnd_2651567] using wordTrace_append hprefix tailTrace_2651567
  have hstable : (prefixWord ++ tailWord_2651567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651567).length < 2 ^ (prefixWord ++ tailWord_2651567).sum := by decide
  have hdescent : baseEnd_2651567 < baseStart_2651567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651584 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 3]
def baseStart_2651584 : Nat := 118140960795 + 2651584 * 2 ^ 59
def prefixEnd_2651584 : Nat := 4983230072969 + 3 ^ 40 * 2651584 * 2
def baseEnd_2651584 : Nat := 1361537087771458899105593

theorem tailTrace_2651584 : CollatzResearch.WordTrace tailWord_2651584 prefixEnd_2651584 1361537087771458899105593 := by
  unfold tailWord_2651584
  simp only [CollatzResearch.WordTrace]
  refine ⟨48355606812885748669360903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64474142417180998225814537 48355606812885748669360903)
  ·
    refine ⟨72533410219328623004041355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48355606812885748669360903 72533410219328623004041355)
    ·
      refine ⟨108800115328992934506062033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72533410219328623004041355 108800115328992934506062033)
      ·
        refine ⟨81600086496744700879546525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108800115328992934506062033 81600086496744700879546525)
        ·
          refine ⟨30600032436279262829829947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81600086496744700879546525 30600032436279262829829947)
          ·
            refine ⟨45900048654418894244744921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30600032436279262829829947 45900048654418894244744921)
            ·
              refine ⟨34425036490814170683558691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45900048654418894244744921 34425036490814170683558691)
              ·
                refine ⟨51637554736221256025338037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34425036490814170683558691 51637554736221256025338037)
                ·
                  refine ⟨4841020756520742752375441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51637554736221256025338037 4841020756520742752375441)
                  ·
                    refine ⟨3630765567390557064281581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4841020756520742752375441 3630765567390557064281581)
                    ·
                      refine ⟨1361537087771458899105593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3630765567390557064281581 1361537087771458899105593)
                      ·
                        rfl

theorem cell23_2651584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_2651584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651584 prefixEnd_2651584 := by exact prefixLift 2651584
  have htrace : WordTrace (prefixWord ++ tailWord_2651584) baseStart_2651584 baseEnd_2651584 := by
    simpa [prefixWord, tailWord_2651584, baseEnd_2651584] using wordTrace_append hprefix tailTrace_2651584
  have hstable : (prefixWord ++ tailWord_2651584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651584).length < 2 ^ (prefixWord ++ tailWord_2651584).sum := by decide
  have hdescent : baseEnd_2651584 < baseStart_2651584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651594 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_2651594 : Nat := 118140960795 + 2651594 * 2 ^ 59
def prefixEnd_2651594 : Nat := 4983230072969 + 3 ^ 40 * 2651594 * 2
def baseEnd_2651594 : Nat := 1361542222578003859980547

theorem tailTrace_2651594 : CollatzResearch.WordTrace tailWord_2651594 prefixEnd_2651594 1361542222578003859980547 := by
  unfold tailWord_2651594
  simp only [CollatzResearch.WordTrace]
  refine ⟨24177894588933817261646459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64474385570490179364390557 24177894588933817261646459)
  ·
    refine ⟨36266841883400725892469689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24177894588933817261646459 36266841883400725892469689)
    ·
      refine ⟨27200131412550544419352267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36266841883400725892469689 27200131412550544419352267)
      ·
        refine ⟨40800197118825816629028401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27200131412550544419352267 40800197118825816629028401)
        ·
          refine ⟨30600147839119362471771301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40800197118825816629028401 30600147839119362471771301)
          ·
            refine ⟨5737527719834880463457119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30600147839119362471771301 5737527719834880463457119)
            ·
              refine ⟨8606291579752320695185679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737527719834880463457119 8606291579752320695185679)
              ·
                refine ⟨12909437369628481042778519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8606291579752320695185679 12909437369628481042778519)
                ·
                  refine ⟨19364156054442721564167779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12909437369628481042778519 19364156054442721564167779)
                  ·
                    refine ⟨29046234081664082346251669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19364156054442721564167779 29046234081664082346251669)
                    ·
                      refine ⟨1361542222578003859980547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29046234081664082346251669 1361542222578003859980547)
                      ·
                        rfl

theorem cell23_2651594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_2651594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651594 prefixEnd_2651594 := by exact prefixLift 2651594
  have htrace : WordTrace (prefixWord ++ tailWord_2651594) baseStart_2651594 baseEnd_2651594 := by
    simpa [prefixWord, tailWord_2651594, baseEnd_2651594] using wordTrace_append hprefix tailTrace_2651594
  have hstable : (prefixWord ++ tailWord_2651594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651594).length < 2 ^ (prefixWord ++ tailWord_2651594).sum := by decide
  have hdescent : baseEnd_2651594 < baseStart_2651594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651598 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2]
def baseStart_2651598 : Nat := 118140960795 + 2651598 * 2 ^ 59
def prefixEnd_2651598 : Nat := 4983230072969 + 3 ^ 40 * 2651598 * 2
def baseEnd_2651598 : Nat := 1361544276500621844330529

theorem tailTrace_2651598 : CollatzResearch.WordTrace tailWord_2651598 prefixEnd_2651598 1361544276500621844330529 := by
  unfold tailWord_2651598
  simp only [CollatzResearch.WordTrace]
  refine ⟨12088965530965097216216431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64474482831813851819820965 12088965530965097216216431)
  ·
    refine ⟨18133448296447645824324647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12088965530965097216216431 18133448296447645824324647)
    ·
      refine ⟨27200172444671468736486971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18133448296447645824324647 27200172444671468736486971)
      ·
        refine ⟨40800258667007203104730457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27200172444671468736486971 40800258667007203104730457)
        ·
          refine ⟨30600194000255402328547843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40800258667007203104730457 30600194000255402328547843)
          ·
            refine ⟨45900291000383103492821765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30600194000255402328547843 45900291000383103492821765)
            ·
              refine ⟨8606304562571831904904081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45900291000383103492821765 8606304562571831904904081)
              ·
                refine ⟨6454728421928873928678061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8606304562571831904904081 6454728421928873928678061)
                ·
                  refine ⟨2420523158223327723254273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6454728421928873928678061 2420523158223327723254273)
                  ·
                    refine ⟨1815392368667495792440705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2420523158223327723254273 1815392368667495792440705)
                    ·
                      refine ⟨1361544276500621844330529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815392368667495792440705 1361544276500621844330529)
                      ·
                        rfl

theorem cell23_2651598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_2651598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651598 prefixEnd_2651598 := by exact prefixLift 2651598
  have htrace : WordTrace (prefixWord ++ tailWord_2651598) baseStart_2651598 baseEnd_2651598 := by
    simpa [prefixWord, tailWord_2651598, baseEnd_2651598] using wordTrace_append hprefix tailTrace_2651598
  have hstable : (prefixWord ++ tailWord_2651598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651598).length < 2 ^ (prefixWord ++ tailWord_2651598).sum := by decide
  have hdescent : baseEnd_2651598 < baseStart_2651598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651607 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_2651607 : Nat := 118140960795 + 2651607 * 2 ^ 59
def prefixEnd_2651607 : Nat := 4983230072969 + 3 ^ 40 * 2651607 * 2
def baseEnd_2651607 : Nat := 1361548897826512309117987

theorem tailTrace_2651607 : CollatzResearch.WordTrace tailWord_2651607 prefixEnd_2651607 1361548897826512309117987 := by
  unfold tailWord_2651607
  simp only [CollatzResearch.WordTrace]
  refine ⟨96712052504688172266809075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64474701669792114844539383 96712052504688172266809075)
  ·
    refine ⟨145068078757032258400213613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96712052504688172266809075 145068078757032258400213613)
    ·
      refine ⟨54400529533887096900080105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145068078757032258400213613 54400529533887096900080105)
      ·
        refine ⟨40800397150415322675060079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54400529533887096900080105 40800397150415322675060079)
        ·
          refine ⟨61200595725622984012590119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40800397150415322675060079 61200595725622984012590119)
          ·
            refine ⟨91800893588434476018885179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61200595725622984012590119 91800893588434476018885179)
            ·
              refine ⟨137701340382651714028327769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91800893588434476018885179 137701340382651714028327769)
              ·
                refine ⟨103276005286988785521245827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137701340382651714028327769 103276005286988785521245827)
                ·
                  refine ⟨154914007930483178281868741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103276005286988785521245827 154914007930483178281868741)
                  ·
                    refine ⟨29046376486965595927850389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154914007930483178281868741 29046376486965595927850389)
                    ·
                      refine ⟨1361548897826512309117987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29046376486965595927850389 1361548897826512309117987)
                      ·
                        rfl

theorem cell23_2651607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_2651607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651607 prefixEnd_2651607 := by exact prefixLift 2651607
  have htrace : WordTrace (prefixWord ++ tailWord_2651607) baseStart_2651607 baseEnd_2651607 := by
    simpa [prefixWord, tailWord_2651607, baseEnd_2651607] using wordTrace_append hprefix tailTrace_2651607
  have hstable : (prefixWord ++ tailWord_2651607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651607).length < 2 ^ (prefixWord ++ tailWord_2651607).sum := by decide
  have hdescent : baseEnd_2651607 < baseStart_2651607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651631 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 4, 1, 3]
def baseStart_2651631 : Nat := 118140960795 + 2651631 * 2 ^ 59
def prefixEnd_2651631 : Nat := 4983230072969 + 3 ^ 40 * 2651631 * 2
def baseEnd_2651631 : Nat := 1361561221362220215217877

theorem tailTrace_2651631 : CollatzResearch.WordTrace tailWord_2651631 prefixEnd_2651631 1361561221362220215217877 := by
  unfold tailWord_2651631
  simp only [CollatzResearch.WordTrace]
  refine ⟨96712927856601224365682747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64475285237734149577121831 96712927856601224365682747)
  ·
    refine ⟨145069391784901836548524121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96712927856601224365682747 145069391784901836548524121)
    ·
      refine ⟨108802043838676377411393091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145069391784901836548524121 108802043838676377411393091)
      ·
        refine ⟨163203065758014566117089637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108802043838676377411393091 163203065758014566117089637)
        ·
          refine ⟨30600574829627731146954307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163203065758014566117089637 30600574829627731146954307)
          ·
            refine ⟨45900862244441596720431461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30600574829627731146954307 45900862244441596720431461)
            ·
              refine ⟨8606411670832799385080899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45900862244441596720431461 8606411670832799385080899)
              ·
                refine ⟨12909617506249199077621349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8606411670832799385080899 12909617506249199077621349)
                ·
                  refine ⟨2420553282421724827054003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12909617506249199077621349 2420553282421724827054003)
                  ·
                    refine ⟨3630829923632587240581005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2420553282421724827054003 3630829923632587240581005)
                    ·
                      refine ⟨1361561221362220215217877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3630829923632587240581005 1361561221362220215217877)
                      ·
                        rfl

theorem cell23_2651631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 1, 3].length) (baseStart_2651631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651631 prefixEnd_2651631 := by exact prefixLift 2651631
  have htrace : WordTrace (prefixWord ++ tailWord_2651631) baseStart_2651631 baseEnd_2651631 := by
    simpa [prefixWord, tailWord_2651631, baseEnd_2651631] using wordTrace_append hprefix tailTrace_2651631
  have hstable : (prefixWord ++ tailWord_2651631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651631).length < 2 ^ (prefixWord ++ tailWord_2651631).sum := by decide
  have hdescent : baseEnd_2651631 < baseStart_2651631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651632 : List Nat := [2, 1, 1, 1, 3, 5, 3, 2, 1, 2, 2]
def baseStart_2651632 : Nat := 118140960795 + 2651632 * 2 ^ 59
def prefixEnd_2651632 : Nat := 4983230072969 + 3 ^ 40 * 2651632 * 2
def baseEnd_2651632 : Nat := 1361561734842874711305373

theorem tailTrace_2651632 : CollatzResearch.WordTrace tailWord_2651632 prefixEnd_2651632 1361561734842874711305373 := by
  unfold tailWord_2651632
  simp only [CollatzResearch.WordTrace]
  refine ⟨48356482164798800768234575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64475309553065067690979433 48356482164798800768234575)
  ·
    refine ⟨72534723247198201152351863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48356482164798800768234575 72534723247198201152351863)
    ·
      refine ⟨108802084870797301728527795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72534723247198201152351863 108802084870797301728527795)
      ·
        refine ⟨163203127306195952592791693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108802084870797301728527795 163203127306195952592791693)
        ·
          refine ⟨61201172739823482222296885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163203127306195952592791693 61201172739823482222296885)
          ·
            refine ⟨5737609944358451458340333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61201172739823482222296885 5737609944358451458340333)
            ·
              refine ⟨2151603729134419296877625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5737609944358451458340333 2151603729134419296877625)
              ·
                refine ⟨1613702796850814472658219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151603729134419296877625 1613702796850814472658219)
                ·
                  refine ⟨2420554195276221708987329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613702796850814472658219 2420554195276221708987329)
                  ·
                    refine ⟨1815415646457166281740497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2420554195276221708987329 1815415646457166281740497)
                    ·
                      refine ⟨1361561734842874711305373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815415646457166281740497 1361561734842874711305373)
                      ·
                        rfl

theorem cell23_2651632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 1, 2, 2].length) (baseStart_2651632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651632 prefixEnd_2651632 := by exact prefixLift 2651632
  have htrace : WordTrace (prefixWord ++ tailWord_2651632) baseStart_2651632 baseEnd_2651632 := by
    simpa [prefixWord, tailWord_2651632, baseEnd_2651632] using wordTrace_append hprefix tailTrace_2651632
  have hstable : (prefixWord ++ tailWord_2651632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651632).length < 2 ^ (prefixWord ++ tailWord_2651632).sum := by decide
  have hdescent : baseEnd_2651632 < baseStart_2651632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651641 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 3, 3, 2]
def baseStart_2651641 : Nat := 118140960795 + 2651641 * 2 ^ 59
def prefixEnd_2651641 : Nat := 4983230072969 + 3 ^ 40 * 2651641 * 2
def baseEnd_2651641 : Nat := 1361566356168765176092831

theorem tailTrace_2651641 : CollatzResearch.WordTrace tailWord_2651641 prefixEnd_2651641 1361566356168765176092831 := by
  unfold tailWord_2651641
  simp only [CollatzResearch.WordTrace]
  refine ⟨96713292586564996073546777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64475528391043330715697851 96713292586564996073546777)
  ·
    refine ⟨72534969439923747055160083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96713292586564996073546777 72534969439923747055160083)
    ·
      refine ⟨108802454159885620582740125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72534969439923747055160083 108802454159885620582740125)
      ·
        refine ⟨40800920309957107718527547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108802454159885620582740125 40800920309957107718527547)
        ·
          refine ⟨61201380464935661577791321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40800920309957107718527547 61201380464935661577791321)
          ·
            refine ⟨45901035348701746183343491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61201380464935661577791321 45901035348701746183343491)
            ·
              refine ⟨68851553023052619275015237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45901035348701746183343491 68851553023052619275015237)
              ·
                refine ⟨12909666191822366114065357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68851553023052619275015237 12909666191822366114065357)
                ·
                  refine ⟨4841124821933387292774509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12909666191822366114065357 4841124821933387292774509)
                  ·
                    refine ⟨1815421808225020234790441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4841124821933387292774509 1815421808225020234790441)
                    ·
                      refine ⟨1361566356168765176092831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815421808225020234790441 1361566356168765176092831)
                      ·
                        rfl

theorem cell23_2651641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_2651641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651641 prefixEnd_2651641 := by exact prefixLift 2651641
  have htrace : WordTrace (prefixWord ++ tailWord_2651641) baseStart_2651641 baseEnd_2651641 := by
    simpa [prefixWord, tailWord_2651641, baseEnd_2651641] using wordTrace_append hprefix tailTrace_2651641
  have hstable : (prefixWord ++ tailWord_2651641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651641).length < 2 ^ (prefixWord ++ tailWord_2651641).sum := by decide
  have hdescent : baseEnd_2651641 < baseStart_2651641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651652 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_2651652 : Nat := 118140960795 + 2651652 * 2 ^ 59
def prefixEnd_2651652 : Nat := 4983230072969 + 3 ^ 40 * 2651652 * 2
def baseEnd_2651652 : Nat := 1361572004455964633055281

theorem tailTrace_2651652 : CollatzResearch.WordTrace tailWord_2651652 prefixEnd_2651652 1361572004455964633055281 := by
  unfold tailWord_2651652
  simp only [CollatzResearch.WordTrace]
  refine ⟨48356846894762572476098605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64475795859683429968131473 48356846894762572476098605)
  ·
    refine ⟨18133817585535964678536977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48356846894762572476098605 18133817585535964678536977)
    ·
      refine ⟨13600363189151973508902733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18133817585535964678536977 13600363189151973508902733)
      ·
        refine ⟨5100136195931990065838525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13600363189151973508902733 5100136195931990065838525)
        ·
          refine ⟨1912551073474496274689447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5100136195931990065838525 1912551073474496274689447)
          ·
            refine ⟨2868826610211744412034171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912551073474496274689447 2868826610211744412034171)
            ·
              refine ⟨4303239915317616618051257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868826610211744412034171 4303239915317616618051257)
              ·
                refine ⟨3227429936488212463538443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4303239915317616618051257 3227429936488212463538443)
                ·
                  refine ⟨4841144904732318695307665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3227429936488212463538443 4841144904732318695307665)
                  ·
                    refine ⟨3630858678549239021480749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4841144904732318695307665 3630858678549239021480749)
                    ·
                      refine ⟨1361572004455964633055281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3630858678549239021480749 1361572004455964633055281)
                      ·
                        rfl

theorem cell23_2651652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_2651652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651652 prefixEnd_2651652 := by exact prefixLift 2651652
  have htrace : WordTrace (prefixWord ++ tailWord_2651652) baseStart_2651652 baseEnd_2651652 := by
    simpa [prefixWord, tailWord_2651652, baseEnd_2651652] using wordTrace_append hprefix tailTrace_2651652
  have hstable : (prefixWord ++ tailWord_2651652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651652).length < 2 ^ (prefixWord ++ tailWord_2651652).sum := by decide
  have hdescent : baseEnd_2651652 < baseStart_2651652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651658 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2]
def baseStart_2651658 : Nat := 118140960795 + 2651658 * 2 ^ 59
def prefixEnd_2651658 : Nat := 4983230072969 + 3 ^ 40 * 2651658 * 2
def baseEnd_2651658 : Nat := 1361575085339891609580253

theorem tailTrace_2651658 : CollatzResearch.WordTrace tailWord_2651658 prefixEnd_2651658 1361575085339891609580253 := by
  unfold tailWord_2651658
  simp only [CollatzResearch.WordTrace]
  refine ⟨24178478156875851994228907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64475941751668938651277085 24178478156875851994228907)
  ·
    refine ⟨36267717235313777991343361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24178478156875851994228907 36267717235313777991343361)
    ·
      refine ⟨27200787926485333493507521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36267717235313777991343361 27200787926485333493507521)
      ·
        refine ⟨20400590944864000120130641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27200787926485333493507521 20400590944864000120130641)
        ·
          refine ⟨15300443208648000090097981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20400590944864000120130641 15300443208648000090097981)
          ·
            refine ⟨5737666203243000033786743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15300443208648000090097981 5737666203243000033786743)
            ·
              refine ⟨8606499304864500050680115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737666203243000033786743 8606499304864500050680115)
              ·
                refine ⟨12909748957296750076020173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8606499304864500050680115 12909748957296750076020173)
                ·
                  refine ⟨4841155858986281278507565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12909748957296750076020173 4841155858986281278507565)
                  ·
                    refine ⟨1815433447119855479440337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4841155858986281278507565 1815433447119855479440337)
                    ·
                      refine ⟨1361575085339891609580253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815433447119855479440337 1361575085339891609580253)
                      ·
                        rfl

theorem cell23_2651658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_2651658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651658 prefixEnd_2651658 := by exact prefixLift 2651658
  have htrace : WordTrace (prefixWord ++ tailWord_2651658) baseStart_2651658 baseEnd_2651658 := by
    simpa [prefixWord, tailWord_2651658, baseEnd_2651658] using wordTrace_append hprefix tailTrace_2651658
  have hstable : (prefixWord ++ tailWord_2651658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651658).length < 2 ^ (prefixWord ++ tailWord_2651658).sum := by decide
  have hdescent : baseEnd_2651658 < baseStart_2651658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651701 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_2651701 : Nat := 118140960795 + 2651701 * 2 ^ 59
def prefixEnd_2651701 : Nat := 4983230072969 + 3 ^ 40 * 2651701 * 2
def baseEnd_2651701 : Nat := 1361597165008034941342555

theorem tailTrace_2651701 : CollatzResearch.WordTrace tailWord_2651701 prefixEnd_2651701 1361597165008034941342555 := by
  unfold tailWord_2651701
  simp only [CollatzResearch.WordTrace]
  refine ⟨96715480966347626320730957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64476987310898417547153971 96715480966347626320730957)
  ·
    refine ⟨36268305362380359870274109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96715480966347626320730957 36268305362380359870274109)
    ·
      refine ⟨13600614510892634951352791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36268305362380359870274109 13600614510892634951352791)
      ·
        refine ⟨20400921766338952427029187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13600614510892634951352791 20400921766338952427029187)
        ·
          refine ⟨30601382649508428640543781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20400921766338952427029187 30601382649508428640543781)
          ·
            refine ⟨5737759246782830370101959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30601382649508428640543781 5737759246782830370101959)
            ·
              refine ⟨8606638870174245555152939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737759246782830370101959 8606638870174245555152939)
              ·
                refine ⟨12909958305261368332729409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8606638870174245555152939 12909958305261368332729409)
                ·
                  refine ⟨9682468728946026249547057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12909958305261368332729409 9682468728946026249547057)
                  ·
                    refine ⟨7261851546709519687160293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9682468728946026249547057 7261851546709519687160293)
                    ·
                      refine ⟨1361597165008034941342555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7261851546709519687160293 1361597165008034941342555)
                      ·
                        rfl

theorem cell23_2651701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_2651701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651701 prefixEnd_2651701 := by exact prefixLift 2651701
  have htrace : WordTrace (prefixWord ++ tailWord_2651701) baseStart_2651701 baseEnd_2651701 := by
    simpa [prefixWord, tailWord_2651701, baseEnd_2651701] using wordTrace_append hprefix tailTrace_2651701
  have hstable : (prefixWord ++ tailWord_2651701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651701).length < 2 ^ (prefixWord ++ tailWord_2651701).sum := by decide
  have hdescent : baseEnd_2651701 < baseStart_2651701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651705 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 2, 2, 2]
def baseStart_2651705 : Nat := 118140960795 + 2651705 * 2 ^ 59
def prefixEnd_2651705 : Nat := 4983230072969 + 3 ^ 40 * 2651705 * 2
def baseEnd_2651705 : Nat := 1361599218930652925692537

theorem tailTrace_2651705 : CollatzResearch.WordTrace tailWord_2651705 prefixEnd_2651705 1361599218930652925692537 := by
  unfold tailWord_2651705
  simp only [CollatzResearch.WordTrace]
  refine ⟨96715626858333135003876569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64477084572222090002584379 96715626858333135003876569)
  ·
    refine ⟨72536720143749851252907427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96715626858333135003876569 72536720143749851252907427)
    ·
      refine ⟨108805080215624776879361141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72536720143749851252907427 108805080215624776879361141)
      ·
        refine ⟨10200476270214822832440107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108805080215624776879361141 10200476270214822832440107)
        ·
          refine ⟨15300714405322234248660161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10200476270214822832440107 15300714405322234248660161)
          ·
            refine ⟨11475535803991675686495121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15300714405322234248660161 11475535803991675686495121)
            ·
              refine ⟨8606651852993756764871341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11475535803991675686495121 8606651852993756764871341)
              ·
                refine ⟨3227494444872658786826753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8606651852993756764871341 3227494444872658786826753)
                ·
                  refine ⟨2420620833654494090120065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3227494444872658786826753 2420620833654494090120065)
                  ·
                    refine ⟨1815465625240870567590049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2420620833654494090120065 1815465625240870567590049)
                    ·
                      refine ⟨1361599218930652925692537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815465625240870567590049 1361599218930652925692537)
                      ·
                        rfl

theorem cell23_2651705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_2651705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651705 prefixEnd_2651705 := by exact prefixLift 2651705
  have htrace : WordTrace (prefixWord ++ tailWord_2651705) baseStart_2651705 baseEnd_2651705 := by
    simpa [prefixWord, tailWord_2651705, baseEnd_2651705] using wordTrace_append hprefix tailTrace_2651705
  have hstable : (prefixWord ++ tailWord_2651705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651705).length < 2 ^ (prefixWord ++ tailWord_2651705).sum := by decide
  have hdescent : baseEnd_2651705 < baseStart_2651705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651771 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 3, 4]
def baseStart_2651771 : Nat := 118140960795 + 2651771 * 2 ^ 59
def prefixEnd_2651771 : Nat := 4983230072969 + 3 ^ 40 * 2651771 * 2
def baseEnd_2651771 : Nat := 453877702884616555822411

theorem tailTrace_2651771 : CollatzResearch.WordTrace tailWord_2651771 prefixEnd_2651771 453877702884616555822411 := by
  unfold tailWord_2651771
  simp only [CollatzResearch.WordTrace]
  refine ⟨96718034076094028275779167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64478689384062685517186111 96718034076094028275779167)
  ·
    refine ⟨145077051114141042413668751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96718034076094028275779167 145077051114141042413668751)
    ·
      refine ⟨217615576671211563620503127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145077051114141042413668751 217615576671211563620503127)
      ·
        refine ⟨326423365006817345430754691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217615576671211563620503127 326423365006817345430754691)
        ·
          refine ⟨489635047510226018146132037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326423365006817345430754691 489635047510226018146132037)
          ·
            refine ⟨91806571408167378402399757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 489635047510226018146132037 91806571408167378402399757)
            ·
              refine ⟨34427464278062766900899909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91806571408167378402399757 34427464278062766900899909)
              ·
                refine ⟨6455149552136768793918733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34427464278062766900899909 6455149552136768793918733)
                ·
                  refine ⟨2420681082051288297719525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6455149552136768793918733 2420681082051288297719525)
                  ·
                    refine ⟨453877702884616555822411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2420681082051288297719525 453877702884616555822411)
                    ·
                      rfl

theorem cell23_2651771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 4].length) (baseStart_2651771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651771 prefixEnd_2651771 := by exact prefixLift 2651771
  have htrace : WordTrace (prefixWord ++ tailWord_2651771) baseStart_2651771 baseEnd_2651771 := by
    simpa [prefixWord, tailWord_2651771, baseEnd_2651771] using wordTrace_append hprefix tailTrace_2651771
  have hstable : (prefixWord ++ tailWord_2651771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651771).length < 2 ^ (prefixWord ++ tailWord_2651771).sum := by decide
  have hdescent : baseEnd_2651771 < baseStart_2651771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651781 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 1, 4, 3]
def baseStart_2651781 : Nat := 118140960795 + 2651781 * 2 ^ 59
def prefixEnd_2651781 : Nat := 4983230072969 + 3 ^ 40 * 2651781 * 2
def baseEnd_2651781 : Nat := 1361638243460394628342187

theorem tailTrace_2651781 : CollatzResearch.WordTrace tailWord_2651781 prefixEnd_2651781 1361638243460394628342187 := by
  unfold tailWord_2651781
  simp only [CollatzResearch.WordTrace]
  refine ⟨96718398806057799983643197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64478932537371866655762131 96718398806057799983643197)
  ·
    refine ⟨36269399552271674993866199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96718398806057799983643197 36269399552271674993866199)
    ·
      refine ⟨54404099328407512490799299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36269399552271674993866199 54404099328407512490799299)
      ·
        refine ⟨81606148992611268736198949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54404099328407512490799299 81606148992611268736198949)
        ·
          refine ⟨15301152936114612888037303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81606148992611268736198949 15301152936114612888037303)
          ·
            refine ⟨22951729404171919332055955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15301152936114612888037303 22951729404171919332055955)
            ·
              refine ⟨34427594106257878998083933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22951729404171919332055955 34427594106257878998083933)
              ·
                refine ⟨12910347789846704624281475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34427594106257878998083933 12910347789846704624281475)
                ·
                  refine ⟨19365521684770056936422213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12910347789846704624281475 19365521684770056936422213)
                  ·
                    refine ⟨3631035315894385675579165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19365521684770056936422213 3631035315894385675579165)
                    ·
                      refine ⟨1361638243460394628342187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3631035315894385675579165 1361638243460394628342187)
                      ·
                        rfl

theorem cell23_2651781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_2651781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651781 prefixEnd_2651781 := by exact prefixLift 2651781
  have htrace : WordTrace (prefixWord ++ tailWord_2651781) baseStart_2651781 baseEnd_2651781 := by
    simpa [prefixWord, tailWord_2651781, baseEnd_2651781] using wordTrace_append hprefix tailTrace_2651781
  have hstable : (prefixWord ++ tailWord_2651781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651781).length < 2 ^ (prefixWord ++ tailWord_2651781).sum := by decide
  have hdescent : baseEnd_2651781 < baseStart_2651781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651871 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 5]
def baseStart_2651871 : Nat := 118140960795 + 2651871 * 2 ^ 59
def prefixEnd_2651871 : Nat := 4983230072969 + 3 ^ 40 * 2651871 * 2
def baseEnd_2651871 : Nat := 1361684456719299276216773

theorem tailTrace_2651871 : CollatzResearch.WordTrace tailWord_2651871 prefixEnd_2651871 1361684456719299276216773 := by
  unfold tailWord_2651871
  simp only [CollatzResearch.WordTrace]
  refine ⟨96721681375731745354419467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64481120917154496902946311 96721681375731745354419467)
  ·
    refine ⟨145082522063597618031629201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96721681375731745354419467 145082522063597618031629201)
    ·
      refine ⟨108811891547698213523721901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145082522063597618031629201 108811891547698213523721901)
      ·
        refine ⟨40804459330386830071395713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108811891547698213523721901 40804459330386830071395713)
        ·
          refine ⟨30603344497790122553546785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40804459330386830071395713 30603344497790122553546785)
          ·
            refine ⟨22952508373342591915160089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30603344497790122553546785 22952508373342591915160089)
            ·
              refine ⟨17214381280006943936370067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22952508373342591915160089 17214381280006943936370067)
              ·
                refine ⟨25821571920010415904555101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17214381280006943936370067 25821571920010415904555101)
                ·
                  refine ⟨9683089470003905964208163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25821571920010415904555101 9683089470003905964208163)
                  ·
                    refine ⟨14524634205005858946312245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9683089470003905964208163 14524634205005858946312245)
                    ·
                      refine ⟨1361684456719299276216773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14524634205005858946312245 1361684456719299276216773)
                      ·
                        rfl

theorem cell23_2651871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_2651871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651871 prefixEnd_2651871 := by exact prefixLift 2651871
  have htrace : WordTrace (prefixWord ++ tailWord_2651871) baseStart_2651871 baseEnd_2651871 := by
    simpa [prefixWord, tailWord_2651871, baseEnd_2651871] using wordTrace_append hprefix tailTrace_2651871
  have hstable : (prefixWord ++ tailWord_2651871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651871).length < 2 ^ (prefixWord ++ tailWord_2651871).sum := by decide
  have hdescent : baseEnd_2651871 < baseStart_2651871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651902 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2651902 : Nat := 118140960795 + 2651902 * 2 ^ 59
def prefixEnd_2651902 : Nat := 4983230072969 + 3 ^ 40 * 2651902 * 2
def baseEnd_2651902 : Nat := 1361700374619588654929131

theorem tailTrace_2651902 : CollatzResearch.WordTrace tailWord_2651902 prefixEnd_2651902 1361700374619588654929131 := by
  unfold tailWord_2651902
  simp only [CollatzResearch.WordTrace]
  refine ⟨12090351504827429706099745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64481874692412958432531973 12090351504827429706099745)
  ·
    refine ⟨9067763628620572279574809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12090351504827429706099745 9067763628620572279574809)
    ·
      refine ⟨6800822721465429209681107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9067763628620572279574809 6800822721465429209681107)
      ·
        refine ⟨10201234082198143814521661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6800822721465429209681107 10201234082198143814521661)
        ·
          refine ⟨3825462780824303930445623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10201234082198143814521661 3825462780824303930445623)
          ·
            refine ⟨5738194171236455895668435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3825462780824303930445623 5738194171236455895668435)
            ·
              refine ⟨8607291256854683843502653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5738194171236455895668435 8607291256854683843502653)
              ·
                refine ⟨3227734221320506441313495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8607291256854683843502653 3227734221320506441313495)
                ·
                  refine ⟨4841601331980759661970243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3227734221320506441313495 4841601331980759661970243)
                  ·
                    refine ⟨7262401997971139492955365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4841601331980759661970243 7262401997971139492955365)
                    ·
                      refine ⟨1361700374619588654929131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7262401997971139492955365 1361700374619588654929131)
                      ·
                        rfl

theorem cell23_2651902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2651902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651902 prefixEnd_2651902 := by exact prefixLift 2651902
  have htrace : WordTrace (prefixWord ++ tailWord_2651902) baseStart_2651902 baseEnd_2651902 := by
    simpa [prefixWord, tailWord_2651902, baseEnd_2651902] using wordTrace_append hprefix tailTrace_2651902
  have hstable : (prefixWord ++ tailWord_2651902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651902).length < 2 ^ (prefixWord ++ tailWord_2651902).sum := by decide
  have hdescent : baseEnd_2651902 < baseStart_2651902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651918 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2651918 : Nat := 118140960795 + 2651918 * 2 ^ 59
def prefixEnd_2651918 : Nat := 4983230072969 + 3 ^ 40 * 2651918 * 2
def baseEnd_2651918 : Nat := 1361708590310060592329057

theorem tailTrace_2651918 : CollatzResearch.WordTrace tailWord_2651918 prefixEnd_2651918 1361708590310060592329057 := by
  unfold tailWord_2651918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12090424450820184047672551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64482263737707648254253605 12090424450820184047672551)
  ·
    refine ⟨18135636676230276071508827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12090424450820184047672551 18135636676230276071508827)
    ·
      refine ⟨27203455014345414107263241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18135636676230276071508827 27203455014345414107263241)
      ·
        refine ⟨20402591260759060580447431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27203455014345414107263241 20402591260759060580447431)
        ·
          refine ⟨30603886891138590870671147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20402591260759060580447431 30603886891138590870671147)
          ·
            refine ⟨45905830336707886306006721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30603886891138590870671147 45905830336707886306006721)
            ·
              refine ⟨34429372752530914729505041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45905830336707886306006721 34429372752530914729505041)
              ·
                refine ⟨25822029564398186047128781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34429372752530914729505041 25822029564398186047128781)
                ·
                  refine ⟨9683261086649319767673293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25822029564398186047128781 9683261086649319767673293)
                  ·
                    refine ⟨3631222907493494912877485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9683261086649319767673293 3631222907493494912877485)
                    ·
                      refine ⟨1361708590310060592329057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3631222907493494912877485 1361708590310060592329057)
                      ·
                        rfl

theorem cell23_2651918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2651918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651918 prefixEnd_2651918 := by exact prefixLift 2651918
  have htrace : WordTrace (prefixWord ++ tailWord_2651918) baseStart_2651918 baseEnd_2651918 := by
    simpa [prefixWord, tailWord_2651918, baseEnd_2651918] using wordTrace_append hprefix tailTrace_2651918
  have hstable : (prefixWord ++ tailWord_2651918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651918).length < 2 ^ (prefixWord ++ tailWord_2651918).sum := by decide
  have hdescent : baseEnd_2651918 < baseStart_2651918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651962 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2]
def baseStart_2651962 : Nat := 118140960795 + 2651962 * 2 ^ 59
def prefixEnd_2651962 : Nat := 4983230072969 + 3 ^ 40 * 2651962 * 2
def baseEnd_2651962 : Nat := 1361731183458858420178855

theorem tailTrace_2651962 : CollatzResearch.WordTrace tailWord_2651962 prefixEnd_2651962 1361731183458858420178855 := by
  unfold tailWord_2651962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24181250104600516973995535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64483333612268045263988093 24181250104600516973995535)
  ·
    refine ⟨36271875156900775460993303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24181250104600516973995535 36271875156900775460993303)
    ·
      refine ⟨54407812735351163191489955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36271875156900775460993303 54407812735351163191489955)
      ·
        refine ⟨81611719103026744787234933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54407812735351163191489955 81611719103026744787234933)
        ·
          refine ⟨7651098665908757323803275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81611719103026744787234933 7651098665908757323803275)
          ·
            refine ⟨11476647998863135985704913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7651098665908757323803275 11476647998863135985704913)
            ·
              refine ⟨8607485999147351989278685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11476647998863135985704913 8607485999147351989278685)
              ·
                refine ⟨3227807249680256995979507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8607485999147351989278685 3227807249680256995979507)
                ·
                  refine ⟨4841710874520385493969261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3227807249680256995979507 4841710874520385493969261)
                  ·
                    refine ⟨1815641577945144560238473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4841710874520385493969261 1815641577945144560238473)
                    ·
                      refine ⟨1361731183458858420178855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815641577945144560238473 1361731183458858420178855)
                      ·
                        rfl

theorem cell23_2651962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2].length) (baseStart_2651962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651962 prefixEnd_2651962 := by exact prefixLift 2651962
  have htrace : WordTrace (prefixWord ++ tailWord_2651962) baseStart_2651962 baseEnd_2651962 := by
    simpa [prefixWord, tailWord_2651962, baseEnd_2651962] using wordTrace_append hprefix tailTrace_2651962
  have hstable : (prefixWord ++ tailWord_2651962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651962).length < 2 ^ (prefixWord ++ tailWord_2651962).sum := by decide
  have hdescent : baseEnd_2651962 < baseStart_2651962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651978 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_2651978 : Nat := 118140960795 + 2651978 * 2 ^ 59
def prefixEnd_2651978 : Nat := 4983230072969 + 3 ^ 40 * 2651978 * 2
def baseEnd_2651978 : Nat := 1361739399149330357578781

theorem tailTrace_2651978 : CollatzResearch.WordTrace tailWord_2651978 prefixEnd_2651978 1361739399149330357578781 := by
  unfold tailWord_2651978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24181395996586025657141147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64483722657562735085709725 24181395996586025657141147)
  ·
    refine ⟨36272093994879038485711721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24181395996586025657141147 36272093994879038485711721)
    ·
      refine ⟨27204070496159278864283791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36272093994879038485711721 27204070496159278864283791)
      ·
        refine ⟨40806105744238918296425687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27204070496159278864283791 40806105744238918296425687)
        ·
          refine ⟨61209158616358377444638531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40806105744238918296425687 61209158616358377444638531)
          ·
            refine ⟨91813737924537566166957797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61209158616358377444638531 91813737924537566166957797)
            ·
              refine ⟨17215075860850793656304587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91813737924537566166957797 17215075860850793656304587)
              ·
                refine ⟨25822613791276190484456881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17215075860850793656304587 25822613791276190484456881)
                ·
                  refine ⟨19366960343457142863342661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25822613791276190484456881 19366960343457142863342661)
                  ·
                    refine ⟨3631305064398214286876749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19366960343457142863342661 3631305064398214286876749)
                    ·
                      refine ⟨1361739399149330357578781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3631305064398214286876749 1361739399149330357578781)
                      ·
                        rfl

theorem cell23_2651978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_2651978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651978 prefixEnd_2651978 := by exact prefixLift 2651978
  have htrace : WordTrace (prefixWord ++ tailWord_2651978) baseStart_2651978 baseEnd_2651978 := by
    simpa [prefixWord, tailWord_2651978, baseEnd_2651978] using wordTrace_append hprefix tailTrace_2651978
  have hstable : (prefixWord ++ tailWord_2651978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651978).length < 2 ^ (prefixWord ++ tailWord_2651978).sum := by decide
  have hdescent : baseEnd_2651978 < baseStart_2651978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651996 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_2651996 : Nat := 118140960795 + 2651996 * 2 ^ 59
def prefixEnd_2651996 : Nat := 4983230072969 + 3 ^ 40 * 2651996 * 2
def baseEnd_2651996 : Nat := 1361748641801111287153699

theorem tailTrace_2651996 : CollatzResearch.WordTrace tailWord_2651996 prefixEnd_2651996 1361748641801111287153699 := by
  unfold tailWord_2651996
  simp only [CollatzResearch.WordTrace]
  refine ⟨48363120250139445851359921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64484160333519261135146561 48363120250139445851359921)
  ·
    refine ⟨36272340187604584388519941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48363120250139445851359921 36272340187604584388519941)
    ·
      refine ⟨6801063785175859572847489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36272340187604584388519941 6801063785175859572847489)
      ·
        refine ⟨5100797838881894679635617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6801063785175859572847489 5100797838881894679635617)
        ·
          refine ⟨3825598379161421009726713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5100797838881894679635617 3825598379161421009726713)
          ·
            refine ⟨2869198784371065757295035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3825598379161421009726713 2869198784371065757295035)
            ·
              refine ⟨4303798176556598635942553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869198784371065757295035 4303798176556598635942553)
              ·
                refine ⟨3227848632417448976956915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4303798176556598635942553 3227848632417448976956915)
                ·
                  refine ⟨4841772948626173465435373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3227848632417448976956915 4841772948626173465435373)
                  ·
                    refine ⟨1815664855734815049538265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4841772948626173465435373 1815664855734815049538265)
                    ·
                      refine ⟨1361748641801111287153699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815664855734815049538265 1361748641801111287153699)
                      ·
                        rfl

theorem cell23_2651996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_2651996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2651996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2651996 prefixEnd_2651996 := by exact prefixLift 2651996
  have htrace : WordTrace (prefixWord ++ tailWord_2651996) baseStart_2651996 baseEnd_2651996 := by
    simpa [prefixWord, tailWord_2651996, baseEnd_2651996] using wordTrace_append hprefix tailTrace_2651996
  have hstable : (prefixWord ++ tailWord_2651996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651996).length < 2 ^ (prefixWord ++ tailWord_2651996).sum := by decide
  have hdescent : baseEnd_2651996 < baseStart_2651996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652035 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 2, 5, 2]
def baseStart_2652035 : Nat := 118140960795 + 2652035 * 2 ^ 59
def prefixEnd_2652035 : Nat := 4983230072969 + 3 ^ 40 * 2652035 * 2
def baseEnd_2652035 : Nat := 1361768667546636634566019

theorem tailTrace_2652035 : CollatzResearch.WordTrace tailWord_2652035 prefixEnd_2652035 1361768667546636634566019 := by
  unfold tailWord_2652035
  simp only [CollatzResearch.WordTrace]
  refine ⟨96727662947137601363389559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64485108631425067575593039 96727662947137601363389559)
  ·
    refine ⟨145091494420706402045084339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96727662947137601363389559 145091494420706402045084339)
    ·
      refine ⟨217637241631059603067626509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145091494420706402045084339 217637241631059603067626509)
      ·
        refine ⟨81613965611647351150359941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217637241631059603067626509 81613965611647351150359941)
        ·
          refine ⟨15302618552183878340692489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81613965611647351150359941 15302618552183878340692489)
          ·
            refine ⟨11476963914137908755519367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15302618552183878340692489 11476963914137908755519367)
            ·
              refine ⟨17215445871206863133279051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11476963914137908755519367 17215445871206863133279051)
              ·
                refine ⟨25823168806810294699918577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17215445871206863133279051 25823168806810294699918577)
                ·
                  refine ⟨19367376605107721024938933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25823168806810294699918577 19367376605107721024938933)
                  ·
                    refine ⟨1815691556728848846088025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19367376605107721024938933 1815691556728848846088025)
                    ·
                      refine ⟨1361768667546636634566019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815691556728848846088025 1361768667546636634566019)
                      ·
                        rfl

theorem cell23_2652035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 5, 2].length) (baseStart_2652035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652035 prefixEnd_2652035 := by exact prefixLift 2652035
  have htrace : WordTrace (prefixWord ++ tailWord_2652035) baseStart_2652035 baseEnd_2652035 := by
    simpa [prefixWord, tailWord_2652035, baseEnd_2652035] using wordTrace_append hprefix tailTrace_2652035
  have hstable : (prefixWord ++ tailWord_2652035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652035).length < 2 ^ (prefixWord ++ tailWord_2652035).sum := by decide
  have hdescent : baseEnd_2652035 < baseStart_2652035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652042 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2652042 : Nat := 118140960795 + 2652042 * 2 ^ 59
def prefixEnd_2652042 : Nat := 4983230072969 + 3 ^ 40 * 2652042 * 2
def baseEnd_2652042 : Nat := 1361772261911218107178487

theorem tailTrace_2652042 : CollatzResearch.WordTrace tailWord_2652042 prefixEnd_2652042 1361772261911218107178487 := by
  unfold tailWord_2652042
  simp only [CollatzResearch.WordTrace]
  refine ⟨24181979564528060389723595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64485278838741494372596253 24181979564528060389723595)
  ·
    refine ⟨36272969346792090584585393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24181979564528060389723595 36272969346792090584585393)
    ·
      refine ⟨27204727010094067938439045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36272969346792090584585393 27204727010094067938439045)
      ·
        refine ⟨5100886314392637738457321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27204727010094067938439045 5100886314392637738457321)
        ·
          refine ⟨3825664735794478303842991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5100886314392637738457321 3825664735794478303842991)
          ·
            refine ⟨5738497103691717455764487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3825664735794478303842991 5738497103691717455764487)
            ·
              refine ⟨8607745655537576183646731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5738497103691717455764487 8607745655537576183646731)
              ·
                refine ⟨12911618483306364275470097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8607745655537576183646731 12911618483306364275470097)
                ·
                  refine ⟨9683713862479773206602573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12911618483306364275470097 9683713862479773206602573)
                  ·
                    refine ⟨3631392698429914952475965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9683713862479773206602573 3631392698429914952475965)
                    ·
                      refine ⟨1361772261911218107178487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3631392698429914952475965 1361772261911218107178487)
                      ·
                        rfl

theorem cell23_2652042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2652042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652042 prefixEnd_2652042 := by exact prefixLift 2652042
  have htrace : WordTrace (prefixWord ++ tailWord_2652042) baseStart_2652042 baseEnd_2652042 := by
    simpa [prefixWord, tailWord_2652042, baseEnd_2652042] using wordTrace_append hprefix tailTrace_2652042
  have hstable : (prefixWord ++ tailWord_2652042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652042).length < 2 ^ (prefixWord ++ tailWord_2652042).sum := by decide
  have hdescent : baseEnd_2652042 < baseStart_2652042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652048 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 4]
def baseStart_2652048 : Nat := 118140960795 + 2652048 * 2 ^ 59
def prefixEnd_2652048 : Nat := 4983230072969 + 3 ^ 40 * 2652048 * 2
def baseEnd_2652048 : Nat := 1361775342795145083703459

theorem tailTrace_2652048 : CollatzResearch.WordTrace tailWord_2652048 prefixEnd_2652048 1361775342795145083703459 := by
  unfold tailWord_2652048
  simp only [CollatzResearch.WordTrace]
  refine ⟨48364068548045252291806399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64485424730727003055741865 48364068548045252291806399)
  ·
    refine ⟨72546102822067878437709599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48364068548045252291806399 72546102822067878437709599)
    ·
      refine ⟨108819154233101817656564399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72546102822067878437709599 108819154233101817656564399)
      ·
        refine ⟨163228731349652726484846599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108819154233101817656564399 163228731349652726484846599)
        ·
          refine ⟨244843097024479089727269899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163228731349652726484846599 244843097024479089727269899)
          ·
            refine ⟨367264645536718634590904849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244843097024479089727269899 367264645536718634590904849)
            ·
              refine ⟨275448484152538975943178637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367264645536718634590904849 275448484152538975943178637)
              ·
                refine ⟨103293181557202115978691989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275448484152538975943178637 103293181557202115978691989)
                ·
                  refine ⟨4841867885493849186501187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103293181557202115978691989 4841867885493849186501187)
                  ·
                    refine ⟨7262801828240773779751781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4841867885493849186501187 7262801828240773779751781)
                    ·
                      refine ⟨1361775342795145083703459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7262801828240773779751781 1361775342795145083703459)
                      ·
                        rfl

theorem cell23_2652048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_2652048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652048 prefixEnd_2652048 := by exact prefixLift 2652048
  have htrace : WordTrace (prefixWord ++ tailWord_2652048) baseStart_2652048 baseEnd_2652048 := by
    simpa [prefixWord, tailWord_2652048, baseEnd_2652048] using wordTrace_append hprefix tailTrace_2652048
  have hstable : (prefixWord ++ tailWord_2652048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652048).length < 2 ^ (prefixWord ++ tailWord_2652048).sum := by decide
  have hdescent : baseEnd_2652048 < baseStart_2652048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652088 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 8]
def baseStart_2652088 : Nat := 118140960795 + 2652088 * 2 ^ 59
def prefixEnd_2652088 : Nat := 4983230072969 + 3 ^ 40 * 2652088 * 2
def baseEnd_2652088 : Nat := 151310653557924991911475

theorem tailTrace_2652088 : CollatzResearch.WordTrace tailWord_2652088 prefixEnd_2652088 151310653557924991911475 := by
  unfold tailWord_2652088
  simp only [CollatzResearch.WordTrace]
  refine ⟨48364798007972795707534459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64486397343963727610045945 48364798007972795707534459)
  ·
    refine ⟨72547197011959193561301689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48364798007972795707534459 72547197011959193561301689)
    ·
      refine ⟨54410397758969395170976267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72547197011959193561301689 54410397758969395170976267)
      ·
        refine ⟨81615596638454092756464401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54410397758969395170976267 81615596638454092756464401)
        ·
          refine ⟨61211697478840569567348301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81615596638454092756464401 61211697478840569567348301)
          ·
            refine ⟨22954386554565213587755613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61211697478840569567348301 22954386554565213587755613)
            ·
              refine ⟨8607894957961955095408355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22954386554565213587755613 8607894957961955095408355)
              ·
                refine ⟨12911842436942932643112533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8607894957961955095408355 12911842436942932643112533)
                ·
                  refine ⟨151310653557924991911475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12911842436942932643112533 151310653557924991911475)
                  ·
                    rfl

theorem cell23_2652088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 8].length) (baseStart_2652088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652088 prefixEnd_2652088 := by exact prefixLift 2652088
  have htrace : WordTrace (prefixWord ++ tailWord_2652088) baseStart_2652088 baseEnd_2652088 := by
    simpa [prefixWord, tailWord_2652088, baseEnd_2652088] using wordTrace_append hprefix tailTrace_2652088
  have hstable : (prefixWord ++ tailWord_2652088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652088).length < 2 ^ (prefixWord ++ tailWord_2652088).sum := by decide
  have hdescent : baseEnd_2652088 < baseStart_2652088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652249 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 1, 3, 2]
def baseStart_2652249 : Nat := 118140960795 + 2652249 * 2 ^ 59
def prefixEnd_2652249 : Nat := 4983230072969 + 3 ^ 40 * 2652249 * 2
def baseEnd_2652249 : Nat := 1361878552406698797290035

theorem tailTrace_2652249 : CollatzResearch.WordTrace tailWord_2652249 prefixEnd_2652249 1361878552406698797290035 := by
  unfold tailWord_2652249
  simp only [CollatzResearch.WordTrace]
  refine ⟨96735468168362315911679801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64490312112241543941119867 96735468168362315911679801)
  ·
    refine ⟨72551601126271736933759851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96735468168362315911679801 72551601126271736933759851)
    ·
      refine ⟨108827401689407605400639777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72551601126271736933759851 108827401689407605400639777)
      ·
        refine ⟨81620551267055704050479833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108827401689407605400639777 81620551267055704050479833)
        ·
          refine ⟨61215413450291778037859875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81620551267055704050479833 61215413450291778037859875)
          ·
            refine ⟨91823120175437667056789813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61215413450291778037859875 91823120175437667056789813)
            ·
              refine ⟨8608417516447281286574045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91823120175437667056789813 8608417516447281286574045)
              ·
                refine ⟨3228156568667730482465267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8608417516447281286574045 3228156568667730482465267)
                ·
                  refine ⟨4842234853001595723697901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228156568667730482465267 4842234853001595723697901)
                  ·
                    refine ⟨1815838069875598396386713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4842234853001595723697901 1815838069875598396386713)
                    ·
                      refine ⟨1361878552406698797290035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815838069875598396386713 1361878552406698797290035)
                      ·
                        rfl

theorem cell23_2652249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 3, 2].length) (baseStart_2652249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652249 prefixEnd_2652249 := by exact prefixLift 2652249
  have htrace : WordTrace (prefixWord ++ tailWord_2652249) baseStart_2652249 baseEnd_2652249 := by
    simpa [prefixWord, tailWord_2652249, baseEnd_2652249] using wordTrace_append hprefix tailTrace_2652249
  have hstable : (prefixWord ++ tailWord_2652249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652249).length < 2 ^ (prefixWord ++ tailWord_2652249).sum := by decide
  have hdescent : baseEnd_2652249 < baseStart_2652249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652256 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 2, 1, 3]
def baseStart_2652256 : Nat := 118140960795 + 2652256 * 2 ^ 59
def prefixEnd_2652256 : Nat := 4983230072969 + 3 ^ 40 * 2652256 * 2
def baseEnd_2652256 : Nat := 1361882146771280269902503

theorem tailTrace_2652256 : CollatzResearch.WordTrace tailWord_2652256 prefixEnd_2652256 1361882146771280269902503 := by
  unfold tailWord_2652256
  simp only [CollatzResearch.WordTrace]
  refine ⟨48367861739668478053592311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64490482319557970738123081 48367861739668478053592311)
  ·
    refine ⟨72551792609502717080388467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48367861739668478053592311 72551792609502717080388467)
    ·
      refine ⟨108827688914254075620582701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72551792609502717080388467 108827688914254075620582701)
      ·
        refine ⟨40810383342845278357718513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108827688914254075620582701 40810383342845278357718513)
        ·
          refine ⟨30607787507133958768288885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40810383342845278357718513 30607787507133958768288885)
          ·
            refine ⟨2869480078793808634527083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30607787507133958768288885 2869480078793808634527083)
            ·
              refine ⟨4304220118190712951790625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869480078793808634527083 4304220118190712951790625)
              ·
                refine ⟨3228165088643034713842969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4304220118190712951790625 3228165088643034713842969)
                ·
                  refine ⟨2421123816482276035382227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3228165088643034713842969 2421123816482276035382227)
                  ·
                    refine ⟨3631685724723414053073341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2421123816482276035382227 3631685724723414053073341)
                    ·
                      refine ⟨1361882146771280269902503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3631685724723414053073341 1361882146771280269902503)
                      ·
                        rfl

theorem cell23_2652256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_2652256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652256 prefixEnd_2652256 := by exact prefixLift 2652256
  have htrace : WordTrace (prefixWord ++ tailWord_2652256) baseStart_2652256 baseEnd_2652256 := by
    simpa [prefixWord, tailWord_2652256, baseEnd_2652256] using wordTrace_append hprefix tailTrace_2652256
  have hstable : (prefixWord ++ tailWord_2652256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652256).length < 2 ^ (prefixWord ++ tailWord_2652256).sum := by decide
  have hdescent : baseEnd_2652256 < baseStart_2652256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652279 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 1, 4, 2]
def baseStart_2652279 : Nat := 118140960795 + 2652279 * 2 ^ 59
def prefixEnd_2652279 : Nat := 4983230072969 + 3 ^ 40 * 2652279 * 2
def baseEnd_2652279 : Nat := 1361893956826333679914897

theorem tailTrace_2652279 : CollatzResearch.WordTrace tailWord_2652279 prefixEnd_2652279 1361893956826333679914897 := by
  unfold tailWord_2652279
  simp only [CollatzResearch.WordTrace]
  refine ⟨96736562358253631035271891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64491041572169087356847927 96736562358253631035271891)
  ·
    refine ⟨145104843537380446552907837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96736562358253631035271891 145104843537380446552907837)
    ·
      refine ⟨54414316326517667457340439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145104843537380446552907837 54414316326517667457340439)
      ·
        refine ⟨81621474489776501186010659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54414316326517667457340439 81621474489776501186010659)
        ·
          refine ⟨122432211734664751779015989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81621474489776501186010659 122432211734664751779015989)
          ·
            refine ⟨11478019850124820479282749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122432211734664751779015989 11478019850124820479282749)
            ·
              refine ⟨4304257443796807679731031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11478019850124820479282749 4304257443796807679731031)
              ·
                refine ⟨6456386165695211519596547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304257443796807679731031 6456386165695211519596547)
                ·
                  refine ⟨9684579248542817279394821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6456386165695211519596547 9684579248542817279394821)
                  ·
                    refine ⟨1815858609101778239886529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9684579248542817279394821 1815858609101778239886529)
                    ·
                      refine ⟨1361893956826333679914897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815858609101778239886529 1361893956826333679914897)
                      ·
                        rfl

theorem cell23_2652279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 4, 2].length) (baseStart_2652279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652279 prefixEnd_2652279 := by exact prefixLift 2652279
  have htrace : WordTrace (prefixWord ++ tailWord_2652279) baseStart_2652279 baseEnd_2652279 := by
    simpa [prefixWord, tailWord_2652279, baseEnd_2652279] using wordTrace_append hprefix tailTrace_2652279
  have hstable : (prefixWord ++ tailWord_2652279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652279).length < 2 ^ (prefixWord ++ tailWord_2652279).sum := by decide
  have hdescent : baseEnd_2652279 < baseStart_2652279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652296 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2652296 : Nat := 118140960795 + 2652296 * 2 ^ 59
def prefixEnd_2652296 : Nat := 4983230072969 + 3 ^ 40 * 2652296 * 2
def baseEnd_2652296 : Nat := 1361902685997460113402319

theorem tailTrace_2652296 : CollatzResearch.WordTrace tailWord_2652296 prefixEnd_2652296 1361902685997460113402319 := by
  unfold tailWord_2652296
  simp only [CollatzResearch.WordTrace]
  refine ⟨48368591199596021469320371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64491454932794695292427161 48368591199596021469320371)
  ·
    refine ⟨72552886799394032203980557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48368591199596021469320371 72552886799394032203980557)
    ·
      refine ⟨27207332549772762076492709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72552886799394032203980557 27207332549772762076492709)
      ·
        refine ⟨5101374853082392889342383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27207332549772762076492709 5101374853082392889342383)
        ·
          refine ⟨7652062279623589334013575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5101374853082392889342383 7652062279623589334013575)
          ·
            refine ⟨11478093419435384001020363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7652062279623589334013575 11478093419435384001020363)
            ·
              refine ⟨17217140129153076001530545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11478093419435384001020363 17217140129153076001530545)
              ·
                refine ⟨12912855096864807001147909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17217140129153076001530545 12912855096864807001147909)
                ·
                  refine ⟨2421160330662151312715233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12912855096864807001147909 2421160330662151312715233)
                  ·
                    refine ⟨1815870247996613484536425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2421160330662151312715233 1815870247996613484536425)
                    ·
                      refine ⟨1361902685997460113402319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815870247996613484536425 1361902685997460113402319)
                      ·
                        rfl

theorem cell23_2652296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2652296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652296 prefixEnd_2652296 := by exact prefixLift 2652296
  have htrace : WordTrace (prefixWord ++ tailWord_2652296) baseStart_2652296 baseEnd_2652296 := by
    simpa [prefixWord, tailWord_2652296, baseEnd_2652296] using wordTrace_append hprefix tailTrace_2652296
  have hstable : (prefixWord ++ tailWord_2652296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652296).length < 2 ^ (prefixWord ++ tailWord_2652296).sum := by decide
  have hdescent : baseEnd_2652296 < baseStart_2652296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652319 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 7]
def baseStart_2652319 : Nat := 118140960795 + 2652319 * 2 ^ 59
def prefixEnd_2652319 : Nat := 4983230072969 + 3 ^ 40 * 2652319 * 2
def baseEnd_2652319 : Nat := 151323832894723724823857

theorem tailTrace_2652319 : CollatzResearch.WordTrace tailWord_2652319 prefixEnd_2652319 151323832894723724823857 := by
  unfold tailWord_2652319
  simp only [CollatzResearch.WordTrace]
  refine ⟨96738021278108717866728011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64492014185405811911152007 96738021278108717866728011)
  ·
    refine ⟨145107031917163076800092017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96738021278108717866728011 145107031917163076800092017)
    ·
      refine ⟨108830273937872307600069013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145107031917163076800092017 108830273937872307600069013)
      ·
        refine ⟨5101419090837764418753235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108830273937872307600069013 5101419090837764418753235)
        ·
          refine ⟨7652128636256646628129853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5101419090837764418753235 7652128636256646628129853)
          ·
            refine ⟨2869548238596242485548695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7652128636256646628129853 2869548238596242485548695)
            ·
              refine ⟨4304322357894363728323043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869548238596242485548695 4304322357894363728323043)
              ·
                refine ⟨6456483536841545592484565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304322357894363728323043 6456483536841545592484565)
                ·
                  refine ⟨151323832894723724823857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6456483536841545592484565 151323832894723724823857)
                  ·
                    rfl

theorem cell23_2652319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 7].length) (baseStart_2652319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652319 prefixEnd_2652319 := by exact prefixLift 2652319
  have htrace : WordTrace (prefixWord ++ tailWord_2652319) baseStart_2652319 baseEnd_2652319 := by
    simpa [prefixWord, tailWord_2652319, baseEnd_2652319] using wordTrace_append hprefix tailTrace_2652319
  have hstable : (prefixWord ++ tailWord_2652319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652319).length < 2 ^ (prefixWord ++ tailWord_2652319).sum := by decide
  have hdescent : baseEnd_2652319 < baseStart_2652319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652330 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_2652330 : Nat := 118140960795 + 2652330 * 2 ^ 59
def prefixEnd_2652330 : Nat := 4983230072969 + 3 ^ 40 * 2652330 * 2
def baseEnd_2652330 : Nat := 1361920144339712980377163

theorem tailTrace_2652330 : CollatzResearch.WordTrace tailWord_2652330 prefixEnd_2652330 1361920144339712980377163 := by
  unfold tailWord_2652330
  simp only [CollatzResearch.WordTrace]
  refine ⟨24184605620267216686344611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64492281654045911163585629 24184605620267216686344611)
  ·
    refine ⟨36276908430400825029516917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24184605620267216686344611 36276908430400825029516917)
    ·
      refine ⟨3400960165350077346517211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36276908430400825029516917 3400960165350077346517211)
      ·
        refine ⟨5101440248025116019775817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400960165350077346517211 5101440248025116019775817)
        ·
          refine ⟨3826080186018837014831863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5101440248025116019775817 3826080186018837014831863)
          ·
            refine ⟨5739120279028255522247795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826080186018837014831863 5739120279028255522247795)
            ·
              refine ⟨8608680418542383283371693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739120279028255522247795 8608680418542383283371693)
              ·
                refine ⟨3228255156953393731264385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8608680418542383283371693 3228255156953393731264385)
                ·
                  refine ⟨2421191367715045298448289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3228255156953393731264385 2421191367715045298448289)
                  ·
                    refine ⟨1815893525786283973836217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2421191367715045298448289 1815893525786283973836217)
                    ·
                      refine ⟨1361920144339712980377163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1815893525786283973836217 1361920144339712980377163)
                      ·
                        rfl

theorem cell23_2652330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_2652330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652330 prefixEnd_2652330 := by exact prefixLift 2652330
  have htrace : WordTrace (prefixWord ++ tailWord_2652330) baseStart_2652330 baseEnd_2652330 := by
    simpa [prefixWord, tailWord_2652330, baseEnd_2652330] using wordTrace_append hprefix tailTrace_2652330
  have hstable : (prefixWord ++ tailWord_2652330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652330).length < 2 ^ (prefixWord ++ tailWord_2652330).sum := by decide
  have hdescent : baseEnd_2652330 < baseStart_2652330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652406 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2652406 : Nat := 118140960795 + 2652406 * 2 ^ 59
def prefixEnd_2652406 : Nat := 4983230072969 + 3 ^ 40 * 2652406 * 2
def baseEnd_2652406 : Nat := 1361959168869454683026813

theorem tailTrace_2652406 : CollatzResearch.WordTrace tailWord_2652406 prefixEnd_2652406 1361959168869454683026813 := by
  unfold tailWord_2652406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6046324651799595732821567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64494129619195687816763381 6046324651799595732821567)
  ·
    refine ⟨9069486977699393599232351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6046324651799595732821567 9069486977699393599232351)
    ·
      refine ⟨13604230466549090398848527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9069486977699393599232351 13604230466549090398848527)
      ·
        refine ⟨20406345699823635598272791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13604230466549090398848527 20406345699823635598272791)
        ·
          refine ⟨30609518549735453397409187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20406345699823635598272791 30609518549735453397409187)
          ·
            refine ⟨45914277824603180096113781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30609518549735453397409187 45914277824603180096113781)
            ·
              refine ⟨4304463546056548134010667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45914277824603180096113781 4304463546056548134010667)
              ·
                refine ⟨6456695319084822201016001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304463546056548134010667 6456695319084822201016001)
                ·
                  refine ⟨4842521489313616650762001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6456695319084822201016001 4842521489313616650762001)
                  ·
                    refine ⟨3631891116985212488071501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4842521489313616650762001 3631891116985212488071501)
                    ·
                      refine ⟨1361959168869454683026813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3631891116985212488071501 1361959168869454683026813)
                      ·
                        rfl

theorem cell23_2652406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2652406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652406 prefixEnd_2652406 := by exact prefixLift 2652406
  have htrace : WordTrace (prefixWord ++ tailWord_2652406) baseStart_2652406 baseEnd_2652406 := by
    simpa [prefixWord, tailWord_2652406, baseEnd_2652406] using wordTrace_append hprefix tailTrace_2652406
  have hstable : (prefixWord ++ tailWord_2652406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652406).length < 2 ^ (prefixWord ++ tailWord_2652406).sum := by decide
  have hdescent : baseEnd_2652406 < baseStart_2652406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652419 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 5, 1, 3]
def baseStart_2652419 : Nat := 118140960795 + 2652419 * 2 ^ 59
def prefixEnd_2652419 : Nat := 4983230072969 + 3 ^ 40 * 2652419 * 2
def baseEnd_2652419 : Nat := 1361965844117963132164253

theorem tailTrace_2652419 : CollatzResearch.WordTrace tailWord_2652419 prefixEnd_2652419 1361965844117963132164253 := by
  unfold tailWord_2652419
  simp only [CollatzResearch.WordTrace]
  refine ⟨96741668577746434945368311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64494445718497623296912207 96741668577746434945368311)
  ·
    refine ⟨145112502866619652418052467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96741668577746434945368311 145112502866619652418052467)
    ·
      refine ⟨217668754299929478627078701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145112502866619652418052467 217668754299929478627078701)
      ·
        refine ⟨81625782862473554485154513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217668754299929478627078701 81625782862473554485154513)
        ·
          refine ⟨61219337146855165863865885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81625782862473554485154513 61219337146855165863865885)
          ·
            refine ⟨22957251430070687198949707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61219337146855165863865885 22957251430070687198949707)
            ·
              refine ⟨34435877145106030798424561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22957251430070687198949707 34435877145106030798424561)
              ·
                refine ⟨25826907858829523098818421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34435877145106030798424561 25826907858829523098818421)
                ·
                  refine ⟨2421272611765267790514227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25826907858829523098818421 2421272611765267790514227)
                  ·
                    refine ⟨3631908917647901685771341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2421272611765267790514227 3631908917647901685771341)
                    ·
                      refine ⟨1361965844117963132164253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3631908917647901685771341 1361965844117963132164253)
                      ·
                        rfl

theorem cell23_2652419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_2652419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652419 prefixEnd_2652419 := by exact prefixLift 2652419
  have htrace : WordTrace (prefixWord ++ tailWord_2652419) baseStart_2652419 baseEnd_2652419 := by
    simpa [prefixWord, tailWord_2652419, baseEnd_2652419] using wordTrace_append hprefix tailTrace_2652419
  have hstable : (prefixWord ++ tailWord_2652419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652419).length < 2 ^ (prefixWord ++ tailWord_2652419).sum := by decide
  have hdescent : baseEnd_2652419 < baseStart_2652419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652469 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 6, 4]
def baseStart_2652469 : Nat := 118140960795 + 2652469 * 2 ^ 59
def prefixEnd_2652469 : Nat := 4983230072969 + 3 ^ 40 * 2652469 * 2
def baseEnd_2652469 : Nat := 453997172716895978846341

theorem tailTrace_2652469 : CollatzResearch.WordTrace tailWord_2652469 prefixEnd_2652469 453997172716895978846341 := by
  unfold tailWord_2652469
  simp only [CollatzResearch.WordTrace]
  refine ⟨96743492227565293484688461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64495661485043528989792307 96743492227565293484688461)
  ·
    refine ⟨36278809585336985056758173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96743492227565293484688461 36278809585336985056758173)
    ·
      refine ⟨13604553594501369396284315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36278809585336985056758173 13604553594501369396284315)
      ·
        refine ⟨20406830391752054094426473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13604553594501369396284315 20406830391752054094426473)
        ·
          refine ⟨15305122793814040570819855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20406830391752054094426473 15305122793814040570819855)
          ·
            refine ⟨22957684190721060856229783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15305122793814040570819855 22957684190721060856229783)
            ·
              refine ⟨34436526286081591284344675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22957684190721060856229783 34436526286081591284344675)
              ·
                refine ⟨51654789429122386926517013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34436526286081591284344675 51654789429122386926517013)
                ·
                  refine ⟨2421318254490111887180485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51654789429122386926517013 2421318254490111887180485)
                  ·
                    refine ⟨453997172716895978846341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2421318254490111887180485 453997172716895978846341)
                    ·
                      rfl

theorem cell23_2652469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_2652469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652469 prefixEnd_2652469 := by exact prefixLift 2652469
  have htrace : WordTrace (prefixWord ++ tailWord_2652469) baseStart_2652469 baseEnd_2652469 := by
    simpa [prefixWord, tailWord_2652469, baseEnd_2652469] using wordTrace_append hprefix tailTrace_2652469
  have hstable : (prefixWord ++ tailWord_2652469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652469).length < 2 ^ (prefixWord ++ tailWord_2652469).sum := by decide
  have hdescent : baseEnd_2652469 < baseStart_2652469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652479 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 5]
def baseStart_2652479 : Nat := 118140960795 + 2652479 * 2 ^ 59
def prefixEnd_2652479 : Nat := 4983230072969 + 3 ^ 40 * 2652479 * 2
def baseEnd_2652479 : Nat := 1361996652957232897413977

theorem tailTrace_2652479 : CollatzResearch.WordTrace tailWord_2652479 prefixEnd_2652479 1361996652957232897413977 := by
  unfold tailWord_2652479
  simp only [CollatzResearch.WordTrace]
  refine ⟨96743856957529065192552491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64495904638352710128368327 96743856957529065192552491)
  ·
    refine ⟨145115785436293597788828737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96743856957529065192552491 145115785436293597788828737)
    ·
      refine ⟨108836839077220198341621553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145115785436293597788828737 108836839077220198341621553)
      ·
        refine ⟨81627629307915148756216165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108836839077220198341621553 81627629307915148756216165)
        ·
          refine ⟨15305180495234090391790531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81627629307915148756216165 15305180495234090391790531)
          ·
            refine ⟨22957770742851135587685797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15305180495234090391790531 22957770742851135587685797)
            ·
              refine ⟨4304582014284587922691087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22957770742851135587685797 4304582014284587922691087)
              ·
                refine ⟨6456873021426881884036631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304582014284587922691087 6456873021426881884036631)
                ·
                  refine ⟨9685309532140322826054947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6456873021426881884036631 9685309532140322826054947)
                  ·
                    refine ⟨14527964298210484239082421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9685309532140322826054947 14527964298210484239082421)
                    ·
                      refine ⟨1361996652957232897413977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14527964298210484239082421 1361996652957232897413977)
                      ·
                        rfl

theorem cell23_2652479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_2652479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652479 prefixEnd_2652479 := by exact prefixLift 2652479
  have htrace : WordTrace (prefixWord ++ tailWord_2652479) baseStart_2652479 baseEnd_2652479 := by
    simpa [prefixWord, tailWord_2652479, baseEnd_2652479] using wordTrace_append hprefix tailTrace_2652479
  have hstable : (prefixWord ++ tailWord_2652479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652479).length < 2 ^ (prefixWord ++ tailWord_2652479).sum := by decide
  have hdescent : baseEnd_2652479 < baseStart_2652479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652569 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 2, 4, 3]
def baseStart_2652569 : Nat := 118140960795 + 2652569 * 2 ^ 59
def prefixEnd_2652569 : Nat := 4983230072969 + 3 ^ 40 * 2652569 * 2
def baseEnd_2652569 : Nat := 1362042866216137545288563

theorem tailTrace_2652569 : CollatzResearch.WordTrace tailWord_2652569 prefixEnd_2652569 1362042866216137545288563 := by
  unfold tailWord_2652569
  simp only [CollatzResearch.WordTrace]
  refine ⟨96747139527203010563328761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64498093018135340375552507 96747139527203010563328761)
  ·
    refine ⟨72560354645402257922496571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96747139527203010563328761 72560354645402257922496571)
    ·
      refine ⟨108840531968103386883744857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72560354645402257922496571 108840531968103386883744857)
      ·
        refine ⟨81630398976077540162808643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108840531968103386883744857 81630398976077540162808643)
        ·
          refine ⟨122445598464116310244212965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81630398976077540162808643 122445598464116310244212965)
          ·
            refine ⟨22958549712021808170789931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122445598464116310244212965 22958549712021808170789931)
            ·
              refine ⟨34437824568032712256184897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22958549712021808170789931 34437824568032712256184897)
              ·
                refine ⟨25828368426024534192138673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34437824568032712256184897 25828368426024534192138673)
                ·
                  refine ⟨19371276319518400644104005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25828368426024534192138673 19371276319518400644104005)
                  ·
                    refine ⟨3632114309909700120769501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19371276319518400644104005 3632114309909700120769501)
                    ·
                      refine ⟨1362042866216137545288563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3632114309909700120769501 1362042866216137545288563)
                      ·
                        rfl

theorem cell23_2652569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_2652569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652569 prefixEnd_2652569 := by exact prefixLift 2652569
  have htrace : WordTrace (prefixWord ++ tailWord_2652569) baseStart_2652569 baseEnd_2652569 := by
    simpa [prefixWord, tailWord_2652569, baseEnd_2652569] using wordTrace_append hprefix tailTrace_2652569
  have hstable : (prefixWord ++ tailWord_2652569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652569).length < 2 ^ (prefixWord ++ tailWord_2652569).sum := by decide
  have hdescent : baseEnd_2652569 < baseStart_2652569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652583 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_2652583 : Nat := 118140960795 + 2652583 * 2 ^ 59
def prefixEnd_2652583 : Nat := 4983230072969 + 3 ^ 40 * 2652583 * 2
def baseEnd_2652583 : Nat := 1362050054945300490513499

theorem tailTrace_2652583 : CollatzResearch.WordTrace tailWord_2652583 prefixEnd_2652583 1362050054945300490513499 := by
  unfold tailWord_2652583
  simp only [CollatzResearch.WordTrace]
  refine ⟨96747650149152290954338403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64498433432768193969558935 96747650149152290954338403)
  ·
    refine ⟨145121475223728436431507605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96747650149152290954338403 145121475223728436431507605)
    ·
      refine ⟨6802569151112270457726919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145121475223728436431507605 6802569151112270457726919)
      ·
        refine ⟨10203853726668405686590379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6802569151112270457726919 10203853726668405686590379)
        ·
          refine ⟨15305780590002608529885569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10203853726668405686590379 15305780590002608529885569)
          ·
            refine ⟨11479335442501956397414177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15305780590002608529885569 11479335442501956397414177)
            ·
              refine ⟨8609501581876467298060633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11479335442501956397414177 8609501581876467298060633)
              ·
                refine ⟨6457126186407350473545475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8609501581876467298060633 6457126186407350473545475)
                ·
                  refine ⟨9685689279611025710318213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6457126186407350473545475 9685689279611025710318213)
                  ·
                    refine ⟨1816066739927067320684665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9685689279611025710318213 1816066739927067320684665)
                    ·
                      refine ⟨1362050054945300490513499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816066739927067320684665 1362050054945300490513499)
                      ·
                        rfl

theorem cell23_2652583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_2652583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652583 prefixEnd_2652583 := by exact prefixLift 2652583
  have htrace : WordTrace (prefixWord ++ tailWord_2652583) baseStart_2652583 baseEnd_2652583 := by
    simpa [prefixWord, tailWord_2652583, baseEnd_2652583] using wordTrace_append hprefix tailTrace_2652583
  have hstable : (prefixWord ++ tailWord_2652583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652583).length < 2 ^ (prefixWord ++ tailWord_2652583).sum := by decide
  have hdescent : baseEnd_2652583 < baseStart_2652583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652616 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_2652616 : Nat := 118140960795 + 2652616 * 2 ^ 59
def prefixEnd_2652616 : Nat := 4983230072969 + 3 ^ 40 * 2652616 * 2
def baseEnd_2652616 : Nat := 1362066999806898861400847

theorem tailTrace_2652616 : CollatzResearch.WordTrace tailWord_2652616 prefixEnd_2652616 1362066999806898861400847 := by
  unfold tailWord_2652616
  simp only [CollatzResearch.WordTrace]
  refine ⟨48374426879016368795144851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64499235838688491726859801 48374426879016368795144851)
  ·
    refine ⟨72561640318524553192717277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48374426879016368795144851 72561640318524553192717277)
    ·
      refine ⟨27210615119446707447268979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72561640318524553192717277 27210615119446707447268979)
      ·
        refine ⟨40815922679170061170903469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27210615119446707447268979 40815922679170061170903469)
        ·
          refine ⟨15305971004688772939088801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40815922679170061170903469 15305971004688772939088801)
          ·
            refine ⟨11479478253516579704316601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15305971004688772939088801 11479478253516579704316601)
            ·
              refine ⟨8609608690137434778237451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11479478253516579704316601 8609608690137434778237451)
              ·
                refine ⟨12914413035206152167356177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8609608690137434778237451 12914413035206152167356177)
                ·
                  refine ⟨9685809776404614125517133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12914413035206152167356177 9685809776404614125517133)
                  ·
                    refine ⟨3632178666151730297068925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9685809776404614125517133 3632178666151730297068925)
                    ·
                      refine ⟨1362066999806898861400847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3632178666151730297068925 1362066999806898861400847)
                      ·
                        rfl

theorem cell23_2652616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_2652616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652616 prefixEnd_2652616 := by exact prefixLift 2652616
  have htrace : WordTrace (prefixWord ++ tailWord_2652616) baseStart_2652616 baseEnd_2652616 := by
    simpa [prefixWord, tailWord_2652616, baseEnd_2652616] using wordTrace_append hprefix tailTrace_2652616
  have hstable : (prefixWord ++ tailWord_2652616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652616).length < 2 ^ (prefixWord ++ tailWord_2652616).sum := by decide
  have hdescent : baseEnd_2652616 < baseStart_2652616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652653 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_2652653 : Nat := 118140960795 + 2652653 * 2 ^ 59
def prefixEnd_2652653 : Nat := 4983230072969 + 3 ^ 40 * 2652653 * 2
def baseEnd_2652653 : Nat := 454028666197038405546059

theorem tailTrace_2652653 : CollatzResearch.WordTrace tailWord_2652653 prefixEnd_2652653 454028666197038405546059 := by
  unfold tailWord_2652653
  simp only [CollatzResearch.WordTrace]
  refine ⟨96750203258898692909386613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64500135505932461939591075 96750203258898692909386613)
  ·
    refine ⟨9070331555521752460254995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96750203258898692909386613 9070331555521752460254995)
    ·
      refine ⟨13605497333282628690382493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9070331555521752460254995 13605497333282628690382493)
      ·
        refine ⟨5102061499980985758893435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13605497333282628690382493 5102061499980985758893435)
        ·
          refine ⟨7653092249971478638340153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5102061499980985758893435 7653092249971478638340153)
          ·
            refine ⟨5739819187478608978755115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7653092249971478638340153 5739819187478608978755115)
            ·
              refine ⟨8609728781217913468132673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739819187478608978755115 8609728781217913468132673)
              ·
                refine ⟨6457296585913435101099505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8609728781217913468132673 6457296585913435101099505)
                ·
                  refine ⟨4842972439435076325824629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6457296585913435101099505 4842972439435076325824629)
                  ·
                    refine ⟨454028666197038405546059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4842972439435076325824629 454028666197038405546059)
                    ·
                      rfl

theorem cell23_2652653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_2652653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652653 prefixEnd_2652653 := by exact prefixLift 2652653
  have htrace : WordTrace (prefixWord ++ tailWord_2652653) baseStart_2652653 baseEnd_2652653 := by
    simpa [prefixWord, tailWord_2652653, baseEnd_2652653] using wordTrace_append hprefix tailTrace_2652653
  have hstable : (prefixWord ++ tailWord_2652653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652653).length < 2 ^ (prefixWord ++ tailWord_2652653).sum := by decide
  have hdescent : baseEnd_2652653 < baseStart_2652653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652656 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 4]
def baseStart_2652656 : Nat := 118140960795 + 2652656 * 2 ^ 59
def prefixEnd_2652656 : Nat := 4983230072969 + 3 ^ 40 * 2652656 * 2
def baseEnd_2652656 : Nat := 1362087539033078704900663

theorem tailTrace_2652656 : CollatzResearch.WordTrace tailWord_2652656 prefixEnd_2652656 1362087539033078704900663 := by
  unfold tailWord_2652656
  simp only [CollatzResearch.WordTrace]
  refine ⟨48375156338943912210872911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64500208451925216281163881 48375156338943912210872911)
  ·
    refine ⟨72562734508415868316309367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48375156338943912210872911 72562734508415868316309367)
    ·
      refine ⟨108844101762623802474464051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72562734508415868316309367 108844101762623802474464051)
      ·
        refine ⟨163266152643935703711696077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108844101762623802474464051 163266152643935703711696077)
        ·
          refine ⟨61224807241475888891886029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163266152643935703711696077 61224807241475888891886029)
          ·
            refine ⟨22959302715553458334457261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61224807241475888891886029 22959302715553458334457261)
            ·
              refine ⟨8609738518332546875421473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22959302715553458334457261 8609738518332546875421473)
              ·
                refine ⟨6457303888749410156566105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8609738518332546875421473 6457303888749410156566105)
                ·
                  refine ⟨4842977916562057617424579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6457303888749410156566105 4842977916562057617424579)
                  ·
                    refine ⟨7264466874843086426136869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4842977916562057617424579 7264466874843086426136869)
                    ·
                      refine ⟨1362087539033078704900663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7264466874843086426136869 1362087539033078704900663)
                      ·
                        rfl

theorem cell23_2652656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_2652656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652656 prefixEnd_2652656 := by exact prefixLift 2652656
  have htrace : WordTrace (prefixWord ++ tailWord_2652656) baseStart_2652656 baseEnd_2652656 := by
    simpa [prefixWord, tailWord_2652656, baseEnd_2652656] using wordTrace_append hprefix tailTrace_2652656
  have hstable : (prefixWord ++ tailWord_2652656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652656).length < 2 ^ (prefixWord ++ tailWord_2652656).sum := by decide
  have hdescent : baseEnd_2652656 < baseStart_2652656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652666 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 3, 4]
def baseStart_2652666 : Nat := 118140960795 + 2652666 * 2 ^ 59
def prefixEnd_2652666 : Nat := 4983230072969 + 3 ^ 40 * 2652666 * 2
def baseEnd_2652666 : Nat := 454030891279874555258539

theorem tailTrace_2652666 : CollatzResearch.WordTrace tailWord_2652666 prefixEnd_2652666 454030891279874555258539 := by
  unfold tailWord_2652666
  simp only [CollatzResearch.WordTrace]
  refine ⟨24187669351962899032402463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64500451605234397419739901 24187669351962899032402463)
  ·
    refine ⟨36281504027944348548603695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24187669351962899032402463 36281504027944348548603695)
    ·
      refine ⟨54422256041916522822905543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36281504027944348548603695 54422256041916522822905543)
      ·
        refine ⟨81633384062874784234358315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54422256041916522822905543 81633384062874784234358315)
        ·
          refine ⟨122450076094312176351537473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81633384062874784234358315 122450076094312176351537473)
          ·
            refine ⟨91837557070734132263653105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122450076094312176351537473 91837557070734132263653105)
            ·
              refine ⟨68878167803050599197739829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91837557070734132263653105 68878167803050599197739829)
              ·
                refine ⟨6457328231535993674788109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68878167803050599197739829 6457328231535993674788109)
                ·
                  refine ⟨2421498086825997628045541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6457328231535993674788109 2421498086825997628045541)
                  ·
                    refine ⟨454030891279874555258539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2421498086825997628045541 454030891279874555258539)
                    ·
                      rfl

theorem cell23_2652666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_2652666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652666 prefixEnd_2652666 := by exact prefixLift 2652666
  have htrace : WordTrace (prefixWord ++ tailWord_2652666) baseStart_2652666 baseEnd_2652666 := by
    simpa [prefixWord, tailWord_2652666, baseEnd_2652666] using wordTrace_append hprefix tailTrace_2652666
  have hstable : (prefixWord ++ tailWord_2652666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652666).length < 2 ^ (prefixWord ++ tailWord_2652666).sum := by decide
  have hdescent : baseEnd_2652666 < baseStart_2652666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652693 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_2652693 : Nat := 118140960795 + 2652693 * 2 ^ 59
def prefixEnd_2652693 : Nat := 4983230072969 + 3 ^ 40 * 2652693 * 2
def baseEnd_2652693 : Nat := 1362106537817295060137993

theorem tailTrace_2652693 : CollatzResearch.WordTrace tailWord_2652693 prefixEnd_2652693 1362106537817295060137993 := by
  unfold tailWord_2652693
  simp only [CollatzResearch.WordTrace]
  refine ⟨96751662178753779740842733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64501108119169186493895155 96751662178753779740842733)
  ·
    refine ⟨36281873317032667402816025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96751662178753779740842733 36281873317032667402816025)
    ·
      refine ⟨27211404987774500552112019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36281873317032667402816025 27211404987774500552112019)
      ·
        refine ⟨40817107481661750828168029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27211404987774500552112019 40817107481661750828168029)
        ·
          refine ⟨15306415305623156560563011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40817107481661750828168029 15306415305623156560563011)
          ·
            refine ⟨22959622958434734840844517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15306415305623156560563011 22959622958434734840844517)
            ·
              refine ⟨4304929304706512782658347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22959622958434734840844517 4304929304706512782658347)
              ·
                refine ⟨6457393957059769173987521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304929304706512782658347 6457393957059769173987521)
                ·
                  refine ⟨4843045467794826880490641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6457393957059769173987521 4843045467794826880490641)
                  ·
                    refine ⟨3632284100846120160367981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4843045467794826880490641 3632284100846120160367981)
                    ·
                      refine ⟨1362106537817295060137993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3632284100846120160367981 1362106537817295060137993)
                      ·
                        rfl

theorem cell23_2652693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_2652693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652693 prefixEnd_2652693 := by exact prefixLift 2652693
  have htrace : WordTrace (prefixWord ++ tailWord_2652693) baseStart_2652693 baseEnd_2652693 := by
    simpa [prefixWord, tailWord_2652693, baseEnd_2652693] using wordTrace_append hprefix tailTrace_2652693
  have hstable : (prefixWord ++ tailWord_2652693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652693).length < 2 ^ (prefixWord ++ tailWord_2652693).sum := by decide
  have hdescent : baseEnd_2652693 < baseStart_2652693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652719 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_2652719 : Nat := 118140960795 + 2652719 * 2 ^ 59
def prefixEnd_2652719 : Nat := 4983230072969 + 3 ^ 40 * 2652719 * 2
def baseEnd_2652719 : Nat := 1362119888314311958412873

theorem tailTrace_2652719 : CollatzResearch.WordTrace tailWord_2652719 prefixEnd_2652719 1362119888314311958412873 := by
  unfold tailWord_2652719
  simp only [CollatzResearch.WordTrace]
  refine ⟨96752610476659586181289211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64501740317773057454192807 96752610476659586181289211)
  ·
    refine ⟨145128915714989379271933817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96752610476659586181289211 145128915714989379271933817)
    ·
      refine ⟨108846686786242034453950363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145128915714989379271933817 108846686786242034453950363)
      ·
        refine ⟨163270030179363051680925545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108846686786242034453950363 163270030179363051680925545)
        ·
          refine ⟨122452522634522288760694159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163270030179363051680925545 122452522634522288760694159)
          ·
            refine ⟨183678783951783433141041239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122452522634522288760694159 183678783951783433141041239)
            ·
              refine ⟨275518175927675149711561859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183678783951783433141041239 275518175927675149711561859)
              ·
                refine ⟨413277263891512724567342789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275518175927675149711561859 413277263891512724567342789)
                ·
                  refine ⟨77489486979658635856376773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 413277263891512724567342789 77489486979658635856376773)
                  ·
                    refine ⟨14529278808685994223070645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77489486979658635856376773 14529278808685994223070645)
                    ·
                      refine ⟨1362119888314311958412873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14529278808685994223070645 1362119888314311958412873)
                      ·
                        rfl

theorem cell23_2652719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_2652719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652719 prefixEnd_2652719 := by exact prefixLift 2652719
  have htrace : WordTrace (prefixWord ++ tailWord_2652719) baseStart_2652719 baseEnd_2652719 := by
    simpa [prefixWord, tailWord_2652719, baseEnd_2652719] using wordTrace_append hprefix tailTrace_2652719
  have hstable : (prefixWord ++ tailWord_2652719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652719).length < 2 ^ (prefixWord ++ tailWord_2652719).sum := by decide
  have hdescent : baseEnd_2652719 < baseStart_2652719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652723 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 3, 1, 3]
def baseStart_2652723 : Nat := 118140960795 + 2652723 * 2 ^ 59
def prefixEnd_2652723 : Nat := 4983230072969 + 3 ^ 40 * 2652723 * 2
def baseEnd_2652723 : Nat := 1362121942236929942762855

theorem tailTrace_2652723 : CollatzResearch.WordTrace tailWord_2652723 prefixEnd_2652723 1362121942236929942762855 := by
  unfold tailWord_2652723
  simp only [CollatzResearch.WordTrace]
  refine ⟨96752756368645094864434823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64501837579096729909623215 96752756368645094864434823)
  ·
    refine ⟨145129134552967642296652235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96752756368645094864434823 145129134552967642296652235)
    ·
      refine ⟨217693701829451463444978353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145129134552967642296652235 217693701829451463444978353)
      ·
        refine ⟨163270276372088597583733765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217693701829451463444978353 163270276372088597583733765)
        ·
          refine ⟨30613176819766612046950081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163270276372088597583733765 30613176819766612046950081)
          ·
            refine ⟨22959882614824959035212561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30613176819766612046950081 22959882614824959035212561)
            ·
              refine ⟨17219911961118719276409421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22959882614824959035212561 17219911961118719276409421)
              ·
                refine ⟨6457466985419519728653533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17219911961118719276409421 6457466985419519728653533)
                ·
                  refine ⟨2421550119532319898245075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6457466985419519728653533 2421550119532319898245075)
                  ·
                    refine ⟨3632325179298479847367613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2421550119532319898245075 3632325179298479847367613)
                    ·
                      refine ⟨1362121942236929942762855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3632325179298479847367613 1362121942236929942762855)
                      ·
                        rfl

theorem cell23_2652723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 1, 3].length) (baseStart_2652723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652723 prefixEnd_2652723 := by exact prefixLift 2652723
  have htrace : WordTrace (prefixWord ++ tailWord_2652723) baseStart_2652723 baseEnd_2652723 := by
    simpa [prefixWord, tailWord_2652723, baseEnd_2652723] using wordTrace_append hprefix tailTrace_2652723
  have hstable : (prefixWord ++ tailWord_2652723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652723).length < 2 ^ (prefixWord ++ tailWord_2652723).sum := by decide
  have hdescent : baseEnd_2652723 < baseStart_2652723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652750 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2]
def baseStart_2652750 : Nat := 118140960795 + 2652750 * 2 ^ 59
def prefixEnd_2652750 : Nat := 4983230072969 + 3 ^ 40 * 2652750 * 2
def baseEnd_2652750 : Nat := 1362135806214601337125231

theorem tailTrace_2652750 : CollatzResearch.WordTrace tailWord_2652750 prefixEnd_2652750 1362135806214601337125231 := by
  unfold tailWord_2652750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12094217642443409809458463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64502494093031518983778469 12094217642443409809458463)
  ·
    refine ⟨18141326463665114714187695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12094217642443409809458463 18141326463665114714187695)
    ·
      refine ⟨27211989695497672071281543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18141326463665114714187695 27211989695497672071281543)
      ·
        refine ⟨40817984543246508106922315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27211989695497672071281543 40817984543246508106922315)
        ·
          refine ⟨61226976814869762160383473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40817984543246508106922315 61226976814869762160383473)
          ·
            refine ⟨45920232611152321620287605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61226976814869762160383473 45920232611152321620287605)
            ·
              refine ⟨4305021807295530151901963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45920232611152321620287605 4305021807295530151901963)
              ·
                refine ⟨6457532710943295227852945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305021807295530151901963 6457532710943295227852945)
                ·
                  refine ⟨4843149533207471420889709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6457532710943295227852945 4843149533207471420889709)
                  ·
                    refine ⟨1816181074952801782833641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4843149533207471420889709 1816181074952801782833641)
                    ·
                      refine ⟨1362135806214601337125231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816181074952801782833641 1362135806214601337125231)
                      ·
                        rfl

theorem cell23_2652750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_2652750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652750 prefixEnd_2652750 := by exact prefixLift 2652750
  have htrace : WordTrace (prefixWord ++ tailWord_2652750) baseStart_2652750 baseEnd_2652750 := by
    simpa [prefixWord, tailWord_2652750, baseEnd_2652750] using wordTrace_append hprefix tailTrace_2652750
  have hstable : (prefixWord ++ tailWord_2652750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652750).length < 2 ^ (prefixWord ++ tailWord_2652750).sum := by decide
  have hdescent : baseEnd_2652750 < baseStart_2652750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652780 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 3, 2, 2]
def baseStart_2652780 : Nat := 118140960795 + 2652780 * 2 ^ 59
def prefixEnd_2652780 : Nat := 4983230072969 + 3 ^ 40 * 2652780 * 2
def baseEnd_2652780 : Nat := 1362151210634236219750093

theorem tailTrace_2652780 : CollatzResearch.WordTrace tailWord_2652780 prefixEnd_2652780 1362151210634236219750093 := by
  unfold tailWord_2652780
  simp only [CollatzResearch.WordTrace]
  refine ⟨48377417664719296799629897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64503223552959062399506529 48377417664719296799629897)
  ·
    refine ⟨36283063248539472599722423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48377417664719296799629897 36283063248539472599722423)
    ·
      refine ⟨54424594872809208899583635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36283063248539472599722423 54424594872809208899583635)
      ·
        refine ⟨81636892309213813349375453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54424594872809208899583635 81636892309213813349375453)
        ·
          refine ⟨30613834615955180006015795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81636892309213813349375453 30613834615955180006015795)
          ·
            refine ⟨45920751923932770009023693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30613834615955180006015795 45920751923932770009023693)
            ·
              refine ⟨17220281971474788753383885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45920751923932770009023693 17220281971474788753383885)
              ·
                refine ⟨6457605739303045782518957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17220281971474788753383885 6457605739303045782518957)
                ·
                  refine ⟨2421602152238642168444609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6457605739303045782518957 2421602152238642168444609)
                  ·
                    refine ⟨1816201614178981626333457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2421602152238642168444609 1816201614178981626333457)
                    ·
                      refine ⟨1362151210634236219750093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816201614178981626333457 1362151210634236219750093)
                      ·
                        rfl

theorem cell23_2652780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 2, 2].length) (baseStart_2652780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652780 prefixEnd_2652780 := by exact prefixLift 2652780
  have htrace : WordTrace (prefixWord ++ tailWord_2652780) baseStart_2652780 baseEnd_2652780 := by
    simpa [prefixWord, tailWord_2652780, baseEnd_2652780] using wordTrace_append hprefix tailTrace_2652780
  have hstable : (prefixWord ++ tailWord_2652780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652780).length < 2 ^ (prefixWord ++ tailWord_2652780).sum := by decide
  have hdescent : baseEnd_2652780 < baseStart_2652780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652793 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 4]
def baseStart_2652793 : Nat := 118140960795 + 2652793 * 2 ^ 59
def prefixEnd_2652793 : Nat := 4983230072969 + 3 ^ 40 * 2652793 * 2
def baseEnd_2652793 : Nat := 1362157885882744668887533

theorem tailTrace_2652793 : CollatzResearch.WordTrace tailWord_2652793 prefixEnd_2652793 1362157885882744668887533 := by
  unfold tailWord_2652793
  simp only [CollatzResearch.WordTrace]
  refine ⟨96755309478391496819483033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64503539652260997879655355 96755309478391496819483033)
  ·
    refine ⟨72566482108793622614612275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96755309478391496819483033 72566482108793622614612275)
    ·
      refine ⟨108849723163190433921918413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72566482108793622614612275 108849723163190433921918413)
      ·
        refine ⟨40818646186196412720719405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108849723163190433921918413 40818646186196412720719405)
        ·
          refine ⟨15306992319823654770269777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40818646186196412720719405 15306992319823654770269777)
          ·
            refine ⟨11480244239867741077702333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15306992319823654770269777 11480244239867741077702333)
            ·
              refine ⟨4305091589950402904138375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11480244239867741077702333 4305091589950402904138375)
              ·
                refine ⟨6457637384925604356207563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305091589950402904138375 6457637384925604356207563)
                ·
                  refine ⟨9686456077388406534311345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6457637384925604356207563 9686456077388406534311345)
                  ·
                    refine ⟨7264842058041304900733509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9686456077388406534311345 7264842058041304900733509)
                    ·
                      refine ⟨1362157885882744668887533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7264842058041304900733509 1362157885882744668887533)
                      ·
                        rfl

theorem cell23_2652793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_2652793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652793 prefixEnd_2652793 := by exact prefixLift 2652793
  have htrace : WordTrace (prefixWord ++ tailWord_2652793) baseStart_2652793 baseEnd_2652793 := by
    simpa [prefixWord, tailWord_2652793, baseEnd_2652793] using wordTrace_append hprefix tailTrace_2652793
  have hstable : (prefixWord ++ tailWord_2652793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652793).length < 2 ^ (prefixWord ++ tailWord_2652793).sum := by decide
  have hdescent : baseEnd_2652793 < baseStart_2652793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652800 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 3]
def baseStart_2652800 : Nat := 118140960795 + 2652800 * 2 ^ 59
def prefixEnd_2652800 : Nat := 4983230072969 + 3 ^ 40 * 2652800 * 2
def baseEnd_2652800 : Nat := 1362161480247326141500001

theorem tailTrace_2652800 : CollatzResearch.WordTrace tailWord_2652800 prefixEnd_2652800 1362161480247326141500001 := by
  unfold tailWord_2652800
  simp only [CollatzResearch.WordTrace]
  refine ⟨48377782394683068507493927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64503709859577424676658569 48377782394683068507493927)
  ·
    refine ⟨72566673592024602761240891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48377782394683068507493927 72566673592024602761240891)
    ·
      refine ⟨108850010388036904141861337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72566673592024602761240891 108850010388036904141861337)
      ·
        refine ⟨81637507791027678106396003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108850010388036904141861337 81637507791027678106396003)
        ·
          refine ⟨122456261686541517159594005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81637507791027678106396003 122456261686541517159594005)
          ·
            refine ⟨5740137266556633616855969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122456261686541517159594005 5740137266556633616855969)
            ·
              refine ⟨4305102949917475212641977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5740137266556633616855969 4305102949917475212641977)
              ·
                refine ⟨3228827212438106409481483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4305102949917475212641977 3228827212438106409481483)
                ·
                  refine ⟨4843240818657159614222225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228827212438106409481483 4843240818657159614222225)
                  ·
                    refine ⟨3632430613992869710666669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4843240818657159614222225 3632430613992869710666669)
                    ·
                      refine ⟨1362161480247326141500001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3632430613992869710666669 1362161480247326141500001)
                      ·
                        rfl

theorem cell23_2652800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_2652800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652800 prefixEnd_2652800 := by exact prefixLift 2652800
  have htrace : WordTrace (prefixWord ++ tailWord_2652800) baseStart_2652800 baseEnd_2652800 := by
    simpa [prefixWord, tailWord_2652800, baseEnd_2652800] using wordTrace_append hprefix tailTrace_2652800
  have hstable : (prefixWord ++ tailWord_2652800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652800).length < 2 ^ (prefixWord ++ tailWord_2652800).sum := by decide
  have hdescent : baseEnd_2652800 < baseStart_2652800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652847 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 2, 1, 3]
def baseStart_2652847 : Nat := 118140960795 + 2652847 * 2 ^ 59
def prefixEnd_2652847 : Nat := 4983230072969 + 3 ^ 40 * 2652847 * 2
def baseEnd_2652847 : Nat := 1362185613838087457612285

theorem tailTrace_2652847 : CollatzResearch.WordTrace tailWord_2652847 prefixEnd_2652847 1362185613838087457612285 := by
  unfold tailWord_2652847
  simp only [CollatzResearch.WordTrace]
  refine ⟨96757279020195864041948795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64504852680130576027965863 96757279020195864041948795)
  ·
    refine ⟨145135918530293796062923193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96757279020195864041948795 145135918530293796062923193)
    ·
      refine ⟨108851938897720347047192395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145135918530293796062923193 108851938897720347047192395)
      ·
        refine ⟨163277908346580520570788593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108851938897720347047192395 163277908346580520570788593)
        ·
          refine ⟨122458431259935390428091445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163277908346580520570788593 122458431259935390428091445)
          ·
            refine ⟨11480477930618942852633573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122458431259935390428091445 11480477930618942852633573)
            ·
              refine ⟨2152589611991051784868795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11480477930618942852633573 2152589611991051784868795)
              ·
                refine ⟨3228884417986577677303193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152589611991051784868795 3228884417986577677303193)
                ·
                  refine ⟨2421663313489933257977395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3228884417986577677303193 2421663313489933257977395)
                  ·
                    refine ⟨3632494970234899886966093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2421663313489933257977395 3632494970234899886966093)
                    ·
                      refine ⟨1362185613838087457612285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3632494970234899886966093 1362185613838087457612285)
                      ·
                        rfl

theorem cell23_2652847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 2, 1, 3].length) (baseStart_2652847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652847 prefixEnd_2652847 := by exact prefixLift 2652847
  have htrace : WordTrace (prefixWord ++ tailWord_2652847) baseStart_2652847 baseEnd_2652847 := by
    simpa [prefixWord, tailWord_2652847, baseEnd_2652847] using wordTrace_append hprefix tailTrace_2652847
  have hstable : (prefixWord ++ tailWord_2652847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652847).length < 2 ^ (prefixWord ++ tailWord_2652847).sum := by decide
  have hdescent : baseEnd_2652847 < baseStart_2652847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652874 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2]
def baseStart_2652874 : Nat := 118140960795 + 2652874 * 2 ^ 59
def prefixEnd_2652874 : Nat := 4983230072969 + 3 ^ 40 * 2652874 * 2
def baseEnd_2652874 : Nat := 1362199477815758851974661

theorem tailTrace_2652874 : CollatzResearch.WordTrace tailWord_2652874 prefixEnd_2652874 1362199477815758851974661 := by
  unfold tailWord_2652874
  simp only [CollatzResearch.WordTrace]
  refine ⟨24189565947774511913295419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64505509194065365102121117 24189565947774511913295419)
  ·
    refine ⟨36284348921661767869943129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24189565947774511913295419 36284348921661767869943129)
    ·
      refine ⟨27213261691246325902457347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36284348921661767869943129 27213261691246325902457347)
      ·
        refine ⟨40819892536869488853686021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27213261691246325902457347 40819892536869488853686021)
        ·
          refine ⟨7653729850663029160066129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40819892536869488853686021 7653729850663029160066129)
          ·
            refine ⟨5740297387997271870049597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7653729850663029160066129 5740297387997271870049597)
            ·
              refine ⟨2152611520498976951268599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5740297387997271870049597 2152611520498976951268599)
              ·
                refine ⟨3228917280748465426902899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152611520498976951268599 3228917280748465426902899)
                ·
                  refine ⟨4843375921122698140354349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228917280748465426902899 4843375921122698140354349)
                  ·
                    refine ⟨1816265970421011802632881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4843375921122698140354349 1816265970421011802632881)
                    ·
                      refine ⟨1362199477815758851974661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816265970421011802632881 1362199477815758851974661)
                      ·
                        rfl

theorem cell23_2652874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_2652874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652874 prefixEnd_2652874 := by exact prefixLift 2652874
  have htrace : WordTrace (prefixWord ++ tailWord_2652874) baseStart_2652874 baseEnd_2652874 := by
    simpa [prefixWord, tailWord_2652874, baseEnd_2652874] using wordTrace_append hprefix tailTrace_2652874
  have hstable : (prefixWord ++ tailWord_2652874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652874).length < 2 ^ (prefixWord ++ tailWord_2652874).sum := by decide
  have hdescent : baseEnd_2652874 < baseStart_2652874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652887 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 2, 2, 2]
def baseStart_2652887 : Nat := 118140960795 + 2652887 * 2 ^ 59
def prefixEnd_2652887 : Nat := 4983230072969 + 3 ^ 40 * 2652887 * 2
def baseEnd_2652887 : Nat := 1362206153064267301112101

theorem tailTrace_2652887 : CollatzResearch.WordTrace tailWord_2652887 prefixEnd_2652887 1362206153064267301112101 := by
  unfold tailWord_2652887
  simp only [CollatzResearch.WordTrace]
  refine ⟨96758737940050950873404915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64505825293367300582269943 96758737940050950873404915)
  ·
    refine ⟨145138106910076426310107373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96758737940050950873404915 145138106910076426310107373)
    ·
      refine ⟨54426790091278659866290265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145138106910076426310107373 54426790091278659866290265)
      ·
        refine ⟨40820092568458994899717699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54426790091278659866290265 40820092568458994899717699)
        ·
          refine ⟨61230138852688492349576549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40820092568458994899717699 61230138852688492349576549)
          ·
            refine ⟨11480651034879092315545603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61230138852688492349576549 11480651034879092315545603)
            ·
              refine ⟨17220976552318638473318405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11480651034879092315545603 17220976552318638473318405)
              ·
                refine ⟨3228933103559744713747201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17220976552318638473318405 3228933103559744713747201)
                ·
                  refine ⟨2421699827669808535310401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3228933103559744713747201 2421699827669808535310401)
                  ·
                    refine ⟨1816274870752356401482801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2421699827669808535310401 1816274870752356401482801)
                    ·
                      refine ⟨1362206153064267301112101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816274870752356401482801 1362206153064267301112101)
                      ·
                        rfl

theorem cell23_2652887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_2652887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652887 prefixEnd_2652887 := by exact prefixLift 2652887
  have htrace : WordTrace (prefixWord ++ tailWord_2652887) baseStart_2652887 baseEnd_2652887 := by
    simpa [prefixWord, tailWord_2652887, baseEnd_2652887] using wordTrace_append hprefix tailTrace_2652887
  have hstable : (prefixWord ++ tailWord_2652887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652887).length < 2 ^ (prefixWord ++ tailWord_2652887).sum := by decide
  have hdescent : baseEnd_2652887 < baseStart_2652887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652896 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_2652896 : Nat := 118140960795 + 2652896 * 2 ^ 59
def prefixEnd_2652896 : Nat := 4983230072969 + 3 ^ 40 * 2652896 * 2
def baseEnd_2652896 : Nat := 1362210774390157765899559

theorem tailTrace_2652896 : CollatzResearch.WordTrace tailWord_2652896 prefixEnd_2652896 1362210774390157765899559 := by
  unfold tailWord_2652896
  simp only [CollatzResearch.WordTrace]
  refine ⟨48379533098509172705241271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64506044131345563606988361 48379533098509172705241271)
  ·
    refine ⟨72569299647763759057861907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48379533098509172705241271 72569299647763759057861907)
    ·
      refine ⟨108853949471645638586792861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72569299647763759057861907 108853949471645638586792861)
      ·
        refine ⟨40820231051867114470047323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108853949471645638586792861 40820231051867114470047323)
        ·
          refine ⟨61230346577800671705070985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40820231051867114470047323 61230346577800671705070985)
          ·
            refine ⟨45922759933350503778803239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61230346577800671705070985 45922759933350503778803239)
            ·
              refine ⟨68884139900025755668204859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45922759933350503778803239 68884139900025755668204859)
              ·
                refine ⟨103326209850038633502307289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68884139900025755668204859 103326209850038633502307289)
                ·
                  refine ⟨77494657387528975126730467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103326209850038633502307289 77494657387528975126730467)
                  ·
                    refine ⟨116241986081293462690095701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77494657387528975126730467 116241986081293462690095701)
                    ·
                      refine ⟨1362210774390157765899559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 116241986081293462690095701 1362210774390157765899559)
                      ·
                        rfl

theorem cell23_2652896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_2652896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652896 prefixEnd_2652896 := by exact prefixLift 2652896
  have htrace : WordTrace (prefixWord ++ tailWord_2652896) baseStart_2652896 baseEnd_2652896 := by
    simpa [prefixWord, tailWord_2652896, baseEnd_2652896] using wordTrace_append hprefix tailTrace_2652896
  have hstable : (prefixWord ++ tailWord_2652896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652896).length < 2 ^ (prefixWord ++ tailWord_2652896).sum := by decide
  have hdescent : baseEnd_2652896 < baseStart_2652896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652943 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 4]
def baseStart_2652943 : Nat := 118140960795 + 2652943 * 2 ^ 59
def prefixEnd_2652943 : Nat := 4983230072969 + 3 ^ 40 * 2652943 * 2
def baseEnd_2652943 : Nat := 1362234907980919082011843

theorem tailTrace_2652943 : CollatzResearch.WordTrace tailWord_2652943 prefixEnd_2652943 1362234907980919082011843 := by
  unfold tailWord_2652943
  simp only [CollatzResearch.WordTrace]
  refine ⟨96760780427848072437443483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64507186951898714958295655 96760780427848072437443483)
  ·
    refine ⟨145141170641772108656165225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96760780427848072437443483 145141170641772108656165225)
    ·
      refine ⟨108855877981329081492123919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145141170641772108656165225 108855877981329081492123919)
      ·
        refine ⟨163283816971993622238185879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108855877981329081492123919 163283816971993622238185879)
        ·
          refine ⟨244925725457990433357278819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163283816971993622238185879 244925725457990433357278819)
          ·
            refine ⟨367388588186985650035918229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244925725457990433357278819 367388588186985650035918229)
            ·
              refine ⟨17221340071264952345433667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 367388588186985650035918229 17221340071264952345433667)
              ·
                refine ⟨25832010106897428518150501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17221340071264952345433667 25832010106897428518150501)
                ·
                  refine ⟨4843501895043267847153219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25832010106897428518150501 4843501895043267847153219)
                  ·
                    refine ⟨7265252842564901770729829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4843501895043267847153219 7265252842564901770729829)
                    ·
                      refine ⟨1362234907980919082011843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7265252842564901770729829 1362234907980919082011843)
                      ·
                        rfl

theorem cell23_2652943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_2652943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2652943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2652943 prefixEnd_2652943 := by exact prefixLift 2652943
  have htrace : WordTrace (prefixWord ++ tailWord_2652943) baseStart_2652943 baseEnd_2652943 := by
    simpa [prefixWord, tailWord_2652943, baseEnd_2652943] using wordTrace_append hprefix tailTrace_2652943
  have hstable : (prefixWord ++ tailWord_2652943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652943).length < 2 ^ (prefixWord ++ tailWord_2652943).sum := by decide
  have hdescent : baseEnd_2652943 < baseStart_2652943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653017 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 6]
def baseStart_2653017 : Nat := 118140960795 + 2653017 * 2 ^ 59
def prefixEnd_2653017 : Nat := 4983230072969 + 3 ^ 40 * 2653017 * 2
def baseEnd_2653017 : Nat := 151363656172150199165167

theorem tailTrace_2653017 : CollatzResearch.WordTrace tailWord_2653017 prefixEnd_2653017 151363656172150199165167 := by
  unfold tailWord_2653017
  simp only [CollatzResearch.WordTrace]
  refine ⟨96763479429579983075637305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64508986286386655383758203 96763479429579983075637305)
  ·
    refine ⟨72572609572184987306727979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96763479429579983075637305 72572609572184987306727979)
    ·
      refine ⟨108858914358277480960091969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72572609572184987306727979 108858914358277480960091969)
      ·
        refine ⟨81644185768708110720068977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108858914358277480960091969 81644185768708110720068977)
        ·
          refine ⟨61233139326531083040051733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81644185768708110720068977 61233139326531083040051733)
          ·
            refine ⟨2870303405931144517502425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61233139326531083040051733 2870303405931144517502425)
            ·
              refine ⟨2152727554448358388126819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870303405931144517502425 2152727554448358388126819)
              ·
                refine ⟨3229091331672537582190229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152727554448358388126819 3229091331672537582190229)
                ·
                  refine ⟨151363656172150199165167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3229091331672537582190229 151363656172150199165167)
                  ·
                    rfl

theorem cell23_2653017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 6].length) (baseStart_2653017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653017 prefixEnd_2653017 := by exact prefixLift 2653017
  have htrace : WordTrace (prefixWord ++ tailWord_2653017) baseStart_2653017 baseEnd_2653017 := by
    simpa [prefixWord, tailWord_2653017, baseEnd_2653017] using wordTrace_append hprefix tailTrace_2653017
  have hstable : (prefixWord ++ tailWord_2653017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653017).length < 2 ^ (prefixWord ++ tailWord_2653017).sum := by decide
  have hdescent : baseEnd_2653017 < baseStart_2653017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653043 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 3, 6]
def baseStart_2653043 : Nat := 118140960795 + 2653043 * 2 ^ 59
def prefixEnd_2653043 : Nat := 4983230072969 + 3 ^ 40 * 2653043 * 2
def baseEnd_2653043 : Nat := 454095418682122896920461

theorem tailTrace_2653043 : CollatzResearch.WordTrace tailWord_2653043 prefixEnd_2653043 454095418682122896920461 := by
  unfold tailWord_2653043
  simp only [CollatzResearch.WordTrace]
  refine ⟨96764427727485789516083783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64509618484990526344055855 96764427727485789516083783)
  ·
    refine ⟨145146641591228684274125675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96764427727485789516083783 145146641591228684274125675)
    ·
      refine ⟨217719962386843026411188513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145146641591228684274125675 217719962386843026411188513)
      ·
        refine ⟨163289971790132269808391385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217719962386843026411188513 163289971790132269808391385)
        ·
          refine ⟨122467478842599202356293539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163289971790132269808391385 122467478842599202356293539)
          ·
            refine ⟨183701218263898803534440309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122467478842599202356293539 183701218263898803534440309)
            ·
              refine ⟨17221989212240512831353779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183701218263898803534440309 17221989212240512831353779)
              ·
                refine ⟨25832983818360769247030669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17221989212240512831353779 25832983818360769247030669)
                ·
                  refine ⟨9687368931885288467636501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25832983818360769247030669 9687368931885288467636501)
                  ·
                    refine ⟨454095418682122896920461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9687368931885288467636501 454095418682122896920461)
                    ·
                      rfl

theorem cell23_2653043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 6].length) (baseStart_2653043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653043 prefixEnd_2653043 := by exact prefixLift 2653043
  have htrace : WordTrace (prefixWord ++ tailWord_2653043) baseStart_2653043 baseEnd_2653043 := by
    simpa [prefixWord, tailWord_2653043, baseEnd_2653043] using wordTrace_append hprefix tailTrace_2653043
  have hstable : (prefixWord ++ tailWord_2653043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653043).length < 2 ^ (prefixWord ++ tailWord_2653043).sum := by decide
  have hdescent : baseEnd_2653043 < baseStart_2653043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653061 : List Nat := [1, 3, 1, 1, 3, 3, 4, 2, 1, 1, 3]
def baseStart_2653061 : Nat := 118140960795 + 2653061 * 2 ^ 59
def prefixEnd_2653061 : Nat := 4983230072969 + 3 ^ 40 * 2653061 * 2
def baseEnd_2653061 : Nat := 1362295498698149620336301

theorem tailTrace_2653061 : CollatzResearch.WordTrace tailWord_2653061 prefixEnd_2653061 1362295498698149620336301 := by
  unfold tailWord_2653061
  simp only [CollatzResearch.WordTrace]
  refine ⟨96765084241420578590239037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64510056160947052393492691 96765084241420578590239037)
  ·
    refine ⟨36286906590532716971339639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96765084241420578590239037 36286906590532716971339639)
    ·
      refine ⟨54430359885799075457009459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36286906590532716971339639 54430359885799075457009459)
      ·
        refine ⟨81645539828698613185514189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54430359885799075457009459 81645539828698613185514189)
        ·
          refine ⟨30617077435761979944567821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81645539828698613185514189 30617077435761979944567821)
          ·
            refine ⟨11481404038410742479212933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30617077435761979944567821 11481404038410742479212933)
            ·
              refine ⟨2152763257202014214852425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11481404038410742479212933 2152763257202014214852425)
              ·
                refine ⟨1614572442901510661139319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2152763257202014214852425 1614572442901510661139319)
                ·
                  refine ⟨2421858664352265991708979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614572442901510661139319 2421858664352265991708979)
                  ·
                    refine ⟨3632787996528398987563469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2421858664352265991708979 3632787996528398987563469)
                    ·
                      refine ⟨1362295498698149620336301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3632787996528398987563469 1362295498698149620336301)
                      ·
                        rfl

theorem cell23_2653061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 1, 1, 3].length) (baseStart_2653061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653061 prefixEnd_2653061 := by exact prefixLift 2653061
  have htrace : WordTrace (prefixWord ++ tailWord_2653061) baseStart_2653061 baseEnd_2653061 := by
    simpa [prefixWord, tailWord_2653061, baseEnd_2653061] using wordTrace_append hprefix tailTrace_2653061
  have hstable : (prefixWord ++ tailWord_2653061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653061).length < 2 ^ (prefixWord ++ tailWord_2653061).sum := by decide
  have hdescent : baseEnd_2653061 < baseStart_2653061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653077 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 2, 4]
def baseStart_2653077 : Nat := 118140960795 + 2653077 * 2 ^ 59
def prefixEnd_2653077 : Nat := 4983230072969 + 3 ^ 40 * 2653077 * 2
def baseEnd_2653077 : Nat := 454101238129540519245409

theorem tailTrace_2653077 : CollatzResearch.WordTrace tailWord_2653077 prefixEnd_2653077 454101238129540519245409 := by
  unfold tailWord_2653077
  simp only [CollatzResearch.WordTrace]
  refine ⟨96765667809362613322821485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64510445206241742215214323 96765667809362613322821485)
  ·
    refine ⟨36287125428510979996058057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96765667809362613322821485 36287125428510979996058057)
    ·
      refine ⟨27215344071383234997043543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36287125428510979996058057 27215344071383234997043543)
      ·
        refine ⟨40823016107074852495565315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27215344071383234997043543 40823016107074852495565315)
        ·
          refine ⟨61234524160612278743347973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40823016107074852495565315 61234524160612278743347973)
          ·
            refine ⟨11481473280114802264377745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61234524160612278743347973 11481473280114802264377745)
            ·
              refine ⟨8611104960086101698283309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11481473280114802264377745 8611104960086101698283309)
              ·
                refine ⟨3229164360032288136856241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8611104960086101698283309 3229164360032288136856241)
                ·
                  refine ⟨2421873270024216102642181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3229164360032288136856241 2421873270024216102642181)
                  ·
                    refine ⟨454101238129540519245409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2421873270024216102642181 454101238129540519245409)
                    ·
                      rfl

theorem cell23_2653077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_2653077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653077 prefixEnd_2653077 := by exact prefixLift 2653077
  have htrace : WordTrace (prefixWord ++ tailWord_2653077) baseStart_2653077 baseEnd_2653077 := by
    simpa [prefixWord, tailWord_2653077, baseEnd_2653077] using wordTrace_append hprefix tailTrace_2653077
  have hstable : (prefixWord ++ tailWord_2653077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653077).length < 2 ^ (prefixWord ++ tailWord_2653077).sum := by decide
  have hdescent : baseEnd_2653077 < baseStart_2653077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653078 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2653078 : Nat := 118140960795 + 2653078 * 2 ^ 59
def prefixEnd_2653078 : Nat := 4983230072969 + 3 ^ 40 * 2653078 * 2
def baseEnd_2653078 : Nat := 1362304227869276053823723

theorem tailTrace_2653078 : CollatzResearch.WordTrace tailWord_2653078 prefixEnd_2653078 1362304227869276053823723 := by
  unfold tailWord_2653078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6047856517647436905850493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64510469521572660329071925 6047856517647436905850493)
  ·
    refine ⟨2267946194117788839693935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6047856517647436905850493 2267946194117788839693935)
    ·
      refine ⟨3401919291176683259540903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267946194117788839693935 3401919291176683259540903)
      ·
        refine ⟨5102878936765024889311355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401919291176683259540903 5102878936765024889311355)
        ·
          refine ⟨7654318405147537333967033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5102878936765024889311355 7654318405147537333967033)
          ·
            refine ⟨5740738803860653000475275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7654318405147537333967033 5740738803860653000475275)
            ·
              refine ⟨8611108205790979500712913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5740738803860653000475275 8611108205790979500712913)
              ·
                refine ⟨6458331154343234625534685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8611108205790979500712913 6458331154343234625534685)
                ·
                  refine ⟨2421874182878712984575507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6458331154343234625534685 2421874182878712984575507)
                  ·
                    refine ⟨3632811274318069476863261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2421874182878712984575507 3632811274318069476863261)
                    ·
                      refine ⟨1362304227869276053823723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3632811274318069476863261 1362304227869276053823723)
                      ·
                        rfl

theorem cell23_2653078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2653078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653078 prefixEnd_2653078 := by exact prefixLift 2653078
  have htrace : WordTrace (prefixWord ++ tailWord_2653078) baseStart_2653078 baseEnd_2653078 := by
    simpa [prefixWord, tailWord_2653078, baseEnd_2653078] using wordTrace_append hprefix tailTrace_2653078
  have hstable : (prefixWord ++ tailWord_2653078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653078).length < 2 ^ (prefixWord ++ tailWord_2653078).sum := by decide
  have hdescent : baseEnd_2653078 < baseStart_2653078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653087 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 3]
def baseStart_2653087 : Nat := 118140960795 + 2653087 * 2 ^ 59
def prefixEnd_2653087 : Nat := 4983230072969 + 3 ^ 40 * 2653087 * 2
def baseEnd_2653087 : Nat := 1362308849195166518611181

theorem tailTrace_2653087 : CollatzResearch.WordTrace tailWord_2653087 prefixEnd_2653087 1362308849195166518611181 := by
  unfold tailWord_2653087
  simp only [CollatzResearch.WordTrace]
  refine ⟨96766032539326385030685515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64510688359550923353790343 96766032539326385030685515)
  ·
    refine ⟨145149048808989577546028273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96766032539326385030685515 145149048808989577546028273)
    ·
      refine ⟨108861786606742183159521205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145149048808989577546028273 108861786606742183159521205)
      ·
        refine ⟨10205792494382079671205113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108861786606742183159521205 10205792494382079671205113)
        ·
          refine ⟨7654344370786559753403835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10205792494382079671205113 7654344370786559753403835)
          ·
            refine ⟨11481516556179839630105753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7654344370786559753403835 11481516556179839630105753)
            ·
              refine ⟨8611137417134879722579315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11481516556179839630105753 8611137417134879722579315)
              ·
                refine ⟨12916706125702319583868973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8611137417134879722579315 12916706125702319583868973)
                ·
                  refine ⟨4843764797138369843950865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12916706125702319583868973 4843764797138369843950865)
                  ·
                    refine ⟨3632823597853777382963149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4843764797138369843950865 3632823597853777382963149)
                    ·
                      refine ⟨1362308849195166518611181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3632823597853777382963149 1362308849195166518611181)
                      ·
                        rfl

theorem cell23_2653087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_2653087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653087 prefixEnd_2653087 := by exact prefixLift 2653087
  have htrace : WordTrace (prefixWord ++ tailWord_2653087) baseStart_2653087 baseEnd_2653087 := by
    simpa [prefixWord, tailWord_2653087, baseEnd_2653087] using wordTrace_append hprefix tailTrace_2653087
  have hstable : (prefixWord ++ tailWord_2653087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653087).length < 2 ^ (prefixWord ++ tailWord_2653087).sum := by decide
  have hdescent : baseEnd_2653087 < baseStart_2653087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653101 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2653101 : Nat := 118140960795 + 2653101 * 2 ^ 59
def prefixEnd_2653101 : Nat := 4983230072969 + 3 ^ 40 * 2653101 * 2
def baseEnd_2653101 : Nat := 1362316037924329463836117

theorem tailTrace_2653101 : CollatzResearch.WordTrace tailWord_2653101 prefixEnd_2653101 1362316037924329463836117 := by
  unfold tailWord_2653101
  simp only [CollatzResearch.WordTrace]
  refine ⟨96766543161275665421695157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64511028774183776947796771 96766543161275665421695157)
  ·
    refine ⟨9071863421369593633283921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96766543161275665421695157 9071863421369593633283921)
    ·
      refine ⟨6803897566027195224962941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9071863421369593633283921 6803897566027195224962941)
      ·
        refine ⟨2551461587260198209361103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6803897566027195224962941 2551461587260198209361103)
        ·
          refine ⟨3827192380890297314041655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551461587260198209361103 3827192380890297314041655)
          ·
            refine ⟨5740788571335445971062483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3827192380890297314041655 5740788571335445971062483)
            ·
              refine ⟨8611182857003168956593725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5740788571335445971062483 8611182857003168956593725)
              ·
                refine ⟨3229193571376188358722647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8611182857003168956593725 3229193571376188358722647)
                ·
                  refine ⟨4843790357064282538083971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229193571376188358722647 4843790357064282538083971)
                  ·
                    refine ⟨7265685535596423807125957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4843790357064282538083971 7265685535596423807125957)
                    ·
                      refine ⟨1362316037924329463836117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7265685535596423807125957 1362316037924329463836117)
                      ·
                        rfl

theorem cell23_2653101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2653101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653101 prefixEnd_2653101 := by exact prefixLift 2653101
  have htrace : WordTrace (prefixWord ++ tailWord_2653101) baseStart_2653101 baseEnd_2653101 := by
    simpa [prefixWord, tailWord_2653101, baseEnd_2653101] using wordTrace_append hprefix tailTrace_2653101
  have hstable : (prefixWord ++ tailWord_2653101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653101).length < 2 ^ (prefixWord ++ tailWord_2653101).sum := by decide
  have hdescent : baseEnd_2653101 < baseStart_2653101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653103 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 1, 9]
def baseStart_2653103 : Nat := 118140960795 + 2653103 * 2 ^ 59
def prefixEnd_2653103 : Nat := 4983230072969 + 3 ^ 40 * 2653103 * 2
def baseEnd_2653103 : Nat := 454105688295212818670369

theorem tailTrace_2653103 : CollatzResearch.WordTrace tailWord_2653103 prefixEnd_2653103 454105688295212818670369 := by
  unfold tailWord_2653103
  simp only [CollatzResearch.WordTrace]
  refine ⟨96766616107268419763267963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64511077404845613175511975 96766616107268419763267963)
  ·
    refine ⟨145149924160902629644901945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96766616107268419763267963 145149924160902629644901945)
    ·
      refine ⟨108862443120676972233676459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145149924160902629644901945 108862443120676972233676459)
      ·
        refine ⟨163293664681015458350514689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108862443120676972233676459 163293664681015458350514689)
        ·
          refine ⟨122470248510761593762886017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163293664681015458350514689 122470248510761593762886017)
          ·
            refine ⟨91852686383071195322164513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122470248510761593762886017 91852686383071195322164513)
            ·
              refine ⟨68889514787303396491623385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91852686383071195322164513 68889514787303396491623385)
              ·
                refine ⟨51667136090477547368717539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68889514787303396491623385 51667136090477547368717539)
                ·
                  refine ⟨77500704135716321053076309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51667136090477547368717539 77500704135716321053076309)
                  ·
                    refine ⟨454105688295212818670369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 77500704135716321053076309 454105688295212818670369)
                    ·
                      rfl

theorem cell23_2653103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_2653103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653103 prefixEnd_2653103 := by exact prefixLift 2653103
  have htrace : WordTrace (prefixWord ++ tailWord_2653103) baseStart_2653103 baseEnd_2653103 := by
    simpa [prefixWord, tailWord_2653103, baseEnd_2653103] using wordTrace_append hprefix tailTrace_2653103
  have hstable : (prefixWord ++ tailWord_2653103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653103).length < 2 ^ (prefixWord ++ tailWord_2653103).sum := by decide
  have hdescent : baseEnd_2653103 < baseStart_2653103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653127 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 5, 3, 2]
def baseStart_2653127 : Nat := 118140960795 + 2653127 * 2 ^ 59
def prefixEnd_2653127 : Nat := 4983230072969 + 3 ^ 40 * 2653127 * 2
def baseEnd_2653127 : Nat := 1362329388421346362110997

theorem tailTrace_2653127 : CollatzResearch.WordTrace tailWord_2653127 prefixEnd_2653127 1362329388421346362110997 := by
  unfold tailWord_2653127
  simp only [CollatzResearch.WordTrace]
  refine ⟨96767491459181471862141635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64511660972787647908094423 96767491459181471862141635)
  ·
    refine ⟨145151237188772207793212453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96767491459181471862141635 145151237188772207793212453)
    ·
      refine ⟨27215856972894788961227335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145151237188772207793212453 27215856972894788961227335)
      ·
        refine ⟨40823785459342183441841003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27215856972894788961227335 40823785459342183441841003)
        ·
          refine ⟨61235678189013275162761505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40823785459342183441841003 61235678189013275162761505)
          ·
            refine ⟨45926758641759956372071129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61235678189013275162761505 45926758641759956372071129)
            ·
              refine ⟨34445068981319967279053347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45926758641759956372071129 34445068981319967279053347)
              ·
                refine ⟨51667603471979950918580021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34445068981319967279053347 51667603471979950918580021)
                ·
                  refine ⟨4843837825498120398616877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51667603471979950918580021 4843837825498120398616877)
                  ·
                    refine ⟨1816439184561795149481329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4843837825498120398616877 1816439184561795149481329)
                    ·
                      refine ⟨1362329388421346362110997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816439184561795149481329 1362329388421346362110997)
                      ·
                        rfl

theorem cell23_2653127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_2653127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653127 prefixEnd_2653127 := by exact prefixLift 2653127
  have htrace : WordTrace (prefixWord ++ tailWord_2653127) baseStart_2653127 baseEnd_2653127 := by
    simpa [prefixWord, tailWord_2653127, baseEnd_2653127] using wordTrace_append hprefix tailTrace_2653127
  have hstable : (prefixWord ++ tailWord_2653127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653127).length < 2 ^ (prefixWord ++ tailWord_2653127).sum := by decide
  have hdescent : baseEnd_2653127 < baseStart_2653127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653134 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_2653134 : Nat := 118140960795 + 2653134 * 2 ^ 59
def prefixEnd_2653134 : Nat := 4983230072969 + 3 ^ 40 * 2653134 * 2
def baseEnd_2653134 : Nat := 1362332982785927834723465

theorem tailTrace_2653134 : CollatzResearch.WordTrace tailWord_2653134 prefixEnd_2653134 1362332982785927834723465 := by
  unfold tailWord_2653134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095968346269514007205807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64511831180104074705097637 12095968346269514007205807)
  ·
    refine ⟨18143952519404271010808711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12095968346269514007205807 18143952519404271010808711)
    ·
      refine ⟨27215928779106406516213067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18143952519404271010808711 27215928779106406516213067)
      ·
        refine ⟨40823893168659609774319601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27215928779106406516213067 40823893168659609774319601)
        ·
          refine ⟨30617919876494707330739701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40823893168659609774319601 30617919876494707330739701)
          ·
            refine ⟨2870429988421378812256847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30617919876494707330739701 2870429988421378812256847)
            ·
              refine ⟨4305644982632068218385271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2870429988421378812256847 4305644982632068218385271)
              ·
                refine ⟨6458467473948102327577907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305644982632068218385271 6458467473948102327577907)
                ·
                  refine ⟨9687701210922153491366861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6458467473948102327577907 9687701210922153491366861)
                  ·
                    refine ⟨3632887954095807559262573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9687701210922153491366861 3632887954095807559262573)
                    ·
                      refine ⟨1362332982785927834723465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3632887954095807559262573 1362332982785927834723465)
                      ·
                        rfl

theorem cell23_2653134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_2653134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653134 prefixEnd_2653134 := by exact prefixLift 2653134
  have htrace : WordTrace (prefixWord ++ tailWord_2653134) baseStart_2653134 baseEnd_2653134 := by
    simpa [prefixWord, tailWord_2653134, baseEnd_2653134] using wordTrace_append hprefix tailTrace_2653134
  have hstable : (prefixWord ++ tailWord_2653134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653134).length < 2 ^ (prefixWord ++ tailWord_2653134).sum := by decide
  have hdescent : baseEnd_2653134 < baseStart_2653134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653144 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 1, 3, 2]
def baseStart_2653144 : Nat := 118140960795 + 2653144 * 2 ^ 59
def prefixEnd_2653144 : Nat := 4983230072969 + 3 ^ 40 * 2653144 * 2
def baseEnd_2653144 : Nat := 1362338117592472795598419

theorem tailTrace_2653144 : CollatzResearch.WordTrace tailWord_2653144 prefixEnd_2653144 1362338117592472795598419 := by
  unfold tailWord_2653144
  simp only [CollatzResearch.WordTrace]
  refine ⟨48384055750059941882755243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64512074333413255843673657 48384055750059941882755243)
  ·
    refine ⟨72576083625089912824132865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48384055750059941882755243 72576083625089912824132865)
    ·
      refine ⟨54432062718817434618099649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72576083625089912824132865 54432062718817434618099649)
      ·
        refine ⟨40824047039113075963574737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54432062718817434618099649 40824047039113075963574737)
        ·
          refine ⟨30618035279334806972681053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40824047039113075963574737 30618035279334806972681053)
          ·
            refine ⟨11481763229750552614755395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30618035279334806972681053 11481763229750552614755395)
            ·
              refine ⟨17222644844625828922133093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11481763229750552614755395 17222644844625828922133093)
              ·
                refine ⟨3229245908367342922899955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17222644844625828922133093 3229245908367342922899955)
                ·
                  refine ⟨4843868862551014384349933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229245908367342922899955 4843868862551014384349933)
                  ·
                    refine ⟨1816450823456630394131225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4843868862551014384349933 1816450823456630394131225)
                    ·
                      refine ⟨1362338117592472795598419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816450823456630394131225 1362338117592472795598419)
                      ·
                        rfl

theorem cell23_2653144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_2653144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653144 prefixEnd_2653144 := by exact prefixLift 2653144
  have htrace : WordTrace (prefixWord ++ tailWord_2653144) baseStart_2653144 baseEnd_2653144 := by
    simpa [prefixWord, tailWord_2653144, baseEnd_2653144] using wordTrace_append hprefix tailTrace_2653144
  have hstable : (prefixWord ++ tailWord_2653144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653144).length < 2 ^ (prefixWord ++ tailWord_2653144).sum := by decide
  have hdescent : baseEnd_2653144 < baseStart_2653144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653160 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2653160 : Nat := 118140960795 + 2653160 * 2 ^ 59
def prefixEnd_2653160 : Nat := 4983230072969 + 3 ^ 40 * 2653160 * 2
def baseEnd_2653160 : Nat := 1362346333282944732998345

theorem tailTrace_2653160 : CollatzResearch.WordTrace tailWord_2653160 prefixEnd_2653160 1362346333282944732998345 := by
  unfold tailWord_2653160
  simp only [CollatzResearch.WordTrace]
  refine ⟨48384347534030959249046467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64512463378707945665395289 48384347534030959249046467)
  ·
    refine ⟨72576521301046438873569701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48384347534030959249046467 72576521301046438873569701)
    ·
      refine ⟨13608097743946207288794319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72576521301046438873569701 13608097743946207288794319)
      ·
        refine ⟨20412146615919310933191479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13608097743946207288794319 20412146615919310933191479)
        ·
          refine ⟨30618219923878966399787219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20412146615919310933191479 30618219923878966399787219)
          ·
            refine ⟨45927329885818449599680829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30618219923878966399787219 45927329885818449599680829)
            ·
              refine ⟨17222748707181918599880311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45927329885818449599680829 17222748707181918599880311)
              ·
                refine ⟨25834123060772877899820467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17222748707181918599880311 25834123060772877899820467)
                ·
                  refine ⟨38751184591159316849730701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25834123060772877899820467 38751184591159316849730701)
                  ·
                    refine ⟨14531694221684743818649013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38751184591159316849730701 14531694221684743818649013)
                    ·
                      refine ⟨1362346333282944732998345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14531694221684743818649013 1362346333282944732998345)
                      ·
                        rfl

theorem cell23_2653160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2653160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653160 prefixEnd_2653160 := by exact prefixLift 2653160
  have htrace : WordTrace (prefixWord ++ tailWord_2653160) baseStart_2653160 baseEnd_2653160 := by
    simpa [prefixWord, tailWord_2653160, baseEnd_2653160] using wordTrace_append hprefix tailTrace_2653160
  have hstable : (prefixWord ++ tailWord_2653160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653160).length < 2 ^ (prefixWord ++ tailWord_2653160).sum := by decide
  have hdescent : baseEnd_2653160 < baseStart_2653160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653191 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 2, 2, 2]
def baseStart_2653191 : Nat := 118140960795 + 2653191 * 2 ^ 59
def prefixEnd_2653191 : Nat := 4983230072969 + 3 ^ 40 * 2653191 * 2
def baseEnd_2653191 : Nat := 1362362251183234111710703

theorem tailTrace_2653191 : CollatzResearch.WordTrace tailWord_2653191 prefixEnd_2653191 1362362251183234111710703 := by
  unfold tailWord_2653191
  simp only [CollatzResearch.WordTrace]
  refine ⟨96769825730949610792471427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64513217153966407194980951 96769825730949610792471427)
  ·
    refine ⟨145154738596424416188707141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96769825730949610792471427 145154738596424416188707141)
    ·
      refine ⟨27216513486829578035382589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145154738596424416188707141 27216513486829578035382589)
      ·
        refine ⟨10206192557561091763268471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27216513486829578035382589 10206192557561091763268471)
        ·
          refine ⟨15309288836341637644902707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10206192557561091763268471 15309288836341637644902707)
          ·
            refine ⟨22963933254512456467354061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15309288836341637644902707 22963933254512456467354061)
            ·
              refine ⟨8611474970442171175257773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22963933254512456467354061 8611474970442171175257773)
              ·
                refine ⟨3229303113915814190721665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8611474970442171175257773 3229303113915814190721665)
                ·
                  refine ⟨2421977335436860643041249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3229303113915814190721665 2421977335436860643041249)
                  ·
                    refine ⟨1816483001577645482280937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2421977335436860643041249 1816483001577645482280937)
                    ·
                      refine ⟨1362362251183234111710703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816483001577645482280937 1362362251183234111710703)
                      ·
                        rfl

theorem cell23_2653191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_2653191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653191 prefixEnd_2653191 := by exact prefixLift 2653191
  have htrace : WordTrace (prefixWord ++ tailWord_2653191) baseStart_2653191 baseEnd_2653191 := by
    simpa [prefixWord, tailWord_2653191, baseEnd_2653191] using wordTrace_append hprefix tailTrace_2653191
  have hstable : (prefixWord ++ tailWord_2653191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653191).length < 2 ^ (prefixWord ++ tailWord_2653191).sum := by decide
  have hdescent : baseEnd_2653191 < baseStart_2653191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653261 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_2653261 : Nat := 118140960795 + 2653261 * 2 ^ 59
def prefixEnd_2653261 : Nat := 4983230072969 + 3 ^ 40 * 2653261 * 2
def baseEnd_2653261 : Nat := 454132731609682945945127

theorem tailTrace_2653261 : CollatzResearch.WordTrace tailWord_2653261 prefixEnd_2653261 454132731609682945945127 := by
  unfold tailWord_2653261
  simp only [CollatzResearch.WordTrace]
  refine ⟨96772378840696012747519637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64514919227130675165013091 96772378840696012747519637)
  ·
    refine ⟨4536205258157625597539983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96772378840696012747519637 4536205258157625597539983)
    ·
      refine ⟨6804307887236438396309975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4536205258157625597539983 6804307887236438396309975)
      ·
        refine ⟨10206461830854657594464963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6804307887236438396309975 10206461830854657594464963)
        ·
          refine ⟨15309692746281986391697445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10206461830854657594464963 15309692746281986391697445)
          ·
            refine ⟨2870567389927872448443271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15309692746281986391697445 2870567389927872448443271)
            ·
              refine ⟨4305851084891808672664907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2870567389927872448443271 4305851084891808672664907)
              ·
                refine ⟨6458776627337713008997361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305851084891808672664907 6458776627337713008997361)
                ·
                  refine ⟨4844082470503284756748021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6458776627337713008997361 4844082470503284756748021)
                  ·
                    refine ⟨454132731609682945945127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4844082470503284756748021 454132731609682945945127)
                    ·
                      rfl

theorem cell23_2653261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_2653261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653261 prefixEnd_2653261 := by exact prefixLift 2653261
  have htrace : WordTrace (prefixWord ++ tailWord_2653261) baseStart_2653261 baseEnd_2653261 := by
    simpa [prefixWord, tailWord_2653261, baseEnd_2653261] using wordTrace_append hprefix tailTrace_2653261
  have hstable : (prefixWord ++ tailWord_2653261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653261).length < 2 ^ (prefixWord ++ tailWord_2653261).sum := by decide
  have hdescent : baseEnd_2653261 < baseStart_2653261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653287 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 8]
def baseStart_2653287 : Nat := 118140960795 + 2653287 * 2 ^ 59
def prefixEnd_2653287 : Nat := 4983230072969 + 3 ^ 40 * 2653287 * 2
def baseEnd_2653287 : Nat := 151379060591785081790029

theorem tailTrace_2653287 : CollatzResearch.WordTrace tailWord_2653287 prefixEnd_2653287 151379060591785081790029 := by
  unfold tailWord_2653287
  simp only [CollatzResearch.WordTrace]
  refine ⟨96773327138601819187966115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64515551425734546125310743 96773327138601819187966115)
  ·
    refine ⟨145159990707902728781949173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96773327138601819187966115 145159990707902728781949173)
    ·
      refine ⟨13608749128865880823307735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145159990707902728781949173 13608749128865880823307735)
      ·
        refine ⟨20413123693298821234961603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13608749128865880823307735 20413123693298821234961603)
        ·
          refine ⟨30619685539948231852442405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20413123693298821234961603 30619685539948231852442405)
          ·
            refine ⟨5741191038740293472332951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30619685539948231852442405 5741191038740293472332951)
            ·
              refine ⟨8611786558110440208499427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5741191038740293472332951 8611786558110440208499427)
              ·
                refine ⟨12917679837165660312749141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8611786558110440208499427 12917679837165660312749141)
                ·
                  refine ⟨151379060591785081790029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12917679837165660312749141 151379060591785081790029)
                  ·
                    rfl

theorem cell23_2653287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 8].length) (baseStart_2653287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653287 prefixEnd_2653287 := by exact prefixLift 2653287
  have htrace : WordTrace (prefixWord ++ tailWord_2653287) baseStart_2653287 baseEnd_2653287 := by
    simpa [prefixWord, tailWord_2653287, baseEnd_2653287] using wordTrace_append hprefix tailTrace_2653287
  have hstable : (prefixWord ++ tailWord_2653287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653287).length < 2 ^ (prefixWord ++ tailWord_2653287).sum := by decide
  have hdescent : baseEnd_2653287 < baseStart_2653287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653324 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 6, 3, 2]
def baseStart_2653324 : Nat := 118140960795 + 2653324 * 2 ^ 59
def prefixEnd_2653324 : Nat := 4983230072969 + 3 ^ 40 * 2653324 * 2
def baseEnd_2653324 : Nat := 1362430544110282091347591

theorem tailTrace_2653324 : CollatzResearch.WordTrace tailWord_2653324 prefixEnd_2653324 1362430544110282091347591 := by
  unfold tailWord_2653324
  simp only [CollatzResearch.WordTrace]
  refine ⟨48387338319733887253531513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64516451092978516338042017 48387338319733887253531513)
  ·
    refine ⟨36290503739800415440148635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48387338319733887253531513 36290503739800415440148635)
    ·
      refine ⟨54435755609700623160222953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36290503739800415440148635 54435755609700623160222953)
      ·
        refine ⟨40826816707275467370167215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54435755609700623160222953 40826816707275467370167215)
        ·
          refine ⟨61240225060913201055250823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40826816707275467370167215 61240225060913201055250823)
          ·
            refine ⟨91860337591369801582876235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61240225060913201055250823 91860337591369801582876235)
            ·
              refine ⟨137790506387054702374314353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91860337591369801582876235 137790506387054702374314353)
              ·
                refine ⟨103342879790291026780735765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137790506387054702374314353 103342879790291026780735765)
                ·
                  refine ⟨4844197490169891880346989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103342879790291026780735765 4844197490169891880346989)
                  ·
                    refine ⟨1816574058813709455130121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4844197490169891880346989 1816574058813709455130121)
                    ·
                      refine ⟨1362430544110282091347591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816574058813709455130121 1362430544110282091347591)
                      ·
                        rfl

theorem cell23_2653324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_2653324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653324 prefixEnd_2653324 := by exact prefixLift 2653324
  have htrace : WordTrace (prefixWord ++ tailWord_2653324) baseStart_2653324 baseEnd_2653324 := by
    simpa [prefixWord, tailWord_2653324, baseEnd_2653324] using wordTrace_append hprefix tailTrace_2653324
  have hstable : (prefixWord ++ tailWord_2653324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653324).length < 2 ^ (prefixWord ++ tailWord_2653324).sum := by decide
  have hdescent : baseEnd_2653324 < baseStart_2653324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653337 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 4]
def baseStart_2653337 : Nat := 118140960795 + 2653337 * 2 ^ 59
def prefixEnd_2653337 : Nat := 4983230072969 + 3 ^ 40 * 2653337 * 2
def baseEnd_2653337 : Nat := 1362437219358790540485031

theorem tailTrace_2653337 : CollatzResearch.WordTrace tailWord_2653337 prefixEnd_2653337 1362437219358790540485031 := by
  unfold tailWord_2653337
  simp only [CollatzResearch.WordTrace]
  refine ⟨96775150788420677727286265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64516767192280451818190843 96775150788420677727286265)
  ·
    refine ⟨72581363091315508295464699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96775150788420677727286265 72581363091315508295464699)
    ·
      refine ⟨108872044636973262443197049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72581363091315508295464699 108872044636973262443197049)
      ·
        refine ⟨81654033477729946832397787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108872044636973262443197049 81654033477729946832397787)
        ·
          refine ⟨122481050216594920248596681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81654033477729946832397787 122481050216594920248596681)
          ·
            refine ⟨91860787662446190186447511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122481050216594920248596681 91860787662446190186447511)
            ·
              refine ⟨137791181493669285279671267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91860787662446190186447511 137791181493669285279671267)
              ·
                refine ⟨206686772240503927919506901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137791181493669285279671267 206686772240503927919506901)
                ·
                  refine ⟨4844221224386810810613443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 206686772240503927919506901 4844221224386810810613443)
                  ·
                    refine ⟨7266331836580216215920165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4844221224386810810613443 7266331836580216215920165)
                    ·
                      refine ⟨1362437219358790540485031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7266331836580216215920165 1362437219358790540485031)
                      ·
                        rfl

theorem cell23_2653337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_2653337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653337 prefixEnd_2653337 := by exact prefixLift 2653337
  have htrace : WordTrace (prefixWord ++ tailWord_2653337) baseStart_2653337 baseEnd_2653337 := by
    simpa [prefixWord, tailWord_2653337, baseEnd_2653337] using wordTrace_append hprefix tailTrace_2653337
  have hstable : (prefixWord ++ tailWord_2653337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653337).length < 2 ^ (prefixWord ++ tailWord_2653337).sum := by decide
  have hdescent : baseEnd_2653337 < baseStart_2653337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653341 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_2653341 : Nat := 118140960795 + 2653341 * 2 ^ 59
def prefixEnd_2653341 : Nat := 4983230072969 + 3 ^ 40 * 2653341 * 2
def baseEnd_2653341 : Nat := 1362439273281408524835013

theorem tailTrace_2653341 : CollatzResearch.WordTrace tailWord_2653341 prefixEnd_2653341 1362439273281408524835013 := by
  unfold tailWord_2653341
  simp only [CollatzResearch.WordTrace]
  refine ⟨96775296680406186410431877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64516864453604124273621251 96775296680406186410431877)
  ·
    refine ⟨18145368127576159951955977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96775296680406186410431877 18145368127576159951955977)
    ·
      refine ⟨13609026095682119963966983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18145368127576159951955977 13609026095682119963966983)
      ·
        refine ⟨20413539143523179945950475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13609026095682119963966983 20413539143523179945950475)
        ·
          refine ⟨30620308715284769918925713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20413539143523179945950475 30620308715284769918925713)
          ·
            refine ⟨22965231536463577439194285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30620308715284769918925713 22965231536463577439194285)
            ·
              refine ⟨8611961826173841539697857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22965231536463577439194285 8611961826173841539697857)
              ·
                refine ⟨6458971369630381154773393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8611961826173841539697857 6458971369630381154773393)
                ·
                  refine ⟨4844228527222785866080045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6458971369630381154773393 4844228527222785866080045)
                  ·
                    refine ⟨1816585697708544699780017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4844228527222785866080045 1816585697708544699780017)
                    ·
                      refine ⟨1362439273281408524835013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816585697708544699780017 1362439273281408524835013)
                      ·
                        rfl

theorem cell23_2653341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_2653341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653341 prefixEnd_2653341 := by exact prefixLift 2653341
  have htrace : WordTrace (prefixWord ++ tailWord_2653341) baseStart_2653341 baseEnd_2653341 := by
    simpa [prefixWord, tailWord_2653341, baseEnd_2653341] using wordTrace_append hprefix tailTrace_2653341
  have hstable : (prefixWord ++ tailWord_2653341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653341).length < 2 ^ (prefixWord ++ tailWord_2653341).sum := by decide
  have hdescent : baseEnd_2653341 < baseStart_2653341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653348 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_2653348 : Nat := 118140960795 + 2653348 * 2 ^ 59
def prefixEnd_2653348 : Nat := 4983230072969 + 3 ^ 40 * 2653348 * 2
def baseEnd_2653348 : Nat := 1362442867645989997447481

theorem tailTrace_2653348 : CollatzResearch.WordTrace tailWord_2653348 prefixEnd_2653348 1362442867645989997447481 := by
  unfold tailWord_2653348
  simp only [CollatzResearch.WordTrace]
  refine ⟨48387775995690413302968349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64517034660920551070624465 48387775995690413302968349)
  ·
    refine ⟨18145415998383904988613131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48387775995690413302968349 18145415998383904988613131)
    ·
      refine ⟨27218123997575857482919697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18145415998383904988613131 27218123997575857482919697)
      ·
        refine ⟨20413592998181893112189773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27218123997575857482919697 20413592998181893112189773)
        ·
          refine ⟨7655097374318209917071165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20413592998181893112189773 7655097374318209917071165)
          ·
            refine ⟨2870661515369328718901687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7655097374318209917071165 2870661515369328718901687)
            ·
              refine ⟨4305992273053993078352531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2870661515369328718901687 4305992273053993078352531)
              ·
                refine ⟨6458988409580989617528797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305992273053993078352531 6458988409580989617528797)
                ·
                  refine ⟨2422120653592871106573299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6458988409580989617528797 2422120653592871106573299)
                  ·
                    refine ⟨3633180980389306659859949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2422120653592871106573299 3633180980389306659859949)
                    ·
                      refine ⟨1362442867645989997447481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3633180980389306659859949 1362442867645989997447481)
                      ·
                        rfl

theorem cell23_2653348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_2653348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653348 prefixEnd_2653348 := by exact prefixLift 2653348
  have htrace : WordTrace (prefixWord ++ tailWord_2653348) baseStart_2653348 baseEnd_2653348 := by
    simpa [prefixWord, tailWord_2653348, baseEnd_2653348] using wordTrace_append hprefix tailTrace_2653348
  have hstable : (prefixWord ++ tailWord_2653348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653348).length < 2 ^ (prefixWord ++ tailWord_2653348).sum := by decide
  have hdescent : baseEnd_2653348 < baseStart_2653348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653367 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_2653367 : Nat := 118140960795 + 2653367 * 2 ^ 59
def prefixEnd_2653367 : Nat := 4983230072969 + 3 ^ 40 * 2653367 * 2
def baseEnd_2653367 : Nat := 1362452623778425423109893

theorem tailTrace_2653367 : CollatzResearch.WordTrace tailWord_2653367 prefixEnd_2653367 1362452623778425423109893 := by
  unfold tailWord_2653367
  simp only [CollatzResearch.WordTrace]
  refine ⟨96776244978311992850878355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64517496652207995233918903 96776244978311992850878355)
  ·
    refine ⟨145164367467467989276317533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96776244978311992850878355 145164367467467989276317533)
    ·
      refine ⟨54436637800300495978619075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145164367467467989276317533 54436637800300495978619075)
      ·
        refine ⟨81654956700450743967928613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54436637800300495978619075 81654956700450743967928613)
        ·
          refine ⟨15310304381334514493986615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81654956700450743967928613 15310304381334514493986615)
          ·
            refine ⟨22965456572001771740979923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15310304381334514493986615 22965456572001771740979923)
            ·
              refine ⟨34448184858002657611469885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22965456572001771740979923 34448184858002657611469885)
              ·
                refine ⟨12918069321750996604301207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34448184858002657611469885 12918069321750996604301207)
                ·
                  refine ⟨19377103982626494906451811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12918069321750996604301207 19377103982626494906451811)
                  ·
                    refine ⟨29065655973939742359677717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19377103982626494906451811 29065655973939742359677717)
                    ·
                      refine ⟨1362452623778425423109893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29065655973939742359677717 1362452623778425423109893)
                      ·
                        rfl

theorem cell23_2653367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_2653367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653367 prefixEnd_2653367 := by exact prefixLift 2653367
  have htrace : WordTrace (prefixWord ++ tailWord_2653367) baseStart_2653367 baseEnd_2653367 := by
    simpa [prefixWord, tailWord_2653367, baseEnd_2653367] using wordTrace_append hprefix tailTrace_2653367
  have hstable : (prefixWord ++ tailWord_2653367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653367).length < 2 ^ (prefixWord ++ tailWord_2653367).sum := by decide
  have hdescent : baseEnd_2653367 < baseStart_2653367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653407 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 2, 7]
def baseStart_2653407 : Nat := 118140960795 + 2653407 * 2 ^ 59
def prefixEnd_2653407 : Nat := 4983230072969 + 3 ^ 40 * 2653407 * 2
def baseEnd_2653407 : Nat := 454157721001535088869903

theorem tailTrace_2653407 : CollatzResearch.WordTrace tailWord_2653407 prefixEnd_2653407 454157721001535088869903 := by
  unfold tailWord_2653407
  simp only [CollatzResearch.WordTrace]
  refine ⟨96777703898167079682334475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64518469265444719788222983 96777703898167079682334475)
  ·
    refine ⟨145166555847250619523501713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96777703898167079682334475 145166555847250619523501713)
    ·
      refine ⟨108874916885437964642626285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145166555847250619523501713 108874916885437964642626285)
      ·
        refine ⟨40828093832039236740984857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108874916885437964642626285 40828093832039236740984857)
        ·
          refine ⟨30621070374029427555738643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40828093832039236740984857 30621070374029427555738643)
          ·
            refine ⟨45931605561044141333607965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30621070374029427555738643 45931605561044141333607965)
            ·
              refine ⟨17224352085391553000102987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45931605561044141333607965 17224352085391553000102987)
              ·
                refine ⟨25836528128087329500154481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17224352085391553000102987 25836528128087329500154481)
                ·
                  refine ⟨19377396096065497125115861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25836528128087329500154481 19377396096065497125115861)
                  ·
                    refine ⟨454157721001535088869903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19377396096065497125115861 454157721001535088869903)
                    ·
                      rfl

theorem cell23_2653407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_2653407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653407 prefixEnd_2653407 := by exact prefixLift 2653407
  have htrace : WordTrace (prefixWord ++ tailWord_2653407) baseStart_2653407 baseEnd_2653407 := by
    simpa [prefixWord, tailWord_2653407, baseEnd_2653407] using wordTrace_append hprefix tailTrace_2653407
  have hstable : (prefixWord ++ tailWord_2653407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653407).length < 2 ^ (prefixWord ++ tailWord_2653407).sum := by decide
  have hdescent : baseEnd_2653407 < baseStart_2653407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653421 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2653421 : Nat := 118140960795 + 2653421 * 2 ^ 59
def prefixEnd_2653421 : Nat := 4983230072969 + 3 ^ 40 * 2653421 * 2
def baseEnd_2653421 : Nat := 1362480351733768211834645

theorem tailTrace_2653421 : CollatzResearch.WordTrace tailWord_2653421 prefixEnd_2653421 1362480351733768211834645 := by
  unfold tailWord_2653421
  simp only [CollatzResearch.WordTrace]
  refine ⟨96778214520116360073344117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64518809680077573382229411 96778214520116360073344117)
  ·
    refine ⟨9072957611260908756876011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96778214520116360073344117 9072957611260908756876011)
    ·
      refine ⟨13609436416891363135314017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9072957611260908756876011 13609436416891363135314017)
      ·
        refine ⟨10207077312668522351485513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13609436416891363135314017 10207077312668522351485513)
        ·
          refine ⟨7655307984501391763614135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10207077312668522351485513 7655307984501391763614135)
          ·
            refine ⟨11482961976752087645421203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7655307984501391763614135 11482961976752087645421203)
            ·
              refine ⟨17224442965128131468131805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11482961976752087645421203 17224442965128131468131805)
              ·
                refine ⟨6459166111923049300549427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17224442965128131468131805 6459166111923049300549427)
                ·
                  refine ⟨9688749167884573950824141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6459166111923049300549427 9688749167884573950824141)
                  ·
                    refine ⟨3633280937956715231559053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9688749167884573950824141 3633280937956715231559053)
                    ·
                      refine ⟨1362480351733768211834645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3633280937956715231559053 1362480351733768211834645)
                      ·
                        rfl

theorem cell23_2653421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2653421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653421 prefixEnd_2653421 := by exact prefixLift 2653421
  have htrace : WordTrace (prefixWord ++ tailWord_2653421) baseStart_2653421 baseEnd_2653421 := by
    simpa [prefixWord, tailWord_2653421, baseEnd_2653421] using wordTrace_append hprefix tailTrace_2653421
  have hstable : (prefixWord ++ tailWord_2653421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653421).length < 2 ^ (prefixWord ++ tailWord_2653421).sum := by decide
  have hdescent : baseEnd_2653421 < baseStart_2653421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653442 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_2653442 : Nat := 118140960795 + 2653442 * 2 ^ 59
def prefixEnd_2653442 : Nat := 4983230072969 + 3 ^ 40 * 2653442 * 2
def baseEnd_2653442 : Nat := 1362491134827512629672049

theorem tailTrace_2653442 : CollatzResearch.WordTrace tailWord_2653442 prefixEnd_2653442 1362491134827512629672049 := by
  unfold tailWord_2653442
  simp only [CollatzResearch.WordTrace]
  refine ⟨24194745113260070164964645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64519320302026853773239053 24194745113260070164964645)
  ·
    refine ⟨4536514708736263155930871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24194745113260070164964645 4536514708736263155930871)
    ·
      refine ⟨6804772063104394733896307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4536514708736263155930871 6804772063104394733896307)
      ·
        refine ⟨10207158094656592100844461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6804772063104394733896307 10207158094656592100844461)
        ·
          refine ⟨3827684285496222037816673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10207158094656592100844461 3827684285496222037816673)
          ·
            refine ⟨2870763214122166528362505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3827684285496222037816673 2870763214122166528362505)
            ·
              refine ⟨2153072410591624896271879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870763214122166528362505 2153072410591624896271879)
              ·
                refine ⟨3229608615887437344407819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153072410591624896271879 3229608615887437344407819)
                ·
                  refine ⟨4844412923831156016611729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229608615887437344407819 4844412923831156016611729)
                  ·
                    refine ⟨3633309692873367012458797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4844412923831156016611729 3633309692873367012458797)
                    ·
                      refine ⟨1362491134827512629672049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3633309692873367012458797 1362491134827512629672049)
                      ·
                        rfl

theorem cell23_2653442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_2653442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653442 prefixEnd_2653442 := by exact prefixLift 2653442
  have htrace : WordTrace (prefixWord ++ tailWord_2653442) baseStart_2653442 baseEnd_2653442 := by
    simpa [prefixWord, tailWord_2653442, baseEnd_2653442] using wordTrace_append hprefix tailTrace_2653442
  have hstable : (prefixWord ++ tailWord_2653442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653442).length < 2 ^ (prefixWord ++ tailWord_2653442).sum := by decide
  have hdescent : baseEnd_2653442 < baseStart_2653442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653454 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_2653454 : Nat := 118140960795 + 2653454 * 2 ^ 59
def prefixEnd_2653454 : Nat := 4983230072969 + 3 ^ 40 * 2653454 * 2
def baseEnd_2653454 : Nat := 454165765531788860907331

theorem tailTrace_2653454 : CollatzResearch.WordTrace tailWord_2653454 prefixEnd_2653454 454165765531788860907331 := by
  unfold tailWord_2653454
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097427266124600838661927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64519612085997871139530277 12097427266124600838661927)
  ·
    refine ⟨18146140899186901257992891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12097427266124600838661927 18146140899186901257992891)
    ·
      refine ⟨27219211348780351886989337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18146140899186901257992891 27219211348780351886989337)
      ·
        refine ⟨20414408511585263915242003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27219211348780351886989337 20414408511585263915242003)
        ·
          refine ⟨30621612767377895872863005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20414408511585263915242003 30621612767377895872863005)
          ·
            refine ⟨11483104787766710952323627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30621612767377895872863005 11483104787766710952323627)
            ·
              refine ⟨17224657181650066428485441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11483104787766710952323627 17224657181650066428485441)
              ·
                refine ⟨12918492886237549821364081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17224657181650066428485441 12918492886237549821364081)
                ·
                  refine ⟨9688869664678162366023061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12918492886237549821364081 9688869664678162366023061)
                  ·
                    refine ⟨454165765531788860907331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9688869664678162366023061 454165765531788860907331)
                    ·
                      rfl

theorem cell23_2653454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_2653454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653454 prefixEnd_2653454 := by exact prefixLift 2653454
  have htrace : WordTrace (prefixWord ++ tailWord_2653454) baseStart_2653454 baseEnd_2653454 := by
    simpa [prefixWord, tailWord_2653454, baseEnd_2653454] using wordTrace_append hprefix tailTrace_2653454
  have hstable : (prefixWord ++ tailWord_2653454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653454).length < 2 ^ (prefixWord ++ tailWord_2653454).sum := by decide
  have hdescent : baseEnd_2653454 < baseStart_2653454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653518 : List Nat := [4, 1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_2653518 : Nat := 118140960795 + 2653518 * 2 ^ 59
def prefixEnd_2653518 : Nat := 4983230072969 + 3 ^ 40 * 2653518 * 2
def baseEnd_2653518 : Nat := 151392239928583814702411

theorem tailTrace_2653518 : CollatzResearch.WordTrace tailWord_2653518 prefixEnd_2653518 151392239928583814702411 := by
  unfold tailWord_2653518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097719050095618204953151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64521168267176630426416805 12097719050095618204953151)
  ·
    refine ⟨18146578575143427307429727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12097719050095618204953151 18146578575143427307429727)
    ·
      refine ⟨27219867862715140961144591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18146578575143427307429727 27219867862715140961144591)
      ·
        refine ⟨40829801794072711441716887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27219867862715140961144591 40829801794072711441716887)
        ·
          refine ⟨61244702691109067162575331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40829801794072711441716887 61244702691109067162575331)
          ·
            refine ⟨91867054036663600743862997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61244702691109067162575331 91867054036663600743862997)
            ·
              refine ⟨2153134078984303142434289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 91867054036663600743862997 2153134078984303142434289)
              ·
                refine ⟨1614850559238227356825717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2153134078984303142434289 1614850559238227356825717)
                ·
                  refine ⟨151392239928583814702411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1614850559238227356825717 151392239928583814702411)
                  ·
                    rfl

theorem cell23_2653518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_2653518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653518 prefixEnd_2653518 := by exact prefixLift 2653518
  have htrace : WordTrace (prefixWord ++ tailWord_2653518) baseStart_2653518 baseEnd_2653518 := by
    simpa [prefixWord, tailWord_2653518, baseEnd_2653518] using wordTrace_append hprefix tailTrace_2653518
  have hstable : (prefixWord ++ tailWord_2653518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653518).length < 2 ^ (prefixWord ++ tailWord_2653518).sum := by decide
  have hdescent : baseEnd_2653518 < baseStart_2653518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653521 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 2, 5, 2]
def baseStart_2653521 : Nat := 118140960795 + 2653521 * 2 ^ 59
def prefixEnd_2653521 : Nat := 4983230072969 + 3 ^ 40 * 2653521 * 2
def baseEnd_2653521 : Nat := 1362531699799217820584185

theorem tailTrace_2653521 : CollatzResearch.WordTrace tailWord_2653521 prefixEnd_2653521 1362531699799217820584185 := by
  unfold tailWord_2653521
  simp only [CollatzResearch.WordTrace]
  refine ⟨96781861819754077151984417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64521241213169384767989611 96781861819754077151984417)
  ·
    refine ⟨72586396364815557863988313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96781861819754077151984417 72586396364815557863988313)
    ·
      refine ⟨54439797273611668397991235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72586396364815557863988313 54439797273611668397991235)
      ·
        refine ⟨81659695910417502596986853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54439797273611668397991235 81659695910417502596986853)
        ·
          refine ⟨15311192983203281736935035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81659695910417502596986853 15311192983203281736935035)
          ·
            refine ⟨22966789474804922605402553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15311192983203281736935035 22966789474804922605402553)
            ·
              refine ⟨17225092106103691954051915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22966789474804922605402553 17225092106103691954051915)
              ·
                refine ⟨25837638159155537931077873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17225092106103691954051915 25837638159155537931077873)
                ·
                  refine ⟨19378228619366653448308405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25837638159155537931077873 19378228619366653448308405)
                  ·
                    refine ⟨1816708933065623760778913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19378228619366653448308405 1816708933065623760778913)
                    ·
                      refine ⟨1362531699799217820584185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816708933065623760778913 1362531699799217820584185)
                      ·
                        rfl

theorem cell23_2653521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 5, 2].length) (baseStart_2653521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653521 prefixEnd_2653521 := by exact prefixLift 2653521
  have htrace : WordTrace (prefixWord ++ tailWord_2653521) baseStart_2653521 baseEnd_2653521 := by
    simpa [prefixWord, tailWord_2653521, baseEnd_2653521] using wordTrace_append hprefix tailTrace_2653521
  have hstable : (prefixWord ++ tailWord_2653521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653521).length < 2 ^ (prefixWord ++ tailWord_2653521).sum := by decide
  have hdescent : baseEnd_2653521 < baseStart_2653521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653551 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 4]
def baseStart_2653551 : Nat := 118140960795 + 2653551 * 2 ^ 59
def prefixEnd_2653551 : Nat := 4983230072969 + 3 ^ 40 * 2653551 * 2
def baseEnd_2653551 : Nat := 1362547104218852703209047

theorem tailTrace_2653551 : CollatzResearch.WordTrace tailWord_2653551 prefixEnd_2653551 1362547104218852703209047 := by
  unfold tailWord_2653551
  simp only [CollatzResearch.WordTrace]
  refine ⟨96782956009645392275576507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64521970673096928183717671 96782956009645392275576507)
  ·
    refine ⟨145174434014468088413364761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96782956009645392275576507 145174434014468088413364761)
    ·
      refine ⟨108880825510851066310023571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145174434014468088413364761 108880825510851066310023571)
      ·
        refine ⟨163321238266276599465035357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108880825510851066310023571 163321238266276599465035357)
        ·
          refine ⟨61245464349853724799388259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163321238266276599465035357 61245464349853724799388259)
          ·
            refine ⟨91868196524780587199082389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61245464349853724799388259 91868196524780587199082389)
            ·
              refine ⟨4306321712099090024956987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91868196524780587199082389 4306321712099090024956987)
              ·
                refine ⟨6459482568148635037435481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4306321712099090024956987 6459482568148635037435481)
                ·
                  refine ⟨4844611926111476278076611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6459482568148635037435481 4844611926111476278076611)
                  ·
                    refine ⟨7266917889167214417114917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4844611926111476278076611 7266917889167214417114917)
                    ·
                      refine ⟨1362547104218852703209047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7266917889167214417114917 1362547104218852703209047)
                      ·
                        rfl

theorem cell23_2653551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 4].length) (baseStart_2653551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653551 prefixEnd_2653551 := by exact prefixLift 2653551
  have htrace : WordTrace (prefixWord ++ tailWord_2653551) baseStart_2653551 baseEnd_2653551 := by
    simpa [prefixWord, tailWord_2653551, baseEnd_2653551] using wordTrace_append hprefix tailTrace_2653551
  have hstable : (prefixWord ++ tailWord_2653551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653551).length < 2 ^ (prefixWord ++ tailWord_2653551).sum := by decide
  have hdescent : baseEnd_2653551 < baseStart_2653551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653564 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_2653564 : Nat := 118140960795 + 2653564 * 2 ^ 59
def prefixEnd_2653564 : Nat := 4983230072969 + 3 ^ 40 * 2653564 * 2
def baseEnd_2653564 : Nat := 1362553779467361152346487

theorem tailTrace_2653564 : CollatzResearch.WordTrace tailWord_2653564 prefixEnd_2653564 1362553779467361152346487 := by
  unfold tailWord_2653564
  simp only [CollatzResearch.WordTrace]
  refine ⟨48391715079299147747899873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64522286772398863663866497 48391715079299147747899873)
  ·
    refine ⟨36293786309474360810924905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48391715079299147747899873 36293786309474360810924905)
    ·
      refine ⟨27220339732105770608193679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36293786309474360810924905 27220339732105770608193679)
      ·
        refine ⟨40830509598158655912290519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27220339732105770608193679 40830509598158655912290519)
        ·
          refine ⟨61245764397237983868435779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40830509598158655912290519 61245764397237983868435779)
          ·
            refine ⟨91868646595856975802653669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61245764397237983868435779 91868646595856975802653669)
            ·
              refine ⟨17225371236723182962997563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91868646595856975802653669 17225371236723182962997563)
              ·
                refine ⟨25838056855084774444496345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17225371236723182962997563 25838056855084774444496345)
                ·
                  refine ⟨19378542641313580833372259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25838056855084774444496345 19378542641313580833372259)
                  ·
                    refine ⟨29067813961970371250058389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19378542641313580833372259 29067813961970371250058389)
                    ·
                      refine ⟨1362553779467361152346487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29067813961970371250058389 1362553779467361152346487)
                      ·
                        rfl

theorem cell23_2653564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_2653564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653564 prefixEnd_2653564 := by exact prefixLift 2653564
  have htrace : WordTrace (prefixWord ++ tailWord_2653564) baseStart_2653564 baseEnd_2653564 := by
    simpa [prefixWord, tailWord_2653564, baseEnd_2653564] using wordTrace_append hprefix tailTrace_2653564
  have hstable : (prefixWord ++ tailWord_2653564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653564).length < 2 ^ (prefixWord ++ tailWord_2653564).sum := by decide
  have hdescent : baseEnd_2653564 < baseStart_2653564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653625 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 6]
def baseStart_2653625 : Nat := 118140960795 + 2653625 * 2 ^ 59
def prefixEnd_2653625 : Nat := 4983230072969 + 3 ^ 40 * 2653625 * 2
def baseEnd_2653625 : Nat := 151398344643031712631523

theorem tailTrace_2653625 : CollatzResearch.WordTrace tailWord_2653625 prefixEnd_2653625 151398344643031712631523 := by
  unfold tailWord_2653625
  simp only [CollatzResearch.WordTrace]
  refine ⟨96785655011377302913770329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64523770007584868609180219 96785655011377302913770329)
  ·
    refine ⟨72589241258532977185327747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96785655011377302913770329 72589241258532977185327747)
    ·
      refine ⟨108883861887799465777991621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72589241258532977185327747 108883861887799465777991621)
      ·
        refine ⟨20415724103962399833373429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108883861887799465777991621 20415724103962399833373429)
        ·
          refine ⟨1913974134746474984378759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20415724103962399833373429 1913974134746474984378759)
          ·
            refine ⟨2870961202119712476568139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913974134746474984378759 2870961202119712476568139)
            ·
              refine ⟨4306441803179568714852209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2870961202119712476568139 4306441803179568714852209)
              ·
                refine ⟨3229831352384676536139157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4306441803179568714852209 3229831352384676536139157)
                ·
                  refine ⟨151398344643031712631523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3229831352384676536139157 151398344643031712631523)
                  ·
                    rfl

theorem cell23_2653625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 6].length) (baseStart_2653625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653625 prefixEnd_2653625 := by exact prefixLift 2653625
  have htrace : WordTrace (prefixWord ++ tailWord_2653625) baseStart_2653625 baseEnd_2653625 := by
    simpa [prefixWord, tailWord_2653625, baseEnd_2653625] using wordTrace_append hprefix tailTrace_2653625
  have hstable : (prefixWord ++ tailWord_2653625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653625).length < 2 ^ (prefixWord ++ tailWord_2653625).sum := by decide
  have hdescent : baseEnd_2653625 < baseStart_2653625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653635 : List Nat := [1, 1, 1, 3, 1, 1, 6, 4, 1, 1, 3]
def baseStart_2653635 : Nat := 118140960795 + 2653635 * 2 ^ 59
def prefixEnd_2653635 : Nat := 4983230072969 + 3 ^ 40 * 2653635 * 2
def baseEnd_2653635 : Nat := 1362590236593830374558661

theorem tailTrace_2653635 : CollatzResearch.WordTrace tailWord_2653635 prefixEnd_2653635 1362590236593830374558661 := by
  unfold tailWord_2653635
  simp only [CollatzResearch.WordTrace]
  refine ⟨96786019741341074621634359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64524013160894049747756239 96786019741341074621634359)
  ·
    refine ⟨145179029612011611932451539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96786019741341074621634359 145179029612011611932451539)
    ·
      refine ⟨217768544418017417898677309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145179029612011611932451539 217768544418017417898677309)
      ·
        refine ⟨81663204156756531712003991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217768544418017417898677309 81663204156756531712003991)
        ·
          refine ⟨122494806235134797568005987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81663204156756531712003991 122494806235134797568005987)
          ·
            refine ⟨183742209352702196352008981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122494806235134797568005987 183742209352702196352008981)
            ·
              refine ⟨8612916063407915454000421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 183742209352702196352008981 8612916063407915454000421)
              ·
                refine ⟨1614921761888984147625079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8612916063407915454000421 1614921761888984147625079)
                ·
                  refine ⟨2422382642833476221437619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614921761888984147625079 2422382642833476221437619)
                  ·
                    refine ⟨3633573964250214332156429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2422382642833476221437619 3633573964250214332156429)
                    ·
                      refine ⟨1362590236593830374558661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3633573964250214332156429 1362590236593830374558661)
                      ·
                        rfl

theorem cell23_2653635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 1, 1, 3].length) (baseStart_2653635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653635 prefixEnd_2653635 := by exact prefixLift 2653635
  have htrace : WordTrace (prefixWord ++ tailWord_2653635) baseStart_2653635 baseEnd_2653635 := by
    simpa [prefixWord, tailWord_2653635, baseEnd_2653635] using wordTrace_append hprefix tailTrace_2653635
  have hstable : (prefixWord ++ tailWord_2653635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653635).length < 2 ^ (prefixWord ++ tailWord_2653635).sum := by decide
  have hdescent : baseEnd_2653635 < baseStart_2653635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653658 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4]
def baseStart_2653658 : Nat := 118140960795 + 2653658 * 2 ^ 59
def prefixEnd_2653658 : Nat := 4983230072969 + 3 ^ 40 * 2653658 * 2
def baseEnd_2653658 : Nat := 1362602046648883784571055

theorem tailTrace_2653658 : CollatzResearch.WordTrace tailWord_2653658 prefixEnd_2653658 1362602046648883784571055 := by
  unfold tailWord_2653658
  simp only [CollatzResearch.WordTrace]
  refine ⟨24196714655064437387430407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64524572413505166366481085 24196714655064437387430407)
  ·
    refine ⟨36295071982596656081145611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24196714655064437387430407 36295071982596656081145611)
    ·
      refine ⟨54442607973894984121718417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36295071982596656081145611 54442607973894984121718417)
      ·
        refine ⟨40831955980421238091288813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54442607973894984121718417 40831955980421238091288813)
        ·
          refine ⟨15311983492657964284233305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40831955980421238091288813 15311983492657964284233305)
          ·
            refine ⟨11483987619493473213174979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15311983492657964284233305 11483987619493473213174979)
            ·
              refine ⟨17225981429240209819762469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11483987619493473213174979 17225981429240209819762469)
              ·
                refine ⟨3229871517982539341205463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17225981429240209819762469 3229871517982539341205463)
                ·
                  refine ⟨4844807276973809011808195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229871517982539341205463 4844807276973809011808195)
                  ·
                    refine ⟨7267210915460713517712293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4844807276973809011808195 7267210915460713517712293)
                    ·
                      refine ⟨1362602046648883784571055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7267210915460713517712293 1362602046648883784571055)
                      ·
                        rfl

theorem cell23_2653658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_2653658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653658 prefixEnd_2653658 := by exact prefixLift 2653658
  have htrace : WordTrace (prefixWord ++ tailWord_2653658) baseStart_2653658 baseEnd_2653658 := by
    simpa [prefixWord, tailWord_2653658, baseEnd_2653658] using wordTrace_append hprefix tailTrace_2653658
  have hstable : (prefixWord ++ tailWord_2653658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653658).length < 2 ^ (prefixWord ++ tailWord_2653658).sum := by decide
  have hdescent : baseEnd_2653658 < baseStart_2653658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653669 : List Nat := [1, 3, 1, 5, 1, 3, 1, 3, 1, 1, 3]
def baseStart_2653669 : Nat := 118140960795 + 2653669 * 2 ^ 59
def prefixEnd_2653669 : Nat := 4983230072969 + 3 ^ 40 * 2653669 * 2
def baseEnd_2653669 : Nat := 1362607694936083241533505

theorem tailTrace_2653669 : CollatzResearch.WordTrace tailWord_2653669 prefixEnd_2653669 1362607694936083241533505 := by
  unfold tailWord_2653669
  simp only [CollatzResearch.WordTrace]
  refine ⟨96787259823217898428372061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64524839882145265618914707 96787259823217898428372061)
  ·
    refine ⟨36295222433706711910639523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96787259823217898428372061 36295222433706711910639523)
    ·
      refine ⟨54442833650560067865959285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36295222433706711910639523 54442833650560067865959285)
      ·
        refine ⟨5104015654740006362433683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54442833650560067865959285 5104015654740006362433683)
        ·
          refine ⟨7656023482110009543650525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5104015654740006362433683 7656023482110009543650525)
          ·
            refine ⟨2871008805791253578868947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7656023482110009543650525 2871008805791253578868947)
            ·
              refine ⟨4306513208686880368303421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871008805791253578868947 4306513208686880368303421)
              ·
                refine ⟨1614942453257580138113783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4306513208686880368303421 1614942453257580138113783)
                ·
                  refine ⟨2422413679886370207170675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614942453257580138113783 2422413679886370207170675)
                  ·
                    refine ⟨3633620519829555310756013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2422413679886370207170675 3633620519829555310756013)
                    ·
                      refine ⟨1362607694936083241533505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3633620519829555310756013 1362607694936083241533505)
                      ·
                        rfl

theorem cell23_2653669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_2653669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653669 prefixEnd_2653669 := by exact prefixLift 2653669
  have htrace : WordTrace (prefixWord ++ tailWord_2653669) baseStart_2653669 baseEnd_2653669 := by
    simpa [prefixWord, tailWord_2653669, baseEnd_2653669] using wordTrace_append hprefix tailTrace_2653669
  have hstable : (prefixWord ++ tailWord_2653669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653669).length < 2 ^ (prefixWord ++ tailWord_2653669).sum := by decide
  have hdescent : baseEnd_2653669 < baseStart_2653669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653678 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_2653678 : Nat := 118140960795 + 2653678 * 2 ^ 59
def prefixEnd_2653678 : Nat := 4983230072969 + 3 ^ 40 * 2653678 * 2
def baseEnd_2653678 : Nat := 1362612316261973706320963

theorem tailTrace_2653678 : CollatzResearch.WordTrace tailWord_2653678 prefixEnd_2653678 1362612316261973706320963 := by
  unfold tailWord_2653678
  simp only [CollatzResearch.WordTrace]
  refine ⟨12098448510023161620681211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64525058720123528643633125 12098448510023161620681211)
  ·
    refine ⟨18147672765034742431021817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12098448510023161620681211 18147672765034742431021817)
    ·
      refine ⟨13610754573776056823266363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18147672765034742431021817 13610754573776056823266363)
      ·
        refine ⟨20416131860664085234899545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13610754573776056823266363 20416131860664085234899545)
        ·
          refine ⟨15312098895498063926174659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20416131860664085234899545 15312098895498063926174659)
          ·
            refine ⟨22968148343247095889261989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15312098895498063926174659 22968148343247095889261989)
            ·
              refine ⟨4306527814358830479236623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22968148343247095889261989 4306527814358830479236623)
              ·
                refine ⟨6459791721538245718854935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4306527814358830479236623 6459791721538245718854935)
                ·
                  refine ⟨9689687582307368578282403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6459791721538245718854935 9689687582307368578282403)
                  ·
                    refine ⟨14534531373461052867423605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9689687582307368578282403 14534531373461052867423605)
                    ·
                      refine ⟨1362612316261973706320963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14534531373461052867423605 1362612316261973706320963)
                      ·
                        rfl

theorem cell23_2653678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_2653678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653678 prefixEnd_2653678 := by exact prefixLift 2653678
  have htrace : WordTrace (prefixWord ++ tailWord_2653678) baseStart_2653678 baseEnd_2653678 := by
    simpa [prefixWord, tailWord_2653678, baseEnd_2653678] using wordTrace_append hprefix tailTrace_2653678
  have hstable : (prefixWord ++ tailWord_2653678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653678).length < 2 ^ (prefixWord ++ tailWord_2653678).sum := by decide
  have hdescent : baseEnd_2653678 < baseStart_2653678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653681 : List Nat := [1, 2, 2, 2, 3, 4, 9]
def baseStart_2653681 : Nat := 118140960795 + 2653681 * 2 ^ 59
def prefixEnd_2653681 : Nat := 4983230072969 + 3 ^ 40 * 2653681 * 2
def baseEnd_2653681 : Nat := 16822393292641199933129

theorem tailTrace_2653681 : CollatzResearch.WordTrace tailWord_2653681 prefixEnd_2653681 16822393292641199933129 := by
  unfold tailWord_2653681
  simp only [CollatzResearch.WordTrace]
  refine ⟨96787697499174424477808897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64525131666116282985205931 96787697499174424477808897)
  ·
    refine ⟨72590773124380818358356673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96787697499174424477808897 72590773124380818358356673)
    ·
      refine ⟨54443079843285613768767505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72590773124380818358356673 54443079843285613768767505)
      ·
        refine ⟨40832309882464210326575629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54443079843285613768767505 40832309882464210326575629)
        ·
          refine ⟨15312116205924078872465861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40832309882464210326575629 15312116205924078872465861)
          ·
            refine ⟨2871021788610764788587349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15312116205924078872465861 2871021788610764788587349)
            ·
              refine ⟨16822393292641199933129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2871021788610764788587349 16822393292641199933129)
              ·
                rfl

theorem cell23_2653681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 9].length) (baseStart_2653681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653681 prefixEnd_2653681 := by exact prefixLift 2653681
  have htrace : WordTrace (prefixWord ++ tailWord_2653681) baseStart_2653681 baseEnd_2653681 := by
    simpa [prefixWord, tailWord_2653681, baseEnd_2653681] using wordTrace_append hprefix tailTrace_2653681
  have hstable : (prefixWord ++ tailWord_2653681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653681).length < 2 ^ (prefixWord ++ tailWord_2653681).sum := by decide
  have hdescent : baseEnd_2653681 < baseStart_2653681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653685 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2653685 : Nat := 118140960795 + 2653685 * 2 ^ 59
def prefixEnd_2653685 : Nat := 4983230072969 + 3 ^ 40 * 2653685 * 2
def baseEnd_2653685 : Nat := 454205303542185059644477

theorem tailTrace_2653685 : CollatzResearch.WordTrace tailWord_2653685 prefixEnd_2653685 454205303542185059644477 := by
  unfold tailWord_2653685
  simp only [CollatzResearch.WordTrace]
  refine ⟨96787843391159933160954509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64525228927439955440636339 96787843391159933160954509)
  ·
    refine ⟨36295441271684974935357941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96787843391159933160954509 36295441271684974935357941)
    ·
      refine ⟨3402697619220466400189807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36295441271684974935357941 3402697619220466400189807)
      ·
        refine ⟨5104046428830699600284711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402697619220466400189807 5104046428830699600284711)
        ·
          refine ⟨7656069643246049400427067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5104046428830699600284711 7656069643246049400427067)
          ·
            refine ⟨11484104464869074100640601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7656069643246049400427067 11484104464869074100640601)
            ·
              refine ⟨8613078348651805575480451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11484104464869074100640601 8613078348651805575480451)
              ·
                refine ⟨12919617522977708363220677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8613078348651805575480451 12919617522977708363220677)
                ·
                  refine ⟨2422428285558320318103877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12919617522977708363220677 2422428285558320318103877)
                  ·
                    refine ⟨454205303542185059644477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2422428285558320318103877 454205303542185059644477)
                    ·
                      rfl

theorem cell23_2653685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2653685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653685 prefixEnd_2653685 := by exact prefixLift 2653685
  have htrace : WordTrace (prefixWord ++ tailWord_2653685) baseStart_2653685 baseEnd_2653685 := by
    simpa [prefixWord, tailWord_2653685, baseEnd_2653685] using wordTrace_append hprefix tailTrace_2653685
  have hstable : (prefixWord ++ tailWord_2653685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653685).length < 2 ^ (prefixWord ++ tailWord_2653685).sum := by decide
  have hdescent : baseEnd_2653685 < baseStart_2653685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653691 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 3]
def baseStart_2653691 : Nat := 118140960795 + 2653691 * 2 ^ 59
def prefixEnd_2653691 : Nat := 4983230072969 + 3 ^ 40 * 2653691 * 2
def baseEnd_2653691 : Nat := 1362618991510482155458403

theorem tailTrace_2653691 : CollatzResearch.WordTrace tailWord_2653691 prefixEnd_2653691 1362618991510482155458403 := by
  unfold tailWord_2653691
  simp only [CollatzResearch.WordTrace]
  refine ⟨96788062229138196185672927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64525374819425464123781951 96788062229138196185672927)
  ·
    refine ⟨145182093343707294278509391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96788062229138196185672927 145182093343707294278509391)
    ·
      refine ⟨217773140015560941417764087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145182093343707294278509391 217773140015560941417764087)
      ·
        refine ⟨326659710023341412126646131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217773140015560941417764087 326659710023341412126646131)
        ·
          refine ⟨489989565035012118189969197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326659710023341412126646131 489989565035012118189969197)
          ·
            refine ⟨183746086888129544321238449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 489989565035012118189969197 183746086888129544321238449)
            ·
              refine ⟨137809565166097158240928837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183746086888129544321238449 137809565166097158240928837)
              ·
                refine ⟨25839293468643217170174157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137809565166097158240928837 25839293468643217170174157)
                ·
                  refine ⟨9689735050741206438815309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25839293468643217170174157 9689735050741206438815309)
                  ·
                    refine ⟨3633650644027952414555741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9689735050741206438815309 3633650644027952414555741)
                    ·
                      refine ⟨1362618991510482155458403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3633650644027952414555741 1362618991510482155458403)
                      ·
                        rfl

theorem cell23_2653691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 3].length) (baseStart_2653691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653691 prefixEnd_2653691 := by exact prefixLift 2653691
  have htrace : WordTrace (prefixWord ++ tailWord_2653691) baseStart_2653691 baseEnd_2653691 := by
    simpa [prefixWord, tailWord_2653691, baseEnd_2653691] using wordTrace_append hprefix tailTrace_2653691
  have hstable : (prefixWord ++ tailWord_2653691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653691).length < 2 ^ (prefixWord ++ tailWord_2653691).sum := by decide
  have hdescent : baseEnd_2653691 < baseStart_2653691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653692 : List Nat := [2, 2, 2, 1, 2, 1, 2, 6, 1, 2, 2]
def baseStart_2653692 : Nat := 118140960795 + 2653692 * 2 ^ 59
def prefixEnd_2653692 : Nat := 4983230072969 + 3 ^ 40 * 2653692 * 2
def baseEnd_2653692 : Nat := 1362619504991136651545899

theorem tailTrace_2653692 : CollatzResearch.WordTrace tailWord_2653692 prefixEnd_2653692 1362619504991136651545899 := by
  unfold tailWord_2653692
  simp only [CollatzResearch.WordTrace]
  refine ⟨48394049351067286678229665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64525399134756382237639553 48394049351067286678229665)
  ·
    refine ⟨36295537013300465008672249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48394049351067286678229665 36295537013300465008672249)
    ·
      refine ⟨27221652759975348756504187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36295537013300465008672249 27221652759975348756504187)
      ·
        refine ⟨40832479139963023134756281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27221652759975348756504187 40832479139963023134756281)
        ·
          refine ⟨30624359354972267351067211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40832479139963023134756281 30624359354972267351067211)
          ·
            refine ⟨45936539032458401026600817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30624359354972267351067211 45936539032458401026600817)
            ·
              refine ⟨34452404274343800769950613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45936539032458401026600817 34452404274343800769950613)
              ·
                refine ⟨1614956450359865661091435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34452404274343800769950613 1614956450359865661091435)
                ·
                  refine ⟨2422434675539798491637153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614956450359865661091435 2422434675539798491637153)
                  ·
                    refine ⟨1816826006654848868727865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2422434675539798491637153 1816826006654848868727865)
                    ·
                      refine ⟨1362619504991136651545899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816826006654848868727865 1362619504991136651545899)
                      ·
                        rfl

theorem cell23_2653692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_2653692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653692 prefixEnd_2653692 := by exact prefixLift 2653692
  have htrace : WordTrace (prefixWord ++ tailWord_2653692) baseStart_2653692 baseEnd_2653692 := by
    simpa [prefixWord, tailWord_2653692, baseEnd_2653692] using wordTrace_append hprefix tailTrace_2653692
  have hstable : (prefixWord ++ tailWord_2653692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653692).length < 2 ^ (prefixWord ++ tailWord_2653692).sum := by decide
  have hdescent : baseEnd_2653692 < baseStart_2653692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653698 : List Nat := [3, 4, 1, 2, 1, 1, 1, 10]
def baseStart_2653698 : Nat := 118140960795 + 2653698 * 2 ^ 59
def prefixEnd_2653698 : Nat := 4983230072969 + 3 ^ 40 * 2653698 * 2
def baseEnd_2653698 : Nat := 50467503180557912150773

theorem tailTrace_2653698 : CollatzResearch.WordTrace tailWord_2653698 prefixEnd_2653698 50467503180557912150773 := by
  unfold tailWord_2653698
  simp only [CollatzResearch.WordTrace]
  refine ⟨24197079385028209095294437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64525545026741890920785165 24197079385028209095294437)
  ·
    refine ⟨4536952384692789205367707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24197079385028209095294437 4536952384692789205367707)
    ·
      refine ⟨6805428577039183808051561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4536952384692789205367707 6805428577039183808051561)
      ·
        refine ⟨5104071432779387856038671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6805428577039183808051561 5104071432779387856038671)
        ·
          refine ⟨7656107149169081784058007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5104071432779387856038671 7656107149169081784058007)
          ·
            refine ⟨11484160723753622676087011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7656107149169081784058007 11484160723753622676087011)
            ·
              refine ⟨17226241085630434014130517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11484160723753622676087011 17226241085630434014130517)
              ·
                refine ⟨50467503180557912150773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17226241085630434014130517 50467503180557912150773)
                ·
                  rfl

theorem cell23_2653698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 10].length) (baseStart_2653698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653698 prefixEnd_2653698 := by exact prefixLift 2653698
  have htrace : WordTrace (prefixWord ++ tailWord_2653698) baseStart_2653698 baseEnd_2653698 := by
    simpa [prefixWord, tailWord_2653698, baseEnd_2653698] using wordTrace_append hprefix tailTrace_2653698
  have hstable : (prefixWord ++ tailWord_2653698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653698).length < 2 ^ (prefixWord ++ tailWord_2653698).sum := by decide
  have hdescent : baseEnd_2653698 < baseStart_2653698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653742 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_2653742 : Nat := 118140960795 + 2653742 * 2 ^ 59
def prefixEnd_2653742 : Nat := 4983230072969 + 3 ^ 40 * 2653742 * 2
def baseEnd_2653742 : Nat := 1362645179023861455920669

theorem tailTrace_2653742 : CollatzResearch.WordTrace tailWord_2653742 prefixEnd_2653742 1362645179023861455920669 := by
  unfold tailWord_2653742
  simp only [CollatzResearch.WordTrace]
  refine ⟨12098740293994178986972435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64526614901302287930519653 12098740293994178986972435)
  ·
    refine ⟨18148110440991268480458653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12098740293994178986972435 18148110440991268480458653)
    ·
      refine ⟨6805541415371725680171995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18148110440991268480458653 6805541415371725680171995)
      ·
        refine ⟨10208312123057588520257993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6805541415371725680171995 10208312123057588520257993)
        ·
          refine ⟨7656234092293191390193495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10208312123057588520257993 7656234092293191390193495)
          ·
            refine ⟨11484351138439787085290243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7656234092293191390193495 11484351138439787085290243)
            ·
              refine ⟨17226526707659680627935365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11484351138439787085290243 17226526707659680627935365)
              ·
                refine ⟨3229973757686190117737881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17226526707659680627935365 3229973757686190117737881)
                ·
                  refine ⟨2422480318264642588303411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3229973757686190117737881 2422480318264642588303411)
                  ·
                    refine ⟨3633720477396963882455117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2422480318264642588303411 3633720477396963882455117)
                    ·
                      refine ⟨1362645179023861455920669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3633720477396963882455117 1362645179023861455920669)
                      ·
                        rfl

theorem cell23_2653742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_2653742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653742 prefixEnd_2653742 := by exact prefixLift 2653742
  have htrace : WordTrace (prefixWord ++ tailWord_2653742) baseStart_2653742 baseEnd_2653742 := by
    simpa [prefixWord, tailWord_2653742, baseEnd_2653742] using wordTrace_append hprefix tailTrace_2653742
  have hstable : (prefixWord ++ tailWord_2653742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653742).length < 2 ^ (prefixWord ++ tailWord_2653742).sum := by decide
  have hdescent : baseEnd_2653742 < baseStart_2653742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653765 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 1, 4, 2]
def baseStart_2653765 : Nat := 118140960795 + 2653765 * 2 ^ 59
def prefixEnd_2653765 : Nat := 4983230072969 + 3 ^ 40 * 2653765 * 2
def baseEnd_2653765 : Nat := 1362656989078914865933063

theorem tailTrace_2653765 : CollatzResearch.WordTrace tailWord_2653765 prefixEnd_2653765 1362656989078914865933063 := by
  unfold tailWord_2653765
  simp only [CollatzResearch.WordTrace]
  refine ⟨96790761230870106823866749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64527174153913404549244499 96790761230870106823866749)
  ·
    refine ⟨36296535461576290058950031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96790761230870106823866749 36296535461576290058950031)
    ·
      refine ⟨54444803192364435088425047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36296535461576290058950031 54444803192364435088425047)
      ·
        refine ⟨81667204788546652632637571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54444803192364435088425047 81667204788546652632637571)
        ·
          refine ⟨122500807182819978948956357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81667204788546652632637571 122500807182819978948956357)
          ·
            refine ⟨22968901346778746052929317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122500807182819978948956357 22968901346778746052929317)
            ·
              refine ⟨4306669002521014884924247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22968901346778746052929317 4306669002521014884924247)
              ·
                refine ⟨6460003503781522327386371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4306669002521014884924247 6460003503781522327386371)
                ·
                  refine ⟨9690005255672283491079557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6460003503781522327386371 9690005255672283491079557)
                  ·
                    refine ⟨1816875985438553154577417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9690005255672283491079557 1816875985438553154577417)
                    ·
                      refine ⟨1362656989078914865933063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1816875985438553154577417 1362656989078914865933063)
                      ·
                        rfl

theorem cell23_2653765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 4, 2].length) (baseStart_2653765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653765 prefixEnd_2653765 := by exact prefixLift 2653765
  have htrace : WordTrace (prefixWord ++ tailWord_2653765) baseStart_2653765 baseEnd_2653765 := by
    simpa [prefixWord, tailWord_2653765, baseEnd_2653765] using wordTrace_append hprefix tailTrace_2653765
  have hstable : (prefixWord ++ tailWord_2653765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653765).length < 2 ^ (prefixWord ++ tailWord_2653765).sum := by decide
  have hdescent : baseEnd_2653765 < baseStart_2653765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653781 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2653781 : Nat := 118140960795 + 2653781 * 2 ^ 59
def prefixEnd_2653781 : Nat := 4983230072969 + 3 ^ 40 * 2653781 * 2
def baseEnd_2653781 : Nat := 1362665204769386803332989

theorem tailTrace_2653781 : CollatzResearch.WordTrace tailWord_2653781 prefixEnd_2653781 1362665204769386803332989 := by
  unfold tailWord_2653781
  simp only [CollatzResearch.WordTrace]
  refine ⟨96791344798812141556449197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64527563199208094370966131 96791344798812141556449197)
  ·
    refine ⟨36296754299554553083668449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96791344798812141556449197 36296754299554553083668449)
    ·
      refine ⟨27222565724665914812751337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36296754299554553083668449 27222565724665914812751337)
      ·
        refine ⟨20416924293499436109563503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27222565724665914812751337 20416924293499436109563503)
        ·
          refine ⟨30625386440249154164345255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20416924293499436109563503 30625386440249154164345255)
          ·
            refine ⟨45938079660373731246517883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30625386440249154164345255 45938079660373731246517883)
            ·
              refine ⟨68907119490560596869776825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45938079660373731246517883 68907119490560596869776825)
              ·
                refine ⟨51680339617920447652332619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68907119490560596869776825 51680339617920447652332619)
                ·
                  refine ⟨77520509426880671478498929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51680339617920447652332619 77520509426880671478498929)
                  ·
                    refine ⟨58140382070160503608874197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77520509426880671478498929 58140382070160503608874197)
                    ·
                      refine ⟨1362665204769386803332989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58140382070160503608874197 1362665204769386803332989)
                      ·
                        rfl

theorem cell23_2653781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2653781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653781 prefixEnd_2653781 := by exact prefixLift 2653781
  have htrace : WordTrace (prefixWord ++ tailWord_2653781) baseStart_2653781 baseEnd_2653781 := by
    simpa [prefixWord, tailWord_2653781, baseEnd_2653781] using wordTrace_append hprefix tailTrace_2653781
  have hstable : (prefixWord ++ tailWord_2653781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653781).length < 2 ^ (prefixWord ++ tailWord_2653781).sum := by decide
  have hdescent : baseEnd_2653781 < baseStart_2653781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653805 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 7]
def baseStart_2653805 : Nat := 118140960795 + 2653805 * 2 ^ 59
def prefixEnd_2653805 : Nat := 4983230072969 + 3 ^ 40 * 2653805 * 2
def baseEnd_2653805 : Nat := 151408614256121634381431

theorem tailTrace_2653805 : CollatzResearch.WordTrace tailWord_2653805 prefixEnd_2653805 151408614256121634381431 := by
  unfold tailWord_2653805
  simp only [CollatzResearch.WordTrace]
  refine ⟨96792220150725193655322869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64528146767150129103548579 96792220150725193655322869)
  ·
    refine ⟨9074270639130486905186519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96792220150725193655322869 9074270639130486905186519)
    ·
      refine ⟨13611405958695730357779779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9074270639130486905186519 13611405958695730357779779)
      ·
        refine ⟨20417108938043595536669669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13611405958695730357779779 20417108938043595536669669)
        ·
          refine ⟨3828207925883174163125563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20417108938043595536669669 3828207925883174163125563)
          ·
            refine ⟨5742311888824761244688345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3828207925883174163125563 5742311888824761244688345)
            ·
              refine ⟨4306733916618570933516259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5742311888824761244688345 4306733916618570933516259)
              ·
                refine ⟨6460100874927856400274389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4306733916618570933516259 6460100874927856400274389)
                ·
                  refine ⟨151408614256121634381431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6460100874927856400274389 151408614256121634381431)
                  ·
                    rfl

theorem cell23_2653805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_2653805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653805 prefixEnd_2653805 := by exact prefixLift 2653805
  have htrace : WordTrace (prefixWord ++ tailWord_2653805) baseStart_2653805 baseEnd_2653805 := by
    simpa [prefixWord, tailWord_2653805, baseEnd_2653805] using wordTrace_append hprefix tailTrace_2653805
  have hstable : (prefixWord ++ tailWord_2653805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653805).length < 2 ^ (prefixWord ++ tailWord_2653805).sum := by decide
  have hdescent : baseEnd_2653805 < baseStart_2653805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653811 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 5]
def baseStart_2653811 : Nat := 118140960795 + 2653811 * 2 ^ 59
def prefixEnd_2653811 : Nat := 4983230072969 + 3 ^ 40 * 2653811 * 2
def baseEnd_2653811 : Nat := 1362680609189021685957851

theorem tailTrace_2653811 : CollatzResearch.WordTrace tailWord_2653811 prefixEnd_2653811 1362680609189021685957851 := by
  unfold tailWord_2653811
  simp only [CollatzResearch.WordTrace]
  refine ⟨96792438988703456680041287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64528292659135637786694191 96792438988703456680041287)
  ·
    refine ⟨145188658483055185020061931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96792438988703456680041287 145188658483055185020061931)
    ·
      refine ⟨217782987724582777530092897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145188658483055185020061931 217782987724582777530092897)
      ·
        refine ⟨163337240793437083147569673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217782987724582777530092897 163337240793437083147569673)
        ·
          refine ⟨122502930595077812360677255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163337240793437083147569673 122502930595077812360677255)
          ·
            refine ⟨183754395892616718541015883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122502930595077812360677255 183754395892616718541015883)
            ·
              refine ⟨275631593838925077811523825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183754395892616718541015883 275631593838925077811523825)
              ·
                refine ⟨206723695379193808358642869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275631593838925077811523825 206723695379193808358642869)
                ·
                  refine ⟨19380346441799419533622769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206723695379193808358642869 19380346441799419533622769)
                  ·
                    refine ⟨14535259831349564650217077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19380346441799419533622769 14535259831349564650217077)
                    ·
                      refine ⟨1362680609189021685957851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14535259831349564650217077 1362680609189021685957851)
                      ·
                        rfl

theorem cell23_2653811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_2653811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653811 prefixEnd_2653811 := by exact prefixLift 2653811
  have htrace : WordTrace (prefixWord ++ tailWord_2653811) baseStart_2653811 baseEnd_2653811 := by
    simpa [prefixWord, tailWord_2653811, baseEnd_2653811] using wordTrace_append hprefix tailTrace_2653811
  have hstable : (prefixWord ++ tailWord_2653811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653811).length < 2 ^ (prefixWord ++ tailWord_2653811).sum := by decide
  have hdescent : baseEnd_2653811 < baseStart_2653811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653892 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2653892 : Nat := 118140960795 + 2653892 * 2 ^ 59
def prefixEnd_2653892 : Nat := 4983230072969 + 3 ^ 40 * 2653892 * 2
def baseEnd_2653892 : Nat := 1362722201122035869044979

theorem tailTrace_2653892 : CollatzResearch.WordTrace tailWord_2653892 prefixEnd_2653892 1362722201122035869044979 := by
  unfold tailWord_2653892
  simp only [CollatzResearch.WordTrace]
  refine ⟨48397696650705003756869965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64530262200940005009159953 48397696650705003756869965)
  ·
    refine ⟨18149136244014376408826237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48397696650705003756869965 18149136244014376408826237)
    ·
      refine ⟨6805926091505391153309839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18149136244014376408826237 6805926091505391153309839)
      ·
        refine ⟨10208889137258086729964759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6805926091505391153309839 10208889137258086729964759)
        ·
          refine ⟨15313333705887130094947139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10208889137258086729964759 15313333705887130094947139)
          ·
            refine ⟨22970000558830695142420709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15313333705887130094947139 22970000558830695142420709)
            ·
              refine ⟨4306875104780755339203883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22970000558830695142420709 4306875104780755339203883)
              ·
                refine ⟨6460312657171133008805825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4306875104780755339203883 6460312657171133008805825)
                ·
                  refine ⟨4845234492878349756604369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6460312657171133008805825 4845234492878349756604369)
                  ·
                    refine ⟨3633925869658762317453277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4845234492878349756604369 3633925869658762317453277)
                    ·
                      refine ⟨1362722201122035869044979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3633925869658762317453277 1362722201122035869044979)
                      ·
                        rfl

theorem cell23_2653892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2653892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653892 prefixEnd_2653892 := by exact prefixLift 2653892
  have htrace : WordTrace (prefixWord ++ tailWord_2653892) baseStart_2653892 baseEnd_2653892 := by
    simpa [prefixWord, tailWord_2653892, baseEnd_2653892] using wordTrace_append hprefix tailTrace_2653892
  have hstable : (prefixWord ++ tailWord_2653892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653892).length < 2 ^ (prefixWord ++ tailWord_2653892).sum := by decide
  have hdescent : baseEnd_2653892 < baseStart_2653892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653916 : List Nat := [2, 2, 5, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2653916 : Nat := 118140960795 + 2653916 * 2 ^ 59
def prefixEnd_2653916 : Nat := 4983230072969 + 3 ^ 40 * 2653916 * 2
def baseEnd_2653916 : Nat := 454244841552581258381623

theorem tailTrace_2653916 : CollatzResearch.WordTrace tailWord_2653916 prefixEnd_2653916 454244841552581258381623 := by
  unfold tailWord_2653916
  simp only [CollatzResearch.WordTrace]
  refine ⟨48398134326661529806306801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64530845768882039741742401 48398134326661529806306801)
  ·
    refine ⟨36298600744996147354730101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48398134326661529806306801 36298600744996147354730101)
    ·
      refine ⟨3402993819843388814505947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36298600744996147354730101 3402993819843388814505947)
      ·
        refine ⟨5104490729765083221758921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402993819843388814505947 5104490729765083221758921)
        ·
          refine ⟨3828368047323812416319191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5104490729765083221758921 3828368047323812416319191)
          ·
            refine ⟨5742552070985718624478787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3828368047323812416319191 5742552070985718624478787)
            ·
              refine ⟨8613828106478577936718181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5742552070985718624478787 8613828106478577936718181)
              ·
                refine ⟨1615092769964733363134659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8613828106478577936718181 1615092769964733363134659)
                ·
                  refine ⟨2422639154947100044701989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615092769964733363134659 2422639154947100044701989)
                  ·
                    refine ⟨454244841552581258381623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2422639154947100044701989 454244841552581258381623)
                    ·
                      rfl

theorem cell23_2653916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2653916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653916 prefixEnd_2653916 := by exact prefixLift 2653916
  have htrace : WordTrace (prefixWord ++ tailWord_2653916) baseStart_2653916 baseEnd_2653916 := by
    simpa [prefixWord, tailWord_2653916, baseEnd_2653916] using wordTrace_append hprefix tailTrace_2653916
  have hstable : (prefixWord ++ tailWord_2653916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653916).length < 2 ^ (prefixWord ++ tailWord_2653916).sum := by decide
  have hdescent : baseEnd_2653916 < baseStart_2653916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653956 : List Nat := [2, 3, 2, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_2653956 : Nat := 118140960795 + 2653956 * 2 ^ 59
def prefixEnd_2653956 : Nat := 4983230072969 + 3 ^ 40 * 2653956 * 2
def baseEnd_2653956 : Nat := 1362755063883923618644685

theorem tailTrace_2653956 : CollatzResearch.WordTrace tailWord_2653956 prefixEnd_2653956 1362755063883923618644685 := by
  unfold tailWord_2653956
  simp only [CollatzResearch.WordTrace]
  refine ⟨48398863786589073222034861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64531818382118764296046481 48398863786589073222034861)
  ·
    refine ⟨18149573919970902458263073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48398863786589073222034861 18149573919970902458263073)
    ·
      refine ⟨13612180439978176843697305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18149573919970902458263073 13612180439978176843697305)
      ·
        refine ⟨10209135329983632632772979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13612180439978176843697305 10209135329983632632772979)
        ·
          refine ⟨15313702994975448949159469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10209135329983632632772979 15313702994975448949159469)
          ·
            refine ⟨5742638623115793355934801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15313702994975448949159469 5742638623115793355934801)
            ·
              refine ⟨4306978967336845016951101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5742638623115793355934801 4306978967336845016951101)
              ·
                refine ⟨1615117112751316881356663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4306978967336845016951101 1615117112751316881356663)
                ·
                  refine ⟨2422675669126975322034995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615117112751316881356663 2422675669126975322034995)
                  ·
                    refine ⟨3634013503690462983052493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2422675669126975322034995 3634013503690462983052493)
                    ·
                      refine ⟨1362755063883923618644685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3634013503690462983052493 1362755063883923618644685)
                      ·
                        rfl

theorem cell23_2653956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_2653956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653956 prefixEnd_2653956 := by exact prefixLift 2653956
  have htrace : WordTrace (prefixWord ++ tailWord_2653956) baseStart_2653956 baseEnd_2653956 := by
    simpa [prefixWord, tailWord_2653956, baseEnd_2653956] using wordTrace_append hprefix tailTrace_2653956
  have hstable : (prefixWord ++ tailWord_2653956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653956).length < 2 ^ (prefixWord ++ tailWord_2653956).sum := by decide
  have hdescent : baseEnd_2653956 < baseStart_2653956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653962 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_2653962 : Nat := 118140960795 + 2653962 * 2 ^ 59
def prefixEnd_2653962 : Nat := 4983230072969 + 3 ^ 40 * 2653962 * 2
def baseEnd_2653962 : Nat := 1362758144767850595169657

theorem tailTrace_2653962 : CollatzResearch.WordTrace tailWord_2653962 prefixEnd_2653962 1362758144767850595169657 := by
  unfold tailWord_2653962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24199486602789102367197035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64531964274104272979192093 24199486602789102367197035)
  ·
    refine ⟨36299229904183653550795553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24199486602789102367197035 36299229904183653550795553)
    ·
      refine ⟨27224422428137740163096665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36299229904183653550795553 27224422428137740163096665)
      ·
        refine ⟨20418316821103305122322499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27224422428137740163096665 20418316821103305122322499)
        ·
          refine ⟨30627475231654957683483749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20418316821103305122322499 30627475231654957683483749)
          ·
            refine ⟨5742651605935304565653203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30627475231654957683483749 5742651605935304565653203)
            ·
              refine ⟨8613977408902956848479805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5742651605935304565653203 8613977408902956848479805)
              ·
                refine ⟨3230241528338608818179927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8613977408902956848479805 3230241528338608818179927)
                ·
                  refine ⟨4845362292507913227269891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230241528338608818179927 4845362292507913227269891)
                  ·
                    refine ⟨7268043438761869840904837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4845362292507913227269891 7268043438761869840904837)
                    ·
                      refine ⟨1362758144767850595169657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7268043438761869840904837 1362758144767850595169657)
                      ·
                        rfl

theorem cell23_2653962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_2653962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653962 prefixEnd_2653962 := by exact prefixLift 2653962
  have htrace : WordTrace (prefixWord ++ tailWord_2653962) baseStart_2653962 baseEnd_2653962 := by
    simpa [prefixWord, tailWord_2653962, baseEnd_2653962] using wordTrace_append hprefix tailTrace_2653962
  have hstable : (prefixWord ++ tailWord_2653962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653962).length < 2 ^ (prefixWord ++ tailWord_2653962).sum := by decide
  have hdescent : baseEnd_2653962 < baseStart_2653962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653989 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 2, 4]
def baseStart_2653989 : Nat := 118140960795 + 2653989 * 2 ^ 59
def prefixEnd_2653989 : Nat := 4983230072969 + 3 ^ 40 * 2653989 * 2
def baseEnd_2653989 : Nat := 454257336248507329844011

theorem tailTrace_2653989 : CollatzResearch.WordTrace tailWord_2653989 prefixEnd_2653989 454257336248507329844011 := by
  unfold tailWord_2653989
  simp only [CollatzResearch.WordTrace]
  refine ⟨96798931182058593080021021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64532620788039062053347347 96798931182058593080021021)
  ·
    refine ⟨36299599193271972405007883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96798931182058593080021021 36299599193271972405007883)
    ·
      refine ⟨54449398789907958607511825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36299599193271972405007883 54449398789907958607511825)
      ·
        refine ⟨40837049092430968955633869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54449398789907958607511825 40837049092430968955633869)
        ·
          refine ⟨15313893409661613358362701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40837049092430968955633869 15313893409661613358362701)
          ·
            refine ⟨5742710028623105009386013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15313893409661613358362701 5742710028623105009386013)
            ·
              refine ⟨2153516260733664378519755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5742710028623105009386013 2153516260733664378519755)
              ·
                refine ⟨3230274391100496567779633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153516260733664378519755 3230274391100496567779633)
                ·
                  refine ⟨2422705793325372425834725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3230274391100496567779633 2422705793325372425834725)
                  ·
                    refine ⟨454257336248507329844011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2422705793325372425834725 454257336248507329844011)
                    ·
                      rfl

theorem cell23_2653989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_2653989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653989 prefixEnd_2653989 := by exact prefixLift 2653989
  have htrace : WordTrace (prefixWord ++ tailWord_2653989) baseStart_2653989 baseEnd_2653989 := by
    simpa [prefixWord, tailWord_2653989, baseEnd_2653989] using wordTrace_append hprefix tailTrace_2653989
  have hstable : (prefixWord ++ tailWord_2653989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653989).length < 2 ^ (prefixWord ++ tailWord_2653989).sum := by decide
  have hdescent : baseEnd_2653989 < baseStart_2653989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653992 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2653992 : Nat := 118140960795 + 2653992 * 2 ^ 59
def prefixEnd_2653992 : Nat := 4983230072969 + 3 ^ 40 * 2653992 * 2
def baseEnd_2653992 : Nat := 1362773549187485477794519

theorem tailTrace_2653992 : CollatzResearch.WordTrace tailWord_2653992 prefixEnd_2653992 1362773549187485477794519 := by
  unfold tailWord_2653992
  simp only [CollatzResearch.WordTrace]
  refine ⟨48399520300523862296190115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64532693734031816394920153 48399520300523862296190115)
  ·
    refine ⟨72599280450785793444285173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48399520300523862296190115 72599280450785793444285173)
    ·
      refine ⟨6806182542261168135401735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72599280450785793444285173 6806182542261168135401735)
      ·
        refine ⟨10209273813391752203102603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6806182542261168135401735 10209273813391752203102603)
        ·
          refine ⟨15313910720087628304653905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10209273813391752203102603 15313910720087628304653905)
          ·
            refine ⟨11485433040065721228490429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15313910720087628304653905 11485433040065721228490429)
            ·
              refine ⟨4307037390024645460683911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11485433040065721228490429 4307037390024645460683911)
              ·
                refine ⟨6460556085036968191025867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4307037390024645460683911 6460556085036968191025867)
                ·
                  refine ⟨9690834127555452286538801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6460556085036968191025867 9690834127555452286538801)
                  ·
                    refine ⟨7268125595666589214904101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9690834127555452286538801 7268125595666589214904101)
                    ·
                      refine ⟨1362773549187485477794519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7268125595666589214904101 1362773549187485477794519)
                      ·
                        rfl

theorem cell23_2653992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2653992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2653992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2653992 prefixEnd_2653992 := by exact prefixLift 2653992
  have htrace : WordTrace (prefixWord ++ tailWord_2653992) baseStart_2653992 baseEnd_2653992 := by
    simpa [prefixWord, tailWord_2653992, baseEnd_2653992] using wordTrace_append hprefix tailTrace_2653992
  have hstable : (prefixWord ++ tailWord_2653992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653992).length < 2 ^ (prefixWord ++ tailWord_2653992).sum := by decide
  have hdescent : baseEnd_2653992 < baseStart_2653992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654002 : List Nat := [3, 2, 1, 1, 3, 4, 2, 7]
def baseStart_2654002 : Nat := 118140960795 + 2654002 * 2 ^ 59
def prefixEnd_2654002 : Nat := 4983230072969 + 3 ^ 40 * 2654002 * 2
def baseEnd_2654002 : Nat := 50473284592371497728499

theorem tailTrace_2654002 : CollatzResearch.WordTrace tailWord_2654002 prefixEnd_2654002 50473284592371497728499 := by
  unfold tailWord_2654002
  simp only [CollatzResearch.WordTrace]
  refine ⟨24199851332752874075061065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64532936887340997533496173 24199851332752874075061065)
  ·
    refine ⟨18149888499564655556295799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24199851332752874075061065 18149888499564655556295799)
    ·
      refine ⟨27224832749346983334443699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18149888499564655556295799 27224832749346983334443699)
      ·
        refine ⟨40837249124020475001665549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27224832749346983334443699 40837249124020475001665549)
        ·
          refine ⟨15313968421507678125624581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40837249124020475001665549 15313968421507678125624581)
          ·
            refine ⟨2871369079032689648554609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15313968421507678125624581 2871369079032689648554609)
            ·
              refine ⟨2153526809274517236415957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2871369079032689648554609 2153526809274517236415957)
              ·
                refine ⟨50473284592371497728499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2153526809274517236415957 50473284592371497728499)
                ·
                  rfl

theorem cell23_2654002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 7].length) (baseStart_2654002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654002 prefixEnd_2654002 := by exact prefixLift 2654002
  have htrace : WordTrace (prefixWord ++ tailWord_2654002) baseStart_2654002 baseEnd_2654002 := by
    simpa [prefixWord, tailWord_2654002, baseEnd_2654002] using wordTrace_append hprefix tailTrace_2654002
  have hstable : (prefixWord ++ tailWord_2654002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654002).length < 2 ^ (prefixWord ++ tailWord_2654002).sum := by decide
  have hdescent : baseEnd_2654002 < baseStart_2654002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654012 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_2654012 : Nat := 118140960795 + 2654012 * 2 ^ 59
def prefixEnd_2654012 : Nat := 4983230072969 + 3 ^ 40 * 2654012 * 2
def baseEnd_2654012 : Nat := 1362783818800575399544427

theorem tailTrace_2654012 : CollatzResearch.WordTrace tailWord_2654012 prefixEnd_2654012 1362783818800575399544427 := by
  unfold tailWord_2654012
  simp only [CollatzResearch.WordTrace]
  refine ⟨48399885030487634004054145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64533180040650178672072193 48399885030487634004054145)
  ·
    refine ⟨36299913772865725503040609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48399885030487634004054145 36299913772865725503040609)
    ·
      refine ⟨27224935329649294127280457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36299913772865725503040609 27224935329649294127280457)
      ·
        refine ⟨20418701497236970595460343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27224935329649294127280457 20418701497236970595460343)
        ·
          refine ⟨30628052245855455893190515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20418701497236970595460343 30628052245855455893190515)
          ·
            refine ⟨45942078368783183839785773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30628052245855455893190515 45942078368783183839785773)
            ·
              refine ⟨17228279388293693939919665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45942078368783183839785773 17228279388293693939919665)
              ·
                refine ⟨12921209541220270454939749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17228279388293693939919665 12921209541220270454939749)
                ·
                  refine ⟨2422726788978800710301203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12921209541220270454939749 2422726788978800710301203)
                  ·
                    refine ⟨3634090183468201065451805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2422726788978800710301203 3634090183468201065451805)
                    ·
                      refine ⟨1362783818800575399544427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3634090183468201065451805 1362783818800575399544427)
                      ·
                        rfl

theorem cell23_2654012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_2654012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654012 prefixEnd_2654012 := by exact prefixLift 2654012
  have htrace : WordTrace (prefixWord ++ tailWord_2654012) baseStart_2654012 baseEnd_2654012 := by
    simpa [prefixWord, tailWord_2654012, baseEnd_2654012] using wordTrace_append hprefix tailTrace_2654012
  have hstable : (prefixWord ++ tailWord_2654012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654012).length < 2 ^ (prefixWord ++ tailWord_2654012).sum := by decide
  have hdescent : baseEnd_2654012 < baseStart_2654012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654013 : List Nat := [1, 4, 1, 4, 1, 1, 3, 3, 1, 2, 2]
def baseStart_2654013 : Nat := 118140960795 + 2654013 * 2 ^ 59
def prefixEnd_2654013 : Nat := 4983230072969 + 3 ^ 40 * 2654013 * 2
def baseEnd_2654013 : Nat := 1362784332281229895631923

theorem tailTrace_2654013 : CollatzResearch.WordTrace tailWord_2654013 prefixEnd_2654013 1362784332281229895631923 := by
  unfold tailWord_2654013
  simp only [CollatzResearch.WordTrace]
  refine ⟨96799806533971645178894693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64533204355981096785929795 96799806533971645178894693)
  ·
    refine ⟨18149963725119683471042755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96799806533971645178894693 18149963725119683471042755)
    ·
      refine ⟨27224945587679525206564133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18149963725119683471042755 27224945587679525206564133)
      ·
        refine ⟨5104677297689910976230775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27224945587679525206564133 5104677297689910976230775)
        ·
          refine ⟨7657015946534866464346163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5104677297689910976230775 7657015946534866464346163)
          ·
            refine ⟨11485523919802299696519245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7657015946534866464346163 11485523919802299696519245)
            ·
              refine ⟨4307071469925862386194717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11485523919802299696519245 4307071469925862386194717)
              ·
                refine ⟨1615151801222198394823019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4307071469925862386194717 1615151801222198394823019)
                ·
                  refine ⟨2422727701833297592234529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615151801222198394823019 2422727701833297592234529)
                  ·
                    refine ⟨1817045776374973194175897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2422727701833297592234529 1817045776374973194175897)
                    ·
                      refine ⟨1362784332281229895631923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817045776374973194175897 1362784332281229895631923)
                      ·
                        rfl

theorem cell23_2654013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_2654013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654013 prefixEnd_2654013 := by exact prefixLift 2654013
  have htrace : WordTrace (prefixWord ++ tailWord_2654013) baseStart_2654013 baseEnd_2654013 := by
    simpa [prefixWord, tailWord_2654013, baseEnd_2654013] using wordTrace_append hprefix tailTrace_2654013
  have hstable : (prefixWord ++ tailWord_2654013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654013).length < 2 ^ (prefixWord ++ tailWord_2654013).sum := by decide
  have hdescent : baseEnd_2654013 < baseStart_2654013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654055 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2654055 : Nat := 118140960795 + 2654055 * 2 ^ 59
def prefixEnd_2654055 : Nat := 4983230072969 + 3 ^ 40 * 2654055 * 2
def baseEnd_2654055 : Nat := 1362805898468718731306729

theorem tailTrace_2654055 : CollatzResearch.WordTrace tailWord_2654055 prefixEnd_2654055 1362805898468718731306729 := by
  unfold tailWord_2654055
  simp only [CollatzResearch.WordTrace]
  refine ⟨96801338399819486351923619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64534225599879657567949079 96801338399819486351923619)
  ·
    refine ⟨145202007599729229527885429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96801338399819486351923619 145202007599729229527885429)
    ·
      refine ⟨13612688212474615268239259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145202007599729229527885429 13612688212474615268239259)
      ·
        refine ⟨20419032318711922902358889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13612688212474615268239259 20419032318711922902358889)
        ·
          refine ⟨15314274239033942176769167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20419032318711922902358889 15314274239033942176769167)
          ·
            refine ⟨22971411358550913265153751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15314274239033942176769167 22971411358550913265153751)
            ·
              refine ⟨34457117037826369897730627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22971411358550913265153751 34457117037826369897730627)
              ·
                refine ⟨51685675556739554846595941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34457117037826369897730627 51685675556739554846595941)
                ·
                  refine ⟨9691064166888666533736739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51685675556739554846595941 9691064166888666533736739)
                  ·
                    refine ⟨14536596250332999800605109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9691064166888666533736739 14536596250332999800605109)
                    ·
                      refine ⟨1362805898468718731306729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14536596250332999800605109 1362805898468718731306729)
                      ·
                        rfl

theorem cell23_2654055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2654055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654055 prefixEnd_2654055 := by exact prefixLift 2654055
  have htrace : WordTrace (prefixWord ++ tailWord_2654055) baseStart_2654055 baseEnd_2654055 := by
    simpa [prefixWord, tailWord_2654055, baseEnd_2654055] using wordTrace_append hprefix tailTrace_2654055
  have hstable : (prefixWord ++ tailWord_2654055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654055).length < 2 ^ (prefixWord ++ tailWord_2654055).sum := by decide
  have hdescent : baseEnd_2654055 < baseStart_2654055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654069 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_2654069 : Nat := 118140960795 + 2654069 * 2 ^ 59
def prefixEnd_2654069 : Nat := 4983230072969 + 3 ^ 40 * 2654069 * 2
def baseEnd_2654069 : Nat := 1362813087197881676531665

theorem tailTrace_2654069 : CollatzResearch.WordTrace tailWord_2654069 prefixEnd_2654069 1362813087197881676531665 := by
  unfold tailWord_2654069
  simp only [CollatzResearch.WordTrace]
  refine ⟨96801849021768766742933261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64534566014512511161955507 96801849021768766742933261)
  ·
    refine ⟨36300693383163287528599973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96801849021768766742933261 36300693383163287528599973)
    ·
      refine ⟨6806380009343116411612495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36300693383163287528599973 6806380009343116411612495)
      ·
        refine ⟨10209570014014674617418743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6806380009343116411612495 10209570014014674617418743)
        ·
          refine ⟨15314355021022011926128115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10209570014014674617418743 15314355021022011926128115)
          ·
            refine ⟨22971532531533017889192173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15314355021022011926128115 22971532531533017889192173)
            ·
              refine ⟨8614324699324881708447065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22971532531533017889192173 8614324699324881708447065)
              ·
                refine ⟨6460743524493661281335299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8614324699324881708447065 6460743524493661281335299)
                ·
                  refine ⟨9691115286740491922002949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6460743524493661281335299 9691115286740491922002949)
                  ·
                    refine ⟨1817084116263842235375553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9691115286740491922002949 1817084116263842235375553)
                    ·
                      refine ⟨1362813087197881676531665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817084116263842235375553 1362813087197881676531665)
                      ·
                        rfl

theorem cell23_2654069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_2654069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654069 prefixEnd_2654069 := by exact prefixLift 2654069
  have htrace : WordTrace (prefixWord ++ tailWord_2654069) baseStart_2654069 baseEnd_2654069 := by
    simpa [prefixWord, tailWord_2654069, baseEnd_2654069] using wordTrace_append hprefix tailTrace_2654069
  have hstable : (prefixWord ++ tailWord_2654069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654069).length < 2 ^ (prefixWord ++ tailWord_2654069).sum := by decide
  have hdescent : baseEnd_2654069 < baseStart_2654069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654105 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 4, 5]
def baseStart_2654105 : Nat := 118140960795 + 2654105 * 2 ^ 59
def prefixEnd_2654105 : Nat := 4983230072969 + 3 ^ 40 * 2654105 * 2
def baseEnd_2654105 : Nat := 454277190833814511893833

theorem tailTrace_2654105 : CollatzResearch.WordTrace tailWord_2654105 prefixEnd_2654105 454277190833814511893833 := by
  unfold tailWord_2654105
  simp only [CollatzResearch.WordTrace]
  refine ⟨96803162049638344891243769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64535441366425563260829179 96803162049638344891243769)
  ·
    refine ⟨72602371537228758668432827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96803162049638344891243769 72602371537228758668432827)
    ·
      refine ⟨108903557305843138002649241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72602371537228758668432827 108903557305843138002649241)
      ·
        refine ⟨81677667979382353501986931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108903557305843138002649241 81677667979382353501986931)
        ·
          refine ⟨122516501969073530252980397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81677667979382353501986931 122516501969073530252980397)
          ·
            refine ⟨45943688238402573844867649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122516501969073530252980397 45943688238402573844867649)
            ·
              refine ⟨34457766178801930383650737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45943688238402573844867649 34457766178801930383650737)
              ·
                refine ⟨25843324634101447787738053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34457766178801930383650737 25843324634101447787738053)
                ·
                  refine ⟨4845623368894021460200885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25843324634101447787738053 4845623368894021460200885)
                  ·
                    refine ⟨454277190833814511893833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4845623368894021460200885 454277190833814511893833)
                    ·
                      rfl

theorem cell23_2654105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_2654105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654105 prefixEnd_2654105 := by exact prefixLift 2654105
  have htrace : WordTrace (prefixWord ++ tailWord_2654105) baseStart_2654105 baseEnd_2654105 := by
    simpa [prefixWord, tailWord_2654105, baseEnd_2654105] using wordTrace_append hprefix tailTrace_2654105
  have hstable : (prefixWord ++ tailWord_2654105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654105).length < 2 ^ (prefixWord ++ tailWord_2654105).sum := by decide
  have hdescent : baseEnd_2654105 < baseStart_2654105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654112 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 4, 5, 2]
def baseStart_2654112 : Nat := 118140960795 + 2654112 * 2 ^ 59
def prefixEnd_2654112 : Nat := 4983230072969 + 3 ^ 40 * 2654112 * 2
def baseEnd_2654112 : Nat := 1362835166866025008293967

theorem tailTrace_2654112 : CollatzResearch.WordTrace tailWord_2654112 prefixEnd_2654112 1362835166866025008293967 := by
  unfold tailWord_2654112
  simp only [CollatzResearch.WordTrace]
  refine ⟨48401708680306492543374295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64535611573741990057832393 48401708680306492543374295)
  ·
    refine ⟨72602563020459738815061443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48401708680306492543374295 72602563020459738815061443)
    ·
      refine ⟨108903844530689608222592165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72602563020459738815061443 108903844530689608222592165)
      ·
        refine ⟨20419470849504301541736031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108903844530689608222592165 20419470849504301541736031)
        ·
          refine ⟨30629206274256452312604047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20419470849504301541736031 30629206274256452312604047)
          ·
            refine ⟨45943809411384678468906071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30629206274256452312604047 45943809411384678468906071)
            ·
              refine ⟨68915714117077017703359107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45943809411384678468906071 68915714117077017703359107)
              ·
                refine ⟨103373571175615526555038661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68915714117077017703359107 103373571175615526555038661)
                ·
                  refine ⟨19382544595427911229069749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103373571175615526555038661 19382544595427911229069749)
                  ·
                    refine ⟨1817113555821366677725289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19382544595427911229069749 1817113555821366677725289)
                    ·
                      refine ⟨1362835166866025008293967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817113555821366677725289 1362835166866025008293967)
                      ·
                        rfl

theorem cell23_2654112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_2654112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654112 prefixEnd_2654112 := by exact prefixLift 2654112
  have htrace : WordTrace (prefixWord ++ tailWord_2654112) baseStart_2654112 baseEnd_2654112 := by
    simpa [prefixWord, tailWord_2654112, baseEnd_2654112] using wordTrace_append hprefix tailTrace_2654112
  have hstable : (prefixWord ++ tailWord_2654112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654112).length < 2 ^ (prefixWord ++ tailWord_2654112).sum := by decide
  have hdescent : baseEnd_2654112 < baseStart_2654112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654155 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 6]
def baseStart_2654155 : Nat := 118140960795 + 2654155 * 2 ^ 59
def prefixEnd_2654155 : Nat := 4983230072969 + 3 ^ 40 * 2654155 * 2
def baseEnd_2654155 : Nat := 1362857246534168340056269

theorem tailTrace_2654155 : CollatzResearch.WordTrace tailWord_2654155 prefixEnd_2654155 1362857246534168340056269 := by
  unfold tailWord_2654155
  simp only [CollatzResearch.WordTrace]
  refine ⟨96804985699457203430563919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64536657132971468953709279 96804985699457203430563919)
  ·
    refine ⟨145207478549185805145845879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96804985699457203430563919 145207478549185805145845879)
    ·
      refine ⟨217811217823778707718768819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145207478549185805145845879 217811217823778707718768819)
      ·
        refine ⟨326716826735668061578153229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217811217823778707718768819 326716826735668061578153229)
        ·
          refine ⟨122518810025875523091807461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326716826735668061578153229 122518810025875523091807461)
          ·
            refine ⟨22972276879851660579713899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122518810025875523091807461 22972276879851660579713899)
            ·
              refine ⟨34458415319777490869570849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22972276879851660579713899 34458415319777490869570849)
              ·
                refine ⟨25843811489833118152178137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34458415319777490869570849 25843811489833118152178137)
                ·
                  refine ⟨19382858617374838614133603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25843811489833118152178137 19382858617374838614133603)
                  ·
                    refine ⟨29074287926062257921200405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19382858617374838614133603 29074287926062257921200405)
                    ·
                      refine ⟨1362857246534168340056269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29074287926062257921200405 1362857246534168340056269)
                      ·
                        rfl

theorem cell23_2654155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_2654155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654155 prefixEnd_2654155 := by exact prefixLift 2654155
  have htrace : WordTrace (prefixWord ++ tailWord_2654155) baseStart_2654155 baseEnd_2654155 := by
    simpa [prefixWord, tailWord_2654155, baseEnd_2654155] using wordTrace_append hprefix tailTrace_2654155
  have hstable : (prefixWord ++ tailWord_2654155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654155).length < 2 ^ (prefixWord ++ tailWord_2654155).sum := by decide
  have hdescent : baseEnd_2654155 < baseStart_2654155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654219 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 4, 3, 2]
def baseStart_2654219 : Nat := 118140960795 + 2654219 * 2 ^ 59
def prefixEnd_2654219 : Nat := 4983230072969 + 3 ^ 40 * 2654219 * 2
def baseEnd_2654219 : Nat := 1362890109296056089655975

theorem tailTrace_2654219 : CollatzResearch.WordTrace tailWord_2654219 prefixEnd_2654219 1362890109296056089655975 := by
  unfold tailWord_2654219
  simp only [CollatzResearch.WordTrace]
  refine ⟨96807319971225342360893711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64538213314150228240595807 96807319971225342360893711)
  ·
    refine ⟨145210979956838013541340567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96807319971225342360893711 145210979956838013541340567)
    ·
      refine ⟨217816469935257020312010851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145210979956838013541340567 217816469935257020312010851)
      ·
        refine ⟨326724704902885530468016277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217816469935257020312010851 326724704902885530468016277)
        ·
          refine ⟨15315220542322759240688263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 326724704902885530468016277 15315220542322759240688263)
          ·
            refine ⟨22972830813484138861032395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15315220542322759240688263 22972830813484138861032395)
            ·
              refine ⟨34459246220226208291548593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22972830813484138861032395 34459246220226208291548593)
              ·
                refine ⟨25844434665169656218661445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34459246220226208291548593 25844434665169656218661445)
                ·
                  refine ⟨4845831499719310540999021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25844434665169656218661445 4845831499719310540999021)
                  ·
                    refine ⟨1817186812394741452874633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4845831499719310540999021 1817186812394741452874633)
                    ·
                      refine ⟨1362890109296056089655975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817186812394741452874633 1362890109296056089655975)
                      ·
                        rfl

theorem cell23_2654219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 3, 2].length) (baseStart_2654219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654219 prefixEnd_2654219 := by exact prefixLift 2654219
  have htrace : WordTrace (prefixWord ++ tailWord_2654219) baseStart_2654219 baseEnd_2654219 := by
    simpa [prefixWord, tailWord_2654219, baseEnd_2654219] using wordTrace_append hprefix tailTrace_2654219
  have hstable : (prefixWord ++ tailWord_2654219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654219).length < 2 ^ (prefixWord ++ tailWord_2654219).sum := by decide
  have hdescent : baseEnd_2654219 < baseStart_2654219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654229 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 3, 5]
def baseStart_2654229 : Nat := 118140960795 + 2654229 * 2 ^ 59
def prefixEnd_2654229 : Nat := 4983230072969 + 3 ^ 40 * 2654229 * 2
def baseEnd_2654229 : Nat := 454298414700867016843643

theorem tailTrace_2654229 : CollatzResearch.WordTrace tailWord_2654229 prefixEnd_2654229 454298414700867016843643 := by
  unfold tailWord_2654229
  simp only [CollatzResearch.WordTrace]
  refine ⟨96807684701189114068757741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64538456467459409379171827 96807684701189114068757741)
  ·
    refine ⟨36302881762945917775784153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96807684701189114068757741 36302881762945917775784153)
    ·
      refine ⟨27227161322209438331838115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36302881762945917775784153 27227161322209438331838115)
      ·
        refine ⟨40840741983314157497757173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27227161322209438331838115 40840741983314157497757173)
        ·
          refine ⟨3828819560935702265414735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40840741983314157497757173 3828819560935702265414735)
          ·
            refine ⟨5743229341403553398122103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3828819560935702265414735 5743229341403553398122103)
            ·
              refine ⟨8614844012105330097183155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5743229341403553398122103 8614844012105330097183155)
              ·
                refine ⟨12922266018157995145774733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8614844012105330097183155 12922266018157995145774733)
                ·
                  refine ⟨4845849756809248179665525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12922266018157995145774733 4845849756809248179665525)
                  ·
                    refine ⟨454298414700867016843643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4845849756809248179665525 454298414700867016843643)
                    ·
                      rfl

theorem cell23_2654229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_2654229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654229 prefixEnd_2654229 := by exact prefixLift 2654229
  have htrace : WordTrace (prefixWord ++ tailWord_2654229) baseStart_2654229 baseEnd_2654229 := by
    simpa [prefixWord, tailWord_2654229, baseEnd_2654229] using wordTrace_append hprefix tailTrace_2654229
  have hstable : (prefixWord ++ tailWord_2654229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654229).length < 2 ^ (prefixWord ++ tailWord_2654229).sum := by decide
  have hdescent : baseEnd_2654229 < baseStart_2654229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654236 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_2654236 : Nat := 118140960795 + 2654236 * 2 ^ 59
def prefixEnd_2654236 : Nat := 4983230072969 + 3 ^ 40 * 2654236 * 2
def baseEnd_2654236 : Nat := 1362898838467182523143397

theorem tailTrace_2654236 : CollatzResearch.WordTrace tailWord_2654236 prefixEnd_2654236 1362898838467182523143397 := by
  unfold tailWord_2654236
  simp only [CollatzResearch.WordTrace]
  refine ⟨48403970006081877132131281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64538626674775836176175041 48403970006081877132131281)
  ·
    refine ⟨36302977504561407849098461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48403970006081877132131281 36302977504561407849098461)
    ·
      refine ⟨13613616564210527943411923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36302977504561407849098461 13613616564210527943411923)
      ·
        refine ⟨20420424846315791915117885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13613616564210527943411923 20420424846315791915117885)
        ·
          refine ⟨7657659317368421968169207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20420424846315791915117885 7657659317368421968169207)
          ·
            refine ⟨11486488976052632952253811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7657659317368421968169207 11486488976052632952253811)
            ·
              refine ⟨17229733464078949428380717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11486488976052632952253811 17229733464078949428380717)
              ·
                refine ⟨6461150049029606035642769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17229733464078949428380717 6461150049029606035642769)
                ·
                  refine ⟨4845862536772204526732077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6461150049029606035642769 4845862536772204526732077)
                  ·
                    refine ⟨1817198451289576697524529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4845862536772204526732077 1817198451289576697524529)
                    ·
                      refine ⟨1362898838467182523143397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817198451289576697524529 1362898838467182523143397)
                      ·
                        rfl

theorem cell23_2654236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_2654236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654236 prefixEnd_2654236 := by exact prefixLift 2654236
  have htrace : WordTrace (prefixWord ++ tailWord_2654236) baseStart_2654236 baseEnd_2654236 := by
    simpa [prefixWord, tailWord_2654236, baseEnd_2654236] using wordTrace_append hprefix tailTrace_2654236
  have hstable : (prefixWord ++ tailWord_2654236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654236).length < 2 ^ (prefixWord ++ tailWord_2654236).sum := by decide
  have hdescent : baseEnd_2654236 < baseStart_2654236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654252 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_2654252 : Nat := 118140960795 + 2654252 * 2 ^ 59
def prefixEnd_2654252 : Nat := 4983230072969 + 3 ^ 40 * 2654252 * 2
def baseEnd_2654252 : Nat := 1362907054157654460543323

theorem tailTrace_2654252 : CollatzResearch.WordTrace tailWord_2654252 prefixEnd_2654252 1362907054157654460543323 := by
  unfold tailWord_2654252
  simp only [CollatzResearch.WordTrace]
  refine ⟨48404261790052894498422505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64539015720070525997896673 48404261790052894498422505)
  ·
    refine ⟨36303196342539670873816879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48404261790052894498422505 36303196342539670873816879)
    ·
      refine ⟨54454794513809506310725319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36303196342539670873816879 54454794513809506310725319)
      ·
        refine ⟨81682191770714259466087979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54454794513809506310725319 81682191770714259466087979)
        ·
          refine ⟨122523287656071389199131969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81682191770714259466087979 122523287656071389199131969)
          ·
            refine ⟨91892465742053541899348977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122523287656071389199131969 91892465742053541899348977)
            ·
              refine ⟨68919349306540156424511733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91892465742053541899348977 68919349306540156424511733)
              ·
                refine ⟨6461188997488139664797975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68919349306540156424511733 6461188997488139664797975)
                ·
                  refine ⟨9691783496232209497196963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6461188997488139664797975 9691783496232209497196963)
                  ·
                    refine ⟨14537675244348314245795445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9691783496232209497196963 14537675244348314245795445)
                    ·
                      refine ⟨1362907054157654460543323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14537675244348314245795445 1362907054157654460543323)
                      ·
                        rfl

theorem cell23_2654252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_2654252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654252 prefixEnd_2654252 := by exact prefixLift 2654252
  have htrace : WordTrace (prefixWord ++ tailWord_2654252) baseStart_2654252 baseEnd_2654252 := by
    simpa [prefixWord, tailWord_2654252, baseEnd_2654252] using wordTrace_append hprefix tailTrace_2654252
  have hstable : (prefixWord ++ tailWord_2654252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654252).length < 2 ^ (prefixWord ++ tailWord_2654252).sum := by decide
  have hdescent : baseEnd_2654252 < baseStart_2654252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654259 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 2, 4]
def baseStart_2654259 : Nat := 118140960795 + 2654259 * 2 ^ 59
def prefixEnd_2654259 : Nat := 4983230072969 + 3 ^ 40 * 2654259 * 2
def baseEnd_2654259 : Nat := 454303549507411977718597

theorem tailTrace_2654259 : CollatzResearch.WordTrace tailWord_2654259 prefixEnd_2654259 454303549507411977718597 := by
  unfold tailWord_2654259
  simp only [CollatzResearch.WordTrace]
  refine ⟨96808778891080429192349831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64539185927386952794899887 96808778891080429192349831)
  ·
    refine ⟨145213168336620643788524747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96808778891080429192349831 145213168336620643788524747)
    ·
      refine ⟨217819752504930965682787121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145213168336620643788524747 217819752504930965682787121)
      ·
        refine ⟨163364814378698224262090341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217819752504930965682787121 163364814378698224262090341)
        ·
          refine ⟨30630902696005917049141939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163364814378698224262090341 30630902696005917049141939)
          ·
            refine ⟨45946354044008875573712909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30630902696005917049141939 45946354044008875573712909)
            ·
              refine ⟨17229882766503328340142341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45946354044008875573712909 17229882766503328340142341)
              ·
                refine ⟨3230603018719374063776689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17229882766503328340142341 3230603018719374063776689)
                ·
                  refine ⟨2422952264039530547832517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3230603018719374063776689 2422952264039530547832517)
                  ·
                    refine ⟨454303549507411977718597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2422952264039530547832517 454303549507411977718597)
                    ·
                      rfl

theorem cell23_2654259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 4].length) (baseStart_2654259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654259 prefixEnd_2654259 := by exact prefixLift 2654259
  have htrace : WordTrace (prefixWord ++ tailWord_2654259) baseStart_2654259 baseEnd_2654259 := by
    simpa [prefixWord, tailWord_2654259, baseEnd_2654259] using wordTrace_append hprefix tailTrace_2654259
  have hstable : (prefixWord ++ tailWord_2654259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654259).length < 2 ^ (prefixWord ++ tailWord_2654259).sum := by decide
  have hdescent : baseEnd_2654259 < baseStart_2654259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654266 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2]
def baseStart_2654266 : Nat := 118140960795 + 2654266 * 2 ^ 59
def prefixEnd_2654266 : Nat := 4983230072969 + 3 ^ 40 * 2654266 * 2
def baseEnd_2654266 : Nat := 1362914242886817405768259

theorem tailTrace_2654266 : CollatzResearch.WordTrace tailWord_2654266 prefixEnd_2654266 1362914242886817405768259 := by
  unfold tailWord_2654266
  simp only [CollatzResearch.WordTrace]
  refine ⟨24202258550513767346963663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64539356134703379591903101 24202258550513767346963663)
  ·
    refine ⟨36303387825770651020445495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24202258550513767346963663 36303387825770651020445495)
    ·
      refine ⟨54455081738655976530668243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36303387825770651020445495 54455081738655976530668243)
      ·
        refine ⟨81682622607983964796002365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54455081738655976530668243 81682622607983964796002365)
        ·
          refine ⟨30630983477993986798500887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81682622607983964796002365 30630983477993986798500887)
          ·
            refine ⟨45946475216990980197751331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30630983477993986798500887 45946475216990980197751331)
            ·
              refine ⟨68919712825486470296626997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45946475216990980197751331 68919712825486470296626997)
              ·
                refine ⟨6461223077389356590308781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68919712825486470296626997 6461223077389356590308781)
                ·
                  refine ⟨2422958654021008721365793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6461223077389356590308781 2422958654021008721365793)
                  ·
                    refine ⟨1817218990515756541024345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2422958654021008721365793 1817218990515756541024345)
                    ·
                      refine ⟨1362914242886817405768259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817218990515756541024345 1362914242886817405768259)
                      ·
                        rfl

theorem cell23_2654266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2].length) (baseStart_2654266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654266 prefixEnd_2654266 := by exact prefixLift 2654266
  have htrace : WordTrace (prefixWord ++ tailWord_2654266) baseStart_2654266 baseEnd_2654266 := by
    simpa [prefixWord, tailWord_2654266, baseEnd_2654266] using wordTrace_append hprefix tailTrace_2654266
  have hstable : (prefixWord ++ tailWord_2654266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654266).length < 2 ^ (prefixWord ++ tailWord_2654266).sum := by decide
  have hdescent : baseEnd_2654266 < baseStart_2654266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654269 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2654269 : Nat := 118140960795 + 2654269 * 2 ^ 59
def prefixEnd_2654269 : Nat := 4983230072969 + 3 ^ 40 * 2654269 * 2
def baseEnd_2654269 : Nat := 1362915783328780894030745

theorem tailTrace_2654269 : CollatzResearch.WordTrace tailWord_2654269 prefixEnd_2654269 1362915783328780894030745 := by
  unfold tailWord_2654269
  simp only [CollatzResearch.WordTrace]
  refine ⟨96809143621044200900213861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64539429080696133933475907 96809143621044200900213861)
  ·
    refine ⟨18151714428945787668790099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96809143621044200900213861 18151714428945787668790099)
    ·
      refine ⟨27227571643418681503185149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18151714428945787668790099 27227571643418681503185149)
      ·
        refine ⟨10210339366282005563694431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27227571643418681503185149 10210339366282005563694431)
        ·
          refine ⟨15315509049423008345541647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10210339366282005563694431 15315509049423008345541647)
          ·
            refine ⟨22973263574134512518312471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15315509049423008345541647 22973263574134512518312471)
            ·
              refine ⟨34459895361201768777468707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22973263574134512518312471 34459895361201768777468707)
              ·
                refine ⟨51689843041802653166203061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34459895361201768777468707 51689843041802653166203061)
                ·
                  refine ⟨4845922785168998734331537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51689843041802653166203061 4845922785168998734331537)
                  ·
                    refine ⟨3634442088876749050748653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4845922785168998734331537 3634442088876749050748653)
                    ·
                      refine ⟨1362915783328780894030745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3634442088876749050748653 1362915783328780894030745)
                      ·
                        rfl

theorem cell23_2654269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2654269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654269 prefixEnd_2654269 := by exact prefixLift 2654269
  have htrace : WordTrace (prefixWord ++ tailWord_2654269) baseStart_2654269 baseEnd_2654269 := by
    simpa [prefixWord, tailWord_2654269, baseEnd_2654269] using wordTrace_append hprefix tailTrace_2654269
  have hstable : (prefixWord ++ tailWord_2654269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654269).length < 2 ^ (prefixWord ++ tailWord_2654269).sum := by decide
  have hdescent : baseEnd_2654269 < baseStart_2654269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654272 : List Nat := [2, 1, 1, 2, 2, 4, 3, 8]
def baseStart_2654272 : Nat := 118140960795 + 2654272 * 2 ^ 59
def prefixEnd_2654272 : Nat := 4983230072969 + 3 ^ 40 * 2654272 * 2
def baseEnd_2654272 : Nat := 50478419398916458603453

theorem tailTrace_2654272 : CollatzResearch.WordTrace tailWord_2654272 prefixEnd_2654272 50478419398916458603453 := by
  unfold tailWord_2654272
  simp only [CollatzResearch.WordTrace]
  refine ⟨48404626520016666206286535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64539502026688888275048713 48404626520016666206286535)
  ·
    refine ⟨72606939780024999309429803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48404626520016666206286535 72606939780024999309429803)
    ·
      refine ⟨108910409670037498964144705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72606939780024999309429803 108910409670037498964144705)
      ·
        refine ⟨81682807252528124223108529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108910409670037498964144705 81682807252528124223108529)
        ·
          refine ⟨61262105439396093167331397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81682807252528124223108529 61262105439396093167331397)
          ·
            refine ⟨11486644769886767468874637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61262105439396093167331397 11486644769886767468874637)
            ·
              refine ⟨4307491788707537800827989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11486644769886767468874637 4307491788707537800827989)
              ·
                refine ⟨50478419398916458603453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4307491788707537800827989 50478419398916458603453)
                ·
                  rfl

theorem cell23_2654272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 8].length) (baseStart_2654272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654272 prefixEnd_2654272 := by exact prefixLift 2654272
  have htrace : WordTrace (prefixWord ++ tailWord_2654272) baseStart_2654272 baseEnd_2654272 := by
    simpa [prefixWord, tailWord_2654272, baseEnd_2654272] using wordTrace_append hprefix tailTrace_2654272
  have hstable : (prefixWord ++ tailWord_2654272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654272).length < 2 ^ (prefixWord ++ tailWord_2654272).sum := by decide
  have hdescent : baseEnd_2654272 < baseStart_2654272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654279 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_2654279 : Nat := 118140960795 + 2654279 * 2 ^ 59
def prefixEnd_2654279 : Nat := 4983230072969 + 3 ^ 40 * 2654279 * 2
def baseEnd_2654279 : Nat := 1362920918135325854905699

theorem tailTrace_2654279 : CollatzResearch.WordTrace tailWord_2654279 prefixEnd_2654279 1362920918135325854905699 := by
  unfold tailWord_2654279
  simp only [CollatzResearch.WordTrace]
  refine ⟨96809508351007972608077891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64539672234005315072051927 96809508351007972608077891)
  ·
    refine ⟨145214262526511958912116837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96809508351007972608077891 145214262526511958912116837)
    ·
      refine ⟨27227674223720992296021907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145214262526511958912116837 27227674223720992296021907)
      ·
        refine ⟨40841511335581488444032861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27227674223720992296021907 40841511335581488444032861)
        ·
          refine ⟨15315566750843058166512323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40841511335581488444032861 15315566750843058166512323)
          ·
            refine ⟨22973350126264587249768485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15315566750843058166512323 22973350126264587249768485)
            ·
              refine ⟨4307503148674610109331591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22973350126264587249768485 4307503148674610109331591)
              ·
                refine ⟨6461254723011915163997387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4307503148674610109331591 6461254723011915163997387)
                ·
                  refine ⟨9691882084517872745996081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6461254723011915163997387 9691882084517872745996081)
                  ·
                    refine ⟨7268911563388404559497061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9691882084517872745996081 7268911563388404559497061)
                    ·
                      refine ⟨1362920918135325854905699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7268911563388404559497061 1362920918135325854905699)
                      ·
                        rfl

theorem cell23_2654279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_2654279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654279 prefixEnd_2654279 := by exact prefixLift 2654279
  have htrace : WordTrace (prefixWord ++ tailWord_2654279) baseStart_2654279 baseEnd_2654279 := by
    simpa [prefixWord, tailWord_2654279, baseEnd_2654279] using wordTrace_append hprefix tailTrace_2654279
  have hstable : (prefixWord ++ tailWord_2654279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654279).length < 2 ^ (prefixWord ++ tailWord_2654279).sum := by decide
  have hdescent : baseEnd_2654279 < baseStart_2654279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654300 : List Nat := [2, 2, 4, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_2654300 : Nat := 118140960795 + 2654300 * 2 ^ 59
def prefixEnd_2654300 : Nat := 4983230072969 + 3 ^ 40 * 2654300 * 2
def baseEnd_2654300 : Nat := 1362931701229070272743103

theorem tailTrace_2654300 : CollatzResearch.WordTrace tailWord_2654300 prefixEnd_2654300 1362931701229070272743103 := by
  unfold tailWord_2654300
  simp only [CollatzResearch.WordTrace]
  refine ⟨48405137141965946597296177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64540182855954595463061569 48405137141965946597296177)
  ·
    refine ⟨36303852856474459947972133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48405137141965946597296177 36303852856474459947972133)
    ·
      refine ⟨6806972410588961240244775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36303852856474459947972133 6806972410588961240244775)
      ·
        refine ⟨10210458615883441860367163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6806972410588961240244775 10210458615883441860367163)
        ·
          refine ⟨15315687923825162790550745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10210458615883441860367163 15315687923825162790550745)
          ·
            refine ⟨11486765942868872092913059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15315687923825162790550745 11486765942868872092913059)
            ·
              refine ⟨17230148914303308139369589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11486765942868872092913059 17230148914303308139369589)
              ·
                refine ⟨1615326460715935138065899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17230148914303308139369589 1615326460715935138065899)
                ·
                  refine ⟨2422989691073902707098849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615326460715935138065899 2422989691073902707098849)
                  ·
                    refine ⟨1817242268305427030324137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2422989691073902707098849 1817242268305427030324137)
                    ·
                      refine ⟨1362931701229070272743103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817242268305427030324137 1362931701229070272743103)
                      ·
                        rfl

theorem cell23_2654300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_2654300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654300 prefixEnd_2654300 := by exact prefixLift 2654300
  have htrace : WordTrace (prefixWord ++ tailWord_2654300) baseStart_2654300 baseEnd_2654300 := by
    simpa [prefixWord, tailWord_2654300, baseEnd_2654300] using wordTrace_append hprefix tailTrace_2654300
  have hstable : (prefixWord ++ tailWord_2654300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654300).length < 2 ^ (prefixWord ++ tailWord_2654300).sum := by decide
  have hdescent : baseEnd_2654300 < baseStart_2654300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654316 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 3]
def baseStart_2654316 : Nat := 118140960795 + 2654316 * 2 ^ 59
def prefixEnd_2654316 : Nat := 4983230072969 + 3 ^ 40 * 2654316 * 2
def baseEnd_2654316 : Nat := 1362939916919542210143029

theorem tailTrace_2654316 : CollatzResearch.WordTrace tailWord_2654316 prefixEnd_2654316 1362939916919542210143029 := by
  unfold tailWord_2654316
  simp only [CollatzResearch.WordTrace]
  refine ⟨48405428925936963963587401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64540571901249285284783201 48405428925936963963587401)
  ·
    refine ⟨36304071694452722972690551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48405428925936963963587401 36304071694452722972690551)
    ·
      refine ⟨54456107541679084459035827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36304071694452722972690551 54456107541679084459035827)
      ·
        refine ⟨81684161312518626688553741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54456107541679084459035827 81684161312518626688553741)
        ·
          refine ⟨30631560492194485008207653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81684161312518626688553741 30631560492194485008207653)
          ·
            refine ⟨5743417592286465939038935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30631560492194485008207653 5743417592286465939038935)
            ·
              refine ⟨8615126388429698908558403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5743417592286465939038935 8615126388429698908558403)
              ·
                refine ⟨12922689582644548362837605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8615126388429698908558403 12922689582644548362837605)
                ·
                  refine ⟨2423004296745852818032051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12922689582644548362837605 2423004296745852818032051)
                  ·
                    refine ⟨3634506445118779227048077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2423004296745852818032051 3634506445118779227048077)
                    ·
                      refine ⟨1362939916919542210143029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3634506445118779227048077 1362939916919542210143029)
                      ·
                        rfl

theorem cell23_2654316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_2654316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654316 prefixEnd_2654316 := by exact prefixLift 2654316
  have htrace : WordTrace (prefixWord ++ tailWord_2654316) baseStart_2654316 baseEnd_2654316 := by
    simpa [prefixWord, tailWord_2654316, baseEnd_2654316] using wordTrace_append hprefix tailTrace_2654316
  have hstable : (prefixWord ++ tailWord_2654316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654316).length < 2 ^ (prefixWord ++ tailWord_2654316).sum := by decide
  have hdescent : baseEnd_2654316 < baseStart_2654316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654373 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 2, 2, 2]
def baseStart_2654373 : Nat := 118140960795 + 2654373 * 2 ^ 59
def prefixEnd_2654373 : Nat := 4983230072969 + 3 ^ 40 * 2654373 * 2
def baseEnd_2654373 : Nat := 1362969185316848487130267

theorem tailTrace_2654373 : CollatzResearch.WordTrace tailWord_2654373 prefixEnd_2654373 1362969185316848487130267 := by
  unfold tailWord_2654373
  simp only [CollatzResearch.WordTrace]
  refine ⟨96812936812667426661999773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64541957875111617774666515 96812936812667426661999773)
  ·
    refine ⟨36304851304750284998249915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96812936812667426661999773 36304851304750284998249915)
    ·
      refine ⟨54457276957125427497374873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36304851304750284998249915 54457276957125427497374873)
      ·
        refine ⟨40842957717844070623031155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54457276957125427497374873 40842957717844070623031155)
        ·
          refine ⟨61264436576766105934546733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40842957717844070623031155 61264436576766105934546733)
          ·
            refine ⟨22974163716287289725455025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61264436576766105934546733 22974163716287289725455025)
            ·
              refine ⟨17230622787215467294091269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22974163716287289725455025 17230622787215467294091269)
              ·
                refine ⟨3230741772602900117642113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17230622787215467294091269 3230741772602900117642113)
                ·
                  refine ⟨2423056329452175088231585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3230741772602900117642113 2423056329452175088231585)
                  ·
                    refine ⟨1817292247089131316173689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2423056329452175088231585 1817292247089131316173689)
                    ·
                      refine ⟨1362969185316848487130267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817292247089131316173689 1362969185316848487130267)
                      ·
                        rfl

theorem cell23_2654373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_2654373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654373 prefixEnd_2654373 := by exact prefixLift 2654373
  have htrace : WordTrace (prefixWord ++ tailWord_2654373) baseStart_2654373 baseEnd_2654373 := by
    simpa [prefixWord, tailWord_2654373, baseEnd_2654373] using wordTrace_append hprefix tailTrace_2654373
  have hstable : (prefixWord ++ tailWord_2654373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654373).length < 2 ^ (prefixWord ++ tailWord_2654373).sum := by decide
  have hdescent : baseEnd_2654373 < baseStart_2654373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654473 : List Nat := [1, 2, 1, 1, 3, 4, 1, 5, 1, 4]
def baseStart_2654473 : Nat := 118140960795 + 2654473 * 2 ^ 59
def prefixEnd_2654473 : Nat := 4983230072969 + 3 ^ 40 * 2654473 * 2
def baseEnd_2654473 : Nat := 454340177794099365293269

theorem tailTrace_2654473 : CollatzResearch.WordTrace tailWord_2654473 prefixEnd_2654473 454340177794099365293269 := by
  unfold tailWord_2654473
  simp only [CollatzResearch.WordTrace]
  refine ⟨96816584112305143740640073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64544389408203429160426715 96816584112305143740640073)
  ·
    refine ⟨72612438084228857805480055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96816584112305143740640073 72612438084228857805480055)
    ·
      refine ⟨108918657126343286708220083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72612438084228857805480055 108918657126343286708220083)
      ·
        refine ⟨163377985689514930062330125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108918657126343286708220083 163377985689514930062330125)
        ·
          refine ⟨61266744633568098773373797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163377985689514930062330125 61266744633568098773373797)
          ·
            refine ⟨11487514618794018520007587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61266744633568098773373797 11487514618794018520007587)
            ·
              refine ⟨17231271928191027780011381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11487514618794018520007587 17231271928191027780011381)
              ·
                refine ⟨1615431743267908854376067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17231271928191027780011381 1615431743267908854376067)
                ·
                  refine ⟨2423147614901863281564101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615431743267908854376067 2423147614901863281564101)
                  ·
                    refine ⟨454340177794099365293269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2423147614901863281564101 454340177794099365293269)
                    ·
                      rfl

theorem cell23_2654473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 1, 4].length) (baseStart_2654473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654473 prefixEnd_2654473 := by exact prefixLift 2654473
  have htrace : WordTrace (prefixWord ++ tailWord_2654473) baseStart_2654473 baseEnd_2654473 := by
    simpa [prefixWord, tailWord_2654473, baseEnd_2654473] using wordTrace_append hprefix tailTrace_2654473
  have hstable : (prefixWord ++ tailWord_2654473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654473).length < 2 ^ (prefixWord ++ tailWord_2654473).sum := by decide
  have hdescent : baseEnd_2654473 < baseStart_2654473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654479 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 3]
def baseStart_2654479 : Nat := 118140960795 + 2654479 * 2 ^ 59
def prefixEnd_2654479 : Nat := 4983230072969 + 3 ^ 40 * 2654479 * 2
def baseEnd_2654479 : Nat := 1363023614266225072404779

theorem tailTrace_2654479 : CollatzResearch.WordTrace tailWord_2654479 prefixEnd_2654479 1363023614266225072404779 := by
  unfold tailWord_2654479
  simp only [CollatzResearch.WordTrace]
  refine ⟨96816802950283406765358491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64544535300188937843572327 96816802950283406765358491)
  ·
    refine ⟨145225204425425110148037737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96816802950283406765358491 145225204425425110148037737)
    ·
      refine ⟨108918903319068832611028303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145225204425425110148037737 108918903319068832611028303)
      ·
        refine ⟨163378354978603248916542455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108918903319068832611028303 163378354978603248916542455)
        ·
          refine ⟨245067532467904873374813683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163378354978603248916542455 245067532467904873374813683)
          ·
            refine ⟨367601298701857310062220525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245067532467904873374813683 367601298701857310062220525)
            ·
              refine ⟨137850487013196491273332697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 367601298701857310062220525 137850487013196491273332697)
              ·
                refine ⟨103387865259897368454999523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137850487013196491273332697 103387865259897368454999523)
                ·
                  refine ⟨155081797889846052682499285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103387865259897368454999523 155081797889846052682499285)
                  ·
                    refine ⟨3634729638043266859746077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 155081797889846052682499285 3634729638043266859746077)
                    ·
                      refine ⟨1363023614266225072404779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3634729638043266859746077 1363023614266225072404779)
                      ·
                        rfl

theorem cell23_2654479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 3].length) (baseStart_2654479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654479 prefixEnd_2654479 := by exact prefixLift 2654479
  have htrace : WordTrace (prefixWord ++ tailWord_2654479) baseStart_2654479 baseEnd_2654479 := by
    simpa [prefixWord, tailWord_2654479, baseEnd_2654479] using wordTrace_append hprefix tailTrace_2654479
  have hstable : (prefixWord ++ tailWord_2654479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654479).length < 2 ^ (prefixWord ++ tailWord_2654479).sum := by decide
  have hdescent : baseEnd_2654479 < baseStart_2654479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654519 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_2654519 : Nat := 118140960795 + 2654519 * 2 ^ 59
def prefixEnd_2654519 : Nat := 4983230072969 + 3 ^ 40 * 2654519 * 2
def baseEnd_2654519 : Nat := 1363044153492404915904595

theorem tailTrace_2654519 : CollatzResearch.WordTrace tailWord_2654519 prefixEnd_2654519 1363044153492404915904595 := by
  unfold tailWord_2654519
  simp only [CollatzResearch.WordTrace]
  refine ⟨96818261870138493596814611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64545507913425662397876407 96818261870138493596814611)
  ·
    refine ⟨145227392805207740395221917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96818261870138493596814611 145227392805207740395221917)
    ·
      refine ⟨54460272301952902648208219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145227392805207740395221917 54460272301952902648208219)
      ·
        refine ⟨81690408452929353972312329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54460272301952902648208219 81690408452929353972312329)
        ·
          refine ⟨61267806339697015479234247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81690408452929353972312329 61267806339697015479234247)
          ·
            refine ⟨91901709509545523218851371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61267806339697015479234247 91901709509545523218851371)
            ·
              refine ⟨137852564264318284828277057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91901709509545523218851371 137852564264318284828277057)
              ·
                refine ⟨103389423198238713621207793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137852564264318284828277057 103389423198238713621207793)
                ·
                  refine ⟨77542067398679035215905845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103389423198238713621207793 77542067398679035215905845)
                  ·
                    refine ⟨7269568818626159551491173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77542067398679035215905845 7269568818626159551491173)
                    ·
                      refine ⟨1363044153492404915904595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7269568818626159551491173 1363044153492404915904595)
                      ·
                        rfl

theorem cell23_2654519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_2654519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654519 prefixEnd_2654519 := by exact prefixLift 2654519
  have htrace : WordTrace (prefixWord ++ tailWord_2654519) baseStart_2654519 baseEnd_2654519 := by
    simpa [prefixWord, tailWord_2654519, baseEnd_2654519] using wordTrace_append hprefix tailTrace_2654519
  have hstable : (prefixWord ++ tailWord_2654519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654519).length < 2 ^ (prefixWord ++ tailWord_2654519).sum := by decide
  have hdescent : baseEnd_2654519 < baseStart_2654519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654559 : List Nat := [1, 1, 2, 3, 1, 2, 3, 10]
def baseStart_2654559 : Nat := 118140960795 + 2654559 * 2 ^ 59
def prefixEnd_2654559 : Nat := 4983230072969 + 3 ^ 40 * 2654559 * 2
def baseEnd_2654559 : Nat := 50483877508095731829793

theorem tailTrace_2654559 : CollatzResearch.WordTrace tailWord_2654559 prefixEnd_2654559 50483877508095731829793 := by
  unfold tailWord_2654559
  simp only [CollatzResearch.WordTrace]
  refine ⟨96819720789993580428270731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64546480526662386952180487 96819720789993580428270731)
  ·
    refine ⟨145229581184990370642406097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96819720789993580428270731 145229581184990370642406097)
    ·
      refine ⟨108922185888742777981804573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145229581184990370642406097 108922185888742777981804573)
      ·
        refine ⟨40845819708278541743176715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108922185888742777981804573 40845819708278541743176715)
        ·
          refine ⟨61268729562417812614765073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40845819708278541743176715 61268729562417812614765073)
          ·
            refine ⟨45951547171813359461073805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61268729562417812614765073 45951547171813359461073805)
            ·
              refine ⟨17231830189430009797902677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45951547171813359461073805 17231830189430009797902677)
              ·
                refine ⟨50483877508095731829793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17231830189430009797902677 50483877508095731829793)
                ·
                  rfl

theorem cell23_2654559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 10].length) (baseStart_2654559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654559 prefixEnd_2654559 := by exact prefixLift 2654559
  have htrace : WordTrace (prefixWord ++ tailWord_2654559) baseStart_2654559 baseEnd_2654559 := by
    simpa [prefixWord, tailWord_2654559, baseEnd_2654559] using wordTrace_append hprefix tailTrace_2654559
  have hstable : (prefixWord ++ tailWord_2654559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654559).length < 2 ^ (prefixWord ++ tailWord_2654559).sum := by decide
  have hdescent : baseEnd_2654559 < baseStart_2654559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654563 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 2, 4]
def baseStart_2654563 : Nat := 118140960795 + 2654563 * 2 ^ 59
def prefixEnd_2654563 : Nat := 4983230072969 + 3 ^ 40 * 2654563 * 2
def baseEnd_2654563 : Nat := 454355582213734247918131

theorem tailTrace_2654563 : CollatzResearch.WordTrace tailWord_2654563 prefixEnd_2654563 454355582213734247918131 := by
  unfold tailWord_2654563
  simp only [CollatzResearch.WordTrace]
  refine ⟨96819866681979089111416343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64546577787986059407610895 96819866681979089111416343)
  ·
    refine ⟨145229800022968633667124515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96819866681979089111416343 145229800022968633667124515)
    ·
      refine ⟨217844700034452950500686773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145229800022968633667124515 217844700034452950500686773)
      ·
        refine ⟨20422940628229964109439385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 217844700034452950500686773 20422940628229964109439385)
        ·
          refine ⟨15317205471172473082079539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20422940628229964109439385 15317205471172473082079539)
          ·
            refine ⟨22975808206758709623119309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15317205471172473082079539 22975808206758709623119309)
            ·
              refine ⟨8615928077534516108669741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22975808206758709623119309 8615928077534516108669741)
              ·
                refine ⟨3230973029075443540751153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8615928077534516108669741 3230973029075443540751153)
                ·
                  refine ⟨2423229771806582655563365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3230973029075443540751153 2423229771806582655563365)
                  ·
                    refine ⟨454355582213734247918131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2423229771806582655563365 454355582213734247918131)
                    ·
                      rfl

theorem cell23_2654563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 4].length) (baseStart_2654563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654563 prefixEnd_2654563 := by exact prefixLift 2654563
  have htrace : WordTrace (prefixWord ++ tailWord_2654563) baseStart_2654563 baseEnd_2654563 := by
    simpa [prefixWord, tailWord_2654563, baseEnd_2654563] using wordTrace_append hprefix tailTrace_2654563
  have hstable : (prefixWord ++ tailWord_2654563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654563).length < 2 ^ (prefixWord ++ tailWord_2654563).sum := by decide
  have hdescent : baseEnd_2654563 < baseStart_2654563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654570 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2654570 : Nat := 118140960795 + 2654570 * 2 ^ 59
def prefixEnd_2654570 : Nat := 4983230072969 + 3 ^ 40 * 2654570 * 2
def baseEnd_2654570 : Nat := 1363070341005784216366861

theorem tailTrace_2654570 : CollatzResearch.WordTrace tailWord_2654570 prefixEnd_2654570 1363070341005784216366861 := by
  unfold tailWord_2654570
  simp only [CollatzResearch.WordTrace]
  refine ⟨24205030498238432326730291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64546747995302486204614109 24205030498238432326730291)
  ·
    refine ⟨36307545747357648490095437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24205030498238432326730291 36307545747357648490095437)
    ·
      refine ⟨13615329655259118183785789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36307545747357648490095437 13615329655259118183785789)
      ·
        refine ⟨5105748620722169318919671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13615329655259118183785789 5105748620722169318919671)
        ·
          refine ⟨7658622931083253978379507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5105748620722169318919671 7658622931083253978379507)
          ·
            refine ⟨11487934396624880967569261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7658622931083253978379507 11487934396624880967569261)
            ·
              refine ⟨4307975398734330362838473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11487934396624880967569261 4307975398734330362838473)
              ·
                refine ⟨3230981549050747772128855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4307975398734330362838473 3230981549050747772128855)
                ·
                  refine ⟨4846472323576121658193283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230981549050747772128855 4846472323576121658193283)
                  ·
                    refine ⟨7269708485364182487289925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4846472323576121658193283 7269708485364182487289925)
                    ·
                      refine ⟨1363070341005784216366861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7269708485364182487289925 1363070341005784216366861)
                      ·
                        rfl

theorem cell23_2654570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2654570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654570 prefixEnd_2654570 := by exact prefixLift 2654570
  have htrace : WordTrace (prefixWord ++ tailWord_2654570) baseStart_2654570 baseEnd_2654570 := by
    simpa [prefixWord, tailWord_2654570, baseEnd_2654570] using wordTrace_append hprefix tailTrace_2654570
  have hstable : (prefixWord ++ tailWord_2654570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654570).length < 2 ^ (prefixWord ++ tailWord_2654570).sum := by decide
  have hdescent : baseEnd_2654570 < baseStart_2654570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654573 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_2654573 : Nat := 118140960795 + 2654573 * 2 ^ 59
def prefixEnd_2654573 : Nat := 4983230072969 + 3 ^ 40 * 2654573 * 2
def baseEnd_2654573 : Nat := 1363071881447747704629347

theorem tailTrace_2654573 : CollatzResearch.WordTrace tailWord_2654573 prefixEnd_2654573 1363071881447747704629347 := by
  unfold tailWord_2654573
  simp only [CollatzResearch.WordTrace]
  refine ⟨96820231411942860819280373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64546820941295240546186915 96820231411942860819280373)
  ·
    refine ⟨9076896694869643201807535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96820231411942860819280373 9076896694869643201807535)
    ·
      refine ⟨13615345042304464802711303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9076896694869643201807535 13615345042304464802711303)
      ·
        refine ⟨20423017563456697204066955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13615345042304464802711303 20423017563456697204066955)
        ·
          refine ⟨30634526345185045806100433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20423017563456697204066955 30634526345185045806100433)
          ·
            refine ⟨22975894758888784354575325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30634526345185045806100433 22975894758888784354575325)
            ·
              refine ⟨8615960534583294132965747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22975894758888784354575325 8615960534583294132965747)
              ·
                refine ⟨12923940801874941199448621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8615960534583294132965747 12923940801874941199448621)
                ·
                  refine ⟨4846477800703102949793233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12923940801874941199448621 4846477800703102949793233)
                  ·
                    refine ⟨3634858350527327212344925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4846477800703102949793233 3634858350527327212344925)
                    ·
                      refine ⟨1363071881447747704629347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3634858350527327212344925 1363071881447747704629347)
                      ·
                        rfl

theorem cell23_2654573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_2654573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654573 prefixEnd_2654573 := by exact prefixLift 2654573
  have htrace : WordTrace (prefixWord ++ tailWord_2654573) baseStart_2654573 baseEnd_2654573 := by
    simpa [prefixWord, tailWord_2654573, baseEnd_2654573] using wordTrace_append hprefix tailTrace_2654573
  have hstable : (prefixWord ++ tailWord_2654573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654573).length < 2 ^ (prefixWord ++ tailWord_2654573).sum := by decide
  have hdescent : baseEnd_2654573 < baseStart_2654573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654579 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 6]
def baseStart_2654579 : Nat := 118140960795 + 2654579 * 2 ^ 59
def prefixEnd_2654579 : Nat := 4983230072969 + 3 ^ 40 * 2654579 * 2
def baseEnd_2654579 : Nat := 1363074962331674681154319

theorem tailTrace_2654579 : CollatzResearch.WordTrace tailWord_2654579 prefixEnd_2654579 1363074962331674681154319 := by
  unfold tailWord_2654579
  simp only [CollatzResearch.WordTrace]
  refine ⟨96820450249921123843998791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64546966833280749229332527 96820450249921123843998791)
  ·
    refine ⟨145230675374881685765998187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96820450249921123843998791 145230675374881685765998187)
    ·
      refine ⟨217846013062322528648997281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145230675374881685765998187 217846013062322528648997281)
      ·
        refine ⟨163384509796741896486747961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217846013062322528648997281 163384509796741896486747961)
        ·
          refine ⟨122538382347556422365060971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163384509796741896486747961 122538382347556422365060971)
          ·
            refine ⟨183807573521334633547591457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122538382347556422365060971 183807573521334633547591457)
            ·
              refine ⟨137855680141000975160693593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183807573521334633547591457 137855680141000975160693593)
              ·
                refine ⟨103391760105750731370520195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137855680141000975160693593 103391760105750731370520195)
                ·
                  refine ⟨155087640158626097055780293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103391760105750731370520195 155087640158626097055780293)
                  ·
                    refine ⟨29078932529742393197958805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155087640158626097055780293 29078932529742393197958805)
                    ·
                      refine ⟨1363074962331674681154319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29078932529742393197958805 1363074962331674681154319)
                      ·
                        rfl

theorem cell23_2654579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_2654579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654579 prefixEnd_2654579 := by exact prefixLift 2654579
  have htrace : WordTrace (prefixWord ++ tailWord_2654579) baseStart_2654579 baseEnd_2654579 := by
    simpa [prefixWord, tailWord_2654579, baseEnd_2654579] using wordTrace_append hprefix tailTrace_2654579
  have hstable : (prefixWord ++ tailWord_2654579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654579).length < 2 ^ (prefixWord ++ tailWord_2654579).sum := by decide
  have hdescent : baseEnd_2654579 < baseStart_2654579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654604 : List Nat := [2, 2, 1, 2, 1, 4, 4, 2, 1, 2, 2]
def baseStart_2654604 : Nat := 118140960795 + 2654604 * 2 ^ 59
def prefixEnd_2654604 : Nat := 4983230072969 + 3 ^ 40 * 2654604 * 2
def baseEnd_2654604 : Nat := 1363087799348037083341705

theorem tailTrace_2654604 : CollatzResearch.WordTrace tailWord_2654604 prefixEnd_2654604 1363087799348037083341705 := by
  unfold tailWord_2654604
  simp only [CollatzResearch.WordTrace]
  refine ⟨48410681037415276556829433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64547574716553702075772577 48410681037415276556829433)
  ·
    refine ⟨36308010778061457417622075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48410681037415276556829433 36308010778061457417622075)
    ·
      refine ⟨54462016167092186126433113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36308010778061457417622075 54462016167092186126433113)
      ·
        refine ⟨40846512125319139594824835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54462016167092186126433113 40846512125319139594824835)
        ·
          refine ⟨61269768187978709392237253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40846512125319139594824835 61269768187978709392237253)
          ·
            refine ⟨11488081535246008011044485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61269768187978709392237253 11488081535246008011044485)
            ·
              refine ⟨2154015287858626502070841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11488081535246008011044485 2154015287858626502070841)
              ·
                refine ⟨1615511465893969876553131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2154015287858626502070841 1615511465893969876553131)
                ·
                  refine ⟨2423267198840954814829697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615511465893969876553131 2423267198840954814829697)
                  ·
                    refine ⟨1817450399130716111122273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2423267198840954814829697 1817450399130716111122273)
                    ·
                      refine ⟨1363087799348037083341705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817450399130716111122273 1363087799348037083341705)
                      ·
                        rfl

theorem cell23_2654604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_2654604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654604 prefixEnd_2654604 := by exact prefixLift 2654604
  have htrace : WordTrace (prefixWord ++ tailWord_2654604) baseStart_2654604 baseEnd_2654604 := by
    simpa [prefixWord, tailWord_2654604, baseEnd_2654604] using wordTrace_append hprefix tailTrace_2654604
  have hstable : (prefixWord ++ tailWord_2654604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654604).length < 2 ^ (prefixWord ++ tailWord_2654604).sum := by decide
  have hdescent : baseEnd_2654604 < baseStart_2654604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654614 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2654614 : Nat := 118140960795 + 2654614 * 2 ^ 59
def prefixEnd_2654614 : Nat := 4983230072969 + 3 ^ 40 * 2654614 * 2
def baseEnd_2654614 : Nat := 454364311384860681405553

theorem tailTrace_2654614 : CollatzResearch.WordTrace tailWord_2654614 prefixEnd_2654614 454364311384860681405553 := by
  unfold tailWord_2654614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6051357925299645301345181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64547817869862883214348597 6051357925299645301345181)
  ·
    refine ⟨2269259221987366988004443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6051357925299645301345181 2269259221987366988004443)
    ·
      refine ⟨3403888832981050482006665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269259221987366988004443 3403888832981050482006665)
      ·
        refine ⟨2552916624735787861504999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3403888832981050482006665 2552916624735787861504999)
        ·
          refine ⟨3829374937103681792257499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552916624735787861504999 3829374937103681792257499)
          ·
            refine ⟨5744062405655522688386249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829374937103681792257499 5744062405655522688386249)
            ·
              refine ⟨4308046804241642016289687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5744062405655522688386249 4308046804241642016289687)
              ·
                refine ⟨6462070206362463024434531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4308046804241642016289687 6462070206362463024434531)
                ·
                  refine ⟨9693105309543694536651797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6462070206362463024434531 9693105309543694536651797)
                  ·
                    refine ⟨454364311384860681405553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9693105309543694536651797 454364311384860681405553)
                    ·
                      rfl

theorem cell23_2654614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2654614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654614 prefixEnd_2654614 := by exact prefixLift 2654614
  have htrace : WordTrace (prefixWord ++ tailWord_2654614) baseStart_2654614 baseEnd_2654614 := by
    simpa [prefixWord, tailWord_2654614, baseEnd_2654614] using wordTrace_append hprefix tailTrace_2654614
  have hstable : (prefixWord ++ tailWord_2654614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654614).length < 2 ^ (prefixWord ++ tailWord_2654614).sum := by decide
  have hdescent : baseEnd_2654614 < baseStart_2654614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654647 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 1, 3, 2]
def baseStart_2654647 : Nat := 118140960795 + 2654647 * 2 ^ 59
def prefixEnd_2654647 : Nat := 4983230072969 + 3 ^ 40 * 2654647 * 2
def baseEnd_2654647 : Nat := 1363109879016180415104007

theorem tailTrace_2654647 : CollatzResearch.WordTrace tailWord_2654647 prefixEnd_2654647 1363109879016180415104007 := by
  unfold tailWord_2654647
  simp only [CollatzResearch.WordTrace]
  refine ⟨96822930413674771457474195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64548620275783180971649463 96822930413674771457474195)
  ·
    refine ⟨145234395620512157186211293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96822930413674771457474195 145234395620512157186211293)
    ·
      refine ⟨54462898357692058944829235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145234395620512157186211293 54462898357692058944829235)
      ·
        refine ⟨81694347536538088417243853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54462898357692058944829235 81694347536538088417243853)
        ·
          refine ⟨30635380326201783156466445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81694347536538088417243853 30635380326201783156466445)
          ·
            refine ⟨11488267622325668683674917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30635380326201783156466445 11488267622325668683674917)
            ·
              refine ⟨2154050179186062878189047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11488267622325668683674917 2154050179186062878189047)
              ·
                refine ⟨3231075268779094317283571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154050179186062878189047 3231075268779094317283571)
                ·
                  refine ⟨4846612903168641475925357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3231075268779094317283571 4846612903168641475925357)
                  ·
                    refine ⟨1817479838688240553472009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4846612903168641475925357 1817479838688240553472009)
                    ·
                      refine ⟨1363109879016180415104007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817479838688240553472009 1363109879016180415104007)
                      ·
                        rfl

theorem cell23_2654647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 3, 2].length) (baseStart_2654647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654647 prefixEnd_2654647 := by exact prefixLift 2654647
  have htrace : WordTrace (prefixWord ++ tailWord_2654647) baseStart_2654647 baseEnd_2654647 := by
    simpa [prefixWord, tailWord_2654647, baseEnd_2654647] using wordTrace_append hprefix tailTrace_2654647
  have hstable : (prefixWord ++ tailWord_2654647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654647).length < 2 ^ (prefixWord ++ tailWord_2654647).sum := by decide
  have hdescent : baseEnd_2654647 < baseStart_2654647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654677 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 1, 4, 2]
def baseStart_2654677 : Nat := 118140960795 + 2654677 * 2 ^ 59
def prefixEnd_2654677 : Nat := 4983230072969 + 3 ^ 40 * 2654677 * 2
def baseEnd_2654677 : Nat := 1363125283435815297728869

theorem tailTrace_2654677 : CollatzResearch.WordTrace tailWord_2654677 prefixEnd_2654677 1363125283435815297728869 := by
  unfold tailWord_2654677
  simp only [CollatzResearch.WordTrace]
  refine ⟨96824024603566086581066285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64549349735710724387377523 96824024603566086581066285)
  ·
    refine ⟨36309009226337282467899857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96824024603566086581066285 36309009226337282467899857)
    ·
      refine ⟨27231756919752961850924893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36309009226337282467899857 27231756919752961850924893)
      ·
        refine ⟨10211908844907360694096835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27231756919752961850924893 10211908844907360694096835)
        ·
          refine ⟨15317863267361041041145253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10211908844907360694096835 15317863267361041041145253)
          ·
            refine ⟨2872099362630195195214735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15317863267361041041145253 2872099362630195195214735)
            ·
              refine ⟨4308149043945292792822103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872099362630195195214735 4308149043945292792822103)
              ·
                refine ⟨6462223565917939189233155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4308149043945292792822103 6462223565917939189233155)
                ·
                  refine ⟨9693335348876908783849733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6462223565917939189233155 9693335348876908783849733)
                  ·
                    refine ⟨1817500377914420396971825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9693335348876908783849733 1817500377914420396971825)
                    ·
                      refine ⟨1363125283435815297728869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817500377914420396971825 1363125283435815297728869)
                      ·
                        rfl

theorem cell23_2654677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_2654677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654677 prefixEnd_2654677 := by exact prefixLift 2654677
  have htrace : WordTrace (prefixWord ++ tailWord_2654677) baseStart_2654677 baseEnd_2654677 := by
    simpa [prefixWord, tailWord_2654677, baseEnd_2654677] using wordTrace_append hprefix tailTrace_2654677
  have hstable : (prefixWord ++ tailWord_2654677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654677).length < 2 ^ (prefixWord ++ tailWord_2654677).sum := by decide
  have hdescent : baseEnd_2654677 < baseStart_2654677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654703 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 1, 7, 2]
def baseStart_2654703 : Nat := 118140960795 + 2654703 * 2 ^ 59
def prefixEnd_2654703 : Nat := 4983230072969 + 3 ^ 40 * 2654703 * 2
def baseEnd_2654703 : Nat := 1363138633932832196003749

theorem tailTrace_2654703 : CollatzResearch.WordTrace tailWord_2654703 prefixEnd_2654703 1363138633932832196003749 := by
  unfold tailWord_2654703
  simp only [CollatzResearch.WordTrace]
  refine ⟨96824972901471893021512763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64549981934314595347675175 96824972901471893021512763)
  ·
    refine ⟨145237459352207839532269145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96824972901471893021512763 145237459352207839532269145)
    ·
      refine ⟨108928094514155879649201859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145237459352207839532269145 108928094514155879649201859)
      ·
        refine ⟨163392141771233819473802789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108928094514155879649201859 163392141771233819473802789)
        ·
          refine ⟨30636026582106341151338023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163392141771233819473802789 30636026582106341151338023)
          ·
            refine ⟨45954039873159511727007035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30636026582106341151338023 45954039873159511727007035)
            ·
              refine ⟨68931059809739267590510553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45954039873159511727007035 68931059809739267590510553)
              ·
                refine ⟨51698294857304450692882915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68931059809739267590510553 51698294857304450692882915)
                ·
                  refine ⟨77547442285956676039324373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51698294857304450692882915 77547442285956676039324373)
                  ·
                    refine ⟨1817518178577109594671665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 77547442285956676039324373 1817518178577109594671665)
                    ·
                      refine ⟨1363138633932832196003749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817518178577109594671665 1363138633932832196003749)
                      ·
                        rfl

theorem cell23_2654703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 7, 2].length) (baseStart_2654703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654703 prefixEnd_2654703 := by exact prefixLift 2654703
  have htrace : WordTrace (prefixWord ++ tailWord_2654703) baseStart_2654703 baseEnd_2654703 := by
    simpa [prefixWord, tailWord_2654703, baseEnd_2654703] using wordTrace_append hprefix tailTrace_2654703
  have hstable : (prefixWord ++ tailWord_2654703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654703).length < 2 ^ (prefixWord ++ tailWord_2654703).sum := by decide
  have hdescent : baseEnd_2654703 < baseStart_2654703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654770 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_2654770 : Nat := 118140960795 + 2654770 * 2 ^ 59
def prefixEnd_2654770 : Nat := 4983230072969 + 3 ^ 40 * 2654770 * 2
def baseEnd_2654770 : Nat := 1363173037136683433865941

theorem tailTrace_2654770 : CollatzResearch.WordTrace tailWord_2654770 prefixEnd_2654770 1363173037136683433865941 := by
  unfold tailWord_2654770
  simp only [CollatzResearch.WordTrace]
  refine ⟨24206854148057290866050441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64551611061486108976134509 24206854148057290866050441)
  ·
    refine ⟨18155140611042968149537831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24206854148057290866050441 18155140611042968149537831)
    ·
      refine ⟨27232710916564452224306747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18155140611042968149537831 27232710916564452224306747)
      ·
        refine ⟨40849066374846678336460121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27232710916564452224306747 40849066374846678336460121)
        ·
          refine ⟨30636799781135008752345091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40849066374846678336460121 30636799781135008752345091)
          ·
            refine ⟨45955199671702513128517637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30636799781135008752345091 45955199671702513128517637)
            ·
              refine ⟨8616599938444221211597057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45955199671702513128517637 8616599938444221211597057)
              ·
                refine ⟨6462449953833165908697793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8616599938444221211597057 6462449953833165908697793)
                ·
                  refine ⟨4846837465374874431523345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6462449953833165908697793 4846837465374874431523345)
                  ·
                    refine ⟨3635128099031155823642509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4846837465374874431523345 3635128099031155823642509)
                    ·
                      refine ⟨1363173037136683433865941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3635128099031155823642509 1363173037136683433865941)
                      ·
                        rfl

theorem cell23_2654770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_2654770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654770 prefixEnd_2654770 := by exact prefixLift 2654770
  have htrace : WordTrace (prefixWord ++ tailWord_2654770) baseStart_2654770 baseEnd_2654770 := by
    simpa [prefixWord, tailWord_2654770, baseEnd_2654770] using wordTrace_append hprefix tailTrace_2654770
  have hstable : (prefixWord ++ tailWord_2654770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654770).length < 2 ^ (prefixWord ++ tailWord_2654770).sum := by decide
  have hdescent : baseEnd_2654770 < baseStart_2654770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654777 : List Nat := [1, 2, 1, 5, 1, 1, 3, 4, 1, 4]
def baseStart_2654777 : Nat := 118140960795 + 2654777 * 2 ^ 59
def prefixEnd_2654777 : Nat := 4983230072969 + 3 ^ 40 * 2654777 * 2
def baseEnd_2654777 : Nat := 454392210500421635492803

theorem tailTrace_2654777 : CollatzResearch.WordTrace tailWord_2654777 prefixEnd_2654777 454392210500421635492803 := by
  unfold tailWord_2654777
  simp only [CollatzResearch.WordTrace]
  refine ⟨96827671903203803659706585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64551781268802535773137723 96827671903203803659706585)
  ·
    refine ⟨72620753927402852744779939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96827671903203803659706585 72620753927402852744779939)
    ·
      refine ⟨108931130891104279117169909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72620753927402852744779939 108931130891104279117169909)
      ·
        refine ⟨10212293521041026167234679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108931130891104279117169909 10212293521041026167234679)
        ·
          refine ⟨15318440281561539250852019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10212293521041026167234679 15318440281561539250852019)
          ·
            refine ⟨22977660422342308876278029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15318440281561539250852019 22977660422342308876278029)
            ·
              refine ⟨8616622658378365828604261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22977660422342308876278029 8616622658378365828604261)
              ·
                refine ⟨1615616748445943592863299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8616622658378365828604261 1615616748445943592863299)
                ·
                  refine ⟨2423425122668915389294949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615616748445943592863299 2423425122668915389294949)
                  ·
                    refine ⟨454392210500421635492803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2423425122668915389294949 454392210500421635492803)
                    ·
                      rfl

theorem cell23_2654777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 1, 4].length) (baseStart_2654777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654777 prefixEnd_2654777 := by exact prefixLift 2654777
  have htrace : WordTrace (prefixWord ++ tailWord_2654777) baseStart_2654777 baseEnd_2654777 := by
    simpa [prefixWord, tailWord_2654777, baseEnd_2654777] using wordTrace_append hprefix tailTrace_2654777
  have hstable : (prefixWord ++ tailWord_2654777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654777).length < 2 ^ (prefixWord ++ tailWord_2654777).sum := by decide
  have hdescent : baseEnd_2654777 < baseStart_2654777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654820 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_2654820 : Nat := 118140960795 + 2654820 * 2 ^ 59
def prefixEnd_2654820 : Nat := 4983230072969 + 3 ^ 40 * 2654820 * 2
def baseEnd_2654820 : Nat := 454399570389802746080237

theorem tailTrace_2654820 : CollatzResearch.WordTrace tailWord_2654820 prefixEnd_2654820 454399570389802746080237 := by
  unfold tailWord_2654820
  simp only [CollatzResearch.WordTrace]
  refine ⟨48414620121024011001760957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64552826828032014669014609 48414620121024011001760957)
  ·
    refine ⟨18155482545384004125660359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48414620121024011001760957 18155482545384004125660359)
    ·
      refine ⟨27233223818076006188490539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18155482545384004125660359 27233223818076006188490539)
      ·
        refine ⟨40849835727114009282735809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27233223818076006188490539 40849835727114009282735809)
        ·
          refine ⟨30637376795335506962051857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40849835727114009282735809 30637376795335506962051857)
          ·
            refine ⟨22978032596501630221538893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30637376795335506962051857 22978032596501630221538893)
            ·
              refine ⟨8616762223688111333077085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22978032596501630221538893 8616762223688111333077085)
              ·
                refine ⟨3231285833883041749903907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8616762223688111333077085 3231285833883041749903907)
                ·
                  refine ⟨4846928750824562624855861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3231285833883041749903907 4846928750824562624855861)
                  ·
                    refine ⟨454399570389802746080237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4846928750824562624855861 454399570389802746080237)
                    ·
                      rfl

theorem cell23_2654820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_2654820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654820 prefixEnd_2654820 := by exact prefixLift 2654820
  have htrace : WordTrace (prefixWord ++ tailWord_2654820) baseStart_2654820 baseEnd_2654820 := by
    simpa [prefixWord, tailWord_2654820, baseEnd_2654820] using wordTrace_append hprefix tailTrace_2654820
  have hstable : (prefixWord ++ tailWord_2654820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654820).length < 2 ^ (prefixWord ++ tailWord_2654820).sum := by decide
  have hdescent : baseEnd_2654820 < baseStart_2654820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654824 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 6]
def baseStart_2654824 : Nat := 118140960795 + 2654824 * 2 ^ 59
def prefixEnd_2654824 : Nat := 4983230072969 + 3 ^ 40 * 2654824 * 2
def baseEnd_2654824 : Nat := 151466751676891802510077

theorem tailTrace_2654824 : CollatzResearch.WordTrace tailWord_2654824 prefixEnd_2654824 151466751676891802510077 := by
  unfold tailWord_2654824
  simp only [CollatzResearch.WordTrace]
  refine ⟨48414693067016765343333763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64552924089355687124445017 48414693067016765343333763)
  ·
    refine ⟨72622039600525148015000645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48414693067016765343333763 72622039600525148015000645)
    ·
      refine ⟨13616632425098465252812621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72622039600525148015000645 13616632425098465252812621)
      ·
        refine ⟨5106237159411924469804733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13616632425098465252812621 5106237159411924469804733)
        ·
          refine ⟨1914838934779471676176775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5106237159411924469804733 1914838934779471676176775)
          ·
            refine ⟨2872258402169207514265163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914838934779471676176775 2872258402169207514265163)
            ·
              refine ⟨4308387603253811271397745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872258402169207514265163 4308387603253811271397745)
              ·
                refine ⟨3231290702440358453548309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4308387603253811271397745 3231290702440358453548309)
                ·
                  refine ⟨151466751676891802510077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3231290702440358453548309 151466751676891802510077)
                  ·
                    rfl

theorem cell23_2654824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 6].length) (baseStart_2654824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654824 prefixEnd_2654824 := by exact prefixLift 2654824
  have htrace : WordTrace (prefixWord ++ tailWord_2654824) baseStart_2654824 baseEnd_2654824 := by
    simpa [prefixWord, tailWord_2654824, baseEnd_2654824] using wordTrace_append hprefix tailTrace_2654824
  have hstable : (prefixWord ++ tailWord_2654824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654824).length < 2 ^ (prefixWord ++ tailWord_2654824).sum := by decide
  have hdescent : baseEnd_2654824 < baseStart_2654824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654834 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_2654834 : Nat := 118140960795 + 2654834 * 2 ^ 59
def prefixEnd_2654834 : Nat := 4983230072969 + 3 ^ 40 * 2654834 * 2
def baseEnd_2654834 : Nat := 1363205899898571183465647

theorem tailTrace_2654834 : CollatzResearch.WordTrace tailWord_2654834 prefixEnd_2654834 1363205899898571183465647 := by
  unfold tailWord_2654834
  simp only [CollatzResearch.WordTrace]
  refine ⟨24207437715999325598632889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64553167242664868263021037 24207437715999325598632889)
  ·
    refine ⟨18155578286999494198974667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24207437715999325598632889 18155578286999494198974667)
    ·
      refine ⟨27233367430499241298462001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18155578286999494198974667 27233367430499241298462001)
      ·
        refine ⟨20425025572874430973846501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27233367430499241298462001 20425025572874430973846501)
        ·
          refine ⟨3829692294913955807596219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20425025572874430973846501 3829692294913955807596219)
          ·
            refine ⟨5744538442370933711394329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829692294913955807596219 5744538442370933711394329)
            ·
              refine ⟨4308403831778200283545747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5744538442370933711394329 4308403831778200283545747)
              ·
                refine ⟨6462605747667300425318621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4308403831778200283545747 6462605747667300425318621)
                ·
                  refine ⟨2423477155375237659494483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6462605747667300425318621 2423477155375237659494483)
                  ·
                    refine ⟨3635215733062856489241725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2423477155375237659494483 3635215733062856489241725)
                    ·
                      refine ⟨1363205899898571183465647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3635215733062856489241725 1363205899898571183465647)
                      ·
                        rfl

theorem cell23_2654834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_2654834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654834 prefixEnd_2654834 := by exact prefixLift 2654834
  have htrace : WordTrace (prefixWord ++ tailWord_2654834) baseStart_2654834 baseEnd_2654834 := by
    simpa [prefixWord, tailWord_2654834, baseEnd_2654834] using wordTrace_append hprefix tailTrace_2654834
  have hstable : (prefixWord ++ tailWord_2654834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654834).length < 2 ^ (prefixWord ++ tailWord_2654834).sum := by decide
  have hdescent : baseEnd_2654834 < baseStart_2654834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654843 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 3]
def baseStart_2654843 : Nat := 118140960795 + 2654843 * 2 ^ 59
def prefixEnd_2654843 : Nat := 4983230072969 + 3 ^ 40 * 2654843 * 2
def baseEnd_2654843 : Nat := 1363210521224461648253105

theorem tailTrace_2654843 : CollatzResearch.WordTrace tailWord_2654843 prefixEnd_2654843 1363210521224461648253105 := by
  unfold tailWord_2654843
  simp only [CollatzResearch.WordTrace]
  refine ⟨96830079120964696931609183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64553386080643131287739455 96830079120964696931609183)
  ·
    refine ⟨145245118681447045397413775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96830079120964696931609183 145245118681447045397413775)
    ·
      refine ⟨217867678022170568096120663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145245118681447045397413775 217867678022170568096120663)
      ·
        refine ⟨326801517033255852144180995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217867678022170568096120663 326801517033255852144180995)
        ·
          refine ⟨490202275549883778216271493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326801517033255852144180995 490202275549883778216271493)
          ·
            refine ⟨91912926665603208415550905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 490202275549883778216271493 91912926665603208415550905)
            ·
              refine ⟨68934694999202406311663179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91912926665603208415550905 68934694999202406311663179)
              ·
                refine ⟨103402042498803609467494769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68934694999202406311663179 103402042498803609467494769)
                ·
                  refine ⟨77551531874102707100621077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103402042498803609467494769 77551531874102707100621077)
                  ·
                    refine ⟨3635228056598564395341613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77551531874102707100621077 3635228056598564395341613)
                    ·
                      refine ⟨1363210521224461648253105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3635228056598564395341613 1363210521224461648253105)
                      ·
                        rfl

theorem cell23_2654843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 3].length) (baseStart_2654843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654843 prefixEnd_2654843 := by exact prefixLift 2654843
  have htrace : WordTrace (prefixWord ++ tailWord_2654843) baseStart_2654843 baseEnd_2654843 := by
    simpa [prefixWord, tailWord_2654843, baseEnd_2654843] using wordTrace_append hprefix tailTrace_2654843
  have hstable : (prefixWord ++ tailWord_2654843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654843).length < 2 ^ (prefixWord ++ tailWord_2654843).sum := by decide
  have hdescent : baseEnd_2654843 < baseStart_2654843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654868 : List Nat := [2, 4, 2, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_2654868 : Nat := 118140960795 + 2654868 * 2 ^ 59
def prefixEnd_2654868 : Nat := 4983230072969 + 3 ^ 40 * 2654868 * 2
def baseEnd_2654868 : Nat := 1363223358240824050440491

theorem tailTrace_2654868 : CollatzResearch.WordTrace tailWord_2654868 prefixEnd_2654868 1363223358240824050440491 := by
  unfold tailWord_2654868
  simp only [CollatzResearch.WordTrace]
  refine ⟨48415495472937063100634629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64553993963916084134179505 48415495472937063100634629)
  ·
    refine ⟨9077905401175699331368993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48415495472937063100634629 9077905401175699331368993)
    ·
      refine ⟨6808429050881774498526745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9077905401175699331368993 6808429050881774498526745)
      ·
        refine ⟨5106321788161330873895059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6808429050881774498526745 5106321788161330873895059)
        ·
          refine ⟨7659482682241996310842589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5106321788161330873895059 7659482682241996310842589)
          ·
            refine ⟨2872306005840748616565971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7659482682241996310842589 2872306005840748616565971)
            ·
              refine ⟨4308459008761122924848957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872306005840748616565971 4308459008761122924848957)
              ·
                refine ⟨1615672128285421096818359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4308459008761122924848957 1615672128285421096818359)
                ·
                  refine ⟨2423508192428131645227539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615672128285421096818359 2423508192428131645227539)
                  ·
                    refine ⟨3635262288642197467841309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2423508192428131645227539 3635262288642197467841309)
                    ·
                      refine ⟨1363223358240824050440491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3635262288642197467841309 1363223358240824050440491)
                      ·
                        rfl

theorem cell23_2654868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_2654868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654868 prefixEnd_2654868 := by exact prefixLift 2654868
  have htrace : WordTrace (prefixWord ++ tailWord_2654868) baseStart_2654868 baseEnd_2654868 := by
    simpa [prefixWord, tailWord_2654868, baseEnd_2654868] using wordTrace_append hprefix tailTrace_2654868
  have hstable : (prefixWord ++ tailWord_2654868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654868).length < 2 ^ (prefixWord ++ tailWord_2654868).sum := by decide
  have hdescent : baseEnd_2654868 < baseStart_2654868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654877 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_2654877 : Nat := 118140960795 + 2654877 * 2 ^ 59
def prefixEnd_2654877 : Nat := 4983230072969 + 3 ^ 40 * 2654877 * 2
def baseEnd_2654877 : Nat := 1363227979566714515227949

theorem tailTrace_2654877 : CollatzResearch.WordTrace tailWord_2654877 prefixEnd_2654877 1363227979566714515227949 := by
  unfold tailWord_2654877
  simp only [CollatzResearch.WordTrace]
  refine ⟨96831319202841520738346885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64554212801894347158897923 96831319202841520738346885)
  ·
    refine ⟨18155872350532785138440041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96831319202841520738346885 18155872350532785138440041)
    ·
      refine ⟨13616904262899588853830031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18155872350532785138440041 13616904262899588853830031)
      ·
        refine ⟨20425356394349383280745047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13616904262899588853830031 20425356394349383280745047)
        ·
          refine ⟨30638034591524074921117571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20425356394349383280745047 30638034591524074921117571)
          ·
            refine ⟨45957051887286112381676357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30638034591524074921117571 45957051887286112381676357)
            ·
              refine ⟨8616947228866146071564317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45957051887286112381676357 8616947228866146071564317)
              ·
                refine ⟨3231355210824804776836619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8616947228866146071564317 3231355210824804776836619)
                ·
                  refine ⟨4847032816237207165254929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3231355210824804776836619 4847032816237207165254929)
                  ·
                    refine ⟨3635274612177905373941197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4847032816237207165254929 3635274612177905373941197)
                    ·
                      refine ⟨1363227979566714515227949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3635274612177905373941197 1363227979566714515227949)
                      ·
                        rfl

theorem cell23_2654877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_2654877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654877 prefixEnd_2654877 := by exact prefixLift 2654877
  have htrace : WordTrace (prefixWord ++ tailWord_2654877) baseStart_2654877 baseEnd_2654877 := by
    simpa [prefixWord, tailWord_2654877, baseEnd_2654877] using wordTrace_append hprefix tailTrace_2654877
  have hstable : (prefixWord ++ tailWord_2654877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654877).length < 2 ^ (prefixWord ++ tailWord_2654877).sum := by decide
  have hdescent : baseEnd_2654877 < baseStart_2654877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654880 : List Nat := [2, 1, 1, 4, 4, 2, 9]
def baseStart_2654880 : Nat := 118140960795 + 2654880 * 2 ^ 59
def prefixEnd_2654880 : Nat := 4983230072969 + 3 ^ 40 * 2654880 * 2
def baseEnd_2654880 : Nat := 16829994074181209919635

theorem tailTrace_2654880 : CollatzResearch.WordTrace tailWord_2654880 prefixEnd_2654880 16829994074181209919635 := by
  unfold tailWord_2654880
  simp only [CollatzResearch.WordTrace]
  refine ⟨48415714310915326125353047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64554285747887101500470729 48415714310915326125353047)
  ·
    refine ⟨72623571466372989188029571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48415714310915326125353047 72623571466372989188029571)
    ·
      refine ⟨108935357199559483782044357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72623571466372989188029571 108935357199559483782044357)
      ·
        refine ⟨20425379474917403209133317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108935357199559483782044357 20425379474917403209133317)
        ·
          refine ⟨3829758651547013101712497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20425379474917403209133317 3829758651547013101712497)
          ·
            refine ⟨2872318988660259826284373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3829758651547013101712497 2872318988660259826284373)
            ·
              refine ⟨16829994074181209919635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2872318988660259826284373 16829994074181209919635)
              ·
                rfl

theorem cell23_2654880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 9].length) (baseStart_2654880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654880 prefixEnd_2654880 := by exact prefixLift 2654880
  have htrace : WordTrace (prefixWord ++ tailWord_2654880) baseStart_2654880 baseEnd_2654880 := by
    simpa [prefixWord, tailWord_2654880, baseEnd_2654880] using wordTrace_append hprefix tailTrace_2654880
  have hstable : (prefixWord ++ tailWord_2654880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654880).length < 2 ^ (prefixWord ++ tailWord_2654880).sum := by decide
  have hdescent : baseEnd_2654880 < baseStart_2654880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654897 : List Nat := [1, 2, 2, 6, 1, 1, 2, 8]
def baseStart_2654897 : Nat := 118140960795 + 2654897 * 2 ^ 59
def prefixEnd_2654897 : Nat := 4983230072969 + 3 ^ 40 * 2654897 * 2
def baseEnd_2654897 : Nat := 50490305525177942110291

theorem tailTrace_2654897 : CollatzResearch.WordTrace tailWord_2654897 prefixEnd_2654897 50490305525177942110291 := by
  unfold tailWord_2654897
  simp only [CollatzResearch.WordTrace]
  refine ⟨96832048662769064154074945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64554699108512709436049963 96832048662769064154074945)
  ·
    refine ⟨72624036497076798115556209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96832048662769064154074945 72624036497076798115556209)
    ·
      refine ⟨54468027372807598586667157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72624036497076798115556209 54468027372807598586667157)
      ·
        refine ⟨2553188783100356183750023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54468027372807598586667157 2553188783100356183750023)
        ·
          refine ⟨3829783174650534275625035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553188783100356183750023 3829783174650534275625035)
          ·
            refine ⟨5744674761975801413437553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829783174650534275625035 5744674761975801413437553)
            ·
              refine ⟨4308506071481851060078165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5744674761975801413437553 4308506071481851060078165)
              ·
                refine ⟨50490305525177942110291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4308506071481851060078165 50490305525177942110291)
                ·
                  rfl

theorem cell23_2654897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 8].length) (baseStart_2654897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654897 prefixEnd_2654897 := by exact prefixLift 2654897
  have htrace : WordTrace (prefixWord ++ tailWord_2654897) baseStart_2654897 baseEnd_2654897 := by
    simpa [prefixWord, tailWord_2654897, baseEnd_2654897] using wordTrace_append hprefix tailTrace_2654897
  have hstable : (prefixWord ++ tailWord_2654897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654897).length < 2 ^ (prefixWord ++ tailWord_2654897).sum := by decide
  have hdescent : baseEnd_2654897 < baseStart_2654897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654901 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2654901 : Nat := 118140960795 + 2654901 * 2 ^ 59
def prefixEnd_2654901 : Nat := 4983230072969 + 3 ^ 40 * 2654901 * 2
def baseEnd_2654901 : Nat := 454413434367474140442613

theorem tailTrace_2654901 : CollatzResearch.WordTrace tailWord_2654901 prefixEnd_2654901 454413434367474140442613 := by
  unfold tailWord_2654901
  simp only [CollatzResearch.WordTrace]
  refine ⟨96832194554754572837220557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64554796369836381891480371 96832194554754572837220557)
  ·
    refine ⟨36312072958032964813957709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96832194554754572837220557 36312072958032964813957709)
    ·
      refine ⟨13617027359262361805234141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36312072958032964813957709 13617027359262361805234141)
      ·
        refine ⟨5106385259723385676962803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13617027359262361805234141 5106385259723385676962803)
        ·
          refine ⟨7659577889585078515444205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5106385259723385676962803 7659577889585078515444205)
          ·
            refine ⟨2872341708594404443291577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7659577889585078515444205 2872341708594404443291577)
            ·
              refine ⟨2154256281445803332468683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2872341708594404443291577 2154256281445803332468683)
              ·
                refine ⟨3231384422168704998703025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154256281445803332468683 3231384422168704998703025)
                ·
                  refine ⟨2423538316626528749027269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3231384422168704998703025 2423538316626528749027269)
                  ·
                    refine ⟨454413434367474140442613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2423538316626528749027269 454413434367474140442613)
                    ·
                      rfl

theorem cell23_2654901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2654901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654901 prefixEnd_2654901 := by exact prefixLift 2654901
  have htrace : WordTrace (prefixWord ++ tailWord_2654901) baseStart_2654901 baseEnd_2654901 := by
    simpa [prefixWord, tailWord_2654901, baseEnd_2654901] using wordTrace_append hprefix tailTrace_2654901
  have hstable : (prefixWord ++ tailWord_2654901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654901).length < 2 ^ (prefixWord ++ tailWord_2654901).sum := by decide
  have hdescent : baseEnd_2654901 < baseStart_2654901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654923 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 6, 6]
def baseStart_2654923 : Nat := 118140960795 + 2654923 * 2 ^ 59
def prefixEnd_2654923 : Nat := 4983230072969 + 3 ^ 40 * 2654923 * 2
def baseEnd_2654923 : Nat := 454417199892273778417579

theorem tailTrace_2654923 : CollatzResearch.WordTrace tailWord_2654923 prefixEnd_2654923 454417199892273778417579 := by
  unfold tailWord_2654923
  simp only [CollatzResearch.WordTrace]
  refine ⟨96832996960674870594521423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64555331307116580396347615 96832996960674870594521423)
  ·
    refine ⟨145249495441012305891782135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96832996960674870594521423 145249495441012305891782135)
    ·
      refine ⟨217874243161518458837673203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145249495441012305891782135 217874243161518458837673203)
      ·
        refine ⟨326811364742277688256509805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217874243161518458837673203 326811364742277688256509805)
        ·
          refine ⟨122554261778354133096191177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326811364742277688256509805 122554261778354133096191177)
          ·
            refine ⟨91915696333765599822143383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122554261778354133096191177 91915696333765599822143383)
            ·
              refine ⟨137873544500648399733215075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91915696333765599822143383 137873544500648399733215075)
              ·
                refine ⟨206810316750972599599822613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137873544500648399733215075 206810316750972599599822613)
                ·
                  refine ⟨9694233597701840606241685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 206810316750972599599822613 9694233597701840606241685)
                  ·
                    refine ⟨454417199892273778417579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9694233597701840606241685 454417199892273778417579)
                    ·
                      rfl

theorem cell23_2654923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 6].length) (baseStart_2654923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654923 prefixEnd_2654923 := by exact prefixLift 2654923
  have htrace : WordTrace (prefixWord ++ tailWord_2654923) baseStart_2654923 baseEnd_2654923 := by
    simpa [prefixWord, tailWord_2654923, baseEnd_2654923] using wordTrace_append hprefix tailTrace_2654923
  have hstable : (prefixWord ++ tailWord_2654923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654923).length < 2 ^ (prefixWord ++ tailWord_2654923).sum := by decide
  have hdescent : baseEnd_2654923 < baseStart_2654923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654960 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 4]
def baseStart_2654960 : Nat := 118140960795 + 2654960 * 2 ^ 59
def prefixEnd_2654960 : Nat := 4983230072969 + 3 ^ 40 * 2654960 * 2
def baseEnd_2654960 : Nat := 1363270598461037690490067

theorem tailTrace_2654960 : CollatzResearch.WordTrace tailWord_2654960 prefixEnd_2654960 1363270598461037690490067 := by
  unfold tailWord_2654960
  simp only [CollatzResearch.WordTrace]
  refine ⟨48417173230770412956809167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64556230974360550609078889 48417173230770412956809167)
  ·
    refine ⟨72625759846155619435213751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48417173230770412956809167 72625759846155619435213751)
    ·
      refine ⟨108938639769233429152820627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72625759846155619435213751 108938639769233429152820627)
      ·
        refine ⟨163407959653850143729230941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108938639769233429152820627 163407959653850143729230941)
        ·
          refine ⟨61277984870193803898461603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163407959653850143729230941 61277984870193803898461603)
          ·
            refine ⟨91916977305290705847692405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61277984870193803898461603 91916977305290705847692405)
            ·
              refine ⟨8617216622371003673221163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91916977305290705847692405 8617216622371003673221163)
              ·
                refine ⟨12925824933556505509831745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8617216622371003673221163 12925824933556505509831745)
                ·
                  refine ⟨9694368700167379132373809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12925824933556505509831745 9694368700167379132373809)
                  ·
                    refine ⟨7270776525125534349280357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9694368700167379132373809 7270776525125534349280357)
                    ·
                      refine ⟨1363270598461037690490067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7270776525125534349280357 1363270598461037690490067)
                      ·
                        rfl

theorem cell23_2654960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_2654960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2654960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2654960 prefixEnd_2654960 := by exact prefixLift 2654960
  have htrace : WordTrace (prefixWord ++ tailWord_2654960) baseStart_2654960 baseEnd_2654960 := by
    simpa [prefixWord, tailWord_2654960, baseEnd_2654960] using wordTrace_append hprefix tailTrace_2654960
  have hstable : (prefixWord ++ tailWord_2654960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654960).length < 2 ^ (prefixWord ++ tailWord_2654960).sum := by decide
  have hdescent : baseEnd_2654960 < baseStart_2654960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655000 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 4, 5]
def baseStart_2655000 : Nat := 118140960795 + 2655000 * 2 ^ 59
def prefixEnd_2655000 : Nat := 4983230072969 + 3 ^ 40 * 2655000 * 2
def baseEnd_2655000 : Nat := 454430379229072511329961

theorem tailTrace_2655000 : CollatzResearch.WordTrace tailWord_2655000 prefixEnd_2655000 454430379229072511329961 := by
  unfold tailWord_2655000
  simp only [CollatzResearch.WordTrace]
  refine ⟨48417902690697956372537227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64557203587597275163382969 48417902690697956372537227)
  ·
    refine ⟨72626854036046934558805841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48417902690697956372537227 72626854036046934558805841)
    ·
      refine ⟨54470140527035200919104381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72626854036046934558805841 54470140527035200919104381)
      ·
        refine ⟨20426302697638200344664143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54470140527035200919104381 20426302697638200344664143)
        ·
          refine ⟨30639454046457300516996215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20426302697638200344664143 30639454046457300516996215)
          ·
            refine ⟨45959181069685950775494323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30639454046457300516996215 45959181069685950775494323)
            ·
              refine ⟨68938771604528926163241485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45959181069685950775494323 68938771604528926163241485)
              ·
                refine ⟨25852039351698347311215557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68938771604528926163241485 25852039351698347311215557)
                ·
                  refine ⟨4847257378443440120852917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25852039351698347311215557 4847257378443440120852917)
                  ·
                    refine ⟨454430379229072511329961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4847257378443440120852917 454430379229072511329961)
                    ·
                      rfl

theorem cell23_2655000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_2655000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655000 prefixEnd_2655000 := by exact prefixLift 2655000
  have htrace : WordTrace (prefixWord ++ tailWord_2655000) baseStart_2655000 baseEnd_2655000 := by
    simpa [prefixWord, tailWord_2655000, baseEnd_2655000] using wordTrace_append hprefix tailTrace_2655000
  have hstable : (prefixWord ++ tailWord_2655000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655000).length < 2 ^ (prefixWord ++ tailWord_2655000).sum := by decide
  have hdescent : baseEnd_2655000 < baseStart_2655000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655020 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_2655020 : Nat := 118140960795 + 2655020 * 2 ^ 59
def prefixEnd_2655020 : Nat := 4983230072969 + 3 ^ 40 * 2655020 * 2
def baseEnd_2655020 : Nat := 1363301407300307455739791

theorem tailTrace_2655020 : CollatzResearch.WordTrace tailWord_2655020 prefixEnd_2655020 1363301407300307455739791 := by
  unfold tailWord_2655020
  simp only [CollatzResearch.WordTrace]
  refine ⟨48418267420661728080401257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64557689894215637440535009 48418267420661728080401257)
  ·
    refine ⟨36313700565496296060300943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48418267420661728080401257 36313700565496296060300943)
    ·
      refine ⟨54470550848244444090451415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36313700565496296060300943 54470550848244444090451415)
      ·
        refine ⟨81705826272366666135677123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54470550848244444090451415 81705826272366666135677123)
        ·
          refine ⟨122558739408549999203515685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81705826272366666135677123 122558739408549999203515685)
          ·
            refine ⟨22979763639103124850659191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122558739408549999203515685 22979763639103124850659191)
            ·
              refine ⟨34469645458654687275988787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22979763639103124850659191 34469645458654687275988787)
              ·
                refine ⟨51704468187982030913983181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34469645458654687275988787 51704468187982030913983181)
                ·
                  refine ⟨19389175570493261592743693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51704468187982030913983181 19389175570493261592743693)
                  ·
                    refine ⟨7270940838934973097278885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19389175570493261592743693 7270940838934973097278885)
                    ·
                      refine ⟨1363301407300307455739791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7270940838934973097278885 1363301407300307455739791)
                      ·
                        rfl

theorem cell23_2655020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_2655020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655020 prefixEnd_2655020 := by exact prefixLift 2655020
  have htrace : WordTrace (prefixWord ++ tailWord_2655020) baseStart_2655020 baseEnd_2655020 := by
    simpa [prefixWord, tailWord_2655020, baseEnd_2655020] using wordTrace_append hprefix tailTrace_2655020
  have hstable : (prefixWord ++ tailWord_2655020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655020).length < 2 ^ (prefixWord ++ tailWord_2655020).sum := by decide
  have hdescent : baseEnd_2655020 < baseStart_2655020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655038 : List Nat := [4, 2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_2655038 : Nat := 118140960795 + 2655038 * 2 ^ 59
def prefixEnd_2655038 : Nat := 4983230072969 + 3 ^ 40 * 2655038 * 2
def baseEnd_2655038 : Nat := 151478961105787598368301

theorem tailTrace_2655038 : CollatzResearch.WordTrace tailWord_2655038 prefixEnd_2655038 151478961105787598368301 := by
  unfold tailWord_2655038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12104648919407280654369721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64558127570172163489971845 12104648919407280654369721)
  ·
    refine ⟨9078486689555460490777291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12104648919407280654369721 9078486689555460490777291)
    ·
      refine ⟨13617730034333190736165937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9078486689555460490777291 13617730034333190736165937)
      ·
        refine ⟨10213297525749893052124453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13617730034333190736165937 10213297525749893052124453)
        ·
          refine ⟨1914993286078104947273335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10213297525749893052124453 1914993286078104947273335)
          ·
            refine ⟨2872489929117157420910003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914993286078104947273335 2872489929117157420910003)
            ·
              refine ⟨4308734893675736131365005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872489929117157420910003 4308734893675736131365005)
              ·
                refine ⟨1615775585128401049261877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4308734893675736131365005 1615775585128401049261877)
                ·
                  refine ⟨151478961105787598368301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1615775585128401049261877 151478961105787598368301)
                  ·
                    rfl

theorem cell23_2655038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_2655038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655038 prefixEnd_2655038 := by exact prefixLift 2655038
  have htrace : WordTrace (prefixWord ++ tailWord_2655038) baseStart_2655038 baseEnd_2655038 := by
    simpa [prefixWord, tailWord_2655038, baseEnd_2655038] using wordTrace_append hprefix tailTrace_2655038
  have hstable : (prefixWord ++ tailWord_2655038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655038).length < 2 ^ (prefixWord ++ tailWord_2655038).sum := by decide
  have hdescent : baseEnd_2655038 < baseStart_2655038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655050 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_2655050 : Nat := 118140960795 + 2655050 * 2 ^ 59
def prefixEnd_2655050 : Nat := 4983230072969 + 3 ^ 40 * 2655050 * 2
def baseEnd_2655050 : Nat := 1363316811719942338364653

theorem tailTrace_2655050 : CollatzResearch.WordTrace tailWord_2655050 prefixEnd_2655050 1363316811719942338364653 := by
  unfold tailWord_2655050
  simp only [CollatzResearch.WordTrace]
  refine ⟨24209407257803692821098651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64558419354143180856263069 24209407257803692821098651)
  ·
    refine ⟨36314110886705539231647977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24209407257803692821098651 36314110886705539231647977)
    ·
      refine ⟨27235583165029154423735983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36314110886705539231647977 27235583165029154423735983)
      ·
        refine ⟨40853374747543731635603975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27235583165029154423735983 40853374747543731635603975)
        ·
          refine ⟨61280062121315597453405963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40853374747543731635603975 61280062121315597453405963)
          ·
            refine ⟨91920093181973396180108945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61280062121315597453405963 91920093181973396180108945)
            ·
              refine ⟨68940069886480047135081709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91920093181973396180108945 68940069886480047135081709)
              ·
                refine ⟨25852526207430017675655641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68940069886480047135081709 25852526207430017675655641)
                ·
                  refine ⟨19389394655572513256741731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25852526207430017675655641 19389394655572513256741731)
                  ·
                    refine ⟨29084091983358769885112597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19389394655572513256741731 29084091983358769885112597)
                    ·
                      refine ⟨1363316811719942338364653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29084091983358769885112597 1363316811719942338364653)
                      ·
                        rfl

theorem cell23_2655050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_2655050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655050 prefixEnd_2655050 := by exact prefixLift 2655050
  have htrace : WordTrace (prefixWord ++ tailWord_2655050) baseStart_2655050 baseEnd_2655050 := by
    simpa [prefixWord, tailWord_2655050, baseEnd_2655050] using wordTrace_append hprefix tailTrace_2655050
  have hstable : (prefixWord ++ tailWord_2655050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655050).length < 2 ^ (prefixWord ++ tailWord_2655050).sum := by decide
  have hdescent : baseEnd_2655050 < baseStart_2655050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655064 : List Nat := [2, 1, 2, 2, 1, 1, 1, 8, 1, 4]
def baseStart_2655064 : Nat := 118140960795 + 2655064 * 2 ^ 59
def prefixEnd_2655064 : Nat := 4983230072969 + 3 ^ 40 * 2655064 * 2
def baseEnd_2655064 : Nat := 454441333483035094529863

theorem tailTrace_2655064 : CollatzResearch.WordTrace tailWord_2655064 prefixEnd_2655064 454441333483035094529863 := by
  unfold tailWord_2655064
  simp only [CollatzResearch.WordTrace]
  refine ⟨48419069826582025837702123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64558759768776034450269497 48419069826582025837702123)
  ·
    refine ⟨72628604739873038756553185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48419069826582025837702123 72628604739873038756553185)
    ·
      refine ⟨54471453554904779067414889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72628604739873038756553185 54471453554904779067414889)
      ·
        refine ⟨40853590166178584300561167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54471453554904779067414889 40853590166178584300561167)
        ·
          refine ⟨61280385249267876450841751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40853590166178584300561167 61280385249267876450841751)
          ·
            refine ⟨91920577873901814676262627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61280385249267876450841751 91920577873901814676262627)
            ·
              refine ⟨137880866810852722014393941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91920577873901814676262627 137880866810852722014393941)
              ·
                refine ⟨1615791407939680336106179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 137880866810852722014393941 1615791407939680336106179)
                ·
                  refine ⟨2423687111909520504159269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615791407939680336106179 2423687111909520504159269)
                  ·
                    refine ⟨454441333483035094529863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2423687111909520504159269 454441333483035094529863)
                    ·
                      rfl

theorem cell23_2655064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_2655064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655064 prefixEnd_2655064 := by exact prefixLift 2655064
  have htrace : WordTrace (prefixWord ++ tailWord_2655064) baseStart_2655064 baseEnd_2655064 := by
    simpa [prefixWord, tailWord_2655064, baseEnd_2655064] using wordTrace_append hprefix tailTrace_2655064
  have hstable : (prefixWord ++ tailWord_2655064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655064).length < 2 ^ (prefixWord ++ tailWord_2655064).sum := by decide
  have hdescent : baseEnd_2655064 < baseStart_2655064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655100 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2655100 : Nat := 118140960795 + 2655100 * 2 ^ 59
def prefixEnd_2655100 : Nat := 4983230072969 + 3 ^ 40 * 2655100 * 2
def baseEnd_2655100 : Nat := 1363342485752667142739423

theorem tailTrace_2655100 : CollatzResearch.WordTrace tailWord_2655100 prefixEnd_2655100 1363342485752667142739423 := by
  unfold tailWord_2655100
  simp only [CollatzResearch.WordTrace]
  refine ⟨48419726340516814911857377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64559635120689086549143169 48419726340516814911857377)
  ·
    refine ⟨36314794755387611183893033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48419726340516814911857377 36314794755387611183893033)
    ·
      refine ⟨27236096066540708387919775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36314794755387611183893033 27236096066540708387919775)
      ·
        refine ⟨40854144099811062581879663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27236096066540708387919775 40854144099811062581879663)
        ·
          refine ⟨61281216149716593872819495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40854144099811062581879663 61281216149716593872819495)
          ·
            refine ⟨91921824224574890809229243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61281216149716593872819495 91921824224574890809229243)
            ·
              refine ⟨137882736336862336213843865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91921824224574890809229243 137882736336862336213843865)
              ·
                refine ⟨103412052252646752160382899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137882736336862336213843865 103412052252646752160382899)
                ·
                  refine ⟨155118078378970128240574349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103412052252646752160382899 155118078378970128240574349)
                  ·
                    refine ⟨58169279392113798090215381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155118078378970128240574349 58169279392113798090215381)
                    ·
                      refine ⟨1363342485752667142739423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58169279392113798090215381 1363342485752667142739423)
                      ·
                        rfl

theorem cell23_2655100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2655100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655100 prefixEnd_2655100 := by exact prefixLift 2655100
  have htrace : WordTrace (prefixWord ++ tailWord_2655100) baseStart_2655100 baseEnd_2655100 := by
    simpa [prefixWord, tailWord_2655100, baseEnd_2655100] using wordTrace_append hprefix tailTrace_2655100
  have hstable : (prefixWord ++ tailWord_2655100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655100).length < 2 ^ (prefixWord ++ tailWord_2655100).sum := by decide
  have hdescent : baseEnd_2655100 < baseStart_2655100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655127 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_2655127 : Nat := 118140960795 + 2655127 * 2 ^ 59
def prefixEnd_2655127 : Nat := 4983230072969 + 3 ^ 40 * 2655127 * 2
def baseEnd_2655127 : Nat := 1363356349730338537101799

theorem tailTrace_2655127 : CollatzResearch.WordTrace tailWord_2655127 prefixEnd_2655127 1363356349730338537101799 := by
  unfold tailWord_2655127
  simp only [CollatzResearch.WordTrace]
  refine ⟨96840437451935813434947635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64560291634623875623298423 96840437451935813434947635)
  ·
    refine ⟨145260656177903720152421453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96840437451935813434947635 145260656177903720152421453)
    ·
      refine ⟨54472746066713895057158045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145260656177903720152421453 54472746066713895057158045)
      ·
        refine ⟨20427279775017710646434267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54472746066713895057158045 20427279775017710646434267)
        ·
          refine ⟨30640919662526565969651401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20427279775017710646434267 30640919662526565969651401)
          ·
            refine ⟨22980689746894924477238551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30640919662526565969651401 22980689746894924477238551)
            ·
              refine ⟨34471034620342386715857827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22980689746894924477238551 34471034620342386715857827)
              ·
                refine ⟨51706551930513580073786741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34471034620342386715857827 51706551930513580073786741)
                ·
                  refine ⟨4847489243485648131917507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51706551930513580073786741 4847489243485648131917507)
                  ·
                    refine ⟨7271233865228472197876261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4847489243485648131917507 7271233865228472197876261)
                    ·
                      refine ⟨1363356349730338537101799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7271233865228472197876261 1363356349730338537101799)
                      ·
                        rfl

theorem cell23_2655127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_2655127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655127 prefixEnd_2655127 := by exact prefixLift 2655127
  have htrace : WordTrace (prefixWord ++ tailWord_2655127) baseStart_2655127 baseEnd_2655127 := by
    simpa [prefixWord, tailWord_2655127, baseEnd_2655127] using wordTrace_append hprefix tailTrace_2655127
  have hstable : (prefixWord ++ tailWord_2655127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655127).length < 2 ^ (prefixWord ++ tailWord_2655127).sum := by decide
  have hdescent : baseEnd_2655127 < baseStart_2655127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655161 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 1, 1, 4]
def baseStart_2655161 : Nat := 118140960795 + 2655161 * 2 ^ 59
def prefixEnd_2655161 : Nat := 4983230072969 + 3 ^ 40 * 2655161 * 2
def baseEnd_2655161 : Nat := 1363373808072591404076643

theorem tailTrace_2655161 : CollatzResearch.WordTrace tailWord_2655161 prefixEnd_2655161 1363373808072591404076643 := by
  unfold tailWord_2655161
  simp only [CollatzResearch.WordTrace]
  refine ⟨96841677533812637241685337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64561118355875091494456891 96841677533812637241685337)
  ·
    refine ⟨72631258150359477931264003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96841677533812637241685337 72631258150359477931264003)
    ·
      refine ⟨108946887225539216896896005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72631258150359477931264003 108946887225539216896896005)
      ·
        refine ⟨20427541354788603168168001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108946887225539216896896005 20427541354788603168168001)
        ·
          refine ⟨15320656016091452376126001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20427541354788603168168001 15320656016091452376126001)
          ·
            refine ⟨11490492012068589282094501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15320656016091452376126001 11490492012068589282094501)
            ·
              refine ⟨2154467252262860490392719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11490492012068589282094501 2154467252262860490392719)
              ·
                refine ⟨3231700878394290735589079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154467252262860490392719 3231700878394290735589079)
                ·
                  refine ⟨4847551317591436103383619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3231700878394290735589079 4847551317591436103383619)
                  ·
                    refine ⟨7271326976387154155075429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4847551317591436103383619 7271326976387154155075429)
                    ·
                      refine ⟨1363373808072591404076643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7271326976387154155075429 1363373808072591404076643)
                      ·
                        rfl

theorem cell23_2655161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_2655161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655161 prefixEnd_2655161 := by exact prefixLift 2655161
  have htrace : WordTrace (prefixWord ++ tailWord_2655161) baseStart_2655161 baseEnd_2655161 := by
    simpa [prefixWord, tailWord_2655161, baseEnd_2655161] using wordTrace_append hprefix tailTrace_2655161
  have hstable : (prefixWord ++ tailWord_2655161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655161).length < 2 ^ (prefixWord ++ tailWord_2655161).sum := by decide
  have hdescent : baseEnd_2655161 < baseStart_2655161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655188 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_2655188 : Nat := 118140960795 + 2655188 * 2 ^ 59
def prefixEnd_2655188 : Nat := 4983230072969 + 3 ^ 40 * 2655188 * 2
def baseEnd_2655188 : Nat := 454462557350087599479673

theorem tailTrace_2655188 : CollatzResearch.WordTrace tailWord_2655188 prefixEnd_2655188 454462557350087599479673 := by
  unfold tailWord_2655188
  simp only [CollatzResearch.WordTrace]
  refine ⟨48421331152357410426459109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64561774869809880568612145 48421331152357410426459109)
  ·
    refine ⟨9078999591067014454961083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48421331152357410426459109 9078999591067014454961083)
    ·
      refine ⟨13618499386600521682441625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9078999591067014454961083 13618499386600521682441625)
      ·
        refine ⟨10213874539950391261831219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13618499386600521682441625 10213874539950391261831219)
        ·
          refine ⟨15320811809925586892746829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10213874539950391261831219 15320811809925586892746829)
          ·
            refine ⟨5745304428722095084780061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15320811809925586892746829 5745304428722095084780061)
            ·
              refine ⟨2154489160770785656792523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5745304428722095084780061 2154489160770785656792523)
              ·
                refine ⟨3231733741156178485188785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154489160770785656792523 3231733741156178485188785)
                ·
                  refine ⟨2423800305867133863891589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3231733741156178485188785 2423800305867133863891589)
                  ·
                    refine ⟨454462557350087599479673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2423800305867133863891589 454462557350087599479673)
                    ·
                      rfl

theorem cell23_2655188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_2655188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655188 prefixEnd_2655188 := by exact prefixLift 2655188
  have htrace : WordTrace (prefixWord ++ tailWord_2655188) baseStart_2655188 baseEnd_2655188 := by
    simpa [prefixWord, tailWord_2655188, baseEnd_2655188] using wordTrace_append hprefix tailTrace_2655188
  have hstable : (prefixWord ++ tailWord_2655188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655188).length < 2 ^ (prefixWord ++ tailWord_2655188).sum := by decide
  have hdescent : baseEnd_2655188 < baseStart_2655188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655237 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_2655237 : Nat := 118140960795 + 2655237 * 2 ^ 59
def prefixEnd_2655237 : Nat := 4983230072969 + 3 ^ 40 * 2655237 * 2
def baseEnd_2655237 : Nat := 1363412832602333106726293

theorem tailTrace_2655237 : CollatzResearch.WordTrace tailWord_2655237 prefixEnd_2655237 1363412832602333106726293 := by
  unfold tailWord_2655237
  simp only [CollatzResearch.WordTrace]
  refine ⟨96844449481537302221451965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64562966321024868147634643 96844449481537302221451965)
  ·
    refine ⟨36316668555576488333044487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96844449481537302221451965 36316668555576488333044487)
    ·
      refine ⟨54475002833364732499566731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36316668555576488333044487 54475002833364732499566731)
      ·
        refine ⟨81712504250047098749350097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54475002833364732499566731 81712504250047098749350097)
        ·
          refine ⟨61284378187535324062012573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81712504250047098749350097 61284378187535324062012573)
          ·
            refine ⟨22981641820325746523254715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61284378187535324062012573 22981641820325746523254715)
            ·
              refine ⟨34472462730488619784882073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22981641820325746523254715 34472462730488619784882073)
              ·
                refine ⟨25854347047866464838661555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34472462730488619784882073 25854347047866464838661555)
                ·
                  refine ⟨38781520571799697257992333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25854347047866464838661555 38781520571799697257992333)
                  ·
                    refine ⟨14543070214424886471747125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38781520571799697257992333 14543070214424886471747125)
                    ·
                      refine ⟨1363412832602333106726293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14543070214424886471747125 1363412832602333106726293)
                      ·
                        rfl

theorem cell23_2655237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_2655237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655237 prefixEnd_2655237 := by exact prefixLift 2655237
  have htrace : WordTrace (prefixWord ++ tailWord_2655237) baseStart_2655237 baseEnd_2655237 := by
    simpa [prefixWord, tailWord_2655237, baseEnd_2655237] using wordTrace_append hprefix tailTrace_2655237
  have hstable : (prefixWord ++ tailWord_2655237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655237).length < 2 ^ (prefixWord ++ tailWord_2655237).sum := by decide
  have hdescent : baseEnd_2655237 < baseStart_2655237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655255 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 1, 3, 2]
def baseStart_2655255 : Nat := 118140960795 + 2655255 * 2 ^ 59
def prefixEnd_2655255 : Nat := 4983230072969 + 3 ^ 40 * 2655255 * 2
def baseEnd_2655255 : Nat := 1363422075254114036301211

theorem tailTrace_2655255 : CollatzResearch.WordTrace tailWord_2655255 prefixEnd_2655255 1363422075254114036301211 := by
  unfold tailWord_2655255
  simp only [CollatzResearch.WordTrace]
  refine ⟨96845105995472091295607219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64563403996981394197071479 96845105995472091295607219)
  ·
    refine ⟨145267658993208136943410829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96845105995472091295607219 145267658993208136943410829)
    ·
      refine ⟨54475372122453051353779061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145267658993208136943410829 54475372122453051353779061)
      ·
        refine ⟨5107066136479973564416787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54475372122453051353779061 5107066136479973564416787)
        ·
          refine ⟨7660599204719960346625181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107066136479973564416787 7660599204719960346625181)
          ·
            refine ⟨2872724701769985129984443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7660599204719960346625181 2872724701769985129984443)
            ·
              refine ⟨4309087052654977694976665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872724701769985129984443 4309087052654977694976665)
              ·
                refine ⟨3231815289491233271232499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4309087052654977694976665 3231815289491233271232499)
                ·
                  refine ⟨4847722934236849906848749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3231815289491233271232499 4847722934236849906848749)
                  ·
                    refine ⟨1817896100338818715068281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4847722934236849906848749 1817896100338818715068281)
                    ·
                      refine ⟨1363422075254114036301211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817896100338818715068281 1363422075254114036301211)
                      ·
                        rfl

theorem cell23_2655255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_2655255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655255 prefixEnd_2655255 := by exact prefixLift 2655255
  have htrace : WordTrace (prefixWord ++ tailWord_2655255) baseStart_2655255 baseEnd_2655255 := by
    simpa [prefixWord, tailWord_2655255, baseEnd_2655255] using wordTrace_append hprefix tailTrace_2655255
  have hstable : (prefixWord ++ tailWord_2655255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655255).length < 2 ^ (prefixWord ++ tailWord_2655255).sum := by decide
  have hdescent : baseEnd_2655255 < baseStart_2655255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655257 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 7]
def baseStart_2655257 : Nat := 118140960795 + 2655257 * 2 ^ 59
def prefixEnd_2655257 : Nat := 4983230072969 + 3 ^ 40 * 2655257 * 2
def baseEnd_2655257 : Nat := 151491455801713669830689

theorem tailTrace_2655257 : CollatzResearch.WordTrace tailWord_2655257 prefixEnd_2655257 151491455801713669830689 := by
  unfold tailWord_2655257
  simp only [CollatzResearch.WordTrace]
  refine ⟨96845178941464845637180025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64563452627643230424786683 96845178941464845637180025)
  ·
    refine ⟨72633884206098634227885019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96845178941464845637180025 72633884206098634227885019)
    ·
      refine ⟨108950826309147951341827529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72633884206098634227885019 108950826309147951341827529)
      ·
        refine ⟨81713119731860963506370647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108950826309147951341827529 81713119731860963506370647)
        ·
          refine ⟨122569679597791445259555971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81713119731860963506370647 122569679597791445259555971)
          ·
            refine ⟨183854519396687167889333957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122569679597791445259555971 183854519396687167889333957)
            ·
              refine ⟨34472722386878843979250117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183854519396687167889333957 34472722386878843979250117)
              ·
                refine ⟨6463635447539783246109397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34472722386878843979250117 6463635447539783246109397)
                ·
                  refine ⟨151491455801713669830689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6463635447539783246109397 151491455801713669830689)
                  ·
                    rfl

theorem cell23_2655257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 7].length) (baseStart_2655257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655257 prefixEnd_2655257 := by exact prefixLift 2655257
  have htrace : WordTrace (prefixWord ++ tailWord_2655257) baseStart_2655257 baseEnd_2655257 := by
    simpa [prefixWord, tailWord_2655257, baseEnd_2655257] using wordTrace_append hprefix tailTrace_2655257
  have hstable : (prefixWord ++ tailWord_2655257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655257).length < 2 ^ (prefixWord ++ tailWord_2655257).sum := by decide
  have hdescent : baseEnd_2655257 < baseStart_2655257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655268 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 1, 4, 2]
def baseStart_2655268 : Nat := 118140960795 + 2655268 * 2 ^ 59
def prefixEnd_2655268 : Nat := 4983230072969 + 3 ^ 40 * 2655268 * 2
def baseEnd_2655268 : Nat := 1363428750502622485438651

theorem tailTrace_2655268 : CollatzResearch.WordTrace tailWord_2655268 prefixEnd_2655268 1363428750502622485438651 := by
  unfold tailWord_2655268
  simp only [CollatzResearch.WordTrace]
  refine ⟨48422790072212497257915229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64563720096283329677220305 48422790072212497257915229)
  ·
    refine ⟨18158546277079686471718211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48422790072212497257915229 18158546277079686471718211)
    ·
      refine ⟨27237819415619529707577317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18158546277079686471718211 27237819415619529707577317)
      ·
        refine ⟨5107091140428661820170747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27237819415619529707577317 5107091140428661820170747)
        ·
          refine ⟨7660636710642992730256121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107091140428661820170747 7660636710642992730256121)
          ·
            refine ⟨5745477532982244547692091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7660636710642992730256121 5745477532982244547692091)
            ·
              refine ⟨8618216299473366821538137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745477532982244547692091 8618216299473366821538137)
              ·
                refine ⟨6463662224605025116153603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8618216299473366821538137 6463662224605025116153603)
                ·
                  refine ⟨9695493336907537674230405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6463662224605025116153603 9695493336907537674230405)
                  ·
                    refine ⟨1817905000670163313918201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9695493336907537674230405 1817905000670163313918201)
                    ·
                      refine ⟨1363428750502622485438651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817905000670163313918201 1363428750502622485438651)
                      ·
                        rfl

theorem cell23_2655268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_2655268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655268 prefixEnd_2655268 := by exact prefixLift 2655268
  have htrace : WordTrace (prefixWord ++ tailWord_2655268) baseStart_2655268 baseEnd_2655268 := by
    simpa [prefixWord, tailWord_2655268, baseEnd_2655268] using wordTrace_append hprefix tailTrace_2655268
  have hstable : (prefixWord ++ tailWord_2655268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655268).length < 2 ^ (prefixWord ++ tailWord_2655268).sum := by decide
  have hdescent : baseEnd_2655268 < baseStart_2655268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655271 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2655271 : Nat := 118140960795 + 2655271 * 2 ^ 59
def prefixEnd_2655271 : Nat := 4983230072969 + 3 ^ 40 * 2655271 * 2
def baseEnd_2655271 : Nat := 1363430290944585973701137

theorem tailTrace_2655271 : CollatzResearch.WordTrace tailWord_2655271 prefixEnd_2655271 1363430290944585973701137 := by
  unfold tailWord_2655271
  simp only [CollatzResearch.WordTrace]
  refine ⟨96845689563414126028189667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64563793042276084018793111 96845689563414126028189667)
  ·
    refine ⟨145268534345121189042284501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96845689563414126028189667 145268534345121189042284501)
    ·
      refine ⟨3404731273713777868178543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 145268534345121189042284501 3404731273713777868178543)
      ·
        refine ⟨5107096910570666802267815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3404731273713777868178543 5107096910570666802267815)
        ·
          refine ⟨7660645365856000203401723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107096910570666802267815 7660645365856000203401723)
          ·
            refine ⟨11490968048784000305102585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7660645365856000203401723 11490968048784000305102585)
            ·
              refine ⟨8618226036588000228826939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11490968048784000305102585 8618226036588000228826939)
              ·
                refine ⟨12927339054882000343240409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8618226036588000228826939 12927339054882000343240409)
                ·
                  refine ⟨9695504291161500257430307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12927339054882000343240409 9695504291161500257430307)
                  ·
                    refine ⟨14543256436742250386145461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9695504291161500257430307 14543256436742250386145461)
                    ·
                      refine ⟨1363430290944585973701137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14543256436742250386145461 1363430290944585973701137)
                      ·
                        rfl

theorem cell23_2655271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2655271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655271 prefixEnd_2655271 := by exact prefixLift 2655271
  have htrace : WordTrace (prefixWord ++ tailWord_2655271) baseStart_2655271 baseEnd_2655271 := by
    simpa [prefixWord, tailWord_2655271, baseEnd_2655271] using wordTrace_append hprefix tailTrace_2655271
  have hstable : (prefixWord ++ tailWord_2655271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655271).length < 2 ^ (prefixWord ++ tailWord_2655271).sum := by decide
  have hdescent : baseEnd_2655271 < baseStart_2655271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655287 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 3, 7]
def baseStart_2655287 : Nat := 118140960795 + 2655287 * 2 ^ 59
def prefixEnd_2655287 : Nat := 4983230072969 + 3 ^ 40 * 2655287 * 2
def baseEnd_2655287 : Nat := 454479502211685970367021

theorem tailTrace_2655287 : CollatzResearch.WordTrace tailWord_2655287 prefixEnd_2655287 454479502211685970367021 := by
  unfold tailWord_2655287
  simp only [CollatzResearch.WordTrace]
  refine ⟨96846273131356160760772115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64564182087570773840514743 96846273131356160760772115)
  ·
    refine ⟨145269409697034241141158173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96846273131356160760772115 145269409697034241141158173)
    ·
      refine ⟨54476028636387840427934315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145269409697034241141158173 54476028636387840427934315)
      ·
        refine ⟨81714042954581760641901473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54476028636387840427934315 81714042954581760641901473)
        ·
          refine ⟨61285532215936320481426105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81714042954581760641901473 61285532215936320481426105)
          ·
            refine ⟨45964149161952240361069579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61285532215936320481426105 45964149161952240361069579)
            ·
              refine ⟨68946223742928360541604369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45964149161952240361069579 68946223742928360541604369)
              ·
                refine ⟨51709667807196270406203277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68946223742928360541604369 51709667807196270406203277)
                ·
                  refine ⟨19391125427698601402326229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51709667807196270406203277 19391125427698601402326229)
                  ·
                    refine ⟨454479502211685970367021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19391125427698601402326229 454479502211685970367021)
                    ·
                      rfl

theorem cell23_2655287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_2655287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655287 prefixEnd_2655287 := by exact prefixLift 2655287
  have htrace : WordTrace (prefixWord ++ tailWord_2655287) baseStart_2655287 baseEnd_2655287 := by
    simpa [prefixWord, tailWord_2655287, baseEnd_2655287] using wordTrace_append hprefix tailTrace_2655287
  have hstable : (prefixWord ++ tailWord_2655287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655287).length < 2 ^ (prefixWord ++ tailWord_2655287).sum := by decide
  have hdescent : baseEnd_2655287 < baseStart_2655287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655302 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_2655302 : Nat := 118140960795 + 2655302 * 2 ^ 59
def prefixEnd_2655302 : Nat := 4983230072969 + 3 ^ 40 * 2655302 * 2
def baseEnd_2655302 : Nat := 1363446208844875352413495

theorem tailTrace_2655302 : CollatzResearch.WordTrace tailWord_2655302 prefixEnd_2655302 1363446208844875352413495 := by
  unfold tailWord_2655302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3026463132071931822580255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64564546817534545548378773 3026463132071931822580255)
  ·
    refine ⟨4539694698107897733870383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3026463132071931822580255 4539694698107897733870383)
    ·
      refine ⟨6809542047161846600805575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4539694698107897733870383 6809542047161846600805575)
      ·
        refine ⟨10214313070742769901208363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6809542047161846600805575 10214313070742769901208363)
        ·
          refine ⟨15321469606114154851812545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10214313070742769901208363 15321469606114154851812545)
          ·
            refine ⟨11491102204585616138859409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15321469606114154851812545 11491102204585616138859409)
            ·
              refine ⟨8618326653439212104144557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11491102204585616138859409 8618326653439212104144557)
              ·
                refine ⟨3231872495039704539054209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8618326653439212104144557 3231872495039704539054209)
                ·
                  refine ⟨2423904371279778404290657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3231872495039704539054209 2423904371279778404290657)
                  ·
                    refine ⟨1817928278459833803217993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2423904371279778404290657 1817928278459833803217993)
                    ·
                      refine ⟨1363446208844875352413495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1817928278459833803217993 1363446208844875352413495)
                      ·
                        rfl

theorem cell23_2655302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_2655302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655302 prefixEnd_2655302 := by exact prefixLift 2655302
  have htrace : WordTrace (prefixWord ++ tailWord_2655302) baseStart_2655302 baseEnd_2655302 := by
    simpa [prefixWord, tailWord_2655302, baseEnd_2655302] using wordTrace_append hprefix tailTrace_2655302
  have hstable : (prefixWord ++ tailWord_2655302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655302).length < 2 ^ (prefixWord ++ tailWord_2655302).sum := by decide
  have hdescent : baseEnd_2655302 < baseStart_2655302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655325 : List Nat := [1, 4, 4, 1, 2, 1, 2, 3, 5]
def baseStart_2655325 : Nat := 118140960795 + 2655325 * 2 ^ 59
def prefixEnd_2655325 : Nat := 4983230072969 + 3 ^ 40 * 2655325 * 2
def baseEnd_2655325 : Nat := 151495335433325418047321

theorem tailTrace_2655325 : CollatzResearch.WordTrace tailWord_2655325 prefixEnd_2655325 151495335433325418047321 := by
  unfold tailWord_2655325
  simp only [CollatzResearch.WordTrace]
  refine ⟨96847659105218493250655429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64565106070145662167103619 96847659105218493250655429)
  ·
    refine ⟨18158936082228467484497893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96847659105218493250655429 18158936082228467484497893)
    ·
      refine ⟨3404800515417837653343355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18158936082228467484497893 3404800515417837653343355)
      ·
        refine ⟨5107200773126756480015033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3404800515417837653343355 5107200773126756480015033)
        ·
          refine ⟨3830400579845067360011275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5107200773126756480015033 3830400579845067360011275)
          ·
            refine ⟨5745600869767601040016913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3830400579845067360011275 5745600869767601040016913)
            ·
              refine ⟨4309200652325700780012685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5745600869767601040016913 4309200652325700780012685)
              ·
                refine ⟨1615950244622137792504757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4309200652325700780012685 1615950244622137792504757)
                ·
                  refine ⟨151495335433325418047321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1615950244622137792504757 151495335433325418047321)
                  ·
                    rfl

theorem cell23_2655325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_2655325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655325 prefixEnd_2655325 := by exact prefixLift 2655325
  have htrace : WordTrace (prefixWord ++ tailWord_2655325) baseStart_2655325 baseEnd_2655325 := by
    simpa [prefixWord, tailWord_2655325, baseEnd_2655325] using wordTrace_append hprefix tailTrace_2655325
  have hstable : (prefixWord ++ tailWord_2655325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655325).length < 2 ^ (prefixWord ++ tailWord_2655325).sum := by decide
  have hdescent : baseEnd_2655325 < baseStart_2655325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655351 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 3, 4]
def baseStart_2655351 : Nat := 118140960795 + 2655351 * 2 ^ 59
def prefixEnd_2655351 : Nat := 4983230072969 + 3 ^ 40 * 2655351 * 2
def baseEnd_2655351 : Nat := 454490456465648553566923

theorem tailTrace_2655351 : CollatzResearch.WordTrace tailWord_2655351 prefixEnd_2655351 454490456465648553566923 := by
  unfold tailWord_2655351
  simp only [CollatzResearch.WordTrace]
  refine ⟨96848607403124299691101907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64565738268749533127401271 96848607403124299691101907)
  ·
    refine ⟨145272911104686449536652861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96848607403124299691101907 145272911104686449536652861)
    ·
      refine ⟨54477341664257418576244823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145272911104686449536652861 54477341664257418576244823)
      ·
        refine ⟨81716012496386127864367235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54477341664257418576244823 81716012496386127864367235)
        ·
          refine ⟨122574018744579191796550853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81716012496386127864367235 122574018744579191796550853)
          ·
            refine ⟨22982628514608598461853285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122574018744579191796550853 22982628514608598461853285)
            ·
              refine ⟨4309242846489112211597491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22982628514608598461853285 4309242846489112211597491)
              ·
                refine ⟨6463864269733668317396237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4309242846489112211597491 6463864269733668317396237)
                ·
                  refine ⟨2423949101150125619023589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6463864269733668317396237 2423949101150125619023589)
                  ·
                    refine ⟨454490456465648553566923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2423949101150125619023589 454490456465648553566923)
                    ·
                      rfl

theorem cell23_2655351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_2655351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655351 prefixEnd_2655351 := by exact prefixLift 2655351
  have htrace : WordTrace (prefixWord ++ tailWord_2655351) baseStart_2655351 baseEnd_2655351 := by
    simpa [prefixWord, tailWord_2655351, baseEnd_2655351] using wordTrace_append hprefix tailTrace_2655351
  have hstable : (prefixWord ++ tailWord_2655351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655351).length < 2 ^ (prefixWord ++ tailWord_2655351).sum := by decide
  have hdescent : baseEnd_2655351 < baseStart_2655351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655361 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2655361 : Nat := 118140960795 + 2655361 * 2 ^ 59
def prefixEnd_2655361 : Nat := 4983230072969 + 3 ^ 40 * 2655361 * 2
def baseEnd_2655361 : Nat := 1363476504203490621575723

theorem tailTrace_2655361 : CollatzResearch.WordTrace tailWord_2655361 prefixEnd_2655361 1363476504203490621575723 := by
  unfold tailWord_2655361
  simp only [CollatzResearch.WordTrace]
  refine ⟨96848972133088071398965937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64565981422058714265977291 96848972133088071398965937)
  ·
    refine ⟨72636729099816053549224453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96848972133088071398965937 72636729099816053549224453)
    ·
      refine ⟨13619386706215510040479585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72636729099816053549224453 13619386706215510040479585)
      ·
        refine ⟨10214540029661632530359689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13619386706215510040479585 10214540029661632530359689)
        ·
          refine ⟨7660905022246224397769767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10214540029661632530359689 7660905022246224397769767)
          ·
            refine ⟨11491357533369336596654651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7660905022246224397769767 11491357533369336596654651)
            ·
              refine ⟨17237036300054004894981977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11491357533369336596654651 17237036300054004894981977)
              ·
                refine ⟨12927777225040503671236483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17237036300054004894981977 12927777225040503671236483)
                ·
                  refine ⟨19391665837560755506854725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12927777225040503671236483 19391665837560755506854725)
                  ·
                    refine ⟨3635937344542641657535261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19391665837560755506854725 3635937344542641657535261)
                    ·
                      refine ⟨1363476504203490621575723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3635937344542641657535261 1363476504203490621575723)
                      ·
                        rfl

theorem cell23_2655361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2655361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655361 prefixEnd_2655361 := by exact prefixLift 2655361
  have htrace : WordTrace (prefixWord ++ tailWord_2655361) baseStart_2655361 baseEnd_2655361 := by
    simpa [prefixWord, tailWord_2655361, baseEnd_2655361] using wordTrace_append hprefix tailTrace_2655361
  have hstable : (prefixWord ++ tailWord_2655361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655361).length < 2 ^ (prefixWord ++ tailWord_2655361).sum := by decide
  have hdescent : baseEnd_2655361 < baseStart_2655361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655428 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2655428 : Nat := 118140960795 + 2655428 * 2 ^ 59
def prefixEnd_2655428 : Nat := 4983230072969 + 3 ^ 40 * 2655428 * 2
def baseEnd_2655428 : Nat := 454503635802447286479305

theorem tailTrace_2655428 : CollatzResearch.WordTrace tailWord_2655428 prefixEnd_2655428 454503635802447286479305 := by
  unfold tailWord_2655428
  simp only [CollatzResearch.WordTrace]
  refine ⟨48425707911922670920827469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64567610549230227894436625 48425707911922670920827469)
  ·
    refine ⟨18159640466971001595310301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48425707911922670920827469 18159640466971001595310301)
    ·
      refine ⟨6809865175114125598241363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18159640466971001595310301 6809865175114125598241363)
      ·
        refine ⟨10214797762671188397362045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6809865175114125598241363 10214797762671188397362045)
        ·
          refine ⟨3830549161001695649010767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10214797762671188397362045 3830549161001695649010767)
          ·
            refine ⟨5745823741502543473516151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3830549161001695649010767 5745823741502543473516151)
            ·
              refine ⟨8618735612253815210274227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745823741502543473516151 8618735612253815210274227)
              ·
                refine ⟨12928103418380722815411341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8618735612253815210274227 12928103418380722815411341)
                ·
                  refine ⟨4848038781892771055779253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12928103418380722815411341 4848038781892771055779253)
                  ·
                    refine ⟨454503635802447286479305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4848038781892771055779253 454503635802447286479305)
                    ·
                      rfl

theorem cell23_2655428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2655428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655428 prefixEnd_2655428 := by exact prefixLift 2655428
  have htrace : WordTrace (prefixWord ++ tailWord_2655428) baseStart_2655428 baseEnd_2655428 := by
    simpa [prefixWord, tailWord_2655428, baseEnd_2655428] using wordTrace_append hprefix tailTrace_2655428
  have hstable : (prefixWord ++ tailWord_2655428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655428).length < 2 ^ (prefixWord ++ tailWord_2655428).sum := by decide
  have hdescent : baseEnd_2655428 < baseStart_2655428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655431 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 2, 6, 2]
def baseStart_2655431 : Nat := 118140960795 + 2655431 * 2 ^ 59
def prefixEnd_2655431 : Nat := 4983230072969 + 3 ^ 40 * 2655431 * 2
def baseEnd_2655431 : Nat := 1363512447849305347700401

theorem tailTrace_2655431 : CollatzResearch.WordTrace tailWord_2655431 prefixEnd_2655431 1363512447849305347700401 := by
  unfold tailWord_2655431
  simp only [CollatzResearch.WordTrace]
  refine ⟨96851525242834473354014147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64567683495222982236009431 96851525242834473354014147)
  ·
    refine ⟨145277287864251710031021221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96851525242834473354014147 145277287864251710031021221)
    ·
      refine ⟨27239491474547195630816479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145277287864251710031021221 27239491474547195630816479)
      ·
        refine ⟨40859237211820793446224719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27239491474547195630816479 40859237211820793446224719)
        ·
          refine ⟨61288855817731190169337079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40859237211820793446224719 61288855817731190169337079)
          ·
            refine ⟨91933283726596785254005619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61288855817731190169337079 91933283726596785254005619)
            ·
              refine ⟨137899925589895177881008429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91933283726596785254005619 137899925589895177881008429)
              ·
                refine ⟨51712472096210691705378161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137899925589895177881008429 51712472096210691705378161)
                ·
                  refine ⟨38784354072158018779033621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51712472096210691705378161 38784354072158018779033621)
                  ·
                    refine ⟨1818016597132407130267201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38784354072158018779033621 1818016597132407130267201)
                    ·
                      refine ⟨1363512447849305347700401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818016597132407130267201 1363512447849305347700401)
                      ·
                        rfl

theorem cell23_2655431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_2655431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655431 prefixEnd_2655431 := by exact prefixLift 2655431
  have htrace : WordTrace (prefixWord ++ tailWord_2655431) baseStart_2655431 baseEnd_2655431 := by
    simpa [prefixWord, tailWord_2655431, baseEnd_2655431] using wordTrace_append hprefix tailTrace_2655431
  have hstable : (prefixWord ++ tailWord_2655431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655431).length < 2 ^ (prefixWord ++ tailWord_2655431).sum := by decide
  have hdescent : baseEnd_2655431 < baseStart_2655431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655445 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 1, 5]
def baseStart_2655445 : Nat := 118140960795 + 2655445 * 2 ^ 59
def prefixEnd_2655445 : Nat := 4983230072969 + 3 ^ 40 * 2655445 * 2
def baseEnd_2655445 : Nat := 454506545526156097641779

theorem tailTrace_2655445 : CollatzResearch.WordTrace tailWord_2655445 prefixEnd_2655445 454506545526156097641779 := by
  unfold tailWord_2655445
  simp only [CollatzResearch.WordTrace]
  refine ⟨96852035864783753745023789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64568023909855835830015859 96852035864783753745023789)
  ·
    refine ⟨36319513449293907654383921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96852035864783753745023789 36319513449293907654383921)
    ·
      refine ⟨27239635086970430740787941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36319513449293907654383921 27239635086970430740787941)
      ·
        refine ⟨5107431578806955763897739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27239635086970430740787941 5107431578806955763897739)
        ·
          refine ⟨7661147368210433645846609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107431578806955763897739 7661147368210433645846609)
          ·
            refine ⟨5745860526157825234384957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7661147368210433645846609 5745860526157825234384957)
            ·
              refine ⟨2154697697309184462894359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5745860526157825234384957 2154697697309184462894359)
              ·
                refine ⟨3232046545963776694341539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154697697309184462894359 3232046545963776694341539)
                ·
                  refine ⟨4848069818945665041512309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3232046545963776694341539 4848069818945665041512309)
                  ·
                    refine ⟨454506545526156097641779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4848069818945665041512309 454506545526156097641779)
                    ·
                      rfl

theorem cell23_2655445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_2655445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655445 prefixEnd_2655445 := by exact prefixLift 2655445
  have htrace : WordTrace (prefixWord ++ tailWord_2655445) baseStart_2655445 baseEnd_2655445 := by
    simpa [prefixWord, tailWord_2655445, baseEnd_2655445] using wordTrace_append hprefix tailTrace_2655445
  have hstable : (prefixWord ++ tailWord_2655445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655445).length < 2 ^ (prefixWord ++ tailWord_2655445).sum := by decide
  have hdescent : baseEnd_2655445 < baseStart_2655445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655498 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_2655498 : Nat := 118140960795 + 2655498 * 2 ^ 59
def prefixEnd_2655498 : Nat := 4983230072969 + 3 ^ 40 * 2655498 * 2
def baseEnd_2655498 : Nat := 1363546851053156585562593

theorem tailTrace_2655498 : CollatzResearch.WordTrace tailWord_2655498 prefixEnd_2655498 1363546851053156585562593 := by
  unfold tailWord_2655498
  simp only [CollatzResearch.WordTrace]
  refine ⟨24213492233397935949175787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64569312622394495864468765 24213492233397935949175787)
  ·
    refine ⟨36320238350096903923763681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24213492233397935949175787 36320238350096903923763681)
    ·
      refine ⟨27240178762572677942822761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36320238350096903923763681 27240178762572677942822761)
      ·
        refine ⟨20430134071929508457117071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27240178762572677942822761 20430134071929508457117071)
        ·
          refine ⟨30645201107894262685675607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20430134071929508457117071 30645201107894262685675607)
          ·
            refine ⟨45967801661841394028513411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30645201107894262685675607 45967801661841394028513411)
            ·
              refine ⟨68951702492762091042770117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45967801661841394028513411 68951702492762091042770117)
              ·
                refine ⟨12928444217392892070519397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68951702492762091042770117 12928444217392892070519397)
                ·
                  refine ⟨2424083290761167263222387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12928444217392892070519397 2424083290761167263222387)
                  ·
                    refine ⟨3636124936141750894833581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2424083290761167263222387 3636124936141750894833581)
                    ·
                      refine ⟨1363546851053156585562593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3636124936141750894833581 1363546851053156585562593)
                      ·
                        rfl

theorem cell23_2655498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_2655498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655498 prefixEnd_2655498 := by exact prefixLift 2655498
  have htrace : WordTrace (prefixWord ++ tailWord_2655498) baseStart_2655498 baseEnd_2655498 := by
    simpa [prefixWord, tailWord_2655498, baseEnd_2655498] using wordTrace_append hprefix tailTrace_2655498
  have hstable : (prefixWord ++ tailWord_2655498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655498).length < 2 ^ (prefixWord ++ tailWord_2655498).sum := by decide
  have hdescent : baseEnd_2655498 < baseStart_2655498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655502 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3]
def baseStart_2655502 : Nat := 118140960795 + 2655502 * 2 ^ 59
def prefixEnd_2655502 : Nat := 4983230072969 + 3 ^ 40 * 2655502 * 2
def baseEnd_2655502 : Nat := 1363548904975774569912575

theorem tailTrace_2655502 : CollatzResearch.WordTrace tailWord_2655502 prefixEnd_2655502 1363548904975774569912575 := by
  unfold tailWord_2655502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12106764353197156559981095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64569409883718168319899173 12106764353197156559981095)
  ·
    refine ⟨18160146529795734839971643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12106764353197156559981095 18160146529795734839971643)
    ·
      refine ⟨27240219794693602259957465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18160146529795734839971643 27240219794693602259957465)
      ·
        refine ⟨20430164846020201694968099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27240219794693602259957465 20430164846020201694968099)
        ·
          refine ⟨30645247269030302542452149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20430164846020201694968099 30645247269030302542452149)
          ·
            refine ⟨2872991931471590863354889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30645247269030302542452149 2872991931471590863354889)
            ·
              refine ⟨2154743948603693147516167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2872991931471590863354889 2154743948603693147516167)
              ·
                refine ⟨3232115922905539721274251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154743948603693147516167 3232115922905539721274251)
                ·
                  refine ⟨4848173884358309581911377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3232115922905539721274251 4848173884358309581911377)
                  ·
                    refine ⟨3636130413268732186433533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4848173884358309581911377 3636130413268732186433533)
                    ·
                      refine ⟨1363548904975774569912575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3636130413268732186433533 1363548904975774569912575)
                      ·
                        rfl

theorem cell23_2655502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_2655502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655502 prefixEnd_2655502 := by exact prefixLift 2655502
  have htrace : WordTrace (prefixWord ++ tailWord_2655502) baseStart_2655502 baseEnd_2655502 := by
    simpa [prefixWord, tailWord_2655502, baseEnd_2655502] using wordTrace_append hprefix tailTrace_2655502
  have hstable : (prefixWord ++ tailWord_2655502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655502).length < 2 ^ (prefixWord ++ tailWord_2655502).sum := by decide
  have hdescent : baseEnd_2655502 < baseStart_2655502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655572 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_2655572 : Nat := 118140960795 + 2655572 * 2 ^ 59
def prefixEnd_2655572 : Nat := 4983230072969 + 3 ^ 40 * 2655572 * 2
def baseEnd_2655572 : Nat := 1363584848621589296037253

theorem tailTrace_2655572 : CollatzResearch.WordTrace tailWord_2655572 prefixEnd_2655572 1363584848621589296037253 := by
  unfold tailWord_2655572
  simp only [CollatzResearch.WordTrace]
  refine ⟨48428333967661827217448485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64571111956882436289931313 48428333967661827217448485)
  ·
    refine ⟨9080312618936592603271591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48428333967661827217448485 9080312618936592603271591)
    ·
      refine ⟨13620468928404888904907387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9080312618936592603271591 13620468928404888904907387)
      ·
        refine ⟨20430703392607333357361081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13620468928404888904907387 20430703392607333357361081)
        ·
          refine ⟨15323027544455500018020811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20430703392607333357361081 15323027544455500018020811)
          ·
            refine ⟨22984541316683250027031217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15323027544455500018020811 22984541316683250027031217)
            ·
              refine ⟨17238405987512437520273413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22984541316683250027031217 17238405987512437520273413)
              ·
                refine ⟨3232201122658582035051265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17238405987512437520273413 3232201122658582035051265)
                ·
                  refine ⟨2424150841993936526288449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3232201122658582035051265 2424150841993936526288449)
                  ·
                    refine ⟨1818113131495452394716337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2424150841993936526288449 1818113131495452394716337)
                    ·
                      refine ⟨1363584848621589296037253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818113131495452394716337 1363584848621589296037253)
                      ·
                        rfl

theorem cell23_2655572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_2655572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655572 prefixEnd_2655572 := by exact prefixLift 2655572
  have htrace : WordTrace (prefixWord ++ tailWord_2655572) baseStart_2655572 baseEnd_2655572 := by
    simpa [prefixWord, tailWord_2655572, baseEnd_2655572] using wordTrace_append hprefix tailTrace_2655572
  have hstable : (prefixWord ++ tailWord_2655572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655572).length < 2 ^ (prefixWord ++ tailWord_2655572).sum := by decide
  have hdescent : baseEnd_2655572 < baseStart_2655572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655578 : List Nat := [3, 1, 1, 2, 1, 2, 2, 6, 5]
def baseStart_2655578 : Nat := 118140960795 + 2655578 * 2 ^ 59
def prefixEnd_2655578 : Nat := 4983230072969 + 3 ^ 40 * 2655578 * 2
def baseEnd_2655578 : Nat := 151509769945057363618025

theorem tailTrace_2655578 : CollatzResearch.WordTrace tailWord_2655578 prefixEnd_2655578 151509769945057363618025 := by
  unfold tailWord_2655578
  simp only [CollatzResearch.WordTrace]
  refine ⟨24214221693325479364903847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64571257848867944973076925 24214221693325479364903847)
  ·
    refine ⟨36321332539988219047355771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24214221693325479364903847 36321332539988219047355771)
    ·
      refine ⟨54481998809982328571033657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36321332539988219047355771 54481998809982328571033657)
      ·
        refine ⟨40861499107486746428275243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54481998809982328571033657 40861499107486746428275243)
        ·
          refine ⟨61292248661230119642412865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40861499107486746428275243 61292248661230119642412865)
          ·
            refine ⟨45969186495922589731809649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61292248661230119642412865 45969186495922589731809649)
            ·
              refine ⟨34476889871941942298857237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45969186495922589731809649 34476889871941942298857237)
              ·
                refine ⟨1616104212747278545258933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34476889871941942298857237 1616104212747278545258933)
                ·
                  refine ⟨151509769945057363618025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1616104212747278545258933 151509769945057363618025)
                  ·
                    rfl

theorem cell23_2655578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_2655578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655578 prefixEnd_2655578 := by exact prefixLift 2655578
  have htrace : WordTrace (prefixWord ++ tailWord_2655578) baseStart_2655578 baseEnd_2655578 := by
    simpa [prefixWord, tailWord_2655578, baseEnd_2655578] using wordTrace_append hprefix tailTrace_2655578
  have hstable : (prefixWord ++ tailWord_2655578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655578).length < 2 ^ (prefixWord ++ tailWord_2655578).sum := by decide
  have hdescent : baseEnd_2655578 < baseStart_2655578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655628 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2655628 : Nat := 118140960795 + 2655628 * 2 ^ 59
def prefixEnd_2655628 : Nat := 4983230072969 + 3 ^ 40 * 2655628 * 2
def baseEnd_2655628 : Nat := 1363613603538241076936995

theorem tailTrace_2655628 : CollatzResearch.WordTrace tailWord_2655628 prefixEnd_2655628 1363613603538241076936995 := by
  unfold tailWord_2655628
  simp only [CollatzResearch.WordTrace]
  refine ⟨48429355211560387999467769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64572473615413850665957025 48429355211560387999467769)
  ·
    refine ⟨36322016408670290999600827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48429355211560387999467769 36322016408670290999600827)
    ·
      refine ⟨54483024613005436499401241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36322016408670290999600827 54483024613005436499401241)
      ·
        refine ⟨40862268459754077374550931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54483024613005436499401241 40862268459754077374550931)
        ·
          refine ⟨61293402689631116061826397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40862268459754077374550931 61293402689631116061826397)
          ·
            refine ⟨22985026008611668523184899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61293402689631116061826397 22985026008611668523184899)
            ·
              refine ⟨34477539012917502784777349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22985026008611668523184899 34477539012917502784777349)
              ·
                refine ⟨6464538564922031772145753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34477539012917502784777349 6464538564922031772145753)
                ·
                  refine ⟨4848403923691523829109315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6464538564922031772145753 4848403923691523829109315)
                  ·
                    refine ⟨7272605885537285743663973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4848403923691523829109315 7272605885537285743663973)
                    ·
                      refine ⟨1363613603538241076936995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7272605885537285743663973 1363613603538241076936995)
                      ·
                        rfl

theorem cell23_2655628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2655628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655628 prefixEnd_2655628 := by exact prefixLift 2655628
  have htrace : WordTrace (prefixWord ++ tailWord_2655628) baseStart_2655628 baseEnd_2655628 := by
    simpa [prefixWord, tailWord_2655628, baseEnd_2655628] using wordTrace_append hprefix tailTrace_2655628
  have hstable : (prefixWord ++ tailWord_2655628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655628).length < 2 ^ (prefixWord ++ tailWord_2655628).sum := by decide
  have hdescent : baseEnd_2655628 < baseStart_2655628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
