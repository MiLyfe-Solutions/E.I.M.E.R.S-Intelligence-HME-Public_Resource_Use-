import V185TrunkScan23Chunk1213

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7192185 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 1, 6]
def baseStart_7192185 : Nat := 118140960795 + 7192185 * 2 ^ 59
def prefixEnd_7192185 : Nat := 4983230072969 + 3 ^ 40 * 7192185 * 2
def baseEnd_7192185 : Nat := 1231015953685682758937083

theorem tailTrace_7192185 : CollatzResearch.WordTrace tailWord_7192185 prefixEnd_7192185 1231015953685682758937083 := by
  unfold tailWord_7192185
  simp only [CollatzResearch.WordTrace]
  refine ⟨262320537448949547250970009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174880358299299698167313339 262320537448949547250970009)
  ·
    refine ⟨196740403086712160438227507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262320537448949547250970009 196740403086712160438227507)
    ·
      refine ⟨295110604630068240657341261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196740403086712160438227507 295110604630068240657341261)
      ·
        refine ⟨110666476736275590246502973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295110604630068240657341261 110666476736275590246502973)
        ·
          refine ⟨41499928776103346342438615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110666476736275590246502973 41499928776103346342438615)
          ·
            refine ⟨62249893164155019513657923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41499928776103346342438615 62249893164155019513657923)
            ·
              refine ⟨93374839746232529270486885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62249893164155019513657923 93374839746232529270486885)
              ·
                refine ⟨17507782452418599238216291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93374839746232529270486885 17507782452418599238216291)
                ·
                  refine ⟨26261673678627898857324437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17507782452418599238216291 26261673678627898857324437)
                  ·
                    refine ⟨1231015953685682758937083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26261673678627898857324437 1231015953685682758937083)
                    ·
                      rfl

theorem cell23_7192185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_7192185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192185 prefixEnd_7192185 := by exact prefixLift 7192185
  have htrace : WordTrace (prefixWord ++ tailWord_7192185) baseStart_7192185 baseEnd_7192185 := by
    simpa [prefixWord, tailWord_7192185, baseEnd_7192185] using wordTrace_append hprefix tailTrace_7192185
  have hstable : (prefixWord ++ tailWord_7192185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192185).length < 2 ^ (prefixWord ++ tailWord_7192185).sum := by decide
  have hdescent : baseEnd_7192185 < baseStart_7192185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192189 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_7192189 : Nat := 118140960795 + 7192189 * 2 ^ 59
def prefixEnd_7192189 : Nat := 4983230072969 + 3 ^ 40 * 7192189 * 2
def baseEnd_7192189 : Nat := 1231016638326555420387077

theorem tailTrace_7192189 : CollatzResearch.WordTrace tailWord_7192189 prefixEnd_7192189 1231016638326555420387077 := by
  unfold tailWord_7192189
  simp only [CollatzResearch.WordTrace]
  refine ⟨262320683340935055934115621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174880455560623370622743747 262320683340935055934115621)
  ·
    refine ⟨49185128126425322987646679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262320683340935055934115621 49185128126425322987646679)
    ·
      refine ⟨73777692189637984481470019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49185128126425322987646679 73777692189637984481470019)
      ·
        refine ⟨110666538284456976722205029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73777692189637984481470019 110666538284456976722205029)
        ·
          refine ⟨20749975928335683135413443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110666538284456976722205029 20749975928335683135413443)
          ·
            refine ⟨31124963892503524703120165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20749975928335683135413443 31124963892503524703120165)
            ·
              refine ⟨5835930729844410881835031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31124963892503524703120165 5835930729844410881835031)
              ·
                refine ⟨8753896094766616322752547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835930729844410881835031 8753896094766616322752547)
                ·
                  refine ⟨13130844142149924484128821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8753896094766616322752547 13130844142149924484128821)
                  ·
                    refine ⟨1231016638326555420387077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13130844142149924484128821 1231016638326555420387077)
                    ·
                      rfl

theorem cell23_7192189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_7192189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192189 prefixEnd_7192189 := by exact prefixLift 7192189
  have htrace : WordTrace (prefixWord ++ tailWord_7192189) baseStart_7192189 baseEnd_7192189 := by
    simpa [prefixWord, tailWord_7192189, baseEnd_7192189] using wordTrace_append hprefix tailTrace_7192189
  have hstable : (prefixWord ++ tailWord_7192189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192189).length < 2 ^ (prefixWord ++ tailWord_7192189).sum := by decide
  have hdescent : baseEnd_7192189 < baseStart_7192189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192192 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 4]
def baseStart_7192192 : Nat := 118140960795 + 7192192 * 2 ^ 59
def prefixEnd_7192192 : Nat := 4983230072969 + 3 ^ 40 * 7192192 * 2
def baseEnd_7192192 : Nat := 3693051455421629749423717

theorem tailTrace_7192192 : CollatzResearch.WordTrace tailWord_7192192 prefixEnd_7192192 3693051455421629749423717 := by
  unfold tailWord_7192192
  simp only [CollatzResearch.WordTrace]
  refine ⟨131160396379962093723237415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174880528506616124964316553 131160396379962093723237415)
  ·
    refine ⟨196740594569943140584856123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131160396379962093723237415 196740594569943140584856123)
    ·
      refine ⟨295110891854914710877284185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196740594569943140584856123 295110891854914710877284185)
      ·
        refine ⟨221333168891186033157963139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295110891854914710877284185 221333168891186033157963139)
        ·
          refine ⟨331999753336779049736944709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221333168891186033157963139 331999753336779049736944709)
          ·
            refine ⟨62249953750646071825677133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331999753336779049736944709 62249953750646071825677133)
            ·
              refine ⟨23343732656492276934628925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62249953750646071825677133 23343732656492276934628925)
              ·
                refine ⟨8753899746184603850485847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23343732656492276934628925 8753899746184603850485847)
                ·
                  refine ⟨13130849619276905775728771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8753899746184603850485847 13130849619276905775728771)
                  ·
                    refine ⟨19696274428915358663593157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13130849619276905775728771 19696274428915358663593157)
                    ·
                      refine ⟨3693051455421629749423717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19696274428915358663593157 3693051455421629749423717)
                      ·
                        rfl

theorem cell23_7192192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_7192192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192192 prefixEnd_7192192 := by exact prefixLift 7192192
  have htrace : WordTrace (prefixWord ++ tailWord_7192192) baseStart_7192192 baseEnd_7192192 := by
    simpa [prefixWord, tailWord_7192192, baseEnd_7192192] using wordTrace_append hprefix tailTrace_7192192
  have hstable : (prefixWord ++ tailWord_7192192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192192).length < 2 ^ (prefixWord ++ tailWord_7192192).sum := by decide
  have hdescent : baseEnd_7192192 < baseStart_7192192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192195 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 5]
def baseStart_7192195 : Nat := 118140960795 + 7192195 * 2 ^ 59
def prefixEnd_7192195 : Nat := 4983230072969 + 3 ^ 40 * 7192195 * 2
def baseEnd_7192195 : Nat := 3693052995863593237686203

theorem tailTrace_7192195 : CollatzResearch.WordTrace tailWord_7192195 prefixEnd_7192195 3693052995863593237686203 := by
  unfold tailWord_7192195
  simp only [CollatzResearch.WordTrace]
  refine ⟨262320902178913318958834039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174880601452608879305889359 262320902178913318958834039)
  ·
    refine ⟨393481353268369978438251059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262320902178913318958834039 393481353268369978438251059)
    ·
      refine ⟨590222029902554967657376589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393481353268369978438251059 590222029902554967657376589)
      ·
        refine ⟨221333261213458112871516221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 590222029902554967657376589 221333261213458112871516221)
        ·
          refine ⟨82999972955046792326818583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221333261213458112871516221 82999972955046792326818583)
          ·
            refine ⟨124499959432570188490227875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82999972955046792326818583 124499959432570188490227875)
            ·
              refine ⟨186749939148855282735341813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124499959432570188490227875 186749939148855282735341813)
              ·
                refine ⟨17507806795205182756438295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186749939148855282735341813 17507806795205182756438295)
                ·
                  refine ⟨26261710192807774134657443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17507806795205182756438295 26261710192807774134657443)
                  ·
                    refine ⟨39392565289211661201986165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26261710192807774134657443 39392565289211661201986165)
                    ·
                      refine ⟨3693052995863593237686203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39392565289211661201986165 3693052995863593237686203)
                      ·
                        rfl

theorem cell23_7192195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_7192195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192195 prefixEnd_7192195 := by exact prefixLift 7192195
  have htrace : WordTrace (prefixWord ++ tailWord_7192195) baseStart_7192195 baseEnd_7192195 := by
    simpa [prefixWord, tailWord_7192195, baseEnd_7192195] using wordTrace_append hprefix tailTrace_7192195
  have hstable : (prefixWord ++ tailWord_7192195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192195).length < 2 ^ (prefixWord ++ tailWord_7192195).sum := by decide
  have hdescent : baseEnd_7192195 < baseStart_7192195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192242 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_7192242 : Nat := 118140960795 + 7192242 * 2 ^ 59
def prefixEnd_7192242 : Nat := 4983230072969 + 3 ^ 40 * 7192242 * 2
def baseEnd_7192242 : Nat := 3693077129454354553798487

theorem tailTrace_7192242 : CollatzResearch.WordTrace tailWord_7192242 prefixEnd_7192242 3693077129454354553798487 := by
  unfold tailWord_7192242
  simp only [CollatzResearch.WordTrace]
  refine ⟨65580654102435761496448745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174881744273162030657196653 65580654102435761496448745)
  ·
    refine ⟨49185490576826821122336559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65580654102435761496448745 49185490576826821122336559)
    ·
      refine ⟨73778235865240231683504839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49185490576826821122336559 73778235865240231683504839)
      ·
        refine ⟨110667353797860347525257259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73778235865240231683504839 110667353797860347525257259)
        ·
          refine ⟨166001030696790521287885889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110667353797860347525257259 166001030696790521287885889)
          ·
            refine ⟨124500773022592890965914417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166001030696790521287885889 124500773022592890965914417)
            ·
              refine ⟨93375579766944668224435813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124500773022592890965914417 93375579766944668224435813)
              ·
                refine ⟨17507921206302125292081715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93375579766944668224435813 17507921206302125292081715)
                ·
                  refine ⟨26261881809453187938122573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17507921206302125292081715 26261881809453187938122573)
                  ·
                    refine ⟨9848205678544945476795965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26261881809453187938122573 9848205678544945476795965)
                    ·
                      refine ⟨3693077129454354553798487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9848205678544945476795965 3693077129454354553798487)
                      ·
                        rfl

theorem cell23_7192242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_7192242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192242 prefixEnd_7192242 := by exact prefixLift 7192242
  have htrace : WordTrace (prefixWord ++ tailWord_7192242) baseStart_7192242 baseEnd_7192242 := by
    simpa [prefixWord, tailWord_7192242, baseEnd_7192242] using wordTrace_append hprefix tailTrace_7192242
  have hstable : (prefixWord ++ tailWord_7192242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192242).length < 2 ^ (prefixWord ++ tailWord_7192242).sum := by decide
  have hdescent : baseEnd_7192242 < baseStart_7192242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192246 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_7192246 : Nat := 118140960795 + 7192246 * 2 ^ 59
def prefixEnd_7192246 : Nat := 4983230072969 + 3 ^ 40 * 7192246 * 2
def baseEnd_7192246 : Nat := 3693079183376972538148469

theorem tailTrace_7192246 : CollatzResearch.WordTrace tailWord_7192246 prefixEnd_7192246 3693079183376972538148469 := by
  unfold tailWord_7192246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16395172643858034666808787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174881841534485703112627061 16395172643858034666808787)
  ·
    refine ⟨24592758965787052000213181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16395172643858034666808787 24592758965787052000213181)
    ·
      refine ⟨9222284612170144500079943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24592758965787052000213181 9222284612170144500079943)
      ·
        refine ⟨13833426918255216750119915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9222284612170144500079943 13833426918255216750119915)
        ·
          refine ⟨20750140377382825125179873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13833426918255216750119915 20750140377382825125179873)
          ·
            refine ⟨15562605283037118843884905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20750140377382825125179873 15562605283037118843884905)
            ·
              refine ⟨11671953962277839132913679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15562605283037118843884905 11671953962277839132913679)
              ·
                refine ⟨17507930943416758699370519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11671953962277839132913679 17507930943416758699370519)
                ·
                  refine ⟨26261896415125138049055779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17507930943416758699370519 26261896415125138049055779)
                  ·
                    refine ⟨39392844622687707073583669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26261896415125138049055779 39392844622687707073583669)
                    ·
                      refine ⟨3693079183376972538148469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39392844622687707073583669 3693079183376972538148469)
                      ·
                        rfl

theorem cell23_7192246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_7192246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192246 prefixEnd_7192246 := by exact prefixLift 7192246
  have htrace : WordTrace (prefixWord ++ tailWord_7192246) baseStart_7192246 baseEnd_7192246 := by
    simpa [prefixWord, tailWord_7192246, baseEnd_7192246] using wordTrace_append hprefix tailTrace_7192246
  have hstable : (prefixWord ++ tailWord_7192246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192246).length < 2 ^ (prefixWord ++ tailWord_7192246).sum := by decide
  have hdescent : baseEnd_7192246 < baseStart_7192246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192255 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_7192255 : Nat := 118140960795 + 7192255 * 2 ^ 59
def prefixEnd_7192255 : Nat := 4983230072969 + 3 ^ 40 * 7192255 * 2
def baseEnd_7192255 : Nat := 3693083804702863002935927

theorem tailTrace_7192255 : CollatzResearch.WordTrace tailWord_7192255 prefixEnd_7192255 3693083804702863002935927 := by
  unfold tailWord_7192255
  simp only [CollatzResearch.WordTrace]
  refine ⟨262323090558695949206018219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174882060372463966137345479 262323090558695949206018219)
  ·
    refine ⟨393484635838043923809027329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262323090558695949206018219 393484635838043923809027329)
    ·
      refine ⟨295113476878532942856770497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393484635838043923809027329 295113476878532942856770497)
      ·
        refine ⟨221335107658899707142577873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295113476878532942856770497 221335107658899707142577873)
        ·
          refine ⟨166001330744174780356933405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221335107658899707142577873 166001330744174780356933405)
          ·
            refine ⟨62250499029065542633850027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166001330744174780356933405 62250499029065542633850027)
            ·
              refine ⟨93375748543598313950775041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62250499029065542633850027 93375748543598313950775041)
              ·
                refine ⟨70031811407698735463081281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93375748543598313950775041 70031811407698735463081281)
                ·
                  refine ⟨52523858555774051597310961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70031811407698735463081281 52523858555774051597310961)
                  ·
                    refine ⟨39392893916830538697983221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52523858555774051597310961 39392893916830538697983221)
                    ·
                      refine ⟨3693083804702863002935927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39392893916830538697983221 3693083804702863002935927)
                      ·
                        rfl

theorem cell23_7192255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_7192255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192255 prefixEnd_7192255 := by exact prefixLift 7192255
  have htrace : WordTrace (prefixWord ++ tailWord_7192255) baseStart_7192255 baseEnd_7192255 := by
    simpa [prefixWord, tailWord_7192255, baseEnd_7192255] using wordTrace_append hprefix tailTrace_7192255
  have hstable : (prefixWord ++ tailWord_7192255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192255).length < 2 ^ (prefixWord ++ tailWord_7192255).sum := by decide
  have hdescent : baseEnd_7192255 < baseStart_7192255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192260 : List Nat := [2, 3, 3, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_7192260 : Nat := 118140960795 + 7192260 * 2 ^ 59
def prefixEnd_7192260 : Nat := 4983230072969 + 3 ^ 40 * 7192260 * 2
def baseEnd_7192260 : Nat := 3693086372106135483373405

theorem tailTrace_7192260 : CollatzResearch.WordTrace tailWord_7192260 prefixEnd_7192260 3693086372106135483373405 := by
  unfold tailWord_7192260
  simp only [CollatzResearch.WordTrace]
  refine ⟨131161636461838917529975117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174882181949118556706633489 131161636461838917529975117)
  ·
    refine ⟨49185613673189594073740669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131161636461838917529975117 49185613673189594073740669)
    ·
      refine ⟨18444605127446097777652751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49185613673189594073740669 18444605127446097777652751)
      ·
        refine ⟨27666907691169146666479127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18444605127446097777652751 27666907691169146666479127)
        ·
          refine ⟨41500361536753719999718691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27666907691169146666479127 41500361536753719999718691)
          ·
            refine ⟨62250542305130579999578037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41500361536753719999718691 62250542305130579999578037)
            ·
              refine ⟨5835988341105991874960441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62250542305130579999578037 5835988341105991874960441)
              ·
                refine ⟨4376991255829493906220331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5835988341105991874960441 4376991255829493906220331)
                ·
                  refine ⟨6565486883744240859330497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376991255829493906220331 6565486883744240859330497)
                  ·
                    refine ⟨4924115162808180644497873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6565486883744240859330497 4924115162808180644497873)
                    ·
                      refine ⟨3693086372106135483373405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4924115162808180644497873 3693086372106135483373405)
                      ·
                        rfl

theorem cell23_7192260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_7192260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192260 prefixEnd_7192260 := by exact prefixLift 7192260
  have htrace : WordTrace (prefixWord ++ tailWord_7192260) baseStart_7192260 baseEnd_7192260 := by
    simpa [prefixWord, tailWord_7192260, baseEnd_7192260] using wordTrace_append hprefix tailTrace_7192260
  have hstable : (prefixWord ++ tailWord_7192260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192260).length < 2 ^ (prefixWord ++ tailWord_7192260).sum := by decide
  have hdescent : baseEnd_7192260 < baseStart_7192260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192299 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 6, 2, 2]
def baseStart_7192299 : Nat := 118140960795 + 7192299 * 2 ^ 59
def prefixEnd_7192299 : Nat := 4983230072969 + 3 ^ 40 * 7192299 * 2
def baseEnd_7192299 : Nat := 3693106397851660830785725

theorem tailTrace_7192299 : CollatzResearch.WordTrace tailWord_7192299 prefixEnd_7192299 3693106397851660830785725 := by
  unfold tailWord_7192299
  simp only [CollatzResearch.WordTrace]
  refine ⟨262324695370536544720619951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174883130247024363147079967 262324695370536544720619951)
  ·
    refine ⟨393487043055804817080929927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262324695370536544720619951 393487043055804817080929927)
    ·
      refine ⟨590230564583707225621394891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393487043055804817080929927 590230564583707225621394891)
      ·
        refine ⟨885345846875560838432092337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590230564583707225621394891 885345846875560838432092337)
        ·
          refine ⟨664009385156670628824069253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 885345846875560838432092337 664009385156670628824069253)
          ·
            refine ⟨124501759716875742904512985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 664009385156670628824069253 124501759716875742904512985)
            ·
              refine ⟨93376319787656807178384739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124501759716875742904512985 93376319787656807178384739)
              ·
                refine ⟨140064479681485210767577109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93376319787656807178384739 140064479681485210767577109)
                ·
                  refine ⟨6565522485069619254730177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140064479681485210767577109 6565522485069619254730177)
                  ·
                    refine ⟨4924141863802214441047633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6565522485069619254730177 4924141863802214441047633)
                    ·
                      refine ⟨3693106397851660830785725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4924141863802214441047633 3693106397851660830785725)
                      ·
                        rfl

theorem cell23_7192299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 2, 2].length) (baseStart_7192299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192299 prefixEnd_7192299 := by exact prefixLift 7192299
  have htrace : WordTrace (prefixWord ++ tailWord_7192299) baseStart_7192299 baseEnd_7192299 := by
    simpa [prefixWord, tailWord_7192299, baseEnd_7192299] using wordTrace_append hprefix tailTrace_7192299
  have hstable : (prefixWord ++ tailWord_7192299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192299).length < 2 ^ (prefixWord ++ tailWord_7192299).sum := by decide
  have hdescent : baseEnd_7192299 < baseStart_7192299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192302 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_7192302 : Nat := 118140960795 + 7192302 * 2 ^ 59
def prefixEnd_7192302 : Nat := 4983230072969 + 3 ^ 40 * 7192302 * 2
def baseEnd_7192302 : Nat := 3693107938293624319048211

theorem tailTrace_7192302 : CollatzResearch.WordTrace tailWord_7192302 prefixEnd_7192302 3693107938293624319048211 := by
  unfold tailWord_7192302
  simp only [CollatzResearch.WordTrace]
  refine ⟨32790600598690709529122395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174883203193017117488652773 32790600598690709529122395)
  ·
    refine ⟨49185900898036064293683593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32790600598690709529122395 49185900898036064293683593)
    ·
      refine ⟨36889425673527048220262695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49185900898036064293683593 36889425673527048220262695)
      ·
        refine ⟨55334138510290572330394043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36889425673527048220262695 55334138510290572330394043)
        ·
          refine ⟨83001207765435858495591065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55334138510290572330394043 83001207765435858495591065)
          ·
            refine ⟨62250905824076893871693299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83001207765435858495591065 62250905824076893871693299)
            ·
              refine ⟨93376358736115340807539949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62250905824076893871693299 93376358736115340807539949)
              ·
                refine ⟨35016134526043252802827481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93376358736115340807539949 35016134526043252802827481)
                ·
                  refine ⟨26262100894532439602120611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35016134526043252802827481 26262100894532439602120611)
                  ·
                    refine ⟨39393151341798659403180917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26262100894532439602120611 39393151341798659403180917)
                    ·
                      refine ⟨3693107938293624319048211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39393151341798659403180917 3693107938293624319048211)
                      ·
                        rfl

theorem cell23_7192302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_7192302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192302 prefixEnd_7192302 := by exact prefixLift 7192302
  have htrace : WordTrace (prefixWord ++ tailWord_7192302) baseStart_7192302 baseEnd_7192302 := by
    simpa [prefixWord, tailWord_7192302, baseEnd_7192302] using wordTrace_append hprefix tailTrace_7192302
  have hstable : (prefixWord ++ tailWord_7192302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192302).length < 2 ^ (prefixWord ++ tailWord_7192302).sum := by decide
  have hdescent : baseEnd_7192302 < baseStart_7192302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192325 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_7192325 : Nat := 118140960795 + 7192325 * 2 ^ 59
def prefixEnd_7192325 : Nat := 4983230072969 + 3 ^ 40 * 7192325 * 2
def baseEnd_7192325 : Nat := 3693119748348677729060605

theorem tailTrace_7192325 : CollatzResearch.WordTrace tailWord_7192325 prefixEnd_7192325 3693119748348677729060605 := by
  unfold tailWord_7192325
  simp only [CollatzResearch.WordTrace]
  refine ⟨262325643668442351161066429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174883762445628234107377619 262325643668442351161066429)
  ·
    refine ⟨98372116375665881685399911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262325643668442351161066429 98372116375665881685399911)
    ·
      refine ⟨147558174563498822528099867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98372116375665881685399911 147558174563498822528099867)
      ·
        refine ⟨221337261845248233792149801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147558174563498822528099867 221337261845248233792149801)
        ·
          refine ⟨166002946383936175344112351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221337261845248233792149801 166002946383936175344112351)
          ·
            refine ⟨249004419575904263016168527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166002946383936175344112351 249004419575904263016168527)
            ·
              refine ⟨373506629363856394524252791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249004419575904263016168527 373506629363856394524252791)
              ·
                refine ⟨560259944045784591786379187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373506629363856394524252791 560259944045784591786379187)
                ·
                  refine ⟨840389916068676887679568781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560259944045784591786379187 840389916068676887679568781)
                  ·
                    refine ⟨315146218525753832879838293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 840389916068676887679568781 315146218525753832879838293)
                    ·
                      refine ⟨3693119748348677729060605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 315146218525753832879838293 3693119748348677729060605)
                      ·
                        rfl

theorem cell23_7192325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_7192325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192325 prefixEnd_7192325 := by exact prefixLift 7192325
  have htrace : WordTrace (prefixWord ++ tailWord_7192325) baseStart_7192325 baseEnd_7192325 := by
    simpa [prefixWord, tailWord_7192325, baseEnd_7192325] using wordTrace_append hprefix tailTrace_7192325
  have hstable : (prefixWord ++ tailWord_7192325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192325).length < 2 ^ (prefixWord ++ tailWord_7192325).sum := by decide
  have hdescent : baseEnd_7192325 < baseStart_7192325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192332 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 1, 5, 3]
def baseStart_7192332 : Nat := 118140960795 + 7192332 * 2 ^ 59
def prefixEnd_7192332 : Nat := 4983230072969 + 3 ^ 40 * 7192332 * 2
def baseEnd_7192332 : Nat := 3693123342713259201673073

theorem tailTrace_7192332 : CollatzResearch.WordTrace tailWord_7192332 prefixEnd_7192332 3693123342713259201673073 := by
  unfold tailWord_7192332
  simp only [CollatzResearch.WordTrace]
  refine ⟨131162949489708495678285625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174883932652944660904380833 131162949489708495678285625)
  ·
    refine ⟨98372212117281371758714219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131162949489708495678285625 98372212117281371758714219)
    ·
      refine ⟨147558318175922057638071329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98372212117281371758714219 147558318175922057638071329)
      ·
        refine ⟨110668738631941543228553497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147558318175922057638071329 110668738631941543228553497)
        ·
          refine ⟨83001553973956157421415123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110668738631941543228553497 83001553973956157421415123)
          ·
            refine ⟨124502330960934236132122685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83001553973956157421415123 124502330960934236132122685)
            ·
              refine ⟨46688374110350338549546007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124502330960934236132122685 46688374110350338549546007)
              ·
                refine ⟨70032561165525507824319011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46688374110350338549546007 70032561165525507824319011)
                ·
                  refine ⟨105048841748288261736478517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70032561165525507824319011 105048841748288261736478517)
                  ·
                    refine ⟨9848328913902024537794861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105048841748288261736478517 9848328913902024537794861)
                    ·
                      refine ⟨3693123342713259201673073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9848328913902024537794861 3693123342713259201673073)
                      ·
                        rfl

theorem cell23_7192332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_7192332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192332 prefixEnd_7192332 := by exact prefixLift 7192332
  have htrace : WordTrace (prefixWord ++ tailWord_7192332) baseStart_7192332 baseEnd_7192332 := by
    simpa [prefixWord, tailWord_7192332, baseEnd_7192332] using wordTrace_append hprefix tailTrace_7192332
  have hstable : (prefixWord ++ tailWord_7192332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192332).length < 2 ^ (prefixWord ++ tailWord_7192332).sum := by decide
  have hdescent : baseEnd_7192332 < baseStart_7192332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192352 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 1, 7]
def baseStart_7192352 : Nat := 118140960795 + 7192352 * 2 ^ 59
def prefixEnd_7192352 : Nat := 4983230072969 + 3 ^ 40 * 7192352 * 2
def baseEnd_7192352 : Nat := 1231044537442116374474327

theorem tailTrace_7192352 : CollatzResearch.WordTrace tailWord_7192352 prefixEnd_7192352 1231044537442116374474327 := by
  unfold tailWord_7192352
  simp only [CollatzResearch.WordTrace]
  refine ⟨131163314219672267386149655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174884418959563023181532873 131163314219672267386149655)
  ·
    refine ⟨196744971329508401079224483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131163314219672267386149655 196744971329508401079224483)
    ·
      refine ⟨295117456994262601618836725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196744971329508401079224483 295117456994262601618836725)
      ·
        refine ⟨27667261593212118901765943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295117456994262601618836725 27667261593212118901765943)
        ·
          refine ⟨41500892389818178352648915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27667261593212118901765943 41500892389818178352648915)
          ·
            refine ⟨62251338584727267528973373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41500892389818178352648915 62251338584727267528973373)
            ·
              refine ⟨23344251969272725323365015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62251338584727267528973373 23344251969272725323365015)
              ·
                refine ⟨35016377953909087985047523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23344251969272725323365015 35016377953909087985047523)
                ·
                  refine ⟨52524566930863631977571285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35016377953909087985047523 52524566930863631977571285)
                  ·
                    refine ⟨1231044537442116374474327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52524566930863631977571285 1231044537442116374474327)
                    ·
                      rfl

theorem cell23_7192352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_7192352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192352 prefixEnd_7192352 := by exact prefixLift 7192352
  have htrace : WordTrace (prefixWord ++ tailWord_7192352) baseStart_7192352 baseEnd_7192352 := by
    simpa [prefixWord, tailWord_7192352, baseEnd_7192352] using wordTrace_append hprefix tailTrace_7192352
  have hstable : (prefixWord ++ tailWord_7192352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192352).length < 2 ^ (prefixWord ++ tailWord_7192352).sum := by decide
  have hdescent : baseEnd_7192352 < baseStart_7192352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192356 : List Nat := [2, 3, 1, 3, 2, 2, 2, 3, 5]
def baseStart_7192356 : Nat := 118140960795 + 7192356 * 2 ^ 59
def prefixEnd_7192356 : Nat := 4983230072969 + 3 ^ 40 * 7192356 * 2
def baseEnd_7192356 : Nat := 410348407360996345308107

theorem tailTrace_7192356 : CollatzResearch.WordTrace tailWord_7192356 prefixEnd_7192356 410348407360996345308107 := by
  unfold tailWord_7192356
  simp only [CollatzResearch.WordTrace]
  refine ⟨131163387165665021727722461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174884516220886695636963281 131163387165665021727722461)
  ·
    refine ⟨49186270187124383147895923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131163387165665021727722461 49186270187124383147895923)
    ·
      refine ⟨73779405280686574721843885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49186270187124383147895923 73779405280686574721843885)
      ·
        refine ⟨27667276980257465520691457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73779405280686574721843885 27667276980257465520691457)
        ·
          refine ⟨20750457735193099140518593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27667276980257465520691457 20750457735193099140518593)
          ·
            refine ⟨15562843301394824355388945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20750457735193099140518593 15562843301394824355388945)
            ·
              refine ⟨11672132476046118266541709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15562843301394824355388945 11672132476046118266541709)
              ·
                refine ⟨4377049678517294349953141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11672132476046118266541709 4377049678517294349953141)
                ·
                  refine ⟨410348407360996345308107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4377049678517294349953141 410348407360996345308107)
                  ·
                    rfl

theorem cell23_7192356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_7192356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192356 prefixEnd_7192356 := by exact prefixLift 7192356
  have htrace : WordTrace (prefixWord ++ tailWord_7192356) baseStart_7192356 baseEnd_7192356 := by
    simpa [prefixWord, tailWord_7192356, baseEnd_7192356] using wordTrace_append hprefix tailTrace_7192356
  have hstable : (prefixWord ++ tailWord_7192356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192356).length < 2 ^ (prefixWord ++ tailWord_7192356).sum := by decide
  have hdescent : baseEnd_7192356 < baseStart_7192356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192389 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 2, 4, 2]
def baseStart_7192389 : Nat := 118140960795 + 7192389 * 2 ^ 59
def prefixEnd_7192389 : Nat := 4983230072969 + 3 ^ 40 * 7192389 * 2
def baseEnd_7192389 : Nat := 3693152611110565478660311

theorem tailTrace_7192389 : CollatzResearch.WordTrace tailWord_7192389 prefixEnd_7192389 3693152611110565478660311 := by
  unfold tailWord_7192389
  simp only [CollatzResearch.WordTrace]
  refine ⟨262327977940210490091396221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174885318626806993394264147 262327977940210490091396221)
  ·
    refine ⟨98372991727578933784273583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262327977940210490091396221 98372991727578933784273583)
    ·
      refine ⟨147559487591368400676410375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98372991727578933784273583 147559487591368400676410375)
      ·
        refine ⟨221339231387052601014615563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147559487591368400676410375 221339231387052601014615563)
        ·
          refine ⟨332008847080578901521923345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221339231387052601014615563 332008847080578901521923345)
          ·
            refine ⟨249006635310434176141442509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332008847080578901521923345 249006635310434176141442509)
            ·
              refine ⟨93377488241412816053040941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249006635310434176141442509 93377488241412816053040941)
              ·
                refine ⟨35016558090529806019890353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93377488241412816053040941 35016558090529806019890353)
                ·
                  refine ⟨26262418567897354514917765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35016558090529806019890353 26262418567897354514917765)
                  ·
                    refine ⟨4924203481480753971547081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26262418567897354514917765 4924203481480753971547081)
                    ·
                      refine ⟨3693152611110565478660311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4924203481480753971547081 3693152611110565478660311)
                      ·
                        rfl

theorem cell23_7192389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 4, 2].length) (baseStart_7192389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192389 prefixEnd_7192389 := by exact prefixLift 7192389
  have htrace : WordTrace (prefixWord ++ tailWord_7192389) baseStart_7192389 baseEnd_7192389 := by
    simpa [prefixWord, tailWord_7192389, baseEnd_7192389] using wordTrace_append hprefix tailTrace_7192389
  have hstable : (prefixWord ++ tailWord_7192389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192389).length < 2 ^ (prefixWord ++ tailWord_7192389).sum := by decide
  have hdescent : baseEnd_7192389 < baseStart_7192389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192409 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 2, 2, 3]
def baseStart_7192409 : Nat := 118140960795 + 7192409 * 2 ^ 59
def prefixEnd_7192409 : Nat := 4983230072969 + 3 ^ 40 * 7192409 * 2
def baseEnd_7192409 : Nat := 3693162880723655400410219

theorem tailTrace_7192409 : CollatzResearch.WordTrace tailWord_7192409 prefixEnd_7192409 3693162880723655400410219 := by
  unfold tailWord_7192409
  simp only [CollatzResearch.WordTrace]
  refine ⟨262328707400138033507124281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174885804933425355671416187 262328707400138033507124281)
  ·
    refine ⟨196746530550103525130343211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262328707400138033507124281 196746530550103525130343211)
    ·
      refine ⟨295119795825155287695514817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196746530550103525130343211 295119795825155287695514817)
      ·
        refine ⟨221339846868866465771636113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295119795825155287695514817 221339846868866465771636113)
        ·
          refine ⟨166004885151649849328727085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221339846868866465771636113 166004885151649849328727085)
          ·
            refine ⟨62251831931868693498272657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166004885151649849328727085 62251831931868693498272657)
            ·
              refine ⟨46688873948901520123704493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62251831931868693498272657 46688873948901520123704493)
              ·
                refine ⟨17508327730838070046389185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46688873948901520123704493 17508327730838070046389185)
                ·
                  refine ⟨13131245798128552534791889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17508327730838070046389185 13131245798128552534791889)
                  ·
                    refine ⟨9848434348596414401093917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13131245798128552534791889 9848434348596414401093917)
                    ·
                      refine ⟨3693162880723655400410219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9848434348596414401093917 3693162880723655400410219)
                      ·
                        rfl

theorem cell23_7192409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_7192409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192409 prefixEnd_7192409 := by exact prefixLift 7192409
  have htrace : WordTrace (prefixWord ++ tailWord_7192409) baseStart_7192409 baseEnd_7192409 := by
    simpa [prefixWord, tailWord_7192409, baseEnd_7192409] using wordTrace_append hprefix tailTrace_7192409
  have hstable : (prefixWord ++ tailWord_7192409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192409).length < 2 ^ (prefixWord ++ tailWord_7192409).sum := by decide
  have hdescent : baseEnd_7192409 < baseStart_7192409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192433 : List Nat := [1, 2, 2, 2, 1, 3, 5, 2, 1, 4]
def baseStart_7192433 : Nat := 118140960795 + 7192433 * 2 ^ 59
def prefixEnd_7192433 : Nat := 4983230072969 + 3 ^ 40 * 7192433 * 2
def baseEnd_7192433 : Nat := 1231058401419787768836703

theorem tailTrace_7192433 : CollatzResearch.WordTrace tailWord_7192433 prefixEnd_7192433 1231058401419787768836703 := by
  unfold tailWord_7192433
  simp only [CollatzResearch.WordTrace]
  refine ⟨262329582752051085605997953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174886388501367390403998635 262329582752051085605997953)
  ·
    refine ⟨196747187064038314204498465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262329582752051085605997953 196747187064038314204498465)
    ·
      refine ⟨147560390298028735653373849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196747187064038314204498465 147560390298028735653373849)
      ·
        refine ⟨110670292723521551740030387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147560390298028735653373849 110670292723521551740030387)
        ·
          refine ⟨166005439085282327610045581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110670292723521551740030387 166005439085282327610045581)
          ·
            refine ⟨62252039656980872853767093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166005439085282327610045581 62252039656980872853767093)
            ·
              refine ⟨5836128717841956830040665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62252039656980872853767093 5836128717841956830040665)
              ·
                refine ⟨4377096538381467622530499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5836128717841956830040665 4377096538381467622530499)
                ·
                  refine ⟨6565644807572201433795749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4377096538381467622530499 6565644807572201433795749)
                  ·
                    refine ⟨1231058401419787768836703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6565644807572201433795749 1231058401419787768836703)
                    ·
                      rfl

theorem cell23_7192433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_7192433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192433 prefixEnd_7192433 := by exact prefixLift 7192433
  have htrace : WordTrace (prefixWord ++ tailWord_7192433) baseStart_7192433 baseEnd_7192433 := by
    simpa [prefixWord, tailWord_7192433, baseEnd_7192433] using wordTrace_append hprefix tailTrace_7192433
  have hstable : (prefixWord ++ tailWord_7192433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192433).length < 2 ^ (prefixWord ++ tailWord_7192433).sum := by decide
  have hdescent : baseEnd_7192433 < baseStart_7192433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192496 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 9, 2, 2]
def baseStart_7192496 : Nat := 118140960795 + 7192496 * 2 ^ 59
def prefixEnd_7192496 : Nat := 4983230072969 + 3 ^ 40 * 7192496 * 2
def baseEnd_7192496 : Nat := 3693207553540596560022319

theorem tailTrace_7192496 : CollatzResearch.WordTrace tailWord_7192496 prefixEnd_7192496 3693207553540596560022319 := by
  unfold tailWord_7192496
  simp only [CollatzResearch.WordTrace]
  refine ⟨131165940275411423682770671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174887920367215231577027561 131165940275411423682770671)
  ·
    refine ⟨196748910413117135524156007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131165940275411423682770671 196748910413117135524156007)
    ·
      refine ⟨295123365619675703286234011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196748910413117135524156007 295123365619675703286234011)
      ·
        refine ⟨442685048429513554929351017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295123365619675703286234011 442685048429513554929351017)
        ·
          refine ⟨332013786322135166197013263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442685048429513554929351017 332013786322135166197013263)
          ·
            refine ⟨498020679483202749295519895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332013786322135166197013263 498020679483202749295519895)
            ·
              refine ⟨747031019224804123943279843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498020679483202749295519895 747031019224804123943279843)
              ·
                refine ⟨1120546528837206185914919765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747031019224804123943279843 1120546528837206185914919765)
                ·
                  refine ⟨6565702317405504995595233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1120546528837206185914919765 6565702317405504995595233)
                  ·
                    refine ⟨4924276738054128746696425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6565702317405504995595233 4924276738054128746696425)
                    ·
                      refine ⟨3693207553540596560022319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4924276738054128746696425 3693207553540596560022319)
                      ·
                        rfl

theorem cell23_7192496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 2, 2].length) (baseStart_7192496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192496 prefixEnd_7192496 := by exact prefixLift 7192496
  have htrace : WordTrace (prefixWord ++ tailWord_7192496) baseStart_7192496 baseEnd_7192496 := by
    simpa [prefixWord, tailWord_7192496, baseEnd_7192496] using wordTrace_append hprefix tailTrace_7192496
  have hstable : (prefixWord ++ tailWord_7192496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192496).length < 2 ^ (prefixWord ++ tailWord_7192496).sum := by decide
  have hdescent : baseEnd_7192496 < baseStart_7192496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192499 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 3]
def baseStart_7192499 : Nat := 118140960795 + 7192499 * 2 ^ 59
def prefixEnd_7192499 : Nat := 4983230072969 + 3 ^ 40 * 7192499 * 2
def baseEnd_7192499 : Nat := 3693209093982560048284805

theorem tailTrace_7192499 : CollatzResearch.WordTrace tailWord_7192499 prefixEnd_7192499 3693209093982560048284805 := by
  unfold tailWord_7192499
  simp only [CollatzResearch.WordTrace]
  refine ⟨262331989969811978877900551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174887993313207985918600367 262331989969811978877900551)
  ·
    refine ⟨393497984954717968316850827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262331989969811978877900551 393497984954717968316850827)
    ·
      refine ⟨590246977432076952475276241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393497984954717968316850827 590246977432076952475276241)
      ·
        refine ⟨442685233074057714356457181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590246977432076952475276241 442685233074057714356457181)
        ·
          refine ⟨166006962402771642883671443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442685233074057714356457181 166006962402771642883671443)
          ·
            refine ⟨249010443604157464325507165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166006962402771642883671443 249010443604157464325507165)
            ·
              refine ⟨93378916351559049122065187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249010443604157464325507165 93378916351559049122065187)
              ·
                refine ⟨140068374527338573683097781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93378916351559049122065187 140068374527338573683097781)
                ·
                  refine ⟨13131410111937991282790417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140068374527338573683097781 13131410111937991282790417)
                  ·
                    refine ⟨9848557583953493462092813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13131410111937991282790417 9848557583953493462092813)
                    ·
                      refine ⟨3693209093982560048284805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9848557583953493462092813 3693209093982560048284805)
                      ·
                        rfl

theorem cell23_7192499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 3].length) (baseStart_7192499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192499 prefixEnd_7192499 := by exact prefixLift 7192499
  have htrace : WordTrace (prefixWord ++ tailWord_7192499) baseStart_7192499 baseEnd_7192499 := by
    simpa [prefixWord, tailWord_7192499, baseEnd_7192499] using wordTrace_append hprefix tailTrace_7192499
  have hstable : (prefixWord ++ tailWord_7192499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192499).length < 2 ^ (prefixWord ++ tailWord_7192499).sum := by decide
  have hdescent : baseEnd_7192499 < baseStart_7192499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192529 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 3, 3, 3]
def baseStart_7192529 : Nat := 118140960795 + 7192529 * 2 ^ 59
def prefixEnd_7192529 : Nat := 4983230072969 + 3 ^ 40 * 7192529 * 2
def baseEnd_7192529 : Nat := 3693224498402194930909667

theorem tailTrace_7192529 : CollatzResearch.WordTrace tailWord_7192529 prefixEnd_7192529 3693224498402194930909667 := by
  unfold tailWord_7192529
  simp only [CollatzResearch.WordTrace]
  refine ⟨262333084159703294001492641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174888722773135529334328427 262333084159703294001492641)
  ·
    refine ⟨196749813119777470501119481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262333084159703294001492641 196749813119777470501119481)
    ·
      refine ⟨147562359839833102875839611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196749813119777470501119481 147562359839833102875839611)
      ·
        refine ⟨221343539759749654313759417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147562359839833102875839611 221343539759749654313759417)
        ·
          refine ⟨166007654819812240735319563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221343539759749654313759417 166007654819812240735319563)
          ·
            refine ⟨249011482229718361102979345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166007654819812240735319563 249011482229718361102979345)
            ·
              refine ⟨186758611672288770827234509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249011482229718361102979345 186758611672288770827234509)
              ·
                refine ⟨70034479377108289060212941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186758611672288770827234509 70034479377108289060212941)
                ·
                  refine ⟨26262929766415608397579853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70034479377108289060212941 26262929766415608397579853)
                  ·
                    refine ⟨9848598662405853149092445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26262929766415608397579853 9848598662405853149092445)
                    ·
                      refine ⟨3693224498402194930909667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9848598662405853149092445 3693224498402194930909667)
                      ·
                        rfl

theorem cell23_7192529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_7192529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192529 prefixEnd_7192529 := by exact prefixLift 7192529
  have htrace : WordTrace (prefixWord ++ tailWord_7192529) baseStart_7192529 baseEnd_7192529 := by
    simpa [prefixWord, tailWord_7192529, baseEnd_7192529] using wordTrace_append hprefix tailTrace_7192529
  have hstable : (prefixWord ++ tailWord_7192529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192529).length < 2 ^ (prefixWord ++ tailWord_7192529).sum := by decide
  have hdescent : baseEnd_7192529 < baseStart_7192529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192533 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_7192533 : Nat := 118140960795 + 7192533 * 2 ^ 59
def prefixEnd_7192533 : Nat := 4983230072969 + 3 ^ 40 * 7192533 * 2
def baseEnd_7192533 : Nat := 3693226552324812915259649

theorem tailTrace_7192533 : CollatzResearch.WordTrace tailWord_7192533 prefixEnd_7192533 3693226552324812915259649 := by
  unfold tailWord_7192533
  simp only [CollatzResearch.WordTrace]
  refine ⟨262333230051688802684638253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174888820034459201789758835 262333230051688802684638253)
  ·
    refine ⟨98374961269383301006739345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262333230051688802684638253 98374961269383301006739345)
    ·
      refine ⟨73781220952037475755054509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98374961269383301006739345 73781220952037475755054509)
      ·
        refine ⟨27667957857014053408145441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73781220952037475755054509 27667957857014053408145441)
        ·
          refine ⟨20750968392760540056109081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27667957857014053408145441 20750968392760540056109081)
          ·
            refine ⟨15563226294570405042081811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20750968392760540056109081 15563226294570405042081811)
            ·
              refine ⟨23344839441855607563122717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15563226294570405042081811 23344839441855607563122717)
              ·
                refine ⟨8754314790695852836171019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23344839441855607563122717 8754314790695852836171019)
                ·
                  refine ⟨13131472186043779254256529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8754314790695852836171019 13131472186043779254256529)
                  ·
                    refine ⟨9848604139532834440692397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13131472186043779254256529 9848604139532834440692397)
                    ·
                      refine ⟨3693226552324812915259649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9848604139532834440692397 3693226552324812915259649)
                      ·
                        rfl

theorem cell23_7192533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_7192533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192533 prefixEnd_7192533 := by exact prefixLift 7192533
  have htrace : WordTrace (prefixWord ++ tailWord_7192533) baseStart_7192533 baseEnd_7192533 := by
    simpa [prefixWord, tailWord_7192533, baseEnd_7192533] using wordTrace_append hprefix tailTrace_7192533
  have hstable : (prefixWord ++ tailWord_7192533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192533).length < 2 ^ (prefixWord ++ tailWord_7192533).sum := by decide
  have hdescent : baseEnd_7192533 < baseStart_7192533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192556 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 5, 3, 2]
def baseStart_7192556 : Nat := 118140960795 + 7192556 * 2 ^ 59
def prefixEnd_7192556 : Nat := 4983230072969 + 3 ^ 40 * 7192556 * 2
def baseEnd_7192556 : Nat := 3693238362379866325272043

theorem tailTrace_7192556 : CollatzResearch.WordTrace tailWord_7192556 prefixEnd_7192556 3693238362379866325272043 := by
  unfold tailWord_7192556
  simp only [CollatzResearch.WordTrace]
  refine ⟨131167034465302738806362761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174889379287070318408483681 131167034465302738806362761)
  ·
    refine ⟨98375275848977054104772071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131167034465302738806362761 98375275848977054104772071)
    ·
      refine ⟨147562913773465581157158107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98375275848977054104772071 147562913773465581157158107)
      ·
        refine ⟨221344370660198371735737161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147562913773465581157158107 221344370660198371735737161)
        ·
          refine ⟨166008277995148778801802871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221344370660198371735737161 166008277995148778801802871)
          ·
            refine ⟨249012416992723168202704307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166008277995148778801802871 249012416992723168202704307)
            ·
              refine ⟨373518625489084752304056461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249012416992723168202704307 373518625489084752304056461)
              ·
                refine ⟨140069484558406782114021173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373518625489084752304056461 140069484558406782114021173)
                ·
                  refine ⟨13131514177350635823189485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140069484558406782114021173 13131514177350635823189485)
                  ·
                    refine ⟨4924317816506488433696057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13131514177350635823189485 4924317816506488433696057)
                    ·
                      refine ⟨3693238362379866325272043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4924317816506488433696057 3693238362379866325272043)
                      ·
                        rfl

theorem cell23_7192556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 3, 2].length) (baseStart_7192556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192556 prefixEnd_7192556 := by exact prefixLift 7192556
  have htrace : WordTrace (prefixWord ++ tailWord_7192556) baseStart_7192556 baseEnd_7192556 := by
    simpa [prefixWord, tailWord_7192556, baseEnd_7192556] using wordTrace_append hprefix tailTrace_7192556
  have hstable : (prefixWord ++ tailWord_7192556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192556).length < 2 ^ (prefixWord ++ tailWord_7192556).sum := by decide
  have hdescent : baseEnd_7192556 < baseStart_7192556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192557 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_7192557 : Nat := 118140960795 + 7192557 * 2 ^ 59
def prefixEnd_7192557 : Nat := 4983230072969 + 3 ^ 40 * 7192557 * 2
def baseEnd_7192557 : Nat := 1231079625286840273786513

theorem tailTrace_7192557 : CollatzResearch.WordTrace tailWord_7192557 prefixEnd_7192557 1231079625286840273786513 := by
  unfold tailWord_7192557
  simp only [CollatzResearch.WordTrace]
  refine ⟨262334105403601854783511925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174889403602401236522341283 262334105403601854783511925)
  ·
    refine ⟨24593822381587673885954243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262334105403601854783511925 24593822381587673885954243)
    ·
      refine ⟨36890733572381510828931365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24593822381587673885954243 36890733572381510828931365)
      ·
        refine ⟨6917012544821533280424631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36890733572381510828931365 6917012544821533280424631)
        ·
          refine ⟨10375518817232299920636947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6917012544821533280424631 10375518817232299920636947)
          ·
            refine ⟨15563278225848449880955421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10375518817232299920636947 15563278225848449880955421)
            ·
              refine ⟨5836229334693168705358283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15563278225848449880955421 5836229334693168705358283)
              ·
                refine ⟨8754344002039753058037425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5836229334693168705358283 8754344002039753058037425)
                ·
                  refine ⟨6565758001529814793528069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8754344002039753058037425 6565758001529814793528069)
                  ·
                    refine ⟨1231079625286840273786513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6565758001529814793528069 1231079625286840273786513)
                    ·
                      rfl

theorem cell23_7192557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_7192557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192557 prefixEnd_7192557 := by exact prefixLift 7192557
  have htrace : WordTrace (prefixWord ++ tailWord_7192557) baseStart_7192557 baseEnd_7192557 := by
    simpa [prefixWord, tailWord_7192557, baseEnd_7192557] using wordTrace_append hprefix tailTrace_7192557
  have hstable : (prefixWord ++ tailWord_7192557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192557).length < 2 ^ (prefixWord ++ tailWord_7192557).sum := by decide
  have hdescent : baseEnd_7192557 < baseStart_7192557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192573 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 1, 3, 2]
def baseStart_7192573 : Nat := 118140960795 + 7192573 * 2 ^ 59
def prefixEnd_7192573 : Nat := 4983230072969 + 3 ^ 40 * 7192573 * 2
def baseEnd_7192573 : Nat := 3693247091550992758759465

theorem tailTrace_7192573 : CollatzResearch.WordTrace tailWord_7192573 prefixEnd_7192573 3693247091550992758759465 := by
  unfold tailWord_7192573
  simp only [CollatzResearch.WordTrace]
  refine ⟨262334688971543889516094373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174889792647695926344062915 262334688971543889516094373)
  ·
    refine ⟨49187754182164479284267695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262334688971543889516094373 49187754182164479284267695)
    ·
      refine ⟨73781631273246718926401543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49187754182164479284267695 73781631273246718926401543)
      ·
        refine ⟨110672446909870078389602315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73781631273246718926401543 110672446909870078389602315)
        ·
          refine ⟨166008670364805117584403473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110672446909870078389602315 166008670364805117584403473)
          ·
            refine ⟨124506502773603838188302605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166008670364805117584403473 124506502773603838188302605)
            ·
              refine ⟨46689938540101439320613477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124506502773603838188302605 46689938540101439320613477)
              ·
                refine ⟨8754363476269019872615027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46689938540101439320613477 8754363476269019872615027)
                ·
                  refine ⟨13131545214403529808922541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8754363476269019872615027 13131545214403529808922541)
                  ·
                    refine ⟨4924329455401323678345953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13131545214403529808922541 4924329455401323678345953)
                    ·
                      refine ⟨3693247091550992758759465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4924329455401323678345953 3693247091550992758759465)
                      ·
                        rfl

theorem cell23_7192573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_7192573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192573 prefixEnd_7192573 := by exact prefixLift 7192573
  have htrace : WordTrace (prefixWord ++ tailWord_7192573) baseStart_7192573 baseEnd_7192573 := by
    simpa [prefixWord, tailWord_7192573, baseEnd_7192573] using wordTrace_append hprefix tailTrace_7192573
  have hstable : (prefixWord ++ tailWord_7192573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192573).length < 2 ^ (prefixWord ++ tailWord_7192573).sum := by decide
  have hdescent : baseEnd_7192573 < baseStart_7192573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192639 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 1, 7]
def baseStart_7192639 : Nat := 118140960795 + 7192639 * 2 ^ 59
def prefixEnd_7192639 : Nat := 4983230072969 + 3 ^ 40 * 7192639 * 2
def baseEnd_7192639 : Nat := 1231093660424729833511387

theorem tailTrace_7192639 : CollatzResearch.WordTrace tailWord_7192639 prefixEnd_7192639 1231093660424729833511387 := by
  unfold tailWord_7192639
  simp only [CollatzResearch.WordTrace]
  refine ⟨262337096189304782787996971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174891397459536521858664647 262337096189304782787996971)
  ·
    refine ⟨393505644283957174181995457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262337096189304782787996971 393505644283957174181995457)
    ·
      refine ⟨295129233212967880636496593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393505644283957174181995457 295129233212967880636496593)
      ·
        refine ⟨221346924909725910477372445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295129233212967880636496593 221346924909725910477372445)
        ·
          refine ⟨83005096841147216429014667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221346924909725910477372445 83005096841147216429014667)
          ·
            refine ⟨124507645261720824643522001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83005096841147216429014667 124507645261720824643522001)
            ·
              refine ⟨93380733946290618482641501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124507645261720824643522001 93380733946290618482641501)
              ·
                refine ⟨35017775229858981930990563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93380733946290618482641501 35017775229858981930990563)
                ·
                  refine ⟨52526662844788472896485845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35017775229858981930990563 52526662844788472896485845)
                  ·
                    refine ⟨1231093660424729833511387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52526662844788472896485845 1231093660424729833511387)
                    ·
                      rfl

theorem cell23_7192639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_7192639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192639 prefixEnd_7192639 := by exact prefixLift 7192639
  have htrace : WordTrace (prefixWord ++ tailWord_7192639) baseStart_7192639 baseEnd_7192639 := by
    simpa [prefixWord, tailWord_7192639, baseEnd_7192639] using wordTrace_append hprefix tailTrace_7192639
  have hstable : (prefixWord ++ tailWord_7192639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192639).length < 2 ^ (prefixWord ++ tailWord_7192639).sum := by decide
  have hdescent : baseEnd_7192639 < baseStart_7192639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192649 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_7192649 : Nat := 118140960795 + 7192649 * 2 ^ 59
def prefixEnd_7192649 : Nat := 4983230072969 + 3 ^ 40 * 7192649 * 2
def baseEnd_7192649 : Nat := 3693286116080734461409115

theorem tailTrace_7192649 : CollatzResearch.WordTrace tailWord_7192649 prefixEnd_7192649 3693286116080734461409115 := by
  unfold tailWord_7192649
  simp only [CollatzResearch.WordTrace]
  refine ⟨262337460919268554495861001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174891640612845702997240667 262337460919268554495861001)
  ·
    refine ⟨196753095689451415871895751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262337460919268554495861001 196753095689451415871895751)
    ·
      refine ⟨295129643534177123807843627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196753095689451415871895751 295129643534177123807843627)
      ·
        refine ⟨442694465301265685711765441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295129643534177123807843627 442694465301265685711765441)
        ·
          refine ⟨332020848975949264283824081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442694465301265685711765441 332020848975949264283824081)
          ·
            refine ⟨249015636731961948212868061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332020848975949264283824081 249015636731961948212868061)
            ·
              refine ⟨93380863774485730579825523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249015636731961948212868061 93380863774485730579825523)
              ·
                refine ⟨140071295661728595869738285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93380863774485730579825523 140071295661728595869738285)
                ·
                  refine ⟨52526735873148223451151857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140071295661728595869738285 52526735873148223451151857)
                  ·
                    refine ⟨39395051904861167588363893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52526735873148223451151857 39395051904861167588363893)
                    ·
                      refine ⟨3693286116080734461409115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39395051904861167588363893 3693286116080734461409115)
                      ·
                        rfl

theorem cell23_7192649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_7192649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192649 prefixEnd_7192649 := by exact prefixLift 7192649
  have htrace : WordTrace (prefixWord ++ tailWord_7192649) baseStart_7192649 baseEnd_7192649 := by
    simpa [prefixWord, tailWord_7192649, baseEnd_7192649] using wordTrace_append hprefix tailTrace_7192649
  have hstable : (prefixWord ++ tailWord_7192649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192649).length < 2 ^ (prefixWord ++ tailWord_7192649).sum := by decide
  have hdescent : baseEnd_7192649 < baseStart_7192649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192653 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_7192653 : Nat := 118140960795 + 7192653 * 2 ^ 59
def prefixEnd_7192653 : Nat := 4983230072969 + 3 ^ 40 * 7192653 * 2
def baseEnd_7192653 : Nat := 3693288170003352445759097

theorem tailTrace_7192653 : CollatzResearch.WordTrace tailWord_7192653 prefixEnd_7192653 3693288170003352445759097 := by
  unfold tailWord_7192653
  simp only [CollatzResearch.WordTrace]
  refine ⟨262337606811254063179006613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174891737874169375452671075 262337606811254063179006613)
  ·
    refine ⟨12297075319277534211515935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 262337606811254063179006613 12297075319277534211515935)
    ·
      refine ⟨18445612978916301317273903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12297075319277534211515935 18445612978916301317273903)
      ·
        refine ⟨27668419468374451975910855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18445612978916301317273903 27668419468374451975910855)
        ·
          refine ⟨41502629202561677963866283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27668419468374451975910855 41502629202561677963866283)
          ·
            refine ⟨62253943803842516945799425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41502629202561677963866283 62253943803842516945799425)
            ·
              refine ⟨46690457852881887709349569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62253943803842516945799425 46690457852881887709349569)
              ·
                refine ⟨35017843389661415782012177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46690457852881887709349569 35017843389661415782012177)
                ·
                  refine ⟨26263382542246061836509133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35017843389661415782012177 26263382542246061836509133)
                  ·
                    refine ⟨9848768453342273188690925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26263382542246061836509133 9848768453342273188690925)
                    ·
                      refine ⟨3693288170003352445759097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9848768453342273188690925 3693288170003352445759097)
                      ·
                        rfl

theorem cell23_7192653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_7192653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192653 prefixEnd_7192653 := by exact prefixLift 7192653
  have htrace : WordTrace (prefixWord ++ tailWord_7192653) baseStart_7192653 baseEnd_7192653 := by
    simpa [prefixWord, tailWord_7192653, baseEnd_7192653] using wordTrace_append hprefix tailTrace_7192653
  have hstable : (prefixWord ++ tailWord_7192653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192653).length < 2 ^ (prefixWord ++ tailWord_7192653).sum := by decide
  have hdescent : baseEnd_7192653 < baseStart_7192653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192676 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_7192676 : Nat := 118140960795 + 7192676 * 2 ^ 59
def prefixEnd_7192676 : Nat := 4983230072969 + 3 ^ 40 * 7192676 * 2
def baseEnd_7192676 : Nat := 3693299980058405855771491

theorem tailTrace_7192676 : CollatzResearch.WordTrace tailWord_7192676 prefixEnd_7192676 3693299980058405855771491 := by
  unfold tailWord_7192676
  simp only [CollatzResearch.WordTrace]
  refine ⟨131169222845085369053546941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174892297126780492071395921 131169222845085369053546941)
  ·
    refine ⟨49188458566907013395080103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131169222845085369053546941 49188458566907013395080103)
    ·
      refine ⟨73782687850360520092620155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49188458566907013395080103 73782687850360520092620155)
      ·
        refine ⟨110674031775540780138930233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73782687850360520092620155 110674031775540780138930233)
        ·
          refine ⟨83005523831655585104197675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110674031775540780138930233 83005523831655585104197675)
          ·
            refine ⟨124508285747483377656296513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83005523831655585104197675 124508285747483377656296513)
            ·
              refine ⟨93381214310612533242222385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124508285747483377656296513 93381214310612533242222385)
              ·
                refine ⟨70035910732959399931666789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93381214310612533242222385 70035910732959399931666789)
                ·
                  refine ⟨13131733262429887487187523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70035910732959399931666789 13131733262429887487187523)
                  ·
                    refine ⟨19697599893644831230781285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13131733262429887487187523 19697599893644831230781285)
                    ·
                      refine ⟨3693299980058405855771491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19697599893644831230781285 3693299980058405855771491)
                      ·
                        rfl

theorem cell23_7192676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_7192676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192676 prefixEnd_7192676 := by exact prefixLift 7192676
  have htrace : WordTrace (prefixWord ++ tailWord_7192676) baseStart_7192676 baseEnd_7192676 := by
    simpa [prefixWord, tailWord_7192676, baseEnd_7192676] using wordTrace_append hprefix tailTrace_7192676
  have hstable : (prefixWord ++ tailWord_7192676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192676).length < 2 ^ (prefixWord ++ tailWord_7192676).sum := by decide
  have hdescent : baseEnd_7192676 < baseStart_7192676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192797 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_7192797 : Nat := 118140960795 + 7192797 * 2 ^ 59
def prefixEnd_7192797 : Nat := 4983230072969 + 3 ^ 40 * 7192797 * 2
def baseEnd_7192797 : Nat := 1231120703739199960786145

theorem tailTrace_7192797 : CollatzResearch.WordTrace tailWord_7192797 prefixEnd_7192797 1231120703739199960786145 := by
  unfold tailWord_7192797
  simp only [CollatzResearch.WordTrace]
  refine ⟨262342858922732375772248645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174895239281821583848165763 262342858922732375772248645)
  ·
    refine ⟨49189286048012320457296621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262342858922732375772248645 49189286048012320457296621)
    ·
      refine ⟨18445982268004620171486233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49189286048012320457296621 18445982268004620171486233)
      ·
        refine ⟨13834486701003465128614675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18445982268004620171486233 13834486701003465128614675)
        ·
          refine ⟨20751730051505197692922013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13834486701003465128614675 20751730051505197692922013)
          ·
            refine ⟨7781898769314449134845755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20751730051505197692922013 7781898769314449134845755)
            ·
              refine ⟨11672848153971673702268633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7781898769314449134845755 11672848153971673702268633)
              ·
                refine ⟨8754636115478755276701475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11672848153971673702268633 8754636115478755276701475)
                ·
                  refine ⟨13131954173218132915052213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8754636115478755276701475 13131954173218132915052213)
                  ·
                    refine ⟨1231120703739199960786145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13131954173218132915052213 1231120703739199960786145)
                    ·
                      rfl

theorem cell23_7192797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_7192797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192797 prefixEnd_7192797 := by exact prefixLift 7192797
  have htrace : WordTrace (prefixWord ++ tailWord_7192797) baseStart_7192797 baseEnd_7192797 := by
    simpa [prefixWord, tailWord_7192797, baseEnd_7192797] using wordTrace_append hprefix tailTrace_7192797
  have hstable : (prefixWord ++ tailWord_7192797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192797).length < 2 ^ (prefixWord ++ tailWord_7192797).sum := by decide
  have hdescent : baseEnd_7192797 < baseStart_7192797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192800 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 5, 2, 2]
def baseStart_7192800 : Nat := 118140960795 + 7192800 * 2 ^ 59
def prefixEnd_7192800 : Nat := 4983230072969 + 3 ^ 40 * 7192800 * 2
def baseEnd_7192800 : Nat := 3693363651659563370620921

theorem tailTrace_7192800 : CollatzResearch.WordTrace tailWord_7192800 prefixEnd_7192800 3693363651659563370620921 := by
  unfold tailWord_7192800
  simp only [CollatzResearch.WordTrace]
  refine ⟨131171484170860753642303927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174895312227814338189738569 131171484170860753642303927)
  ·
    refine ⟨196757226256291130463455891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131171484170860753642303927 196757226256291130463455891)
    ·
      refine ⟨295135839384436695695183837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196757226256291130463455891 295135839384436695695183837)
      ·
        refine ⟨110675939769163760885693939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295135839384436695695183837 110675939769163760885693939)
        ·
          refine ⟨166013909653745641328540909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110675939769163760885693939 166013909653745641328540909)
          ·
            refine ⟨62255216120154615498202841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166013909653745641328540909 62255216120154615498202841)
            ·
              refine ⟨46691412090115961623652131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62255216120154615498202841 46691412090115961623652131)
              ·
                refine ⟨70037118135173942435478197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46691412090115961623652131 70037118135173942435478197)
                ·
                  refine ⟨6565979825172557103326081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70037118135173942435478197 6565979825172557103326081)
                  ·
                    refine ⟨4924484868879417827494561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6565979825172557103326081 4924484868879417827494561)
                    ·
                      refine ⟨3693363651659563370620921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4924484868879417827494561 3693363651659563370620921)
                      ·
                        rfl

theorem cell23_7192800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_7192800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192800 prefixEnd_7192800 := by exact prefixLift 7192800
  have htrace : WordTrace (prefixWord ++ tailWord_7192800) baseStart_7192800 baseEnd_7192800 := by
    simpa [prefixWord, tailWord_7192800, baseEnd_7192800] using wordTrace_append hprefix tailTrace_7192800
  have hstable : (prefixWord ++ tailWord_7192800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192800).length < 2 ^ (prefixWord ++ tailWord_7192800).sum := by decide
  have hdescent : baseEnd_7192800 < baseStart_7192800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192833 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_7192833 : Nat := 118140960795 + 7192833 * 2 ^ 59
def prefixEnd_7192833 : Nat := 4983230072969 + 3 ^ 40 * 7192833 * 2
def baseEnd_7192833 : Nat := 3693380596521161741508269

theorem tailTrace_7192833 : CollatzResearch.WordTrace tailWord_7192833 prefixEnd_7192833 3693380596521161741508269 := by
  unfold tailWord_7192833
  simp only [CollatzResearch.WordTrace]
  refine ⟨262344171950601953920559153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174896114633734635947039435 262344171950601953920559153)
  ·
    refine ⟨196758128962951465440419365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262344171950601953920559153 196758128962951465440419365)
    ·
      refine ⟨36892149180553399770078631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196758128962951465440419365 36892149180553399770078631)
      ·
        refine ⟨55338223770830099655117947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36892149180553399770078631 55338223770830099655117947)
        ·
          refine ⟨83007335656245149482676921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55338223770830099655117947 83007335656245149482676921)
          ·
            refine ⟨62255501742183862112007691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83007335656245149482676921 62255501742183862112007691)
            ·
              refine ⟨93383252613275793168011537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62255501742183862112007691 93383252613275793168011537)
              ·
                refine ⟨70037439459956844876008653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93383252613275793168011537 70037439459956844876008653)
                ·
                  refine ⟨26264039797483816828503245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70037439459956844876008653 26264039797483816828503245)
                  ·
                    refine ⟨9849014924056431310688717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26264039797483816828503245 9849014924056431310688717)
                    ·
                      refine ⟨3693380596521161741508269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9849014924056431310688717 3693380596521161741508269)
                      ·
                        rfl

theorem cell23_7192833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_7192833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192833 prefixEnd_7192833 := by exact prefixLift 7192833
  have htrace : WordTrace (prefixWord ++ tailWord_7192833) baseStart_7192833 baseEnd_7192833 := by
    simpa [prefixWord, tailWord_7192833, baseEnd_7192833] using wordTrace_append hprefix tailTrace_7192833
  have hstable : (prefixWord ++ tailWord_7192833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192833).length < 2 ^ (prefixWord ++ tailWord_7192833).sum := by decide
  have hdescent : baseEnd_7192833 < baseStart_7192833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192871 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_7192871 : Nat := 118140960795 + 7192871 * 2 ^ 59
def prefixEnd_7192871 : Nat := 4983230072969 + 3 ^ 40 * 7192871 * 2
def baseEnd_7192871 : Nat := 3693400108786032592833095

theorem tailTrace_7192871 : CollatzResearch.WordTrace tailWord_7192871 prefixEnd_7192871 3693400108786032592833095 := by
  unfold tailWord_7192871
  simp only [CollatzResearch.WordTrace]
  refine ⟨262345557924464286410442467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174897038616309524273628311 262345557924464286410442467)
  ·
    refine ⟨393518336886696429615663701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262345557924464286410442467 393518336886696429615663701)
    ·
      refine ⟨4611543010390973784558559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 393518336886696429615663701 4611543010390973784558559)
      ·
        refine ⟨6917314515586460676837839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4611543010390973784558559 6917314515586460676837839)
        ·
          refine ⟨10375971773379691015256759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6917314515586460676837839 10375971773379691015256759)
          ·
            refine ⟨15563957660069536522885139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10375971773379691015256759 15563957660069536522885139)
            ·
              refine ⟨23345936490104304784327709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15563957660069536522885139 23345936490104304784327709)
              ·
                refine ⟨8754726183789114294122891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23345936490104304784327709 8754726183789114294122891)
                ·
                  refine ⟨13132089275683671441184337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8754726183789114294122891 13132089275683671441184337)
                  ·
                    refine ⟨9849066956762753580888253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13132089275683671441184337 9849066956762753580888253)
                    ·
                      refine ⟨3693400108786032592833095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9849066956762753580888253 3693400108786032592833095)
                      ·
                        rfl

theorem cell23_7192871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_7192871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192871 prefixEnd_7192871 := by exact prefixLift 7192871
  have htrace : WordTrace (prefixWord ++ tailWord_7192871) baseStart_7192871 baseEnd_7192871 := by
    simpa [prefixWord, tailWord_7192871, baseEnd_7192871] using wordTrace_append hprefix tailTrace_7192871
  have hstable : (prefixWord ++ tailWord_7192871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192871).length < 2 ^ (prefixWord ++ tailWord_7192871).sum := by decide
  have hdescent : baseEnd_7192871 < baseStart_7192871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192884 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_7192884 : Nat := 118140960795 + 7192884 * 2 ^ 59
def prefixEnd_7192884 : Nat := 4983230072969 + 3 ^ 40 * 7192884 * 2
def baseEnd_7192884 : Nat := 3693406784034541041970535

theorem tailTrace_7192884 : CollatzResearch.WordTrace tailWord_7192884 prefixEnd_7192884 3693406784034541041970535 := by
  unfold tailWord_7192884
  simp only [CollatzResearch.WordTrace]
  refine ⟨131173016036708594815332853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174897354715611459753777137 131173016036708594815332853)
  ·
    refine ⟨12297470253441430763937455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131173016036708594815332853 12297470253441430763937455)
    ·
      refine ⟨18446205380162146145906183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12297470253441430763937455 18446205380162146145906183)
      ·
        refine ⟨27669308070243219218859275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18446205380162146145906183 27669308070243219218859275)
        ·
          refine ⟨41503962105364828828288913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27669308070243219218859275 41503962105364828828288913)
          ·
            refine ⟨31127971579023621621216685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41503962105364828828288913 31127971579023621621216685)
            ·
              refine ⟨11672989342133858107956257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31127971579023621621216685 11672989342133858107956257)
              ·
                refine ⟨8754742006600393580967193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11672989342133858107956257 8754742006600393580967193)
                ·
                  refine ⟨6566056504950295185725395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8754742006600393580967193 6566056504950295185725395)
                  ·
                    refine ⟨9849084757425442778588093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6566056504950295185725395 9849084757425442778588093)
                    ·
                      refine ⟨3693406784034541041970535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9849084757425442778588093 3693406784034541041970535)
                      ·
                        rfl

theorem cell23_7192884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_7192884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192884 prefixEnd_7192884 := by exact prefixLift 7192884
  have htrace : WordTrace (prefixWord ++ tailWord_7192884) baseStart_7192884 baseEnd_7192884 := by
    simpa [prefixWord, tailWord_7192884, baseEnd_7192884] using wordTrace_append hprefix tailTrace_7192884
  have hstable : (prefixWord ++ tailWord_7192884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192884).length < 2 ^ (prefixWord ++ tailWord_7192884).sum := by decide
  have hdescent : baseEnd_7192884 < baseStart_7192884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192903 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_7192903 : Nat := 118140960795 + 7192903 * 2 ^ 59
def prefixEnd_7192903 : Nat := 4983230072969 + 3 ^ 40 * 7192903 * 2
def baseEnd_7192903 : Nat := 3693416540166976467632947

theorem tailTrace_7192903 : CollatzResearch.WordTrace tailWord_7192903 prefixEnd_7192903 3693416540166976467632947 := by
  unfold tailWord_7192903
  simp only [CollatzResearch.WordTrace]
  refine ⟨262346725060348355875607363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174897816706898903917071575 262346725060348355875607363)
  ·
    refine ⟨393520087590522533813411045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262346725060348355875607363 393520087590522533813411045)
    ·
      refine ⟨73785016423222975090014571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393520087590522533813411045 73785016423222975090014571)
      ·
        refine ⟨110677524634834462635021857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73785016423222975090014571 110677524634834462635021857)
        ·
          refine ⟨83008143476125846976266393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110677524634834462635021857 83008143476125846976266393)
          ·
            refine ⟨62256107607094385232199795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83008143476125846976266393 62256107607094385232199795)
            ·
              refine ⟨93384161410641577848299693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62256107607094385232199795 93384161410641577848299693)
              ·
                refine ⟨35019060528990591693112385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93384161410641577848299693 35019060528990591693112385)
                ·
                  refine ⟨26264295396742943769834289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35019060528990591693112385 26264295396742943769834289)
                  ·
                    refine ⟨19698221547557207827375717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26264295396742943769834289 19698221547557207827375717)
                    ·
                      refine ⟨3693416540166976467632947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19698221547557207827375717 3693416540166976467632947)
                      ·
                        rfl

theorem cell23_7192903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_7192903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192903 prefixEnd_7192903 := by exact prefixLift 7192903
  have htrace : WordTrace (prefixWord ++ tailWord_7192903) baseStart_7192903 baseEnd_7192903 := by
    simpa [prefixWord, tailWord_7192903, baseEnd_7192903] using wordTrace_append hprefix tailTrace_7192903
  have hstable : (prefixWord ++ tailWord_7192903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192903).length < 2 ^ (prefixWord ++ tailWord_7192903).sum := by decide
  have hdescent : baseEnd_7192903 < baseStart_7192903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7192913 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 7]
def baseStart_7192913 : Nat := 118140960795 + 7192913 * 2 ^ 59
def prefixEnd_7192913 : Nat := 4983230072969 + 3 ^ 40 * 7192913 * 2
def baseEnd_7192913 : Nat := 410380186108169047611989

theorem tailTrace_7192913 : CollatzResearch.WordTrace tailWord_7192913 prefixEnd_7192913 410380186108169047611989 := by
  unfold tailWord_7192913
  simp only [CollatzResearch.WordTrace]
  refine ⟨262347089790312127583471393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174898059860208085055647595 262347089790312127583471393)
  ·
    refine ⟨196760317342734095687603545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262347089790312127583471393 196760317342734095687603545)
    ·
      refine ⟨147570238007050571765702659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196760317342734095687603545 147570238007050571765702659)
      ·
        refine ⟨221355357010575857648553989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147570238007050571765702659 221355357010575857648553989)
        ·
          refine ⟨41504129439482973309103873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221355357010575857648553989 41504129439482973309103873)
          ·
            refine ⟨31128097079612229981827905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41504129439482973309103873 31128097079612229981827905)
            ·
              refine ⟨23346072809709172486370929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31128097079612229981827905 23346072809709172486370929)
              ·
                refine ⟨17509554607281879364778197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23346072809709172486370929 17509554607281879364778197)
                ·
                  refine ⟨410380186108169047611989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17509554607281879364778197 410380186108169047611989)
                  ·
                    rfl

theorem cell23_7192913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 7].length) (baseStart_7192913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7192913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7192913 prefixEnd_7192913 := by exact prefixLift 7192913
  have htrace : WordTrace (prefixWord ++ tailWord_7192913) baseStart_7192913 baseEnd_7192913 := by
    simpa [prefixWord, tailWord_7192913, baseEnd_7192913] using wordTrace_append hprefix tailTrace_7192913
  have hstable : (prefixWord ++ tailWord_7192913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7192913).length < 2 ^ (prefixWord ++ tailWord_7192913).sum := by decide
  have hdescent : baseEnd_7192913 < baseStart_7192913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7192913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193057 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 4, 3, 2]
def baseStart_7193057 : Nat := 118140960795 + 7193057 * 2 ^ 59
def prefixEnd_7193057 : Nat := 4983230072969 + 3 ^ 40 * 7193057 * 2
def baseEnd_7193057 : Nat := 3693495616187768865107239

theorem tailTrace_7193057 : CollatzResearch.WordTrace tailWord_7193057 prefixEnd_7193057 3693495616187768865107239 := by
  unfold tailWord_7193057
  simp only [CollatzResearch.WordTrace]
  refine ⟨262352341901790440176713425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174901561267860293451142283 262352341901790440176713425)
  ·
    refine ⟨196764256426342830132535069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262352341901790440176713425 196764256426342830132535069)
    ·
      refine ⟨73786596159878561299700651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196764256426342830132535069 73786596159878561299700651)
      ·
        refine ⟨110679894239817841949550977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73786596159878561299700651 110679894239817841949550977)
        ·
          refine ⟨83009920679863381462163233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110679894239817841949550977 83009920679863381462163233)
          ·
            refine ⟨62257440509897536096622425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83009920679863381462163233 62257440509897536096622425)
            ·
              refine ⟨46693080382423152072466819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62257440509897536096622425 46693080382423152072466819)
              ·
                refine ⟨70039620573634728108700229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46693080382423152072466819 70039620573634728108700229)
                ·
                  refine ⟨13132428857556511520381293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70039620573634728108700229 13132428857556511520381293)
                  ·
                    refine ⟨4924660821583691820142985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13132428857556511520381293 4924660821583691820142985)
                    ·
                      refine ⟨3693495616187768865107239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4924660821583691820142985 3693495616187768865107239)
                      ·
                        rfl

theorem cell23_7193057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_7193057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193057 prefixEnd_7193057 := by exact prefixLift 7193057
  have htrace : WordTrace (prefixWord ++ tailWord_7193057) baseStart_7193057 baseEnd_7193057 := by
    simpa [prefixWord, tailWord_7193057, baseEnd_7193057] using wordTrace_append hprefix tailTrace_7193057
  have hstable : (prefixWord ++ tailWord_7193057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193057).length < 2 ^ (prefixWord ++ tailWord_7193057).sum := by decide
  have hdescent : baseEnd_7193057 < baseStart_7193057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193064 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_7193064 : Nat := 118140960795 + 7193064 * 2 ^ 59
def prefixEnd_7193064 : Nat := 4983230072969 + 3 ^ 40 * 7193064 * 2
def baseEnd_7193064 : Nat := 3693499210552350337719707

theorem tailTrace_7193064 : CollatzResearch.WordTrace tailWord_7193064 prefixEnd_7193064 3693499210552350337719707 := by
  unfold tailWord_7193064
  simp only [CollatzResearch.WordTrace]
  refine ⟨131176298606382540186109123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174901731475176720248145497 131176298606382540186109123)
  ·
    refine ⟨196764447909573810279163685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131176298606382540186109123 196764447909573810279163685)
    ·
      refine ⟨36893333983045089427343191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196764447909573810279163685 36893333983045089427343191)
      ·
        refine ⟨55340000974567634141014787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36893333983045089427343191 55340000974567634141014787)
        ·
          refine ⟨83010001461851451211522181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55340000974567634141014787 83010001461851451211522181)
          ·
            refine ⟨15564375274097147102160409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83010001461851451211522181 15564375274097147102160409)
            ·
              refine ⟨11673281455572860326620307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15564375274097147102160409 11673281455572860326620307)
              ·
                refine ⟨17509922183359290489930461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11673281455572860326620307 17509922183359290489930461)
                ·
                  refine ⟨6566220818759733933723923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17509922183359290489930461 6566220818759733933723923)
                  ·
                    refine ⟨9849331228139600900585885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6566220818759733933723923 9849331228139600900585885)
                    ·
                      refine ⟨3693499210552350337719707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9849331228139600900585885 3693499210552350337719707)
                      ·
                        rfl

theorem cell23_7193064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_7193064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193064 prefixEnd_7193064 := by exact prefixLift 7193064
  have htrace : WordTrace (prefixWord ++ tailWord_7193064) baseStart_7193064 baseEnd_7193064 := by
    simpa [prefixWord, tailWord_7193064, baseEnd_7193064] using wordTrace_append hprefix tailTrace_7193064
  have hstable : (prefixWord ++ tailWord_7193064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193064).length < 2 ^ (prefixWord ++ tailWord_7193064).sum := by decide
  have hdescent : baseEnd_7193064 < baseStart_7193064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193087 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 4]
def baseStart_7193087 : Nat := 118140960795 + 7193087 * 2 ^ 59
def prefixEnd_7193087 : Nat := 4983230072969 + 3 ^ 40 * 7193087 * 2
def baseEnd_7193087 : Nat := 3693511020607403747732101

theorem tailTrace_7193087 : CollatzResearch.WordTrace tailWord_7193087 prefixEnd_7193087 3693511020607403747732101 := by
  unfold tailWord_7193087
  simp only [CollatzResearch.WordTrace]
  refine ⟨262353436091681755300305515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174902290727787836866870343 262353436091681755300305515)
  ·
    refine ⟨393530154137522632950458273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262353436091681755300305515 393530154137522632950458273)
    ·
      refine ⟨295147615603141974712843705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393530154137522632950458273 295147615603141974712843705)
      ·
        refine ⟨221360711702356481034632779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295147615603141974712843705 221360711702356481034632779)
        ·
          refine ⟨332041067553534721551949169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221360711702356481034632779 332041067553534721551949169)
          ·
            refine ⟨249030800665151041163961877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332041067553534721551949169 249030800665151041163961877)
            ·
              refine ⟨11673318781178955054560713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 249030800665151041163961877 11673318781178955054560713)
              ·
                refine ⟨8754989085884216290920535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11673318781178955054560713 8754989085884216290920535)
                ·
                  refine ⟨13132483628826324436380803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8754989085884216290920535 13132483628826324436380803)
                  ·
                    refine ⟨19698725443239486654571205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13132483628826324436380803 19698725443239486654571205)
                    ·
                      refine ⟨3693511020607403747732101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19698725443239486654571205 3693511020607403747732101)
                      ·
                        rfl

theorem cell23_7193087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_7193087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193087 prefixEnd_7193087 := by exact prefixLift 7193087
  have htrace : WordTrace (prefixWord ++ tailWord_7193087) baseStart_7193087 baseEnd_7193087 := by
    simpa [prefixWord, tailWord_7193087, baseEnd_7193087] using wordTrace_append hprefix tailTrace_7193087
  have hstable : (prefixWord ++ tailWord_7193087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193087).length < 2 ^ (prefixWord ++ tailWord_7193087).sum := by decide
  have hdescent : baseEnd_7193087 < baseStart_7193087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193101 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7193101 : Nat := 118140960795 + 7193101 * 2 ^ 59
def prefixEnd_7193101 : Nat := 4983230072969 + 3 ^ 40 * 7193101 * 2
def baseEnd_7193101 : Nat := 1231172736445522230985679

theorem tailTrace_7193101 : CollatzResearch.WordTrace tailWord_7193101 prefixEnd_7193101 1231172736445522230985679 := by
  unfold tailWord_7193101
  simp only [CollatzResearch.WordTrace]
  refine ⟨262353946713631035691315157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174902631142420690460876771 262353946713631035691315157)
  ·
    refine ⟨6148920626100727399015199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 262353946713631035691315157 6148920626100727399015199)
    ·
      refine ⟨9223380939151091098522799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6148920626100727399015199 9223380939151091098522799)
      ·
        refine ⟨13835071408726636647784199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9223380939151091098522799 13835071408726636647784199)
        ·
          refine ⟨20752607113089954971676299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13835071408726636647784199 20752607113089954971676299)
          ·
            refine ⟨31128910669634932457514449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20752607113089954971676299 31128910669634932457514449)
            ·
              refine ⟨23346683002226199343135837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31128910669634932457514449 23346683002226199343135837)
              ·
                refine ⟨8755006125834824753675939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23346683002226199343135837 8755006125834824753675939)
                ·
                  refine ⟨13132509188752237130513909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8755006125834824753675939 13132509188752237130513909)
                  ·
                    refine ⟨1231172736445522230985679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13132509188752237130513909 1231172736445522230985679)
                    ·
                      rfl

theorem cell23_7193101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7193101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193101 prefixEnd_7193101 := by exact prefixLift 7193101
  have htrace : WordTrace (prefixWord ++ tailWord_7193101) baseStart_7193101 baseEnd_7193101 := by
    simpa [prefixWord, tailWord_7193101, baseEnd_7193101] using wordTrace_append hprefix tailTrace_7193101
  have hstable : (prefixWord ++ tailWord_7193101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193101).length < 2 ^ (prefixWord ++ tailWord_7193101).sum := by decide
  have hdescent : baseEnd_7193101 < baseStart_7193101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193107 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 1, 2, 3]
def baseStart_7193107 : Nat := 118140960795 + 7193107 * 2 ^ 59
def prefixEnd_7193107 : Nat := 4983230072969 + 3 ^ 40 * 7193107 * 2
def baseEnd_7193107 : Nat := 3693521290220493669482009

theorem tailTrace_7193107 : CollatzResearch.WordTrace tailWord_7193107 prefixEnd_7193107 3693521290220493669482009 := by
  unfold tailWord_7193107
  simp only [CollatzResearch.WordTrace]
  refine ⟨262354165551609298716033575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174902777034406199144022383 262354165551609298716033575)
  ·
    refine ⟨393531248327413948074050363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262354165551609298716033575 393531248327413948074050363)
    ·
      refine ⟨590296872491120922111075545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393531248327413948074050363 590296872491120922111075545)
      ·
        refine ⟨442722654368340691583306659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590296872491120922111075545 442722654368340691583306659)
        ·
          refine ⟨664083981552511037374959989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442722654368340691583306659 664083981552511037374959989)
          ·
            refine ⟨62257873270547909753902499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 664083981552511037374959989 62257873270547909753902499)
            ·
              refine ⟨93386809905821864630853749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62257873270547909753902499 93386809905821864630853749)
              ·
                refine ⟨8755013428670799809142539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93386809905821864630853749 8755013428670799809142539)
                ·
                  refine ⟨13132520143006199713713809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8755013428670799809142539 13132520143006199713713809)
                  ·
                    refine ⟨9849390107254649785285357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13132520143006199713713809 9849390107254649785285357)
                    ·
                      refine ⟨3693521290220493669482009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9849390107254649785285357 3693521290220493669482009)
                      ·
                        rfl

theorem cell23_7193107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 2, 3].length) (baseStart_7193107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193107 prefixEnd_7193107 := by exact prefixLift 7193107
  have htrace : WordTrace (prefixWord ++ tailWord_7193107) baseStart_7193107 baseEnd_7193107 := by
    simpa [prefixWord, tailWord_7193107, baseEnd_7193107] using wordTrace_append hprefix tailTrace_7193107
  have hstable : (prefixWord ++ tailWord_7193107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193107).length < 2 ^ (prefixWord ++ tailWord_7193107).sum := by decide
  have hdescent : baseEnd_7193107 < baseStart_7193107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193160 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_7193160 : Nat := 118140960795 + 7193160 * 2 ^ 59
def prefixEnd_7193160 : Nat := 4983230072969 + 3 ^ 40 * 7193160 * 2
def baseEnd_7193160 : Nat := 3693548504695181962119265

theorem tailTrace_7193160 : CollatzResearch.WordTrace tailWord_7193160 prefixEnd_7193160 3693548504695181962119265 := by
  unfold tailWord_7193160
  simp only [CollatzResearch.WordTrace]
  refine ⟨131178049310208644383856467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174904065746944859178475289 131178049310208644383856467)
  ·
    refine ⟨196767073965312966575784701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131178049310208644383856467 196767073965312966575784701)
    ·
      refine ⟨73787652736992362465919263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196767073965312966575784701 73787652736992362465919263)
      ·
        refine ⟨110681479105488543698878895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73787652736992362465919263 110681479105488543698878895)
        ·
          refine ⟨166022218658232815548318343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110681479105488543698878895 166022218658232815548318343)
          ·
            refine ⟨249033327987349223322477515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166022218658232815548318343 249033327987349223322477515)
            ·
              refine ⟨373549991981023834983716273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249033327987349223322477515 373549991981023834983716273)
              ·
                refine ⟨280162493985767876237787205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373549991981023834983716273 280162493985767876237787205)
                ·
                  refine ⟨52530467622331476794585101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280162493985767876237787205 52530467622331476794585101)
                  ·
                    refine ⟨19698925358374303797969413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52530467622331476794585101 19698925358374303797969413)
                    ·
                      refine ⟨3693548504695181962119265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19698925358374303797969413 3693548504695181962119265)
                      ·
                        rfl

theorem cell23_7193160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_7193160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193160 prefixEnd_7193160 := by exact prefixLift 7193160
  have htrace : WordTrace (prefixWord ++ tailWord_7193160) baseStart_7193160 baseEnd_7193160 := by
    simpa [prefixWord, tailWord_7193160, baseEnd_7193160] using wordTrace_append hprefix tailTrace_7193160
  have hstable : (prefixWord ++ tailWord_7193160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193160).length < 2 ^ (prefixWord ++ tailWord_7193160).sum := by decide
  have hdescent : baseEnd_7193160 < baseStart_7193160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193234 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 7]
def baseStart_7193234 : Nat := 118140960795 + 7193234 * 2 ^ 59
def prefixEnd_7193234 : Nat := 4983230072969 + 3 ^ 40 * 7193234 * 2
def baseEnd_7193234 : Nat := 410398500251512741399325

theorem tailTrace_7193234 : CollatzResearch.WordTrace tailWord_7193234 prefixEnd_7193234 410398500251512741399325 := by
  unfold tailWord_7193234
  simp only [CollatzResearch.WordTrace]
  refine ⟨65589699405537299851476689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174905865081432799603937837 65589699405537299851476689)
  ·
    refine ⟨49192274554152974888607517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65589699405537299851476689 49192274554152974888607517)
    ·
      refine ⟨18447102957807365583227819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49192274554152974888607517 18447102957807365583227819)
      ·
        refine ⟨27670654436711048374841729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18447102957807365583227819 27670654436711048374841729)
        ·
          refine ⟨20752990827533286281131297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27670654436711048374841729 20752990827533286281131297)
          ·
            refine ⟨15564743120649964710848473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20752990827533286281131297 15564743120649964710848473)
            ·
              refine ⟨11673557340487473533136355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15564743120649964710848473 11673557340487473533136355)
              ·
                refine ⟨17510336010731210299704533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11673557340487473533136355 17510336010731210299704533)
                ·
                  refine ⟨410398500251512741399325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17510336010731210299704533 410398500251512741399325)
                  ·
                    rfl

theorem cell23_7193234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_7193234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193234 prefixEnd_7193234 := by exact prefixLift 7193234
  have htrace : WordTrace (prefixWord ++ tailWord_7193234) baseStart_7193234 baseEnd_7193234 := by
    simpa [prefixWord, tailWord_7193234, baseEnd_7193234] using wordTrace_append hprefix tailTrace_7193234
  have hstable : (prefixWord ++ tailWord_7193234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193234).length < 2 ^ (prefixWord ++ tailWord_7193234).sum := by decide
  have hdescent : baseEnd_7193234 < baseStart_7193234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193244 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_7193244 : Nat := 118140960795 + 7193244 * 2 ^ 59
def prefixEnd_7193244 : Nat := 4983230072969 + 3 ^ 40 * 7193244 * 2
def baseEnd_7193244 : Nat := 3693591637070159633468879

theorem tailTrace_7193244 : CollatzResearch.WordTrace tailWord_7193244 prefixEnd_7193244 3693591637070159633468879 := by
  unfold tailWord_7193244
  simp only [CollatzResearch.WordTrace]
  refine ⟨131179581176056485556885393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174906108234741980742513857 131179581176056485556885393)
  ·
    refine ⟨98384685882042364167664045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131179581176056485556885393 98384685882042364167664045)
    ·
      refine ⟨36894257205765886562874017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98384685882042364167664045 36894257205765886562874017)
      ·
        refine ⟨27670692904324414922155513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36894257205765886562874017 27670692904324414922155513)
        ·
          refine ⟨20753019678243311191616635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27670692904324414922155513 20753019678243311191616635)
          ·
            refine ⟨31129529517364966787424953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20753019678243311191616635 31129529517364966787424953)
            ·
              refine ⟨23347147138023725090568715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31129529517364966787424953 23347147138023725090568715)
              ·
                refine ⟨35020720707035587635853073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23347147138023725090568715 35020720707035587635853073)
                ·
                  refine ⟨26265540530276690726889805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35020720707035587635853073 26265540530276690726889805)
                  ·
                    refine ⟨9849577698853759022583677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26265540530276690726889805 9849577698853759022583677)
                    ·
                      refine ⟨3693591637070159633468879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9849577698853759022583677 3693591637070159633468879)
                      ·
                        rfl

theorem cell23_7193244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_7193244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193244 prefixEnd_7193244 := by exact prefixLift 7193244
  have htrace : WordTrace (prefixWord ++ tailWord_7193244) baseStart_7193244 baseEnd_7193244 := by
    simpa [prefixWord, tailWord_7193244, baseEnd_7193244] using wordTrace_append hprefix tailTrace_7193244
  have hstable : (prefixWord ++ tailWord_7193244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193244).length < 2 ^ (prefixWord ++ tailWord_7193244).sum := by decide
  have hdescent : baseEnd_7193244 < baseStart_7193244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193267 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 4]
def baseStart_7193267 : Nat := 118140960795 + 7193267 * 2 ^ 59
def prefixEnd_7193267 : Nat := 4983230072969 + 3 ^ 40 * 7193267 * 2
def baseEnd_7193267 : Nat := 3693603447125213043481273

theorem tailTrace_7193267 : CollatzResearch.WordTrace tailWord_7193267 prefixEnd_7193267 3693603447125213043481273 := by
  unfold tailWord_7193267
  simp only [CollatzResearch.WordTrace]
  refine ⟨262360001231029646041858055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174906667487353097361238703 262360001231029646041858055)
  ·
    refine ⟨393540001846544469062787083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262360001231029646041858055 393540001846544469062787083)
    ·
      refine ⟨590310002769816703594180625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393540001846544469062787083 590310002769816703594180625)
      ·
        refine ⟨442732502077362527695635469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590310002769816703594180625 442732502077362527695635469)
        ·
          refine ⟨166024688279010947885863301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442732502077362527695635469 166024688279010947885863301)
          ·
            refine ⟨31129629052314552728599369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166024688279010947885863301 31129629052314552728599369)
            ·
              refine ⟨23347221789235914546449527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31129629052314552728599369 23347221789235914546449527)
              ·
                refine ⟨35020832683853871819674291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23347221789235914546449527 35020832683853871819674291)
                ·
                  refine ⟨52531249025780807729511437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35020832683853871819674291 52531249025780807729511437)
                  ·
                    refine ⟨19699218384667802898566789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52531249025780807729511437 19699218384667802898566789)
                    ·
                      refine ⟨3693603447125213043481273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19699218384667802898566789 3693603447125213043481273)
                      ·
                        rfl

theorem cell23_7193267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_7193267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193267 prefixEnd_7193267 := by exact prefixLift 7193267
  have htrace : WordTrace (prefixWord ++ tailWord_7193267) baseStart_7193267 baseEnd_7193267 := by
    simpa [prefixWord, tailWord_7193267, baseEnd_7193267] using wordTrace_append hprefix tailTrace_7193267
  have hstable : (prefixWord ++ tailWord_7193267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193267).length < 2 ^ (prefixWord ++ tailWord_7193267).sum := by decide
  have hdescent : baseEnd_7193267 < baseStart_7193267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193284 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_7193284 : Nat := 118140960795 + 7193284 * 2 ^ 59
def prefixEnd_7193284 : Nat := 4983230072969 + 3 ^ 40 * 7193284 * 2
def baseEnd_7193284 : Nat := 3693612176296339476968695

theorem tailTrace_7193284 : CollatzResearch.WordTrace tailWord_7193284 prefixEnd_7193284 3693612176296339476968695 := by
  unfold tailWord_7193284
  simp only [CollatzResearch.WordTrace]
  refine ⟨131180310635984028972613453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174907080847978705296817937 131180310635984028972613453)
  ·
    refine ⟨49192616488494010864730045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131180310635984028972613453 49192616488494010864730045)
    ·
      refine ⟨18447231183185254074273767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49192616488494010864730045 18447231183185254074273767)
      ·
        refine ⟨27670846774777881111410651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18447231183185254074273767 27670846774777881111410651)
        ·
          refine ⟨41506270162166821667115977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27670846774777881111410651 41506270162166821667115977)
          ·
            refine ⟨31129702621625116250336983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41506270162166821667115977 31129702621625116250336983)
            ·
              refine ⟨46694553932437674375505475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31129702621625116250336983 46694553932437674375505475)
              ·
                refine ⟨70041830898656511563258213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46694553932437674375505475 70041830898656511563258213)
                ·
                  refine ⟨13132843293498095918110915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70041830898656511563258213 13132843293498095918110915)
                  ·
                    refine ⟨19699264940247143877166373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13132843293498095918110915 19699264940247143877166373)
                    ·
                      refine ⟨3693612176296339476968695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19699264940247143877166373 3693612176296339476968695)
                      ·
                        rfl

theorem cell23_7193284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_7193284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193284 prefixEnd_7193284 := by exact prefixLift 7193284
  have htrace : WordTrace (prefixWord ++ tailWord_7193284) baseStart_7193284 baseEnd_7193284 := by
    simpa [prefixWord, tailWord_7193284, baseEnd_7193284] using wordTrace_append hprefix tailTrace_7193284
  have hstable : (prefixWord ++ tailWord_7193284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193284).length < 2 ^ (prefixWord ++ tailWord_7193284).sum := by decide
  have hdescent : baseEnd_7193284 < baseStart_7193284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193287 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_7193287 : Nat := 118140960795 + 7193287 * 2 ^ 59
def prefixEnd_7193287 : Nat := 4983230072969 + 3 ^ 40 * 7193287 * 2
def baseEnd_7193287 : Nat := 3693613716738302965231181

theorem tailTrace_7193287 : CollatzResearch.WordTrace tailWord_7193287 prefixEnd_7193287 3693613716738302965231181 := by
  unfold tailWord_7193287
  simp only [CollatzResearch.WordTrace]
  refine ⟨262360730690957189457586115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174907153793971459638390743 262360730690957189457586115)
  ·
    refine ⟨393541096036435784186379173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262360730690957189457586115 393541096036435784186379173)
    ·
      refine ⟨73788955506831709534946095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393541096036435784186379173 73788955506831709534946095)
      ·
        refine ⟨110683433260247564302419143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73788955506831709534946095 110683433260247564302419143)
        ·
          refine ⟨166025149890371346453628715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110683433260247564302419143 166025149890371346453628715)
          ·
            refine ⟨249037724835557019680443073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166025149890371346453628715 249037724835557019680443073)
            ·
              refine ⟨186778293626667764760332305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249037724835557019680443073 186778293626667764760332305)
              ·
                refine ⟨140083720220000823570249229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186778293626667764760332305 140083720220000823570249229)
                ·
                  refine ⟨52531395082500308838843461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140083720220000823570249229 52531395082500308838843461)
                  ·
                    refine ⟨9849636577968807907283149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52531395082500308838843461 9849636577968807907283149)
                    ·
                      refine ⟨3693613716738302965231181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9849636577968807907283149 3693613716738302965231181)
                      ·
                        rfl

theorem cell23_7193287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_7193287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193287 prefixEnd_7193287 := by exact prefixLift 7193287
  have htrace : WordTrace (prefixWord ++ tailWord_7193287) baseStart_7193287 baseEnd_7193287 := by
    simpa [prefixWord, tailWord_7193287, baseEnd_7193287] using wordTrace_append hprefix tailTrace_7193287
  have hstable : (prefixWord ++ tailWord_7193287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193287).length < 2 ^ (prefixWord ++ tailWord_7193287).sum := by decide
  have hdescent : baseEnd_7193287 < baseStart_7193287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193378 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_7193378 : Nat := 118140960795 + 7193378 * 2 ^ 59
def prefixEnd_7193378 : Nat := 4983230072969 + 3 ^ 40 * 7193378 * 2
def baseEnd_7193378 : Nat := 3693660443477862109193263

theorem tailTrace_7193378 : CollatzResearch.WordTrace tailWord_7193378 prefixEnd_7193378 3693660443477862109193263 := by
  unfold tailWord_7193378
  simp only [CollatzResearch.WordTrace]
  refine ⟨65591012433406877999787197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174909366489085007999432525 65591012433406877999787197)
  ·
    refine ⟨24596629662527579249920199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65591012433406877999787197 24596629662527579249920199)
    ·
      refine ⟨36894944493791368874880299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24596629662527579249920199 36894944493791368874880299)
      ·
        refine ⟨55342416740687053312320449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36894944493791368874880299 55342416740687053312320449)
        ·
          refine ⟨41506812555515289984240337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55342416740687053312320449 41506812555515289984240337)
          ·
            refine ⟨31130109416636467488180253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41506812555515289984240337 31130109416636467488180253)
            ·
              refine ⟨11673791031238675308067595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31130109416636467488180253 11673791031238675308067595)
              ·
                refine ⟨17510686546858012962101393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11673791031238675308067595 17510686546858012962101393)
                ·
                  refine ⟨13133014910143509721576045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17510686546858012962101393 13133014910143509721576045)
                  ·
                    refine ⟨4924880591303816145591017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13133014910143509721576045 4924880591303816145591017)
                    ·
                      refine ⟨3693660443477862109193263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4924880591303816145591017 3693660443477862109193263)
                      ·
                        rfl

theorem cell23_7193378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_7193378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193378 prefixEnd_7193378 := by exact prefixLift 7193378
  have htrace : WordTrace (prefixWord ++ tailWord_7193378) baseStart_7193378 baseEnd_7193378 := by
    simpa [prefixWord, tailWord_7193378, baseEnd_7193378] using wordTrace_append hprefix tailTrace_7193378
  have hstable : (prefixWord ++ tailWord_7193378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193378).length < 2 ^ (prefixWord ++ tailWord_7193378).sum := by decide
  have hdescent : baseEnd_7193378 < baseStart_7193378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193384 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 1, 6]
def baseStart_7193384 : Nat := 118140960795 + 7193384 * 2 ^ 59
def prefixEnd_7193384 : Nat := 4983230072969 + 3 ^ 40 * 7193384 * 2
def baseEnd_7193384 : Nat := 1231221174787263028572745

theorem tailTrace_7193384 : CollatzResearch.WordTrace tailWord_7193384 prefixEnd_7193384 1231221174787263028572745 := by
  unfold tailWord_7193384
  simp only [CollatzResearch.WordTrace]
  refine ⟨131182134285802887511933603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174909512381070516682578137 131182134285802887511933603)
  ·
    refine ⟨196773201428704331267900405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131182134285802887511933603 196773201428704331267900405)
    ·
      refine ⟨18447487633941031056365663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196773201428704331267900405 18447487633941031056365663)
      ·
        refine ⟨27671231450911546584548495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18447487633941031056365663 27671231450911546584548495)
        ·
          refine ⟨41506847176367319876822743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27671231450911546584548495 41506847176367319876822743)
          ·
            refine ⟨62260270764550979815234115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41506847176367319876822743 62260270764550979815234115)
            ·
              refine ⟨93390406146826469722851173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62260270764550979815234115 93390406146826469722851173)
              ·
                refine ⟨17510701152529963073034595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93390406146826469722851173 17510701152529963073034595)
                ·
                  refine ⟨26266051728794944609551893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17510701152529963073034595 26266051728794944609551893)
                  ·
                    refine ⟨1231221174787263028572745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26266051728794944609551893 1231221174787263028572745)
                    ·
                      rfl

theorem cell23_7193384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_7193384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193384 prefixEnd_7193384 := by exact prefixLift 7193384
  have htrace : WordTrace (prefixWord ++ tailWord_7193384) baseStart_7193384 baseEnd_7193384 := by
    simpa [prefixWord, tailWord_7193384, baseEnd_7193384] using wordTrace_append hprefix tailTrace_7193384
  have hstable : (prefixWord ++ tailWord_7193384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193384).length < 2 ^ (prefixWord ++ tailWord_7193384).sum := by decide
  have hdescent : baseEnd_7193384 < baseStart_7193384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193394 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_7193394 : Nat := 118140960795 + 7193394 * 2 ^ 59
def prefixEnd_7193394 : Nat := 4983230072969 + 3 ^ 40 * 7193394 * 2
def baseEnd_7193394 : Nat := 3693668659168334046593189

theorem tailTrace_7193394 : CollatzResearch.WordTrace tailWord_7193394 prefixEnd_7193394 3693668659168334046593189 := by
  unfold tailWord_7193394
  simp only [CollatzResearch.WordTrace]
  refine ⟨65591158325392386682932809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174909755534379697821154157 65591158325392386682932809)
  ·
    refine ⟨49193368744044290012199607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65591158325392386682932809 49193368744044290012199607)
    ·
      refine ⟨73790053116066435018299411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49193368744044290012199607 73790053116066435018299411)
      ·
        refine ⟨110685079674099652527449117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73790053116066435018299411 110685079674099652527449117)
        ·
          refine ⟨41506904877787369697793419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110685079674099652527449117 41506904877787369697793419)
          ·
            refine ⟨62260357316681054546690129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41506904877787369697793419 62260357316681054546690129)
            ·
              refine ⟨46695267987510790910017597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62260357316681054546690129 46695267987510790910017597)
              ·
                refine ⟨17510725495316546591256599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46695267987510790910017597 17510725495316546591256599)
                ·
                  refine ⟨26266088242974819886884899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17510725495316546591256599 26266088242974819886884899)
                  ·
                    refine ⟨39399132364462229830327349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26266088242974819886884899 39399132364462229830327349)
                    ·
                      refine ⟨3693668659168334046593189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39399132364462229830327349 3693668659168334046593189)
                      ·
                        rfl

theorem cell23_7193394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_7193394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193394 prefixEnd_7193394 := by exact prefixLift 7193394
  have htrace : WordTrace (prefixWord ++ tailWord_7193394) baseStart_7193394 baseEnd_7193394 := by
    simpa [prefixWord, tailWord_7193394, baseEnd_7193394] using wordTrace_append hprefix tailTrace_7193394
  have hstable : (prefixWord ++ tailWord_7193394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193394).length < 2 ^ (prefixWord ++ tailWord_7193394).sum := by decide
  have hdescent : baseEnd_7193394 < baseStart_7193394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193427 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 2, 7]
def baseStart_7193427 : Nat := 118140960795 + 7193427 * 2 ^ 59
def prefixEnd_7193427 : Nat := 4983230072969 + 3 ^ 40 * 7193427 * 2
def baseEnd_7193427 : Nat := 1231228534676644139160179

theorem tailTrace_7193427 : CollatzResearch.WordTrace tailWord_7193427 prefixEnd_7193427 1231228534676644139160179 := by
  unfold tailWord_7193427
  simp only [CollatzResearch.WordTrace]
  refine ⟨262365836910449993367682535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174910557940299995578455023 262365836910449993367682535)
  ·
    refine ⟨393548755365674990051523803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262365836910449993367682535 393548755365674990051523803)
    ·
      refine ⟨590323133048512485077285705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393548755365674990051523803 590323133048512485077285705)
      ·
        refine ⟨442742349786384363807964279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590323133048512485077285705 442742349786384363807964279)
        ·
          refine ⟨664113524679576545711946419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442742349786384363807964279 664113524679576545711946419)
          ·
            refine ⟨996170287019364818567919629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664113524679576545711946419 996170287019364818567919629)
            ·
              refine ⟨373563857632261806962969861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 996170287019364818567919629 373563857632261806962969861)
              ·
                refine ⟨70043223306049088805556849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373563857632261806962969861 70043223306049088805556849)
                ·
                  refine ⟨52532417479536816604167637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70043223306049088805556849 52532417479536816604167637)
                  ·
                    refine ⟨1231228534676644139160179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52532417479536816604167637 1231228534676644139160179)
                    ·
                      rfl

theorem cell23_7193427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 7].length) (baseStart_7193427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193427 prefixEnd_7193427 := by exact prefixLift 7193427
  have htrace : WordTrace (prefixWord ++ tailWord_7193427) baseStart_7193427 baseEnd_7193427 := by
    simpa [prefixWord, tailWord_7193427, baseEnd_7193427] using wordTrace_append hprefix tailTrace_7193427
  have hstable : (prefixWord ++ tailWord_7193427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193427).length < 2 ^ (prefixWord ++ tailWord_7193427).sum := by decide
  have hdescent : baseEnd_7193427 < baseStart_7193427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193431 : List Nat := [1, 1, 3, 2, 4, 3, 2, 7]
def baseStart_7193431 : Nat := 118140960795 + 7193431 * 2 ^ 59
def prefixEnd_7193431 : Nat := 4983230072969 + 3 ^ 40 * 7193431 * 2
def baseEnd_7193431 : Nat := 136803246590835200067797

theorem tailTrace_7193431 : CollatzResearch.WordTrace tailWord_7193431 prefixEnd_7193431 136803246590835200067797 := by
  unfold tailWord_7193431
  simp only [CollatzResearch.WordTrace]
  refine ⟨262365982802435502050828147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174910655201623668033885431 262365982802435502050828147)
  ·
    refine ⟨393548974203653253076242221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262365982802435502050828147 393548974203653253076242221)
    ·
      refine ⟨147580865326369969903590833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393548974203653253076242221 147580865326369969903590833)
      ·
        refine ⟨110685648994777477427693125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147580865326369969903590833 110685648994777477427693125)
        ·
          refine ⟨20753559186520777017692461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110685648994777477427693125 20753559186520777017692461)
          ·
            refine ⟨7782584694945291381634673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20753559186520777017692461 7782584694945291381634673)
            ·
              refine ⟨5836938521208968536226005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7782584694945291381634673 5836938521208968536226005)
              ·
                refine ⟨136803246590835200067797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5836938521208968536226005 136803246590835200067797)
                ·
                  rfl

theorem cell23_7193431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 7].length) (baseStart_7193431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193431 prefixEnd_7193431 := by exact prefixLift 7193431
  have htrace : WordTrace (prefixWord ++ tailWord_7193431) baseStart_7193431 baseEnd_7193431 := by
    simpa [prefixWord, tailWord_7193431, baseEnd_7193431] using wordTrace_append hprefix tailTrace_7193431
  have hstable : (prefixWord ++ tailWord_7193431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193431).length < 2 ^ (prefixWord ++ tailWord_7193431).sum := by decide
  have hdescent : baseEnd_7193431 < baseStart_7193431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193484 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_7193484 : Nat := 118140960795 + 7193484 * 2 ^ 59
def prefixEnd_7193484 : Nat := 4983230072969 + 3 ^ 40 * 7193484 * 2
def baseEnd_7193484 : Nat := 3693714872427238694467775

theorem tailTrace_7193484 : CollatzResearch.WordTrace tailWord_7193484 prefixEnd_7193484 3693714872427238694467775 := by
  unfold tailWord_7193484
  simp only [CollatzResearch.WordTrace]
  refine ⟨131183957935621746051253753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174911943914162328068338337 131183957935621746051253753)
  ·
    refine ⟨98387968451716309538440315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131183957935621746051253753 98387968451716309538440315)
    ·
      refine ⟨147581952677574464307660473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98387968451716309538440315 147581952677574464307660473)
      ·
        refine ⟨110686464508180848230745355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147581952677574464307660473 110686464508180848230745355)
        ·
          refine ⟨166029696762271272346118033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110686464508180848230745355 166029696762271272346118033)
          ·
            refine ⟨124522272571703454259588525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166029696762271272346118033 124522272571703454259588525)
            ·
              refine ⟨46695852214388795347345697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124522272571703454259588525 46695852214388795347345697)
              ·
                refine ⟨35021889160791596510509273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46695852214388795347345697 35021889160791596510509273)
                ·
                  refine ⟨26266416870593697382881955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35021889160791596510509273 26266416870593697382881955)
                  ·
                    refine ⟨39399625305890546074322933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26266416870593697382881955 39399625305890546074322933)
                    ·
                      refine ⟨3693714872427238694467775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39399625305890546074322933 3693714872427238694467775)
                      ·
                        rfl

theorem cell23_7193484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_7193484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193484 prefixEnd_7193484 := by exact prefixLift 7193484
  have htrace : WordTrace (prefixWord ++ tailWord_7193484) baseStart_7193484 baseEnd_7193484 := by
    simpa [prefixWord, tailWord_7193484, baseEnd_7193484] using wordTrace_append hprefix tailTrace_7193484
  have hstable : (prefixWord ++ tailWord_7193484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193484).length < 2 ^ (prefixWord ++ tailWord_7193484).sum := by decide
  have hdescent : baseEnd_7193484 < baseStart_7193484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193551 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 2, 5]
def baseStart_7193551 : Nat := 118140960795 + 7193551 * 2 ^ 59
def prefixEnd_7193551 : Nat := 4983230072969 + 3 ^ 40 * 7193551 * 2
def baseEnd_7193551 : Nat := 1231249758543696644109989

theorem tailTrace_7193551 : CollatzResearch.WordTrace tailWord_7193551 prefixEnd_7193551 1231249758543696644109989 := by
  unfold tailWord_7193551
  simp only [CollatzResearch.WordTrace]
  refine ⟨262370359562000762545196507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174913573041333841696797671 262370359562000762545196507)
  ·
    refine ⟨393555539343001143817794761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262370359562000762545196507 393555539343001143817794761)
    ·
      refine ⟨295166654507250857863346071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393555539343001143817794761 295166654507250857863346071)
      ·
        refine ⟨442749981760876286795019107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295166654507250857863346071 442749981760876286795019107)
        ·
          refine ⟨664124972641314430192528661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442749981760876286795019107 664124972641314430192528661)
          ·
            refine ⟨31130858092561613915274781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 664124972641314430192528661 31130858092561613915274781)
            ·
              refine ⟨11674071784710605218228043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31130858092561613915274781 11674071784710605218228043)
              ·
                refine ⟨17511107677065907827342065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11674071784710605218228043 17511107677065907827342065)
                ·
                  refine ⟨13133330757799430870506549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17511107677065907827342065 13133330757799430870506549)
                  ·
                    refine ⟨1231249758543696644109989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13133330757799430870506549 1231249758543696644109989)
                    ·
                      rfl

theorem cell23_7193551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 5].length) (baseStart_7193551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193551 prefixEnd_7193551 := by exact prefixLift 7193551
  have htrace : WordTrace (prefixWord ++ tailWord_7193551) baseStart_7193551 baseEnd_7193551 := by
    simpa [prefixWord, tailWord_7193551, baseEnd_7193551] using wordTrace_append hprefix tailTrace_7193551
  have hstable : (prefixWord ++ tailWord_7193551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193551).length < 2 ^ (prefixWord ++ tailWord_7193551).sum := by decide
  have hdescent : baseEnd_7193551 < baseStart_7193551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193571 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 4]
def baseStart_7193571 : Nat := 118140960795 + 7193571 * 2 ^ 59
def prefixEnd_7193571 : Nat := 4983230072969 + 3 ^ 40 * 7193571 * 2
def baseEnd_7193571 : Nat := 3693759545244179854079875

theorem tailTrace_7193571 : CollatzResearch.WordTrace tailWord_7193571 prefixEnd_7193571 3693759545244179854079875 := by
  unfold tailWord_7193571
  simp only [CollatzResearch.WordTrace]
  refine ⟨262371089021928305960924567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174914059347952203973949711 262371089021928305960924567)
  ·
    refine ⟨393556633532892458941386851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262371089021928305960924567 393556633532892458941386851)
    ·
      refine ⟨590334950299338688412080277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393556633532892458941386851 590334950299338688412080277)
      ·
        refine ⟨27671950795281501019316263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 590334950299338688412080277 27671950795281501019316263)
        ·
          refine ⟨41507926192922251528974395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27671950795281501019316263 41507926192922251528974395)
          ·
            refine ⟨62261889289383377293461593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41507926192922251528974395 62261889289383377293461593)
            ·
              refine ⟨46696416967037532970096195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62261889289383377293461593 46696416967037532970096195)
              ·
                refine ⟨70044625450556299455144293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46696416967037532970096195 70044625450556299455144293)
                ·
                  refine ⟨13133367271979306147839555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70044625450556299455144293 13133367271979306147839555)
                  ·
                    refine ⟨19700050907968959221759333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13133367271979306147839555 19700050907968959221759333)
                    ·
                      refine ⟨3693759545244179854079875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19700050907968959221759333 3693759545244179854079875)
                      ·
                        rfl

theorem cell23_7193571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_7193571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193571 prefixEnd_7193571 := by exact prefixLift 7193571
  have htrace : WordTrace (prefixWord ++ tailWord_7193571) baseStart_7193571 baseEnd_7193571 := by
    simpa [prefixWord, tailWord_7193571, baseEnd_7193571] using wordTrace_append hprefix tailTrace_7193571
  have hstable : (prefixWord ++ tailWord_7193571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193571).length < 2 ^ (prefixWord ++ tailWord_7193571).sum := by decide
  have hdescent : baseEnd_7193571 < baseStart_7193571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193584 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_7193584 : Nat := 118140960795 + 7193584 * 2 ^ 59
def prefixEnd_7193584 : Nat := 4983230072969 + 3 ^ 40 * 7193584 * 2
def baseEnd_7193584 : Nat := 3693766220492688303217315

theorem tailTrace_7193584 : CollatzResearch.WordTrace tailWord_7193584 prefixEnd_7193584 3693766220492688303217315 := by
  unfold tailWord_7193584
  simp only [CollatzResearch.WordTrace]
  refine ⟨131185781585440604590573903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174914375447254139454098537 131185781585440604590573903)
  ·
    refine ⟨196778672378160906885860855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131185781585440604590573903 196778672378160906885860855)
    ·
      refine ⟨295168008567241360328791283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196778672378160906885860855 295168008567241360328791283)
      ·
        refine ⟨442752012850862040493186925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295168008567241360328791283 442752012850862040493186925)
        ·
          refine ⟨166032004819073265184945097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442752012850862040493186925 166032004819073265184945097)
          ·
            refine ⟨124524003614304948888708823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166032004819073265184945097 124524003614304948888708823)
            ·
              refine ⟨186786005421457423333063235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124524003614304948888708823 186786005421457423333063235)
              ·
                refine ⟨280179008132186134999594853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186786005421457423333063235 280179008132186134999594853)
                ·
                  refine ⟨52533564024784900312424035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280179008132186134999594853 52533564024784900312424035)
                  ·
                    refine ⟨78800346037177350468636053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52533564024784900312424035 78800346037177350468636053)
                    ·
                      refine ⟨3693766220492688303217315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78800346037177350468636053 3693766220492688303217315)
                      ·
                        rfl

theorem cell23_7193584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_7193584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193584 prefixEnd_7193584 := by exact prefixLift 7193584
  have htrace : WordTrace (prefixWord ++ tailWord_7193584) baseStart_7193584 baseEnd_7193584 := by
    simpa [prefixWord, tailWord_7193584, baseEnd_7193584] using wordTrace_append hprefix tailTrace_7193584
  have hstable : (prefixWord ++ tailWord_7193584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193584).length < 2 ^ (prefixWord ++ tailWord_7193584).sum := by decide
  have hdescent : baseEnd_7193584 < baseStart_7193584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193632 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 3, 4]
def baseStart_7193632 : Nat := 118140960795 + 7193632 * 2 ^ 59
def prefixEnd_7193632 : Nat := 4983230072969 + 3 ^ 40 * 7193632 * 2
def baseEnd_7193632 : Nat := 1231263622521368038472365

theorem tailTrace_7193632 : CollatzResearch.WordTrace tailWord_7193632 prefixEnd_7193632 1231263622521368038472365 := by
  unfold tailWord_7193632
  simp only [CollatzResearch.WordTrace]
  refine ⟨131186656937353656689447575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174915542583138208919263433 131186656937353656689447575)
  ·
    refine ⟨196779985406030485034171363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131186656937353656689447575 196779985406030485034171363)
    ·
      refine ⟨295169978109045727551257045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196779985406030485034171363 295169978109045727551257045)
      ·
        refine ⟨6918046361930759239482587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 295169978109045727551257045 6918046361930759239482587)
        ·
          refine ⟨10377069542896138859223881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6918046361930759239482587 10377069542896138859223881)
          ·
            refine ⟨7782802157172104144417911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10377069542896138859223881 7782802157172104144417911)
            ·
              refine ⟨11674203235758156216626867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7782802157172104144417911 11674203235758156216626867)
              ·
                refine ⟨17511304853637234324940301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11674203235758156216626867 17511304853637234324940301)
                ·
                  refine ⟨6566739320113962871852613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17511304853637234324940301 6566739320113962871852613)
                  ·
                    refine ⟨1231263622521368038472365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6566739320113962871852613 1231263622521368038472365)
                    ·
                      rfl

theorem cell23_7193632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 3, 4].length) (baseStart_7193632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193632 prefixEnd_7193632 := by exact prefixLift 7193632
  have htrace : WordTrace (prefixWord ++ tailWord_7193632) baseStart_7193632 baseEnd_7193632 := by
    simpa [prefixWord, tailWord_7193632, baseEnd_7193632] using wordTrace_append hprefix tailTrace_7193632
  have hstable : (prefixWord ++ tailWord_7193632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193632).length < 2 ^ (prefixWord ++ tailWord_7193632).sum := by decide
  have hdescent : baseEnd_7193632 < baseStart_7193632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193648 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 4, 3, 2]
def baseStart_7193648 : Nat := 118140960795 + 7193648 * 2 ^ 59
def prefixEnd_7193648 : Nat := 4983230072969 + 3 ^ 40 * 7193648 * 2
def baseEnd_7193648 : Nat := 3693799083254576052817021

theorem tailTrace_7193648 : CollatzResearch.WordTrace tailWord_7193648 prefixEnd_7193648 3693799083254576052817021 := by
  unfold tailWord_7193648
  simp only [CollatzResearch.WordTrace]
  refine ⟨131186948721324674055738799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174915931628432898740985065 131186948721324674055738799)
  ·
    refine ⟨196780423081987011083608199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131186948721324674055738799 196780423081987011083608199)
    ·
      refine ⟨295170634622980516625412299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196780423081987011083608199 295170634622980516625412299)
      ·
        refine ⟨442755951934470774938118449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295170634622980516625412299 442755951934470774938118449)
        ·
          refine ⟨332066963950853081203588837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442755951934470774938118449 332066963950853081203588837)
          ·
            refine ⟨62262555740784952725672907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332066963950853081203588837 62262555740784952725672907)
            ·
              refine ⟨93393833611177429088509361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62262555740784952725672907 93393833611177429088509361)
              ·
                refine ⟨70045375208383071816382021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93393833611177429088509361 70045375208383071816382021)
                ·
                  refine ⟨13133507851571825965571629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70045375208383071816382021 13133507851571825965571629)
                  ·
                    refine ⟨4925065444339434737089361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13133507851571825965571629 4925065444339434737089361)
                    ·
                      refine ⟨3693799083254576052817021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4925065444339434737089361 3693799083254576052817021)
                      ·
                        rfl

theorem cell23_7193648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 3, 2].length) (baseStart_7193648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193648 prefixEnd_7193648 := by exact prefixLift 7193648
  have htrace : WordTrace (prefixWord ++ tailWord_7193648) baseStart_7193648 baseEnd_7193648 := by
    simpa [prefixWord, tailWord_7193648, baseEnd_7193648] using wordTrace_append hprefix tailTrace_7193648
  have hstable : (prefixWord ++ tailWord_7193648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193648).length < 2 ^ (prefixWord ++ tailWord_7193648).sum := by decide
  have hdescent : baseEnd_7193648 < baseStart_7193648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193658 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 1, 5]
def baseStart_7193658 : Nat := 118140960795 + 7193658 * 2 ^ 59
def prefixEnd_7193658 : Nat := 4983230072969 + 3 ^ 40 * 7193658 * 2
def baseEnd_7193658 : Nat := 1231268072687040337897325

theorem tailTrace_7193658 : CollatzResearch.WordTrace tailWord_7193658 prefixEnd_7193658 1231268072687040337897325 := by
  unfold tailWord_7193658
  simp only [CollatzResearch.WordTrace]
  refine ⟨65593565543153279954835407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174916174781742079879561085 65593565543153279954835407)
  ·
    refine ⟨98390348314729919932253111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65593565543153279954835407 98390348314729919932253111)
    ·
      refine ⟨147585522472094879898379667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98390348314729919932253111 147585522472094879898379667)
      ·
        refine ⟨221378283708142319847569501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147585522472094879898379667 221378283708142319847569501)
        ·
          refine ⟨83016856390553369942838563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221378283708142319847569501 83016856390553369942838563)
          ·
            refine ⟨124525284585830054914257845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83016856390553369942838563 124525284585830054914257845)
            ·
              refine ⟨11674245429921567648211673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124525284585830054914257845 11674245429921567648211673)
              ·
                refine ⟨8755684072441175736158755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11674245429921567648211673 8755684072441175736158755)
                ·
                  refine ⟨13133526108661763604238133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8755684072441175736158755 13133526108661763604238133)
                  ·
                    refine ⟨1231268072687040337897325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13133526108661763604238133 1231268072687040337897325)
                    ·
                      rfl

theorem cell23_7193658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_7193658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193658 prefixEnd_7193658 := by exact prefixLift 7193658
  have htrace : WordTrace (prefixWord ++ tailWord_7193658) baseStart_7193658 baseEnd_7193658 := by
    simpa [prefixWord, tailWord_7193658, baseEnd_7193658] using wordTrace_append hprefix tailTrace_7193658
  have hstable : (prefixWord ++ tailWord_7193658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193658).length < 2 ^ (prefixWord ++ tailWord_7193658).sum := by decide
  have hdescent : baseEnd_7193658 < baseStart_7193658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193671 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 3, 6]
def baseStart_7193671 : Nat := 118140960795 + 7193671 * 2 ^ 59
def prefixEnd_7193671 : Nat := 4983230072969 + 3 ^ 40 * 7193671 * 2
def baseEnd_7193671 : Nat := 1231270297769876487609805

theorem tailTrace_7193671 : CollatzResearch.WordTrace tailWord_7193671 prefixEnd_7193671 1231270297769876487609805 := by
  unfold tailWord_7193671
  simp only [CollatzResearch.WordTrace]
  refine ⟨262374736321566023039564867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174916490881044015359709911 262374736321566023039564867)
  ·
    refine ⟨393562104482349034559347301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262374736321566023039564867 393562104482349034559347301)
    ·
      refine ⟨73792894590440443979877619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393562104482349034559347301 73792894590440443979877619)
      ·
        refine ⟨110689341885660665969816429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73792894590440443979877619 110689341885660665969816429)
        ·
          refine ⟨41508503207122749738681161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110689341885660665969816429 41508503207122749738681161)
          ·
            refine ⟨31131377405342062304010871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41508503207122749738681161 31131377405342062304010871)
            ·
              refine ⟨46697066108013093456016307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31131377405342062304010871 46697066108013093456016307)
              ·
                refine ⟨70045599162019640184024461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46697066108013093456016307 70045599162019640184024461)
                ·
                  refine ⟨26267099685757365069009173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70045599162019640184024461 26267099685757365069009173)
                  ·
                    refine ⟨1231270297769876487609805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26267099685757365069009173 1231270297769876487609805)
                    ·
                      rfl

theorem cell23_7193671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_7193671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193671 prefixEnd_7193671 := by exact prefixLift 7193671
  have htrace : WordTrace (prefixWord ++ tailWord_7193671) baseStart_7193671 baseEnd_7193671 := by
    simpa [prefixWord, tailWord_7193671, baseEnd_7193671] using wordTrace_append hprefix tailTrace_7193671
  have hstable : (prefixWord ++ tailWord_7193671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193671).length < 2 ^ (prefixWord ++ tailWord_7193671).sum := by decide
  have hdescent : baseEnd_7193671 < baseStart_7193671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193695 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 3, 2, 2]
def baseStart_7193695 : Nat := 118140960795 + 7193695 * 2 ^ 59
def prefixEnd_7193695 : Nat := 4983230072969 + 3 ^ 40 * 7193695 * 2
def baseEnd_7193695 : Nat := 3693823216845337368929305

theorem tailTrace_7193695 : CollatzResearch.WordTrace tailWord_7193695 prefixEnd_7193695 3693823216845337368929305 := by
  unfold tailWord_7193695
  simp only [CollatzResearch.WordTrace]
  refine ⟨262375611673479075138438539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174917074448986050092292359 262375611673479075138438539)
  ·
    refine ⟨393563417510218612707657809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262375611673479075138438539 393563417510218612707657809)
    ·
      refine ⟨295172563132663959530743357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393563417510218612707657809 295172563132663959530743357)
      ·
        refine ⟨110689711174748984824028759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295172563132663959530743357 110689711174748984824028759)
        ·
          refine ⟨166034566762123477236043139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110689711174748984824028759 166034566762123477236043139)
          ·
            refine ⟨249051850143185215854064709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166034566762123477236043139 249051850143185215854064709)
            ·
              refine ⟨46697221901847227972637133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249051850143185215854064709 46697221901847227972637133)
              ·
                refine ⟨17511458213192710489738925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46697221901847227972637133 17511458213192710489738925)
                ·
                  refine ⟨6566796829947266433652097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17511458213192710489738925 6566796829947266433652097)
                  ·
                    refine ⟨4925097622460449825239073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6566796829947266433652097 4925097622460449825239073)
                    ·
                      refine ⟨3693823216845337368929305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4925097622460449825239073 3693823216845337368929305)
                      ·
                        rfl

theorem cell23_7193695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_7193695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193695 prefixEnd_7193695 := by exact prefixLift 7193695
  have htrace : WordTrace (prefixWord ++ tailWord_7193695) baseStart_7193695 baseEnd_7193695 := by
    simpa [prefixWord, tailWord_7193695, baseEnd_7193695] using wordTrace_append hprefix tailTrace_7193695
  have hstable : (prefixWord ++ tailWord_7193695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193695).length < 2 ^ (prefixWord ++ tailWord_7193695).sum := by decide
  have hdescent : baseEnd_7193695 < baseStart_7193695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193708 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 4]
def baseStart_7193708 : Nat := 118140960795 + 7193708 * 2 ^ 59
def prefixEnd_7193708 : Nat := 4983230072969 + 3 ^ 40 * 7193708 * 2
def baseEnd_7193708 : Nat := 3693829892093845818066745

theorem tailTrace_7193708 : CollatzResearch.WordTrace tailWord_7193708 prefixEnd_7193708 3693829892093845818066745 := by
  unfold tailWord_7193708
  simp only [CollatzResearch.WordTrace]
  refine ⟨131188042911215989179330889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174917390548287985572441185 131188042911215989179330889)
  ·
    refine ⟨98391032183411991884498167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131188042911215989179330889 98391032183411991884498167)
    ·
      refine ⟨147586548275117987826747251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98391032183411991884498167 147586548275117987826747251)
      ·
        refine ⟨221379822412676981740120877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147586548275117987826747251 221379822412676981740120877)
        ·
          refine ⟨83017433404753868152545329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221379822412676981740120877 83017433404753868152545329)
          ·
            refine ⟨62263075053565401114408997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83017433404753868152545329 62263075053565401114408997)
            ·
              refine ⟨11674326572543512708951687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62263075053565401114408997 11674326572543512708951687)
              ·
                refine ⟨17511489858815269063427531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11674326572543512708951687 17511489858815269063427531)
                ·
                  refine ⟨26267234788222903595141297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17511489858815269063427531 26267234788222903595141297)
                  ·
                    refine ⟨19700426091167177696355973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26267234788222903595141297 19700426091167177696355973)
                    ·
                      refine ⟨3693829892093845818066745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19700426091167177696355973 3693829892093845818066745)
                      ·
                        rfl

theorem cell23_7193708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_7193708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193708 prefixEnd_7193708 := by exact prefixLift 7193708
  have htrace : WordTrace (prefixWord ++ tailWord_7193708) baseStart_7193708 baseEnd_7193708 := by
    simpa [prefixWord, tailWord_7193708, baseEnd_7193708] using wordTrace_append hprefix tailTrace_7193708
  have hstable : (prefixWord ++ tailWord_7193708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193708).length < 2 ^ (prefixWord ++ tailWord_7193708).sum := by decide
  have hdescent : baseEnd_7193708 < baseStart_7193708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193728 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 3]
def baseStart_7193728 : Nat := 118140960795 + 7193728 * 2 ^ 59
def prefixEnd_7193728 : Nat := 4983230072969 + 3 ^ 40 * 7193728 * 2
def baseEnd_7193728 : Nat := 3693840161706935739816653

theorem tailTrace_7193728 : CollatzResearch.WordTrace tailWord_7193728 prefixEnd_7193728 3693840161706935739816653 := by
  unfold tailWord_7193728
  simp only [CollatzResearch.WordTrace]
  refine ⟨131188407641179760887194919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174917876854906347849593225 131188407641179760887194919)
  ·
    refine ⟨196782611461769641330792379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131188407641179760887194919 196782611461769641330792379)
    ·
      refine ⟨295173917192654461996188569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196782611461769641330792379 295173917192654461996188569)
      ·
        refine ⟨221380437894490846497141427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295173917192654461996188569 221380437894490846497141427)
        ·
          refine ⟨332070656841736269745712141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221380437894490846497141427 332070656841736269745712141)
          ·
            refine ⟨124526496315651101154642053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332070656841736269745712141 124526496315651101154642053)
            ·
              refine ⟨23348718059184581466495385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124526496315651101154642053 23348718059184581466495385)
              ·
                refine ⟨17511538544388436099871539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23348718059184581466495385 17511538544388436099871539)
                ·
                  refine ⟨26267307816582654149807309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17511538544388436099871539 26267307816582654149807309)
                  ·
                    refine ⟨9850240431218495306177741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26267307816582654149807309 9850240431218495306177741)
                    ·
                      refine ⟨3693840161706935739816653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9850240431218495306177741 3693840161706935739816653)
                      ·
                        rfl

theorem cell23_7193728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_7193728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193728 prefixEnd_7193728 := by exact prefixLift 7193728
  have htrace : WordTrace (prefixWord ++ tailWord_7193728) baseStart_7193728 baseEnd_7193728 := by
    simpa [prefixWord, tailWord_7193728, baseEnd_7193728] using wordTrace_append hprefix tailTrace_7193728
  have hstable : (prefixWord ++ tailWord_7193728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193728).length < 2 ^ (prefixWord ++ tailWord_7193728).sum := by decide
  have hdescent : baseEnd_7193728 < baseStart_7193728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193729 : List Nat := [1, 2, 4, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_7193729 : Nat := 118140960795 + 7193729 * 2 ^ 59
def prefixEnd_7193729 : Nat := 4983230072969 + 3 ^ 40 * 7193729 * 2
def baseEnd_7193729 : Nat := 3693840675187590235904149

theorem tailTrace_7193729 : CollatzResearch.WordTrace tailWord_7193729 prefixEnd_7193729 3693840675187590235904149 := by
  unfold tailWord_7193729
  simp only [CollatzResearch.WordTrace]
  refine ⟨262376851755355898945176241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174917901170237265963450827 262376851755355898945176241)
  ·
    refine ⟨196782638816516924208882181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262376851755355898945176241 196782638816516924208882181)
    ·
      refine ⟨36896744778096923289165409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196782638816516924208882181 36896744778096923289165409)
      ·
        refine ⟨27672558583572692466874057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36896744778096923289165409 27672558583572692466874057)
        ·
          refine ⟨20754418937679519350155543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27672558583572692466874057 20754418937679519350155543)
          ·
            refine ⟨31131628406519279025233315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20754418937679519350155543 31131628406519279025233315)
            ·
              refine ⟨46697442609778918537849973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31131628406519279025233315 46697442609778918537849973)
              ·
                refine ⟨4377885244666773612923435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46697442609778918537849973 4377885244666773612923435)
                ·
                  refine ⟨6566827867000160419385153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4377885244666773612923435 6566827867000160419385153)
                  ·
                    refine ⟨4925120900250120314538865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6566827867000160419385153 4925120900250120314538865)
                    ·
                      refine ⟨3693840675187590235904149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4925120900250120314538865 3693840675187590235904149)
                      ·
                        rfl

theorem cell23_7193729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_7193729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193729 prefixEnd_7193729 := by exact prefixLift 7193729
  have htrace : WordTrace (prefixWord ++ tailWord_7193729) baseStart_7193729 baseEnd_7193729 := by
    simpa [prefixWord, tailWord_7193729, baseEnd_7193729] using wordTrace_append hprefix tailTrace_7193729
  have hstable : (prefixWord ++ tailWord_7193729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193729).length < 2 ^ (prefixWord ++ tailWord_7193729).sum := by decide
  have hdescent : baseEnd_7193729 < baseStart_7193729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193732 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_7193732 : Nat := 118140960795 + 7193732 * 2 ^ 59
def prefixEnd_7193732 : Nat := 4983230072969 + 3 ^ 40 * 7193732 * 2
def baseEnd_7193732 : Nat := 3693842215629553724166635

theorem tailTrace_7193732 : CollatzResearch.WordTrace tailWord_7193732 prefixEnd_7193732 3693842215629553724166635 := by
  unfold tailWord_7193732
  simp only [CollatzResearch.WordTrace]
  refine ⟨131188480587172515228767725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174917974116230020305023633 131188480587172515228767725)
  ·
    refine ⟨49195680220189693210787897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131188480587172515228767725 49195680220189693210787897)
    ·
      refine ⟨36896760165142269908090923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49195680220189693210787897 36896760165142269908090923)
      ·
        refine ⟨55345140247713404862136385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36896760165142269908090923 55345140247713404862136385)
        ·
          refine ⟨41508855185785053646602289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55345140247713404862136385 41508855185785053646602289)
          ·
            refine ⟨31131641389338790234951717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41508855185785053646602289 31131641389338790234951717)
            ·
              refine ⟨5837182760501023169053447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31131641389338790234951717 5837182760501023169053447)
              ·
                refine ⟨8755774140751534753580171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837182760501023169053447 8755774140751534753580171)
                ·
                  refine ⟨13133661211127302130370257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8755774140751534753580171 13133661211127302130370257)
                  ·
                    refine ⟨9850245908345476597777693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13133661211127302130370257 9850245908345476597777693)
                    ·
                      refine ⟨3693842215629553724166635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9850245908345476597777693 3693842215629553724166635)
                      ·
                        rfl

theorem cell23_7193732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_7193732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193732 prefixEnd_7193732 := by exact prefixLift 7193732
  have htrace : WordTrace (prefixWord ++ tailWord_7193732) baseStart_7193732 baseEnd_7193732 := by
    simpa [prefixWord, tailWord_7193732, baseEnd_7193732] using wordTrace_append hprefix tailTrace_7193732
  have hstable : (prefixWord ++ tailWord_7193732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193732).length < 2 ^ (prefixWord ++ tailWord_7193732).sum := by decide
  have hdescent : baseEnd_7193732 < baseStart_7193732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193788 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_7193788 : Nat := 118140960795 + 7193788 * 2 ^ 59
def prefixEnd_7193788 : Nat := 4983230072969 + 3 ^ 40 * 7193788 * 2
def baseEnd_7193788 : Nat := 3693870970546205505066377

theorem tailTrace_7193788 : CollatzResearch.WordTrace tailWord_7193788 prefixEnd_7193788 3693870970546205505066377 := by
  unfold tailWord_7193788
  simp only [CollatzResearch.WordTrace]
  refine ⟨131189501831071076010787009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174919335774761434681049345 131189501831071076010787009)
  ·
    refine ⟨98392126373303307008090257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131189501831071076010787009 98392126373303307008090257)
    ·
      refine ⟨73794094779977480256067693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98392126373303307008090257 73794094779977480256067693)
      ·
        refine ⟨27672785542491555096025385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73794094779977480256067693 27672785542491555096025385)
        ·
          refine ⟨20754589156868666322019039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27672785542491555096025385 20754589156868666322019039)
          ·
            refine ⟨31131883735302999483028559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20754589156868666322019039 31131883735302999483028559)
            ·
              refine ⟨46697825602954499224542839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31131883735302999483028559 46697825602954499224542839)
              ·
                refine ⟨70046738404431748836814259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46697825602954499224542839 70046738404431748836814259)
                ·
                  refine ⟨105070107606647623255221389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70046738404431748836814259 105070107606647623255221389)
                  ·
                    refine ⟨39401290352492858720708021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105070107606647623255221389 39401290352492858720708021)
                    ·
                      refine ⟨3693870970546205505066377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39401290352492858720708021 3693870970546205505066377)
                      ·
                        rfl

theorem cell23_7193788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_7193788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193788 prefixEnd_7193788 := by exact prefixLift 7193788
  have htrace : WordTrace (prefixWord ++ tailWord_7193788) baseStart_7193788 baseEnd_7193788 := by
    simpa [prefixWord, tailWord_7193788, baseEnd_7193788] using wordTrace_append hprefix tailTrace_7193788
  have hstable : (prefixWord ++ tailWord_7193788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193788).length < 2 ^ (prefixWord ++ tailWord_7193788).sum := by decide
  have hdescent : baseEnd_7193788 < baseStart_7193788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193791 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 9]
def baseStart_7193791 : Nat := 118140960795 + 7193791 * 2 ^ 59
def prefixEnd_7193791 : Nat := 4983230072969 + 3 ^ 40 * 7193791 * 2
def baseEnd_7193791 : Nat := 410430278998685443703207

theorem tailTrace_7193791 : CollatzResearch.WordTrace tailWord_7193791 prefixEnd_7193791 410430278998685443703207 := by
  unfold tailWord_7193791
  simp only [CollatzResearch.WordTrace]
  refine ⟨262379113081131283533933227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174919408720754189022622151 262379113081131283533933227)
  ·
    refine ⟨393568669621696925300899841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262379113081131283533933227 393568669621696925300899841)
    ·
      refine ⟨295176502216272693975674881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393568669621696925300899841 295176502216272693975674881)
      ·
        refine ⟨221382376662204520481756161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295176502216272693975674881 221382376662204520481756161)
        ·
          refine ⟨166036782496653390361317121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221382376662204520481756161 166036782496653390361317121)
          ·
            refine ⟨124527586872490042770987841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166036782496653390361317121 124527586872490042770987841)
            ·
              refine ⟨93395690154367532078240881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124527586872490042770987841 93395690154367532078240881)
              ·
                refine ⟨70046767615775649058680661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93395690154367532078240881 70046767615775649058680661)
                ·
                  refine ⟨410430278998685443703207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70046767615775649058680661 410430278998685443703207)
                  ·
                    rfl

theorem cell23_7193791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 9].length) (baseStart_7193791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193791 prefixEnd_7193791 := by exact prefixLift 7193791
  have htrace : WordTrace (prefixWord ++ tailWord_7193791) baseStart_7193791 baseEnd_7193791 := by
    simpa [prefixWord, tailWord_7193791, baseEnd_7193791] using wordTrace_append hprefix tailTrace_7193791
  have hstable : (prefixWord ++ tailWord_7193791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193791).length < 2 ^ (prefixWord ++ tailWord_7193791).sum := by decide
  have hdescent : baseEnd_7193791 < baseStart_7193791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193802 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2]
def baseStart_7193802 : Nat := 118140960795 + 7193802 * 2 ^ 59
def prefixEnd_7193802 : Nat := 4983230072969 + 3 ^ 40 * 7193802 * 2
def baseEnd_7193802 : Nat := 3693878159275368450291313

theorem tailTrace_7193802 : CollatzResearch.WordTrace tailWord_7193802 prefixEnd_7193802 3693878159275368450291313 := by
  unfold tailWord_7193802
  simp only [CollatzResearch.WordTrace]
  refine ⟨65594878571022858103145915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174919676189394288275055773 65594878571022858103145915)
  ·
    refine ⟨98392317856534287154718873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65594878571022858103145915 98392317856534287154718873)
    ·
      refine ⟨73794238392400715366039155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98392317856534287154718873 73794238392400715366039155)
      ·
        refine ⟨110691357588601073049058733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73794238392400715366039155 110691357588601073049058733)
        ·
          refine ⟨41509259095725402393397025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110691357588601073049058733 41509259095725402393397025)
          ·
            refine ⟨31131944321794051795047769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41509259095725402393397025 31131944321794051795047769)
            ·
              refine ⟨23348958241345538846285827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31131944321794051795047769 23348958241345538846285827)
              ·
                refine ⟨35023437362018308269428741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23348958241345538846285827 35023437362018308269428741)
                ·
                  refine ⟨6566894505378432800517889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35023437362018308269428741 6566894505378432800517889)
                  ·
                    refine ⟨4925170879033824600388417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6566894505378432800517889 4925170879033824600388417)
                    ·
                      refine ⟨3693878159275368450291313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4925170879033824600388417 3693878159275368450291313)
                      ·
                        rfl

theorem cell23_7193802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_7193802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193802 prefixEnd_7193802 := by exact prefixLift 7193802
  have htrace : WordTrace (prefixWord ++ tailWord_7193802) baseStart_7193802 baseEnd_7193802 := by
    simpa [prefixWord, tailWord_7193802, baseEnd_7193802] using wordTrace_append hprefix tailTrace_7193802
  have hstable : (prefixWord ++ tailWord_7193802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193802).length < 2 ^ (prefixWord ++ tailWord_7193802).sum := by decide
  have hdescent : baseEnd_7193802 < baseStart_7193802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193818 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3]
def baseStart_7193818 : Nat := 118140960795 + 7193818 * 2 ^ 59
def prefixEnd_7193818 : Nat := 4983230072969 + 3 ^ 40 * 7193818 * 2
def baseEnd_7193818 : Nat := 3693886374965840387691239

theorem tailTrace_7193818 : CollatzResearch.WordTrace tailWord_7193818 prefixEnd_7193818 3693886374965840387691239 := by
  unfold tailWord_7193818
  simp only [CollatzResearch.WordTrace]
  refine ⟨65595024463008366786291527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174920065234688978096777405 65595024463008366786291527)
  ·
    refine ⟨98392536694512550179437291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65595024463008366786291527 98392536694512550179437291)
    ·
      refine ⟨147588805041768825269155937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98392536694512550179437291 147588805041768825269155937)
      ·
        refine ⟨110691603781326618951866953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147588805041768825269155937 110691603781326618951866953)
        ·
          refine ⟨83018702835994964213900215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110691603781326618951866953 83018702835994964213900215)
          ·
            refine ⟨124528054253992446320850323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83018702835994964213900215 124528054253992446320850323)
            ·
              refine ⟨186792081380988669481275485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124528054253992446320850323 186792081380988669481275485)
              ·
                refine ⟨70047030517870751055478307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186792081380988669481275485 70047030517870751055478307)
                ·
                  refine ⟨105070545776806126583217461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70047030517870751055478307 105070545776806126583217461)
                  ·
                    refine ⟨9850363666575574367176637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105070545776806126583217461 9850363666575574367176637)
                    ·
                      refine ⟨3693886374965840387691239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9850363666575574367176637 3693886374965840387691239)
                      ·
                        rfl

theorem cell23_7193818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_7193818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193818 prefixEnd_7193818 := by exact prefixLift 7193818
  have htrace : WordTrace (prefixWord ++ tailWord_7193818) baseStart_7193818 baseEnd_7193818 := by
    simpa [prefixWord, tailWord_7193818, baseEnd_7193818] using wordTrace_append hprefix tailTrace_7193818
  have hstable : (prefixWord ++ tailWord_7193818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193818).length < 2 ^ (prefixWord ++ tailWord_7193818).sum := by decide
  have hdescent : baseEnd_7193818 < baseStart_7193818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193838 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_7193838 : Nat := 118140960795 + 7193838 * 2 ^ 59
def prefixEnd_7193838 : Nat := 4983230072969 + 3 ^ 40 * 7193838 * 2
def baseEnd_7193838 : Nat := 1231298881526310103147049

theorem tailTrace_7193838 : CollatzResearch.WordTrace tailWord_7193838 prefixEnd_7193838 1231298881526310103147049 := by
  unfold tailWord_7193838
  simp only [CollatzResearch.WordTrace]
  refine ⟨32797603413995126320111771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174920551541307340373929445 32797603413995126320111771)
  ·
    refine ⟨49196405120992689480167657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32797603413995126320111771 49196405120992689480167657)
    ·
      refine ⟨36897303840744517110125743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49196405120992689480167657 36897303840744517110125743)
      ·
        refine ⟨55345955761116775665188615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36897303840744517110125743 55345955761116775665188615)
        ·
          refine ⟨83018933641675163497782923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55345955761116775665188615 83018933641675163497782923)
          ·
            refine ⟨124528400462512745246674385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83018933641675163497782923 124528400462512745246674385)
            ·
              refine ⟨93396300346884558935005789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124528400462512745246674385 93396300346884558935005789)
              ·
                refine ⟨35023612630081709600627171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93396300346884558935005789 35023612630081709600627171)
                ·
                  refine ⟨52535418945122564400940757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35023612630081709600627171 52535418945122564400940757)
                  ·
                    refine ⟨1231298881526310103147049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52535418945122564400940757 1231298881526310103147049)
                    ·
                      rfl

theorem cell23_7193838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_7193838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193838 prefixEnd_7193838 := by exact prefixLift 7193838
  have htrace : WordTrace (prefixWord ++ tailWord_7193838) baseStart_7193838 baseEnd_7193838 := by
    simpa [prefixWord, tailWord_7193838, baseEnd_7193838] using wordTrace_append hprefix tailTrace_7193838
  have hstable : (prefixWord ++ tailWord_7193838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193838).length < 2 ^ (prefixWord ++ tailWord_7193838).sum := by decide
  have hdescent : baseEnd_7193838 < baseStart_7193838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193932 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 6]
def baseStart_7193932 : Nat := 118140960795 + 7193932 * 2 ^ 59
def prefixEnd_7193932 : Nat := 4983230072969 + 3 ^ 40 * 7193932 * 2
def baseEnd_7193932 : Nat := 410438323528939215740635

theorem tailTrace_7193932 : CollatzResearch.WordTrace tailWord_7193932 prefixEnd_7193932 410438323528939215740635 := by
  unfold tailWord_7193932
  simp only [CollatzResearch.WordTrace]
  refine ⟨131192127886810232307408025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174922837182413643076544033 131192127886810232307408025)
  ·
    refine ⟨98394095915107674230556019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131192127886810232307408025 98394095915107674230556019)
    ·
      refine ⟨147591143872661511345834029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98394095915107674230556019 147591143872661511345834029)
      ·
        refine ⟨55346678952248066754687761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147591143872661511345834029 55346678952248066754687761)
        ·
          refine ⟨41510009214186050066015821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55346678952248066754687761 41510009214186050066015821)
          ·
            refine ⟨15566253455319768774755933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41510009214186050066015821 15566253455319768774755933)
            ·
              refine ⟨5837345045744913290533475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15566253455319768774755933 5837345045744913290533475)
              ·
                refine ⟨8756017568617369935800213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837345045744913290533475 8756017568617369935800213)
                ·
                  refine ⟨410438323528939215740635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8756017568617369935800213 410438323528939215740635)
                  ·
                    rfl

theorem cell23_7193932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_7193932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193932 prefixEnd_7193932 := by exact prefixLift 7193932
  have htrace : WordTrace (prefixWord ++ tailWord_7193932) baseStart_7193932 baseEnd_7193932 := by
    simpa [prefixWord, tailWord_7193932, baseEnd_7193932] using wordTrace_append hprefix tailTrace_7193932
  have hstable : (prefixWord ++ tailWord_7193932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193932).length < 2 ^ (prefixWord ++ tailWord_7193932).sum := by decide
  have hdescent : baseEnd_7193932 < baseStart_7193932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193945 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 1, 5]
def baseStart_7193945 : Nat := 118140960795 + 7193945 * 2 ^ 59
def prefixEnd_7193945 : Nat := 4983230072969 + 3 ^ 40 * 7193945 * 2
def baseEnd_7193945 : Nat := 1231317195669653796934385

theorem tailTrace_7193945 : CollatzResearch.WordTrace tailWord_7193945 prefixEnd_7193945 1231317195669653796934385 := by
  unfold tailWord_7193945
  simp only [CollatzResearch.WordTrace]
  refine ⟨262384729922573367835039289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174923153281715578556692859 262384729922573367835039289)
  ·
    refine ⟨196788547441930025876279467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262384729922573367835039289 196788547441930025876279467)
    ·
      refine ⟨295182821162895038814419201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196788547441930025876279467 295182821162895038814419201)
      ·
        refine ⟨221387115872171279110814401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295182821162895038814419201 221387115872171279110814401)
        ·
          refine ⟨166040336904128459333110801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221387115872171279110814401 166040336904128459333110801)
          ·
            refine ⟨124530252678096344499833101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166040336904128459333110801 124530252678096344499833101)
            ·
              refine ⟨46698844754286129187437413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124530252678096344499833101 46698844754286129187437413)
              ·
                refine ⟨8756033391428649222644515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46698844754286129187437413 8756033391428649222644515)
                ·
                  refine ⟨13134050087142973833966773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8756033391428649222644515 13134050087142973833966773)
                  ·
                    refine ⟨1231317195669653796934385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13134050087142973833966773 1231317195669653796934385)
                    ·
                      rfl

theorem cell23_7193945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 5].length) (baseStart_7193945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193945 prefixEnd_7193945 := by exact prefixLift 7193945
  have htrace : WordTrace (prefixWord ++ tailWord_7193945) baseStart_7193945 baseEnd_7193945 := by
    simpa [prefixWord, tailWord_7193945, baseEnd_7193945] using wordTrace_append hprefix tailTrace_7193945
  have hstable : (prefixWord ++ tailWord_7193945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193945).length < 2 ^ (prefixWord ++ tailWord_7193945).sum := by decide
  have hdescent : baseEnd_7193945 < baseStart_7193945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193952 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 1, 5, 2]
def baseStart_7193952 : Nat := 118140960795 + 7193952 * 2 ^ 59
def prefixEnd_7193952 : Nat := 4983230072969 + 3 ^ 40 * 7193952 * 2
def baseEnd_7193952 : Nat := 3693955181373542863415623

theorem tailTrace_7193952 : CollatzResearch.WordTrace tailWord_7193952 prefixEnd_7193952 3693955181373542863415623 := by
  unfold tailWord_7193952
  simp only [CollatzResearch.WordTrace]
  refine ⟨131192492616774004015272055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174923323489032005353696073 131192492616774004015272055)
  ·
    refine ⟨196788738925161006022908083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131192492616774004015272055 196788738925161006022908083)
    ·
      refine ⟨295183108387741509034362125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196788738925161006022908083 295183108387741509034362125)
      ·
        refine ⟨110693665645403065887885797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295183108387741509034362125 110693665645403065887885797)
        ·
          refine ⟨20755062308513074853978587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110693665645403065887885797 20755062308513074853978587)
          ·
            refine ⟨31132593462769612280967881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20755062308513074853978587 31132593462769612280967881)
            ·
              refine ⟨23349445097077209210725911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31132593462769612280967881 23349445097077209210725911)
              ·
                refine ⟨35024167645615813816088867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23349445097077209210725911 35024167645615813816088867)
                ·
                  refine ⟨52536251468423720724133301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35024167645615813816088867 52536251468423720724133301)
                  ·
                    refine ⟨4925273575164723817887497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52536251468423720724133301 4925273575164723817887497)
                    ·
                      refine ⟨3693955181373542863415623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4925273575164723817887497 3693955181373542863415623)
                      ·
                        rfl

theorem cell23_7193952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_7193952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193952 prefixEnd_7193952 := by exact prefixLift 7193952
  have htrace : WordTrace (prefixWord ++ tailWord_7193952) baseStart_7193952 baseEnd_7193952 := by
    simpa [prefixWord, tailWord_7193952, baseEnd_7193952] using wordTrace_append hprefix tailTrace_7193952
  have hstable : (prefixWord ++ tailWord_7193952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193952).length < 2 ^ (prefixWord ++ tailWord_7193952).sum := by decide
  have hdescent : baseEnd_7193952 < baseStart_7193952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193975 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 4, 4]
def baseStart_7193975 : Nat := 118140960795 + 7193975 * 2 ^ 59
def prefixEnd_7193975 : Nat := 4983230072969 + 3 ^ 40 * 7193975 * 2
def baseEnd_7193975 : Nat := 1231322330476198757809339

theorem tailTrace_7193975 : CollatzResearch.WordTrace tailWord_7193975 prefixEnd_7193975 1231322330476198757809339 := by
  unfold tailWord_7193975
  simp only [CollatzResearch.WordTrace]
  refine ⟨262385824112464682958631379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174923882741643121972420919 262385824112464682958631379)
  ·
    refine ⟨393578736168697024437947069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262385824112464682958631379 393578736168697024437947069)
    ·
      refine ⟨147592026063261384164230151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393578736168697024437947069 147592026063261384164230151)
      ·
        refine ⟨221388039094892076246345227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147592026063261384164230151 221388039094892076246345227)
        ·
          refine ⟨332082058642338114369517841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221388039094892076246345227 332082058642338114369517841)
          ·
            refine ⟨249061543981753585777138381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332082058642338114369517841 249061543981753585777138381)
            ·
              refine ⟨93398078993157594666426893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249061543981753585777138381 93398078993157594666426893)
              ·
                refine ⟨35024279622434097999910085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93398078993157594666426893 35024279622434097999910085)
                ·
                  refine ⟨6567052429206393374983141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35024279622434097999910085 6567052429206393374983141)
                  ·
                    refine ⟨1231322330476198757809339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6567052429206393374983141 1231322330476198757809339)
                    ·
                      rfl

theorem cell23_7193975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_7193975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193975 prefixEnd_7193975 := by exact prefixLift 7193975
  have htrace : WordTrace (prefixWord ++ tailWord_7193975) baseStart_7193975 baseEnd_7193975 := by
    simpa [prefixWord, tailWord_7193975, baseEnd_7193975] using wordTrace_append hprefix tailTrace_7193975
  have hstable : (prefixWord ++ tailWord_7193975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193975).length < 2 ^ (prefixWord ++ tailWord_7193975).sum := by decide
  have hdescent : baseEnd_7193975 < baseStart_7193975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7193995 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 4]
def baseStart_7193995 : Nat := 118140960795 + 7193995 * 2 ^ 59
def prefixEnd_7193995 : Nat := 4983230072969 + 3 ^ 40 * 7193995 * 2
def baseEnd_7193995 : Nat := 3693977261041686195177925

theorem tailTrace_7193995 : CollatzResearch.WordTrace tailWord_7193995 prefixEnd_7193995 3693977261041686195177925 := by
  unfold tailWord_7193995
  simp only [CollatzResearch.WordTrace]
  refine ⟨262386553572392226374359439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174924369048261484249572959 262386553572392226374359439)
  ·
    refine ⟨393579830358588339561539159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262386553572392226374359439 393579830358588339561539159)
    ·
      refine ⟨590369745537882509342308739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393579830358588339561539159 590369745537882509342308739)
      ·
        refine ⟨885554618306823764013463109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590369745537882509342308739 885554618306823764013463109)
        ·
          refine ⟨166041490932529455752524333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 885554618306823764013463109 166041490932529455752524333)
          ·
            refine ⟨62265559099698545907196625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166041490932529455752524333 62265559099698545907196625)
            ·
              refine ⟨46699169324773909430397469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62265559099698545907196625 46699169324773909430397469)
              ·
                refine ⟨17512188496790216036399051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46699169324773909430397469 17512188496790216036399051)
                ·
                  refine ⟨26268282745185324054598577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17512188496790216036399051 26268282745185324054598577)
                  ·
                    refine ⟨19701212058888993040948933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26268282745185324054598577 19701212058888993040948933)
                    ·
                      refine ⟨3693977261041686195177925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19701212058888993040948933 3693977261041686195177925)
                      ·
                        rfl

theorem cell23_7193995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 4].length) (baseStart_7193995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7193995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7193995 prefixEnd_7193995 := by exact prefixLift 7193995
  have htrace : WordTrace (prefixWord ++ tailWord_7193995) baseStart_7193995 baseEnd_7193995 := by
    simpa [prefixWord, tailWord_7193995, baseEnd_7193995] using wordTrace_append hprefix tailTrace_7193995
  have hstable : (prefixWord ++ tailWord_7193995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7193995).length < 2 ^ (prefixWord ++ tailWord_7193995).sum := by decide
  have hdescent : baseEnd_7193995 < baseStart_7193995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7193995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194016 : List Nat := [2, 1, 1, 4, 1, 2, 2, 5, 1, 2, 2]
def baseStart_7194016 : Nat := 118140960795 + 7194016 * 2 ^ 59
def prefixEnd_7194016 : Nat := 4983230072969 + 3 ^ 40 * 7194016 * 2
def baseEnd_7194016 : Nat := 3693988044135430613015329

theorem tailTrace_7194016 : CollatzResearch.WordTrace tailWord_7194016 prefixEnd_7194016 3693988044135430613015329 := by
  unfold tailWord_7194016
  simp only [CollatzResearch.WordTrace]
  refine ⟨131193659752658073480436951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174924879670210764640582601 131193659752658073480436951)
  ·
    refine ⟨196790489628987110220655427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131193659752658073480436951 196790489628987110220655427)
    ·
      refine ⟨295185734443480665330983141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196790489628987110220655427 295185734443480665330983141)
      ·
        refine ⟨55347325208152624749559339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295185734443480665330983141 55347325208152624749559339)
        ·
          refine ⟨83020987812228937124339009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55347325208152624749559339 83020987812228937124339009)
          ·
            refine ⟨62265740859171702843254257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83020987812228937124339009 62265740859171702843254257)
            ·
              refine ⟨46699305644378777132440693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62265740859171702843254257 46699305644378777132440693)
              ·
                refine ⟨4378059904160510356166315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46699305644378777132440693 4378059904160510356166315)
                ·
                  refine ⟨6567089856240765534249473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4378059904160510356166315 6567089856240765534249473)
                  ·
                    refine ⟨4925317392180574150687105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6567089856240765534249473 4925317392180574150687105)
                    ·
                      refine ⟨3693988044135430613015329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4925317392180574150687105 3693988044135430613015329)
                      ·
                        rfl

theorem cell23_7194016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_7194016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194016 prefixEnd_7194016 := by exact prefixLift 7194016
  have htrace : WordTrace (prefixWord ++ tailWord_7194016) baseStart_7194016 baseEnd_7194016 := by
    simpa [prefixWord, tailWord_7194016, baseEnd_7194016] using wordTrace_append hprefix tailTrace_7194016
  have hstable : (prefixWord ++ tailWord_7194016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194016).length < 2 ^ (prefixWord ++ tailWord_7194016).sum := by decide
  have hdescent : baseEnd_7194016 < baseStart_7194016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194019 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 1, 2, 3]
def baseStart_7194019 : Nat := 118140960795 + 7194019 * 2 ^ 59
def prefixEnd_7194019 : Nat := 4983230072969 + 3 ^ 40 * 7194019 * 2
def baseEnd_7194019 : Nat := 3693989584577394101277815

theorem tailTrace_7194019 : CollatzResearch.WordTrace tailWord_7194019 prefixEnd_7194019 3693989584577394101277815 := by
  unfold tailWord_7194019
  simp only [CollatzResearch.WordTrace]
  refine ⟨262387428924305278473233111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174924952616203518982155407 262387428924305278473233111)
  ·
    refine ⟨393581143386457917709849667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262387428924305278473233111 393581143386457917709849667)
    ·
      refine ⟨590371715079686876564774501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393581143386457917709849667 590371715079686876564774501)
      ·
        refine ⟨110694696577441289355895219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 590371715079686876564774501 110694696577441289355895219)
        ·
          refine ⟨166042044866161934033842829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110694696577441289355895219 166042044866161934033842829)
          ·
            refine ⟨62265766824810725262691061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166042044866161934033842829 62265766824810725262691061)
            ·
              refine ⟨5837415639826005493377287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62265766824810725262691061 5837415639826005493377287)
              ·
                refine ⟨8756123459739008240065931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837415639826005493377287 8756123459739008240065931)
                ·
                  refine ⟨13134185189608512360098897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8756123459739008240065931 13134185189608512360098897)
                  ·
                    refine ⟨9850638892206384270074173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13134185189608512360098897 9850638892206384270074173)
                    ·
                      refine ⟨3693989584577394101277815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9850638892206384270074173 3693989584577394101277815)
                      ·
                        rfl

theorem cell23_7194019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_7194019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194019 prefixEnd_7194019 := by exact prefixLift 7194019
  have htrace : WordTrace (prefixWord ++ tailWord_7194019) baseStart_7194019 baseEnd_7194019 := by
    simpa [prefixWord, tailWord_7194019, baseEnd_7194019] using wordTrace_append hprefix tailTrace_7194019
  have hstable : (prefixWord ++ tailWord_7194019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194019).length < 2 ^ (prefixWord ++ tailWord_7194019).sum := by decide
  have hdescent : baseEnd_7194019 < baseStart_7194019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194055 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_7194055 : Nat := 118140960795 + 7194055 * 2 ^ 59
def prefixEnd_7194055 : Nat := 4983230072969 + 3 ^ 40 * 7194055 * 2
def baseEnd_7194055 : Nat := 3694008069880955960427649

theorem tailTrace_7194055 : CollatzResearch.WordTrace tailWord_7194055 prefixEnd_7194055 3694008069880955960427649 := by
  unfold tailWord_7194055
  simp only [CollatzResearch.WordTrace]
  refine ⟨262388741952174856621543619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174925827968116571081029079 262388741952174856621543619)
  ·
    refine ⟨393583112928262284932315429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262388741952174856621543619 393583112928262284932315429)
    ·
      refine ⟨73796833674049178424809143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393583112928262284932315429 73796833674049178424809143)
      ·
        refine ⟨110695250511073767637213715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73796833674049178424809143 110695250511073767637213715)
        ·
          refine ⟨166042875766610651455820573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110695250511073767637213715 166042875766610651455820573)
          ·
            refine ⟨62266078412478994295932715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166042875766610651455820573 62266078412478994295932715)
            ·
              refine ⟨93399117618718491443899073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62266078412478994295932715 93399117618718491443899073)
              ·
                refine ⟨70049338214038868582924305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93399117618718491443899073 70049338214038868582924305)
                ·
                  refine ⟨52537003660529151437193229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70049338214038868582924305 52537003660529151437193229)
                  ·
                    refine ⟨19701376372698431788947461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52537003660529151437193229 19701376372698431788947461)
                    ·
                      refine ⟨3694008069880955960427649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19701376372698431788947461 3694008069880955960427649)
                      ·
                        rfl

theorem cell23_7194055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_7194055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194055 prefixEnd_7194055 := by exact prefixLift 7194055
  have htrace : WordTrace (prefixWord ++ tailWord_7194055) baseStart_7194055 baseEnd_7194055 := by
    simpa [prefixWord, tailWord_7194055, baseEnd_7194055] using wordTrace_append hprefix tailTrace_7194055
  have hstable : (prefixWord ++ tailWord_7194055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194055).length < 2 ^ (prefixWord ++ tailWord_7194055).sum := by decide
  have hdescent : baseEnd_7194055 < baseStart_7194055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194095 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 7]
def baseStart_7194095 : Nat := 118140960795 + 7194095 * 2 ^ 59
def prefixEnd_7194095 : Nat := 4983230072969 + 3 ^ 40 * 7194095 * 2
def baseEnd_7194095 : Nat := 410447623234126200436385

theorem tailTrace_7194095 : CollatzResearch.WordTrace tailWord_7194095 prefixEnd_7194095 410447623234126200436385 := by
  unfold tailWord_7194095
  simp only [CollatzResearch.WordTrace]
  refine ⟨262390200872029943452999739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174926800581353295635333159 262390200872029943452999739)
  ·
    refine ⟨393585301308044915179499609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262390200872029943452999739 393585301308044915179499609)
    ·
      refine ⟨295188975981033686384624707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393585301308044915179499609 295188975981033686384624707)
      ·
        refine ⟨442783463971550529576937061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295188975981033686384624707 442783463971550529576937061)
        ·
          refine ⟨83021899494665724295675699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442783463971550529576937061 83021899494665724295675699)
          ·
            refine ⟨124532849241998586443513549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83021899494665724295675699 124532849241998586443513549)
            ·
              refine ⟨46699818465749469916317581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124532849241998586443513549 46699818465749469916317581)
              ·
                refine ⟨17512431924656051218619093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46699818465749469916317581 17512431924656051218619093)
                ·
                  refine ⟨410447623234126200436385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17512431924656051218619093 410447623234126200436385)
                  ·
                    rfl

theorem cell23_7194095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 7].length) (baseStart_7194095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194095 prefixEnd_7194095 := by exact prefixLift 7194095
  have htrace : WordTrace (prefixWord ++ tailWord_7194095) baseStart_7194095 baseEnd_7194095 := by
    simpa [prefixWord, tailWord_7194095, baseEnd_7194095] using wordTrace_append hprefix tailTrace_7194095
  have hstable : (prefixWord ++ tailWord_7194095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194095).length < 2 ^ (prefixWord ++ tailWord_7194095).sum := by decide
  have hdescent : baseEnd_7194095 < baseStart_7194095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194110 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_7194110 : Nat := 118140960795 + 7194110 * 2 ^ 59
def prefixEnd_7194110 : Nat := 4983230072969 + 3 ^ 40 * 7194110 * 2
def baseEnd_7194110 : Nat := 3694036311316953245239897

theorem tailTrace_7194110 : CollatzResearch.WordTrace tailWord_7194110 prefixEnd_7194110 3694036311316953245239897 := by
  unfold tailWord_7194110
  simp only [CollatzResearch.WordTrace]
  refine ⟨32798843495871950126849473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174927165311317067343197189 32798843495871950126849473)
  ·
    refine ⟨24599132621903962595137105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32798843495871950126849473 24599132621903962595137105)
    ·
      refine ⟨18449349466427971946352829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24599132621903962595137105 18449349466427971946352829)
      ·
        refine ⟨6918506049910489479882311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18449349466427971946352829 6918506049910489479882311)
        ·
          refine ⟨10377759074865734219823467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6918506049910489479882311 10377759074865734219823467)
          ·
            refine ⟨15566638612298601329735201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10377759074865734219823467 15566638612298601329735201)
            ·
              refine ⟨11674978959223950997301401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15566638612298601329735201 11674978959223950997301401)
              ·
                refine ⟨8756234219417963247976051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11674978959223950997301401 8756234219417963247976051)
                ·
                  refine ⟨13134351329126944871964077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8756234219417963247976051 13134351329126944871964077)
                  ·
                    refine ⟨4925381748422604326986529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13134351329126944871964077 4925381748422604326986529)
                    ·
                      refine ⟨3694036311316953245239897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4925381748422604326986529 3694036311316953245239897)
                      ·
                        rfl

theorem cell23_7194110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_7194110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194110 prefixEnd_7194110 := by exact prefixLift 7194110
  have htrace : WordTrace (prefixWord ++ tailWord_7194110) baseStart_7194110 baseEnd_7194110 := by
    simpa [prefixWord, tailWord_7194110, baseEnd_7194110] using wordTrace_append hprefix tailTrace_7194110
  have hstable : (prefixWord ++ tailWord_7194110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194110).length < 2 ^ (prefixWord ++ tailWord_7194110).sum := by decide
  have hdescent : baseEnd_7194110 < baseStart_7194110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194162 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_7194162 : Nat := 118140960795 + 7194162 * 2 ^ 59
def prefixEnd_7194162 : Nat := 4983230072969 + 3 ^ 40 * 7194162 * 2
def baseEnd_7194162 : Nat := 3694063012310987041789657

theorem tailTrace_7194162 : CollatzResearch.WordTrace tailWord_7194162 prefixEnd_7194162 3694063012310987041789657 := by
  unfold tailWord_7194162
  simp only [CollatzResearch.WordTrace]
  refine ⟨65598161140696803473922185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174928429708524809263792493 65598161140696803473922185)
  ·
    refine ⟨49198620855522602605441639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65598161140696803473922185 49198620855522602605441639)
    ·
      refine ⟨73797931283283903908162459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49198620855522602605441639 73797931283283903908162459)
      ·
        refine ⟨110696896924925855862243689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73797931283283903908162459 110696896924925855862243689)
        ·
          refine ⟨83022672693694391896682767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110696896924925855862243689 83022672693694391896682767)
          ·
            refine ⟨124534009040541587845024151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83022672693694391896682767 124534009040541587845024151)
            ·
              refine ⟨186801013560812381767536227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124534009040541587845024151 186801013560812381767536227)
              ·
                refine ⟨280201520341218572651304341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186801013560812381767536227 280201520341218572651304341)
                ·
                  refine ⟨13134446265994620593029891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 280201520341218572651304341 13134446265994620593029891)
                  ·
                    refine ⟨19701669398991930889544837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13134446265994620593029891 19701669398991930889544837)
                    ·
                      refine ⟨3694063012310987041789657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19701669398991930889544837 3694063012310987041789657)
                      ·
                        rfl

theorem cell23_7194162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_7194162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194162 prefixEnd_7194162 := by exact prefixLift 7194162
  have htrace : WordTrace (prefixWord ++ tailWord_7194162) baseStart_7194162 baseEnd_7194162 := by
    simpa [prefixWord, tailWord_7194162, baseEnd_7194162] using wordTrace_append hprefix tailTrace_7194162
  have hstable : (prefixWord ++ tailWord_7194162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194162).length < 2 ^ (prefixWord ++ tailWord_7194162).sum := by decide
  have hdescent : baseEnd_7194162 < baseStart_7194162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194185 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 10]
def baseStart_7194185 : Nat := 118140960795 + 7194185 * 2 ^ 59
def prefixEnd_7194185 : Nat := 4983230072969 + 3 ^ 40 * 7194185 * 2
def baseEnd_7194185 : Nat := 410452758040671161311339

theorem tailTrace_7194185 : CollatzResearch.WordTrace tailWord_7194185 prefixEnd_7194185 410452758040671161311339 := by
  unfold tailWord_7194185
  simp only [CollatzResearch.WordTrace]
  refine ⟨262393483441703888823776009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174928988961135925882517339 262393483441703888823776009)
  ·
    refine ⟨196795112581277916617832007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262393483441703888823776009 196795112581277916617832007)
    ·
      refine ⟨295192668871916874926748011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196795112581277916617832007 295192668871916874926748011)
      ·
        refine ⟨442789003307875312390122017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295192668871916874926748011 442789003307875312390122017)
        ·
          refine ⟨332091752480906484292591513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442789003307875312390122017 332091752480906484292591513)
          ·
            refine ⟨249068814360679863219443635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332091752480906484292591513 249068814360679863219443635)
            ·
              refine ⟨373603221541019794829165453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249068814360679863219443635 373603221541019794829165453)
              ·
                refine ⟨140101208077882423060937045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373603221541019794829165453 140101208077882423060937045)
                ·
                  refine ⟨410452758040671161311339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 140101208077882423060937045 410452758040671161311339)
                  ·
                    rfl

theorem cell23_7194185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 10].length) (baseStart_7194185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194185 prefixEnd_7194185 := by exact prefixLift 7194185
  have htrace : WordTrace (prefixWord ++ tailWord_7194185) baseStart_7194185 baseEnd_7194185 := by
    simpa [prefixWord, tailWord_7194185, baseEnd_7194185] using wordTrace_append hprefix tailTrace_7194185
  have hstable : (prefixWord ++ tailWord_7194185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194185).length < 2 ^ (prefixWord ++ tailWord_7194185).sum := by decide
  have hdescent : baseEnd_7194185 < baseStart_7194185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194195 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 7]
def baseStart_7194195 : Nat := 118140960795 + 7194195 * 2 ^ 59
def prefixEnd_7194195 : Nat := 4983230072969 + 3 ^ 40 * 7194195 * 2
def baseEnd_7194195 : Nat := 3694079957172585412677005

theorem tailTrace_7194195 : CollatzResearch.WordTrace tailWord_7194195 prefixEnd_7194195 3694079957172585412677005 := by
  unfold tailWord_7194195
  simp only [CollatzResearch.WordTrace]
  refine ⟨262393848171667660531640039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174929232114445107021093359 262393848171667660531640039)
  ·
    refine ⟨393590772257501490797460059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262393848171667660531640039 393590772257501490797460059)
    ·
      refine ⟨590386158386252236196190089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393590772257501490797460059 590386158386252236196190089)
      ·
        refine ⟨442789618789689177147142567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590386158386252236196190089 442789618789689177147142567)
        ·
          refine ⟨664184428184533765720713851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442789618789689177147142567 664184428184533765720713851)
          ·
            refine ⟨996276642276800648581070777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664184428184533765720713851 996276642276800648581070777)
            ·
              refine ⟨747207481707600486435803083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996276642276800648581070777 747207481707600486435803083)
              ·
                refine ⟨1120811222561400729653704625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747207481707600486435803083 1120811222561400729653704625)
                ·
                  refine ⟨840608416921050547240278469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1120811222561400729653704625 840608416921050547240278469)
                  ·
                    refine ⟨157614078172696977607552213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 840608416921050547240278469 157614078172696977607552213)
                    ·
                      refine ⟨3694079957172585412677005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157614078172696977607552213 3694079957172585412677005)
                      ·
                        rfl

theorem cell23_7194195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_7194195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194195 prefixEnd_7194195 := by exact prefixLift 7194195
  have htrace : WordTrace (prefixWord ++ tailWord_7194195) baseStart_7194195 baseEnd_7194195 := by
    simpa [prefixWord, tailWord_7194195, baseEnd_7194195] using wordTrace_append hprefix tailTrace_7194195
  have hstable : (prefixWord ++ tailWord_7194195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194195).length < 2 ^ (prefixWord ++ tailWord_7194195).sum := by decide
  have hdescent : baseEnd_7194195 < baseStart_7194195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194199 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 3]
def baseStart_7194199 : Nat := 118140960795 + 7194199 * 2 ^ 59
def prefixEnd_7194199 : Nat := 4983230072969 + 3 ^ 40 * 7194199 * 2
def baseEnd_7194199 : Nat := 3694082011095203397026987

theorem tailTrace_7194199 : CollatzResearch.WordTrace tailWord_7194199 prefixEnd_7194199 3694082011095203397026987 := by
  unfold tailWord_7194199
  simp only [CollatzResearch.WordTrace]
  refine ⟨262393994063653169214785651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174929329375768779476523767 262393994063653169214785651)
  ·
    refine ⟨393590991095479753822178477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262393994063653169214785651 393590991095479753822178477)
    ·
      refine ⟨147596621660804907683316929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393590991095479753822178477 147596621660804907683316929)
      ·
        refine ⟨110697466245603680762487697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147596621660804907683316929 110697466245603680762487697)
        ·
          refine ⟨83023099684202760571865773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110697466245603680762487697 83023099684202760571865773)
          ·
            refine ⟨31133662381576035214449665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83023099684202760571865773 31133662381576035214449665)
            ·
              refine ⟨23350246786182026410837249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31133662381576035214449665 23350246786182026410837249)
              ·
                refine ⟨17512685089636519808127937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23350246786182026410837249 17512685089636519808127937)
                ·
                  refine ⟨13134513817227389856095953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17512685089636519808127937 13134513817227389856095953)
                  ·
                    refine ⟨9850885362920542392071965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13134513817227389856095953 9850885362920542392071965)
                    ·
                      refine ⟨3694082011095203397026987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9850885362920542392071965 3694082011095203397026987)
                      ·
                        rfl

theorem cell23_7194199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_7194199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194199 prefixEnd_7194199 := by exact prefixLift 7194199
  have htrace : WordTrace (prefixWord ++ tailWord_7194199) baseStart_7194199 baseEnd_7194199 := by
    simpa [prefixWord, tailWord_7194199, baseEnd_7194199] using wordTrace_append hprefix tailTrace_7194199
  have hstable : (prefixWord ++ tailWord_7194199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194199).length < 2 ^ (prefixWord ++ tailWord_7194199).sum := by decide
  have hdescent : baseEnd_7194199 < baseStart_7194199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194263 : List Nat := [1, 1, 3, 3, 2, 2, 2, 4, 1, 1, 3]
def baseStart_7194263 : Nat := 118140960795 + 7194263 * 2 ^ 59
def prefixEnd_7194263 : Nat := 4983230072969 + 3 ^ 40 * 7194263 * 2
def baseEnd_7194263 : Nat := 3694114873857091146626693

theorem tailTrace_7194263 : CollatzResearch.WordTrace tailWord_7194263 prefixEnd_7194263 3694114873857091146626693 := by
  unfold tailWord_7194263
  simp only [CollatzResearch.WordTrace]
  refine ⟨262396328335421308145115443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174930885556947538763410295 262396328335421308145115443)
  ·
    refine ⟨393594492503131962217673165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262396328335421308145115443 393594492503131962217673165)
    ·
      refine ⟨147597934688674485831627437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393594492503131962217673165 147597934688674485831627437)
      ·
        refine ⟨55349225508252932186860289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147597934688674485831627437 55349225508252932186860289)
        ·
          refine ⟨41511919131189699140145217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55349225508252932186860289 41511919131189699140145217)
          ·
            refine ⟨31133939348392274355108913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41511919131189699140145217 31133939348392274355108913)
            ·
              refine ⟨23350454511294205766331685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31133939348392274355108913 23350454511294205766331685)
              ·
                refine ⟨4378210220867663581187191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23350454511294205766331685 4378210220867663581187191)
                ·
                  refine ⟨6567315331301495371780787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4378210220867663581187191 6567315331301495371780787)
                  ·
                    refine ⟨9850972996952243057671181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6567315331301495371780787 9850972996952243057671181)
                    ·
                      refine ⟨3694114873857091146626693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9850972996952243057671181 3694114873857091146626693)
                      ·
                        rfl

theorem cell23_7194263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_7194263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194263 prefixEnd_7194263 := by exact prefixLift 7194263
  have htrace : WordTrace (prefixWord ++ tailWord_7194263) baseStart_7194263 baseEnd_7194263 := by
    simpa [prefixWord, tailWord_7194263, baseEnd_7194263] using wordTrace_append hprefix tailTrace_7194263
  have hstable : (prefixWord ++ tailWord_7194263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194263).length < 2 ^ (prefixWord ++ tailWord_7194263).sum := by decide
  have hdescent : baseEnd_7194263 < baseStart_7194263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194352 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 3, 8]
def baseStart_7194352 : Nat := 118140960795 + 7194352 * 2 ^ 59
def prefixEnd_7194352 : Nat := 4983230072969 + 3 ^ 40 * 7194352 * 2
def baseEnd_7194352 : Nat := 1231386857878447099471261

theorem tailTrace_7194352 : CollatzResearch.WordTrace tailWord_7194352 prefixEnd_7194352 1231386857878447099471261 := by
  unfold tailWord_7194352
  simp only [CollatzResearch.WordTrace]
  refine ⟨131199787216049438172552655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174933049621399250896736873 131199787216049438172552655)
  ·
    refine ⟨196799680824074157258828983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131199787216049438172552655 196799680824074157258828983)
    ·
      refine ⟨295199521236111235888243475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196799680824074157258828983 295199521236111235888243475)
      ·
        refine ⟨442799281854166853832365213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295199521236111235888243475 442799281854166853832365213)
        ·
          refine ⟨166049730695312570187136955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442799281854166853832365213 166049730695312570187136955)
          ·
            refine ⟨249074596042968855280705433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166049730695312570187136955 249074596042968855280705433)
            ·
              refine ⟨186805947032226641460529075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249074596042968855280705433 186805947032226641460529075)
              ·
                refine ⟨280208920548339962190793613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186805947032226641460529075 280208920548339962190793613)
                ·
                  refine ⟨105078345205627485821547605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280208920548339962190793613 105078345205627485821547605)
                  ·
                    refine ⟨1231386857878447099471261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105078345205627485821547605 1231386857878447099471261)
                    ·
                      rfl

theorem cell23_7194352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_7194352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194352 prefixEnd_7194352 := by exact prefixLift 7194352
  have htrace : WordTrace (prefixWord ++ tailWord_7194352) baseStart_7194352 baseEnd_7194352 := by
    simpa [prefixWord, tailWord_7194352, baseEnd_7194352] using wordTrace_append hprefix tailTrace_7194352
  have hstable : (prefixWord ++ tailWord_7194352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194352).length < 2 ^ (prefixWord ++ tailWord_7194352).sum := by decide
  have hdescent : baseEnd_7194352 < baseStart_7194352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194370 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_7194370 : Nat := 118140960795 + 7194370 * 2 ^ 59
def prefixEnd_7194370 : Nat := 4983230072969 + 3 ^ 40 * 7194370 * 2
def baseEnd_7194370 : Nat := 3694169816287122227988701

theorem tailTrace_7194370 : CollatzResearch.WordTrace tailWord_7194370 prefixEnd_7194370 3694169816287122227988701 := by
  unfold tailWord_7194370
  simp only [CollatzResearch.WordTrace]
  refine ⟨65600057736508416354815141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174933487297355776946173709 65600057736508416354815141)
  ·
    refine ⟨12300010825595328066527839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65600057736508416354815141 12300010825595328066527839)
    ·
      refine ⟨18450016238392992099791759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12300010825595328066527839 18450016238392992099791759)
      ·
        refine ⟨27675024357589488149687639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18450016238392992099791759 27675024357589488149687639)
        ·
          refine ⟨41512536536384232224531459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27675024357589488149687639 41512536536384232224531459)
          ·
            refine ⟨62268804804576348336797189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41512536536384232224531459 62268804804576348336797189)
            ·
              refine ⟨11675400900858065313149473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62268804804576348336797189 11675400900858065313149473)
              ·
                refine ⟨8756550675643548984862105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11675400900858065313149473 8756550675643548984862105)
                ·
                  refine ⟨6567413006732661738646579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8756550675643548984862105 6567413006732661738646579)
                  ·
                    refine ⟨9851119510098992607969869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6567413006732661738646579 9851119510098992607969869)
                    ·
                      refine ⟨3694169816287122227988701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9851119510098992607969869 3694169816287122227988701)
                      ·
                        rfl

theorem cell23_7194370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_7194370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194370 prefixEnd_7194370 := by exact prefixLift 7194370
  have htrace : WordTrace (prefixWord ++ tailWord_7194370) baseStart_7194370 baseEnd_7194370 := by
    simpa [prefixWord, tailWord_7194370, baseEnd_7194370] using wordTrace_append hprefix tailTrace_7194370
  have hstable : (prefixWord ++ tailWord_7194370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194370).length < 2 ^ (prefixWord ++ tailWord_7194370).sum := by decide
  have hdescent : baseEnd_7194370 < baseStart_7194370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194376 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 3, 4, 2]
def baseStart_7194376 : Nat := 118140960795 + 7194376 * 2 ^ 59
def prefixEnd_7194376 : Nat := 4983230072969 + 3 ^ 40 * 7194376 * 2
def baseEnd_7194376 : Nat := 3694172897171049204513673

theorem tailTrace_7194376 : CollatzResearch.WordTrace tailWord_7194376 prefixEnd_7194376 3694172897171049204513673 := by
  unfold tailWord_7194376
  simp only [CollatzResearch.WordTrace]
  refine ⟨131200224892005964221989491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174933633189341285629319321 131200224892005964221989491)
  ·
    refine ⟨196800337338008946332984237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131200224892005964221989491 196800337338008946332984237)
    ·
      refine ⟨73800126501753354874869089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196800337338008946332984237 73800126501753354874869089)
      ·
        refine ⟨55350094876315016156151817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73800126501753354874869089 55350094876315016156151817)
        ·
          refine ⟨41512571157236262117113863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55350094876315016156151817 41512571157236262117113863)
          ·
            refine ⟨62268856735854393175670795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41512571157236262117113863 62268856735854393175670795)
            ·
              refine ⟨93403285103781589763506193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62268856735854393175670795 93403285103781589763506193)
              ·
                refine ⟨70052463827836192322629645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93403285103781589763506193 70052463827836192322629645)
                ·
                  refine ⟨26269673935438572120986117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70052463827836192322629645 26269673935438572120986117)
                  ·
                    refine ⟨4925563862894732272684897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26269673935438572120986117 4925563862894732272684897)
                    ·
                      refine ⟨3694172897171049204513673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4925563862894732272684897 3694172897171049204513673)
                      ·
                        rfl

theorem cell23_7194376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_7194376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194376 prefixEnd_7194376 := by exact prefixLift 7194376
  have htrace : WordTrace (prefixWord ++ tailWord_7194376) baseStart_7194376 baseEnd_7194376 := by
    simpa [prefixWord, tailWord_7194376, baseEnd_7194376] using wordTrace_append hprefix tailTrace_7194376
  have hstable : (prefixWord ++ tailWord_7194376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194376).length < 2 ^ (prefixWord ++ tailWord_7194376).sum := by decide
  have hdescent : baseEnd_7194376 < baseStart_7194376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194379 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 3]
def baseStart_7194379 : Nat := 118140960795 + 7194379 * 2 ^ 59
def prefixEnd_7194379 : Nat := 4983230072969 + 3 ^ 40 * 7194379 * 2
def baseEnd_7194379 : Nat := 3694174437613012692776159

theorem tailTrace_7194379 : CollatzResearch.WordTrace tailWord_7194379 prefixEnd_7194379 3694174437613012692776159 := by
  unfold tailWord_7194379
  simp only [CollatzResearch.WordTrace]
  refine ⟨262400559203001059956338191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174933706135334039970892127 262400559203001059956338191)
  ·
    refine ⟨393600838804501589934507287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262400559203001059956338191 393600838804501589934507287)
    ·
      refine ⟨590401258206752384901760931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393600838804501589934507287 590401258206752384901760931)
      ·
        refine ⟨885601887310128577352641397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590401258206752384901760931 885601887310128577352641397)
        ·
          refine ⟨83025176935324554126810131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 885601887310128577352641397 83025176935324554126810131)
          ·
            refine ⟨124537765402986831190215197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83025176935324554126810131 124537765402986831190215197)
            ·
              refine ⟨46701662026120061696330699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124537765402986831190215197 46701662026120061696330699)
              ·
                refine ⟨70052493039180092544496049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46701662026120061696330699 70052493039180092544496049)
                ·
                  refine ⟨52539369779385069408372037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70052493039180092544496049 52539369779385069408372037)
                  ·
                    refine ⟨9851131833634700514069757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52539369779385069408372037 9851131833634700514069757)
                    ·
                      refine ⟨3694174437613012692776159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9851131833634700514069757 3694174437613012692776159)
                      ·
                        rfl

theorem cell23_7194379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 3].length) (baseStart_7194379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194379 prefixEnd_7194379 := by exact prefixLift 7194379
  have htrace : WordTrace (prefixWord ++ tailWord_7194379) baseStart_7194379 baseEnd_7194379 := by
    simpa [prefixWord, tailWord_7194379, baseEnd_7194379] using wordTrace_append hprefix tailTrace_7194379
  have hstable : (prefixWord ++ tailWord_7194379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194379).length < 2 ^ (prefixWord ++ tailWord_7194379).sum := by decide
  have hdescent : baseEnd_7194379 < baseStart_7194379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194386 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_7194386 : Nat := 118140960795 + 7194386 * 2 ^ 59
def prefixEnd_7194386 : Nat := 4983230072969 + 3 ^ 40 * 7194386 * 2
def baseEnd_7194386 : Nat := 1231392677325864721796209

theorem tailTrace_7194386 : CollatzResearch.WordTrace tailWord_7194386 prefixEnd_7194386 1231392677325864721796209 := by
  unfold tailWord_7194386
  simp only [CollatzResearch.WordTrace]
  refine ⟨65600203628493925037960753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174933876342650466767895341 65600203628493925037960753)
  ·
    refine ⟨49200152721370443778470565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65600203628493925037960753 49200152721370443778470565)
    ·
      refine ⟨9225028635256958208463231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49200152721370443778470565 9225028635256958208463231)
      ·
        refine ⟨13837542952885437312694847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9225028635256958208463231 13837542952885437312694847)
        ·
          refine ⟨20756314429328155969042271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13837542952885437312694847 20756314429328155969042271)
          ·
            refine ⟨31134471643992233953563407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20756314429328155969042271 31134471643992233953563407)
            ·
              refine ⟨46701707465988350930345111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31134471643992233953563407 46701707465988350930345111)
              ·
                refine ⟨70052561198982526395517667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46701707465988350930345111 70052561198982526395517667)
                ·
                  refine ⟨105078841798473789593276501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70052561198982526395517667 105078841798473789593276501)
                  ·
                    refine ⟨1231392677325864721796209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105078841798473789593276501 1231392677325864721796209)
                    ·
                      rfl

theorem cell23_7194386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_7194386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194386 prefixEnd_7194386 := by exact prefixLift 7194386
  have htrace : WordTrace (prefixWord ++ tailWord_7194386) baseStart_7194386 baseEnd_7194386 := by
    simpa [prefixWord, tailWord_7194386, baseEnd_7194386] using wordTrace_append hprefix tailTrace_7194386
  have hstable : (prefixWord ++ tailWord_7194386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194386).length < 2 ^ (prefixWord ++ tailWord_7194386).sum := by decide
  have hdescent : baseEnd_7194386 < baseStart_7194386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194389 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_7194389 : Nat := 118140960795 + 7194389 * 2 ^ 59
def prefixEnd_7194389 : Nat := 4983230072969 + 3 ^ 40 * 7194389 * 2
def baseEnd_7194389 : Nat := 3694179572419557653651113

theorem tailTrace_7194389 : CollatzResearch.WordTrace tailWord_7194389 prefixEnd_7194389 3694179572419557653651113 := by
  unfold tailWord_7194389
  simp only [CollatzResearch.WordTrace]
  refine ⟨262400923932964831664202221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174933949288643221109468147 262400923932964831664202221)
  ·
    refine ⟨98400346474861811874075833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262400923932964831664202221 98400346474861811874075833)
    ·
      refine ⟨73800259856146358905556875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98400346474861811874075833 73800259856146358905556875)
      ·
        refine ⟨110700389784219538358335313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73800259856146358905556875 110700389784219538358335313)
        ·
          refine ⟨83025292338164653768751485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110700389784219538358335313 83025292338164653768751485)
          ·
            refine ⟨31134484626811745163281807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83025292338164653768751485 31134484626811745163281807)
            ·
              refine ⟨46701726940217617744922711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31134484626811745163281807 46701726940217617744922711)
              ·
                refine ⟨70052590410326426617384067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46701726940217617744922711 70052590410326426617384067)
                ·
                  refine ⟨105078885615489639926076101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70052590410326426617384067 105078885615489639926076101)
                  ·
                    refine ⟨19702291052904307486139269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105078885615489639926076101 19702291052904307486139269)
                    ·
                      refine ⟨3694179572419557653651113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19702291052904307486139269 3694179572419557653651113)
                      ·
                        rfl

theorem cell23_7194389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_7194389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194389 prefixEnd_7194389 := by exact prefixLift 7194389
  have htrace : WordTrace (prefixWord ++ tailWord_7194389) baseStart_7194389 baseEnd_7194389 := by
    simpa [prefixWord, tailWord_7194389, baseEnd_7194389] using wordTrace_append hprefix tailTrace_7194389
  have hstable : (prefixWord ++ tailWord_7194389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194389).length < 2 ^ (prefixWord ++ tailWord_7194389).sum := by decide
  have hdescent : baseEnd_7194389 < baseStart_7194389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194399 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 7]
def baseStart_7194399 : Nat := 118140960795 + 7194399 * 2 ^ 59
def prefixEnd_7194399 : Nat := 4983230072969 + 3 ^ 40 * 7194399 * 2
def baseEnd_7194399 : Nat := 410464967469566957169563

theorem tailTrace_7194399 : CollatzResearch.WordTrace tailWord_7194399 prefixEnd_7194399 410464967469566957169563 := by
  unfold tailWord_7194399
  simp only [CollatzResearch.WordTrace]
  refine ⟨262401288662928603372066251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174934192441952402248044167 262401288662928603372066251)
  ·
    refine ⟨393601932994392905058099377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262401288662928603372066251 393601932994392905058099377)
    ·
      refine ⟨295201449745794678793574533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393601932994392905058099377 295201449745794678793574533)
      ·
        refine ⟨55350271827336502273795225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295201449745794678793574533 55350271827336502273795225)
        ·
          refine ⟨41512703870502376705346419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55350271827336502273795225 41512703870502376705346419)
          ·
            refine ⟨62269055805753565058019629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41512703870502376705346419 62269055805753565058019629)
            ·
              refine ⟨23350895927157586896757361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62269055805753565058019629 23350895927157586896757361)
              ·
                refine ⟨17513171945368190172568021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23350895927157586896757361 17513171945368190172568021)
                ·
                  refine ⟨410464967469566957169563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17513171945368190172568021 410464967469566957169563)
                  ·
                    rfl

theorem cell23_7194399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 7].length) (baseStart_7194399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194399 prefixEnd_7194399 := by exact prefixLift 7194399
  have htrace : WordTrace (prefixWord ++ tailWord_7194399) baseStart_7194399 baseEnd_7194399 := by
    simpa [prefixWord, tailWord_7194399, baseEnd_7194399] using wordTrace_append hprefix tailTrace_7194399
  have hstable : (prefixWord ++ tailWord_7194399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194399).length < 2 ^ (prefixWord ++ tailWord_7194399).sum := by decide
  have hdescent : baseEnd_7194399 < baseStart_7194399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194409 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 6, 3, 3]
def baseStart_7194409 : Nat := 118140960795 + 7194409 * 2 ^ 59
def prefixEnd_7194409 : Nat := 4983230072969 + 3 ^ 40 * 7194409 * 2
def baseEnd_7194409 : Nat := 3694189842032647575401021

theorem tailTrace_7194409 : CollatzResearch.WordTrace tailWord_7194409 prefixEnd_7194409 3694189842032647575401021 := by
  unfold tailWord_7194409
  simp only [CollatzResearch.WordTrace]
  refine ⟨262401653392892375079930281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174934435595261583386620187 262401653392892375079930281)
  ·
    refine ⟨196801240044669281309947711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262401653392892375079930281 196801240044669281309947711)
    ·
      refine ⟨295201860067003921964921567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196801240044669281309947711 295201860067003921964921567)
      ·
        refine ⟨442802790100505882947382351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295201860067003921964921567 442802790100505882947382351)
        ·
          refine ⟨664204185150758824421073527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442802790100505882947382351 664204185150758824421073527)
          ·
            refine ⟨996306277726138236631610291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664204185150758824421073527 996306277726138236631610291)
            ·
              refine ⟨1494459416589207354947415437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996306277726138236631610291 1494459416589207354947415437)
              ·
                refine ⟨560422281220952758105280789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1494459416589207354947415437 560422281220952758105280789)
                ·
                  refine ⟨26269794432232160536185037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 560422281220952758105280789 26269794432232160536185037)
                  ·
                    refine ⟨9851172912087060201069389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26269794432232160536185037 9851172912087060201069389)
                    ·
                      refine ⟨3694189842032647575401021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9851172912087060201069389 3694189842032647575401021)
                      ·
                        rfl

theorem cell23_7194409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3, 3].length) (baseStart_7194409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194409 prefixEnd_7194409 := by exact prefixLift 7194409
  have htrace : WordTrace (prefixWord ++ tailWord_7194409) baseStart_7194409 baseEnd_7194409 := by
    simpa [prefixWord, tailWord_7194409, baseEnd_7194409] using wordTrace_append hprefix tailTrace_7194409
  have hstable : (prefixWord ++ tailWord_7194409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194409).length < 2 ^ (prefixWord ++ tailWord_7194409).sum := by decide
  have hdescent : baseEnd_7194409 < baseStart_7194409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194414 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_7194414 : Nat := 118140960795 + 7194414 * 2 ^ 59
def prefixEnd_7194414 : Nat := 4983230072969 + 3 ^ 40 * 7194414 * 2
def baseEnd_7194414 : Nat := 3694192409435920055838499

theorem tailTrace_7194414 : CollatzResearch.WordTrace tailWord_7194414 prefixEnd_7194414 3694192409435920055838499 := by
  unfold tailWord_7194414
  simp only [CollatzResearch.WordTrace]
  refine ⟨32800229469734282616732787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174934557171916173955908197 32800229469734282616732787)
  ·
    refine ⟨49200344204601423925099181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32800229469734282616732787 49200344204601423925099181)
    ·
      refine ⟨18450129076725533971912193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49200344204601423925099181 18450129076725533971912193)
      ·
        refine ⟨13837596807544150478934145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18450129076725533971912193 13837596807544150478934145)
        ·
          refine ⟨10378197605658112859200609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13837596807544150478934145 10378197605658112859200609)
          ·
            refine ⟨7783648204243584644400457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10378197605658112859200609 7783648204243584644400457)
            ·
              refine ⟨5837736153182688483300343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7783648204243584644400457 5837736153182688483300343)
              ·
                refine ⟨8756604229774032724950515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837736153182688483300343 8756604229774032724950515)
                ·
                  refine ⟨13134906344661049087425773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8756604229774032724950515 13134906344661049087425773)
                  ·
                    refine ⟨4925589879247893407784665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13134906344661049087425773 4925589879247893407784665)
                    ·
                      refine ⟨3694192409435920055838499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4925589879247893407784665 3694192409435920055838499)
                      ·
                        rfl

theorem cell23_7194414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_7194414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194414 prefixEnd_7194414 := by exact prefixLift 7194414
  have htrace : WordTrace (prefixWord ++ tailWord_7194414) baseStart_7194414 baseEnd_7194414 := by
    simpa [prefixWord, tailWord_7194414, baseEnd_7194414] using wordTrace_append hprefix tailTrace_7194414
  have hstable : (prefixWord ++ tailWord_7194414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194414).length < 2 ^ (prefixWord ++ tailWord_7194414).sum := by decide
  have hdescent : baseEnd_7194414 < baseStart_7194414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194426 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3]
def baseStart_7194426 : Nat := 118140960795 + 7194426 * 2 ^ 59
def prefixEnd_7194426 : Nat := 4983230072969 + 3 ^ 40 * 7194426 * 2
def baseEnd_7194426 : Nat := 3694198571203774008888443

theorem tailTrace_7194426 : CollatzResearch.WordTrace tailWord_7194426 prefixEnd_7194426 3694198571203774008888443 := by
  unfold tailWord_7194426
  simp only [CollatzResearch.WordTrace]
  refine ⟨65600568358457696745824783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174934848955887191322199421 65600568358457696745824783)
  ·
    refine ⟨98400852537686545118737175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65600568358457696745824783 98400852537686545118737175)
    ·
      refine ⟨147601278806529817678105763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98400852537686545118737175 147601278806529817678105763)
      ·
        refine ⟨221401918209794726517158645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147601278806529817678105763 221401918209794726517158645)
        ·
          refine ⟨20756429832168255610983623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221401918209794726517158645 20756429832168255610983623)
          ·
            refine ⟨31134644748252383416475435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20756429832168255610983623 31134644748252383416475435)
            ·
              refine ⟨46701967122378575124713153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31134644748252383416475435 46701967122378575124713153)
              ·
                refine ⟨35026475341783931343534865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46701967122378575124713153 35026475341783931343534865)
                ·
                  refine ⟨26269856506337948507651149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35026475341783931343534865 26269856506337948507651149)
                  ·
                    refine ⟨9851196189876730690369181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26269856506337948507651149 9851196189876730690369181)
                    ·
                      refine ⟨3694198571203774008888443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9851196189876730690369181 3694198571203774008888443)
                      ·
                        rfl

theorem cell23_7194426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_7194426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194426 prefixEnd_7194426 := by exact prefixLift 7194426
  have htrace : WordTrace (prefixWord ++ tailWord_7194426) baseStart_7194426 baseEnd_7194426 := by
    simpa [prefixWord, tailWord_7194426, baseEnd_7194426] using wordTrace_append hprefix tailTrace_7194426
  have hstable : (prefixWord ++ tailWord_7194426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194426).length < 2 ^ (prefixWord ++ tailWord_7194426).sum := by decide
  have hdescent : baseEnd_7194426 < baseStart_7194426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194439 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_7194439 : Nat := 118140960795 + 7194439 * 2 ^ 59
def prefixEnd_7194439 : Nat := 4983230072969 + 3 ^ 40 * 7194439 * 2
def baseEnd_7194439 : Nat := 3694205246452282458025883

theorem tailTrace_7194439 : CollatzResearch.WordTrace tailWord_7194439 prefixEnd_7194439 3694205246452282458025883 := by
  unfold tailWord_7194439
  simp only [CollatzResearch.WordTrace]
  refine ⟨262402747582783690203522371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174935165055189126802348247 262402747582783690203522371)
  ·
    refine ⟨393604121374175535305283557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262402747582783690203522371 393604121374175535305283557)
    ·
      refine ⟨73800772757657912869740667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393604121374175535305283557 73800772757657912869740667)
      ·
        refine ⟨110701159136486869304611001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73800772757657912869740667 110701159136486869304611001)
        ·
          refine ⟨83025869352365151978458251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110701159136486869304611001 83025869352365151978458251)
          ·
            refine ⟨124538804028547727967687377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83025869352365151978458251 124538804028547727967687377)
            ·
              refine ⟨93404103021410795975765533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124538804028547727967687377 93404103021410795975765533)
              ·
                refine ⟨35026538633029048490912075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93404103021410795975765533 35026538633029048490912075)
                ·
                  refine ⟨52539807949543572736368113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35026538633029048490912075 52539807949543572736368113)
                  ·
                    refine ⟨39404855962157679552276085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52539807949543572736368113 39404855962157679552276085)
                    ·
                      refine ⟨3694205246452282458025883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39404855962157679552276085 3694205246452282458025883)
                      ·
                        rfl

theorem cell23_7194439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_7194439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194439 prefixEnd_7194439 := by exact prefixLift 7194439
  have htrace : WordTrace (prefixWord ++ tailWord_7194439) baseStart_7194439 baseEnd_7194439 := by
    simpa [prefixWord, tailWord_7194439, baseEnd_7194439] using wordTrace_append hprefix tailTrace_7194439
  have hstable : (prefixWord ++ tailWord_7194439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194439).length < 2 ^ (prefixWord ++ tailWord_7194439).sum := by decide
  have hdescent : baseEnd_7194439 < baseStart_7194439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194469 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_7194469 : Nat := 118140960795 + 7194469 * 2 ^ 59
def prefixEnd_7194469 : Nat := 4983230072969 + 3 ^ 40 * 7194469 * 2
def baseEnd_7194469 : Nat := 3694220650871917340650745

theorem tailTrace_7194469 : CollatzResearch.WordTrace tailWord_7194469 prefixEnd_7194469 3694220650871917340650745 := by
  unfold tailWord_7194469
  simp only [CollatzResearch.WordTrace]
  refine ⟨262403841772675005327114461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174935894515116670218076307 262403841772675005327114461)
  ·
    refine ⟨98401440664753126997667923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262403841772675005327114461 98401440664753126997667923)
    ·
      refine ⟨147602160997129690496501885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98401440664753126997667923 147602160997129690496501885)
      ·
        refine ⟨55350810373923633936188207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147602160997129690496501885 55350810373923633936188207)
        ·
          refine ⟨83026215560885450904282311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55350810373923633936188207 83026215560885450904282311)
          ·
            refine ⟨124539323341328176356423467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83026215560885450904282311 124539323341328176356423467)
            ·
              refine ⟨186808985011992264534635201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124539323341328176356423467 186808985011992264534635201)
              ·
                refine ⟨140106738758994198400976401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186808985011992264534635201 140106738758994198400976401)
                ·
                  refine ⟨105080054069245648800732301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140106738758994198400976401 105080054069245648800732301)
                  ·
                    refine ⟨39405020275967118300274613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105080054069245648800732301 39405020275967118300274613)
                    ·
                      refine ⟨3694220650871917340650745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39405020275967118300274613 3694220650871917340650745)
                      ·
                        rfl

theorem cell23_7194469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_7194469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194469 prefixEnd_7194469 := by exact prefixLift 7194469
  have htrace : WordTrace (prefixWord ++ tailWord_7194469) baseStart_7194469 baseEnd_7194469 := by
    simpa [prefixWord, tailWord_7194469, baseEnd_7194469] using wordTrace_append hprefix tailTrace_7194469
  have hstable : (prefixWord ++ tailWord_7194469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194469).length < 2 ^ (prefixWord ++ tailWord_7194469).sum := by decide
  have hdescent : baseEnd_7194469 < baseStart_7194469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194489 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 8]
def baseStart_7194489 : Nat := 118140960795 + 7194489 * 2 ^ 59
def prefixEnd_7194489 : Nat := 4983230072969 + 3 ^ 40 * 7194489 * 2
def baseEnd_7194489 : Nat := 410470102276111918044517

theorem tailTrace_7194489 : CollatzResearch.WordTrace tailWord_7194489 prefixEnd_7194489 410470102276111918044517 := by
  unfold tailWord_7194489
  simp only [CollatzResearch.WordTrace]
  refine ⟨262404571232602548742842521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174936380821735032495228347 262404571232602548742842521)
  ·
    refine ⟨196803428424451911557131891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262404571232602548742842521 196803428424451911557131891)
    ·
      refine ⟨295205142636677867335697837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196803428424451911557131891 295205142636677867335697837)
      ·
        refine ⟨110701928488754200250886689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295205142636677867335697837 110701928488754200250886689)
        ·
          refine ⟨83026446366565650188165017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110701928488754200250886689 83026446366565650188165017)
          ·
            refine ⟨62269834774924237641123763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83026446366565650188165017 62269834774924237641123763)
            ·
              refine ⟨93404752162386356461685645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62269834774924237641123763 93404752162386356461685645)
              ·
                refine ⟨35026782060894883673132117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93404752162386356461685645 35026782060894883673132117)
                ·
                  refine ⟨410470102276111918044517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35026782060894883673132117 410470102276111918044517)
                  ·
                    rfl

theorem cell23_7194489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 8].length) (baseStart_7194489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194489 prefixEnd_7194489 := by exact prefixLift 7194489
  have htrace : WordTrace (prefixWord ++ tailWord_7194489) baseStart_7194489 baseEnd_7194489 := by
    simpa [prefixWord, tailWord_7194489, baseEnd_7194489] using wordTrace_append hprefix tailTrace_7194489
  have hstable : (prefixWord ++ tailWord_7194489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194489).length < 2 ^ (prefixWord ++ tailWord_7194489).sum := by decide
  have hdescent : baseEnd_7194489 < baseStart_7194489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194543 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 2, 3, 2]
def baseStart_7194543 : Nat := 118140960795 + 7194543 * 2 ^ 59
def prefixEnd_7194543 : Nat := 4983230072969 + 3 ^ 40 * 7194543 * 2
def baseEnd_7194543 : Nat := 3694258648440350051125405

theorem tailTrace_7194543 : CollatzResearch.WordTrace tailWord_7194543 prefixEnd_7194543 3694258648440350051125405 := by
  unfold tailWord_7194543
  simp only [CollatzResearch.WordTrace]
  refine ⟨262406540774406915965308283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174937693849604610643538855 262406540774406915965308283)
  ·
    refine ⟨393609811161610373947962425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262406540774406915965308283 393609811161610373947962425)
    ·
      refine ⟨295207358371207780460971819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393609811161610373947962425 295207358371207780460971819)
      ·
        refine ⟨442811037556811670691457729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295207358371207780460971819 442811037556811670691457729)
        ·
          refine ⟨332108278167608753018593297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442811037556811670691457729 332108278167608753018593297)
          ·
            refine ⟨249081208625706564763944973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332108278167608753018593297 249081208625706564763944973)
            ·
              refine ⟨93405453234639961786479365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249081208625706564763944973 93405453234639961786479365)
              ·
                refine ⟨17513522481494992834964881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93405453234639961786479365 17513522481494992834964881)
                ·
                  refine ⟨13135141861121244626223661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17513522481494992834964881 13135141861121244626223661)
                  ·
                    refine ⟨4925678197920466734833873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13135141861121244626223661 4925678197920466734833873)
                    ·
                      refine ⟨3694258648440350051125405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4925678197920466734833873 3694258648440350051125405)
                      ·
                        rfl

theorem cell23_7194543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 3, 2].length) (baseStart_7194543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194543 prefixEnd_7194543 := by exact prefixLift 7194543
  have htrace : WordTrace (prefixWord ++ tailWord_7194543) baseStart_7194543 baseEnd_7194543 := by
    simpa [prefixWord, tailWord_7194543, baseEnd_7194543] using wordTrace_append hprefix tailTrace_7194543
  have hstable : (prefixWord ++ tailWord_7194543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194543).length < 2 ^ (prefixWord ++ tailWord_7194543).sum := by decide
  have hdescent : baseEnd_7194543 < baseStart_7194543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194607 : List Nat := [1, 1, 2, 1, 4, 2, 1, 6, 1, 2, 2]
def baseStart_7194607 : Nat := 118140960795 + 7194607 * 2 ^ 59
def prefixEnd_7194607 : Nat := 4983230072969 + 3 ^ 40 * 7194607 * 2
def baseEnd_7194607 : Nat := 3694291511202237800725111

theorem tailTrace_7194607 : CollatzResearch.WordTrace tailWord_7194607 prefixEnd_7194607 3694291511202237800725111 := by
  unfold tailWord_7194607
  simp only [CollatzResearch.WordTrace]
  refine ⟨262408875046175054895638075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174939250030783369930425383 262408875046175054895638075)
  ·
    refine ⟨393613312569262582343457113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262408875046175054895638075 393613312569262582343457113)
    ·
      refine ⟨295209984426946936757592835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393613312569262582343457113 295209984426946936757592835)
      ·
        refine ⟨442814976640420405136389253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295209984426946936757592835 442814976640420405136389253)
        ·
          refine ⟨83027808120078825963072985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442814976640420405136389253 83027808120078825963072985)
          ·
            refine ⟨62270856090059119472304739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83027808120078825963072985 62270856090059119472304739)
            ·
              refine ⟨93406284135088679208457109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62270856090059119472304739 93406284135088679208457109)
              ·
                refine ⟨4378419568832281837896427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93406284135088679208457109 4378419568832281837896427)
                ·
                  refine ⟨6567629353248422756844641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4378419568832281837896427 6567629353248422756844641)
                  ·
                    refine ⟨4925722014936317067633481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6567629353248422756844641 4925722014936317067633481)
                    ·
                      refine ⟨3694291511202237800725111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4925722014936317067633481 3694291511202237800725111)
                      ·
                        rfl

theorem cell23_7194607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 1, 2, 2].length) (baseStart_7194607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194607 prefixEnd_7194607 := by exact prefixLift 7194607
  have htrace : WordTrace (prefixWord ++ tailWord_7194607) baseStart_7194607 baseEnd_7194607 := by
    simpa [prefixWord, tailWord_7194607, baseEnd_7194607] using wordTrace_append hprefix tailTrace_7194607
  have hstable : (prefixWord ++ tailWord_7194607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194607).length < 2 ^ (prefixWord ++ tailWord_7194607).sum := by decide
  have hdescent : baseEnd_7194607 < baseStart_7194607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194636 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_7194636 : Nat := 118140960795 + 7194636 * 2 ^ 59
def prefixEnd_7194636 : Nat := 4983230072969 + 3 ^ 40 * 7194636 * 2
def baseEnd_7194636 : Nat := 3694306402141218187262477

theorem tailTrace_7194636 : CollatzResearch.WordTrace tailWord_7194636 prefixEnd_7194636 3694306402141218187262477 := by
  unfold tailWord_7194636
  simp only [CollatzResearch.WordTrace]
  refine ⟨131204966381534996424221881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174939955175379995232295841 131204966381534996424221881)
  ·
    refine ⟨98403724786151247318166411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131204966381534996424221881 98403724786151247318166411)
    ·
      refine ⟨147605587179226870977249617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98403724786151247318166411 147605587179226870977249617)
      ·
        refine ⟨110704190384420153232937213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147605587179226870977249617 110704190384420153232937213)
        ·
          refine ⟨41514071394157557462351455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110704190384420153232937213 41514071394157557462351455)
          ·
            refine ⟨62271107091236336193527183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41514071394157557462351455 62271107091236336193527183)
            ·
              refine ⟨93406660636854504290290775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62271107091236336193527183 93406660636854504290290775)
              ·
                refine ⟨140109990955281756435436163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93406660636854504290290775 140109990955281756435436163)
                ·
                  refine ⟨210164986432922634653154245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140109990955281756435436163 210164986432922634653154245)
                  ·
                    refine ⟨39405934956172993997466421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 210164986432922634653154245 39405934956172993997466421)
                    ·
                      refine ⟨3694306402141218187262477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39405934956172993997466421 3694306402141218187262477)
                      ·
                        rfl

theorem cell23_7194636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_7194636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194636 prefixEnd_7194636 := by exact prefixLift 7194636
  have htrace : WordTrace (prefixWord ++ tailWord_7194636) baseStart_7194636 baseEnd_7194636 := by
    simpa [prefixWord, tailWord_7194636, baseEnd_7194636] using wordTrace_append hprefix tailTrace_7194636
  have hstable : (prefixWord ++ tailWord_7194636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194636).length < 2 ^ (prefixWord ++ tailWord_7194636).sum := by decide
  have hdescent : baseEnd_7194636 < baseStart_7194636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194674 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3]
def baseStart_7194674 : Nat := 118140960795 + 7194674 * 2 ^ 59
def prefixEnd_7194674 : Nat := 4983230072969 + 3 ^ 40 * 7194674 * 2
def baseEnd_7194674 : Nat := 3694325914406089038587303

theorem tailTrace_7194674 : CollatzResearch.WordTrace tailWord_7194674 prefixEnd_7194674 3694325914406089038587303 := by
  unfold tailWord_7194674
  simp only [CollatzResearch.WordTrace]
  refine ⟨65602829684233081334581769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174940879157954883558884717 65602829684233081334581769)
  ·
    refine ⟨49202122263174811000936327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65602829684233081334581769 49202122263174811000936327)
    ·
      refine ⟨73803183394762216501404491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49202122263174811000936327 73803183394762216501404491)
      ·
        refine ⟨110704775092143324752106737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73803183394762216501404491 110704775092143324752106737)
        ·
          refine ⟨83028581319107493564080053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110704775092143324752106737 83028581319107493564080053)
          ·
            refine ⟨7783929498666327521632505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83028581319107493564080053 7783929498666327521632505)
            ·
              refine ⟨5837947123999745641224379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7783929498666327521632505 5837947123999745641224379)
              ·
                refine ⟨8756920685999618461836569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837947123999745641224379 8756920685999618461836569)
                ·
                  refine ⟨6567690514499713846377427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8756920685999618461836569 6567690514499713846377427)
                  ·
                    refine ⟨9851535771749570769566141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6567690514499713846377427 9851535771749570769566141)
                    ·
                      refine ⟨3694325914406089038587303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9851535771749570769566141 3694325914406089038587303)
                      ·
                        rfl

theorem cell23_7194674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_7194674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194674 prefixEnd_7194674 := by exact prefixLift 7194674
  have htrace : WordTrace (prefixWord ++ tailWord_7194674) baseStart_7194674 baseEnd_7194674 := by
    simpa [prefixWord, tailWord_7194674, baseEnd_7194674] using wordTrace_append hprefix tailTrace_7194674
  have hstable : (prefixWord ++ tailWord_7194674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194674).length < 2 ^ (prefixWord ++ tailWord_7194674).sum := by decide
  have hdescent : baseEnd_7194674 < baseStart_7194674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194696 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_7194696 : Nat := 118140960795 + 7194696 * 2 ^ 59
def prefixEnd_7194696 : Nat := 4983230072969 + 3 ^ 40 * 7194696 * 2
def baseEnd_7194696 : Nat := 3694337210980487952512201

theorem tailTrace_7194696 : CollatzResearch.WordTrace tailWord_7194696 prefixEnd_7194696 3694337210980487952512201 := by
  unfold tailWord_7194696
  simp only [CollatzResearch.WordTrace]
  refine ⟨131206060571426311547813971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174941414095235082063751961 131206060571426311547813971)
  ·
    refine ⟨196809090857139467321720957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131206060571426311547813971 196809090857139467321720957)
    ·
      refine ⟨73803409071427300245645359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196809090857139467321720957 73803409071427300245645359)
      ·
        refine ⟨110705113607140950368468039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73803409071427300245645359 110705113607140950368468039)
        ·
          refine ⟨166057670410711425552702059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110705113607140950368468039 166057670410711425552702059)
          ·
            refine ⟨249086505616067138329053089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166057670410711425552702059 249086505616067138329053089)
            ·
              refine ⟨186814879212050353746789817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249086505616067138329053089 186814879212050353746789817)
              ·
                refine ⟨140111159409037765310092363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186814879212050353746789817 140111159409037765310092363)
                ·
                  refine ⟨210166739113556647965138545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140111159409037765310092363 210166739113556647965138545)
                  ·
                    refine ⟨157625054335167485973853909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210166739113556647965138545 157625054335167485973853909)
                    ·
                      refine ⟨3694337210980487952512201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157625054335167485973853909 3694337210980487952512201)
                      ·
                        rfl

theorem cell23_7194696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_7194696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194696 prefixEnd_7194696 := by exact prefixLift 7194696
  have htrace : WordTrace (prefixWord ++ tailWord_7194696) baseStart_7194696 baseEnd_7194696 := by
    simpa [prefixWord, tailWord_7194696, baseEnd_7194696] using wordTrace_append hprefix tailTrace_7194696
  have hstable : (prefixWord ++ tailWord_7194696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194696).length < 2 ^ (prefixWord ++ tailWord_7194696).sum := by decide
  have hdescent : baseEnd_7194696 < baseStart_7194696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194713 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 2, 3, 3]
def baseStart_7194713 : Nat := 118140960795 + 7194713 * 2 ^ 59
def prefixEnd_7194713 : Nat := 4983230072969 + 3 ^ 40 * 7194713 * 2
def baseEnd_7194713 : Nat := 3694345940151614385999623

theorem tailTrace_7194713 : CollatzResearch.WordTrace tailWord_7194713 prefixEnd_7194713 3694345940151614385999623 := by
  unfold tailWord_7194713
  simp only [CollatzResearch.WordTrace]
  refine ⟨262412741183791034998996793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174941827455860689999331195 262412741183791034998996793)
  ·
    refine ⟨196809555887843276249247595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262412741183791034998996793 196809555887843276249247595)
    ·
      refine ⟨295214333831764914373871393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196809555887843276249247595 295214333831764914373871393)
      ·
        refine ⟨221410750373823685780403545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295214333831764914373871393 221410750373823685780403545)
        ·
          refine ⟨166058062780367764335302659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221410750373823685780403545 166058062780367764335302659)
          ·
            refine ⟨249087094170551646502953989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166058062780367764335302659 249087094170551646502953989)
            ·
              refine ⟨46703830156978433719303873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249087094170551646502953989 46703830156978433719303873)
              ·
                refine ⟨35027872617733825289477905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46703830156978433719303873 35027872617733825289477905)
                ·
                  refine ⟨26270904463300368967108429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35027872617733825289477905 26270904463300368967108429)
                  ·
                    refine ⟨9851589173737638362665661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26270904463300368967108429 9851589173737638362665661)
                    ·
                      refine ⟨3694345940151614385999623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9851589173737638362665661 3694345940151614385999623)
                      ·
                        rfl

theorem cell23_7194713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_7194713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194713 prefixEnd_7194713 := by exact prefixLift 7194713
  have htrace : WordTrace (prefixWord ++ tailWord_7194713) baseStart_7194713 baseEnd_7194713 := by
    simpa [prefixWord, tailWord_7194713, baseEnd_7194713] using wordTrace_append hprefix tailTrace_7194713
  have hstable : (prefixWord ++ tailWord_7194713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194713).length < 2 ^ (prefixWord ++ tailWord_7194713).sum := by decide
  have hdescent : baseEnd_7194713 < baseStart_7194713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194720 : List Nat := [2, 1, 1, 3, 2, 4, 1, 4, 5]
def baseStart_7194720 : Nat := 118140960795 + 7194720 * 2 ^ 59
def prefixEnd_7194720 : Nat := 4983230072969 + 3 ^ 40 * 7194720 * 2
def baseEnd_7194720 : Nat := 410483281612910650956899

theorem tailTrace_7194720 : CollatzResearch.WordTrace tailWord_7194720 prefixEnd_7194720 410483281612910650956899 := by
  unfold tailWord_7194720
  simp only [CollatzResearch.WordTrace]
  refine ⟨131206498247382837597250807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174941997663177116796334409 131206498247382837597250807)
  ·
    refine ⟨196809747371074256395876211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131206498247382837597250807 196809747371074256395876211)
    ·
      refine ⟨295214621056611384593814317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196809747371074256395876211 295214621056611384593814317)
      ·
        refine ⟨110705482896229269222680369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295214621056611384593814317 110705482896229269222680369)
        ·
          refine ⟨83029112172171951917010277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110705482896229269222680369 83029112172171951917010277)
          ·
            refine ⟨15567958532282240984439427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83029112172171951917010277 15567958532282240984439427)
            ·
              refine ⟨23351937798423361476659141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15567958532282240984439427 23351937798423361476659141)
              ·
                refine ⟨4378488337204380276873589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23351937798423361476659141 4378488337204380276873589)
                ·
                  refine ⟨410483281612910650956899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4378488337204380276873589 410483281612910650956899)
                  ·
                    rfl

theorem cell23_7194720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 5].length) (baseStart_7194720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194720 prefixEnd_7194720 := by exact prefixLift 7194720
  have htrace : WordTrace (prefixWord ++ tailWord_7194720) baseStart_7194720 baseEnd_7194720 := by
    simpa [prefixWord, tailWord_7194720, baseEnd_7194720] using wordTrace_append hprefix tailTrace_7194720
  have hstable : (prefixWord ++ tailWord_7194720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194720).length < 2 ^ (prefixWord ++ tailWord_7194720).sum := by decide
  have hdescent : baseEnd_7194720 < baseStart_7194720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194733 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_7194733 : Nat := 118140960795 + 7194733 * 2 ^ 59
def prefixEnd_7194733 : Nat := 4983230072969 + 3 ^ 40 * 7194733 * 2
def baseEnd_7194733 : Nat := 1231452069921568102583177

theorem tailTrace_7194733 : CollatzResearch.WordTrace tailWord_7194733 prefixEnd_7194733 1231452069921568102583177 := by
  unfold tailWord_7194733
  simp only [CollatzResearch.WordTrace]
  refine ⟨262413470643718578414724853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174942313762479052276483235 262413470643718578414724853)
  ·
    refine ⟨24601262872848616726380455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262413470643718578414724853 24601262872848616726380455)
    ·
      refine ⟨36901894309272925089570683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24601262872848616726380455 36901894309272925089570683)
      ·
        refine ⟨55352841463909387634356025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36901894309272925089570683 55352841463909387634356025)
        ·
          refine ⟨41514631097932040725767019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55352841463909387634356025 41514631097932040725767019)
          ·
            refine ⟨62271946646898061088650529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41514631097932040725767019 62271946646898061088650529)
            ·
              refine ⟨46703959985173545816487897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62271946646898061088650529 46703959985173545816487897)
              ·
                refine ⟨35027969988880159362365923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46703959985173545816487897 35027969988880159362365923)
                ·
                  refine ⟨52541954983320239043548885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35027969988880159362365923 52541954983320239043548885)
                  ·
                    refine ⟨1231452069921568102583177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52541954983320239043548885 1231452069921568102583177)
                    ·
                      rfl

theorem cell23_7194733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_7194733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194733 prefixEnd_7194733 := by exact prefixLift 7194733
  have htrace : WordTrace (prefixWord ++ tailWord_7194733) baseStart_7194733 baseEnd_7194733 := by
    simpa [prefixWord, tailWord_7194733, baseEnd_7194733] using wordTrace_append hprefix tailTrace_7194733
  have hstable : (prefixWord ++ tailWord_7194733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194733).length < 2 ^ (prefixWord ++ tailWord_7194733).sum := by decide
  have hdescent : baseEnd_7194733 < baseStart_7194733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194770 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_7194770 : Nat := 118140960795 + 7194770 * 2 ^ 59
def prefixEnd_7194770 : Nat := 4983230072969 + 3 ^ 40 * 7194770 * 2
def baseEnd_7194770 : Nat := 3694375208548920662986861

theorem tailTrace_7194770 : CollatzResearch.WordTrace tailWord_7194770 prefixEnd_7194770 3694375208548920662986861 := by
  unfold tailWord_7194770
  simp only [CollatzResearch.WordTrace]
  refine ⟨65603705036146133433455441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174943213429723022489214509 65603705036146133433455441)
  ·
    refine ⟨49202778777109600075091581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65603705036146133433455441 49202778777109600075091581)
    ·
      refine ⟨18451042041416100028159343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49202778777109600075091581 18451042041416100028159343)
      ·
        refine ⟨27676563062124150042239015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18451042041416100028159343 27676563062124150042239015)
        ·
          refine ⟨41514844593186225063358523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27676563062124150042239015 41514844593186225063358523)
          ·
            refine ⟨62272266889779337595037785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41514844593186225063358523 62272266889779337595037785)
            ·
              refine ⟨46704200167334503196278339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62272266889779337595037785 46704200167334503196278339)
              ·
                refine ⟨70056300251001754794417509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46704200167334503196278339 70056300251001754794417509)
                ·
                  refine ⟨13135556297062829023953283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70056300251001754794417509 13135556297062829023953283)
                  ·
                    refine ⟨19703334445594243535929925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13135556297062829023953283 19703334445594243535929925)
                    ·
                      refine ⟨3694375208548920662986861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19703334445594243535929925 3694375208548920662986861)
                      ·
                        rfl

theorem cell23_7194770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_7194770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194770 prefixEnd_7194770 := by exact prefixLift 7194770
  have htrace : WordTrace (prefixWord ++ tailWord_7194770) baseStart_7194770 baseEnd_7194770 := by
    simpa [prefixWord, tailWord_7194770, baseEnd_7194770] using wordTrace_append hprefix tailTrace_7194770
  have hstable : (prefixWord ++ tailWord_7194770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194770).length < 2 ^ (prefixWord ++ tailWord_7194770).sum := by decide
  have hdescent : baseEnd_7194770 < baseStart_7194770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194797 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_7194797 : Nat := 118140960795 + 7194797 * 2 ^ 59
def prefixEnd_7194797 : Nat := 4983230072969 + 3 ^ 40 * 7194797 * 2
def baseEnd_7194797 : Nat := 1231463024175530685783079

theorem tailTrace_7194797 : CollatzResearch.WordTrace tailWord_7194797 prefixEnd_7194797 1231463024175530685783079 := by
  unfold tailWord_7194797
  simp only [CollatzResearch.WordTrace]
  refine ⟨262415804915486717345054645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174943869943657811563369763 262415804915486717345054645)
  ·
    refine ⟨24601481710826879751098873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262415804915486717345054645 24601481710826879751098873)
    ·
      refine ⟨18451111283120159813324155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24601481710826879751098873 18451111283120159813324155)
      ·
        refine ⟨27676666924680239719986233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18451111283120159813324155 27676666924680239719986233)
        ·
          refine ⟨20757500193510179789989675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27676666924680239719986233 20757500193510179789989675)
          ·
            refine ⟨31136250290265269684984513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20757500193510179789989675 31136250290265269684984513)
            ·
              refine ⟨23352187717698952263738385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31136250290265269684984513 23352187717698952263738385)
              ·
                refine ⟨17514140788274214197803789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23352187717698952263738385 17514140788274214197803789)
                ·
                  refine ⟨6567802795602830324176421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17514140788274214197803789 6567802795602830324176421)
                  ·
                    refine ⟨1231463024175530685783079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6567802795602830324176421 1231463024175530685783079)
                    ·
                      rfl

theorem cell23_7194797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_7194797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194797 prefixEnd_7194797 := by exact prefixLift 7194797
  have htrace : WordTrace (prefixWord ++ tailWord_7194797) baseStart_7194797 baseEnd_7194797 := by
    simpa [prefixWord, tailWord_7194797, baseEnd_7194797] using wordTrace_append hprefix tailTrace_7194797
  have hstable : (prefixWord ++ tailWord_7194797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194797).length < 2 ^ (prefixWord ++ tailWord_7194797).sum := by decide
  have hdescent : baseEnd_7194797 < baseStart_7194797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194803 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 3]
def baseStart_7194803 : Nat := 118140960795 + 7194803 * 2 ^ 59
def prefixEnd_7194803 : Nat := 4983230072969 + 3 ^ 40 * 7194803 * 2
def baseEnd_7194803 : Nat := 3694392153410519033874209

theorem tailTrace_7194803 : CollatzResearch.WordTrace tailWord_7194803 prefixEnd_7194803 3694392153410519033874209 := by
  unfold tailWord_7194803
  simp only [CollatzResearch.WordTrace]
  refine ⟨262416023753464980369773063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174944015835643320246515375 262416023753464980369773063)
  ·
    refine ⟨393624035630197470554659595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262416023753464980369773063 393624035630197470554659595)
    ·
      refine ⟨590436053445296205831989393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393624035630197470554659595 590436053445296205831989393)
      ·
        refine ⟨442827040083972154373992045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590436053445296205831989393 442827040083972154373992045)
        ·
          refine ⟨166060140031489557890247017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442827040083972154373992045 166060140031489557890247017)
          ·
            refine ⟨124545105023617168417685263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166060140031489557890247017 124545105023617168417685263)
            ·
              refine ⟨186817657535425752626527895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124545105023617168417685263 186817657535425752626527895)
              ·
                refine ⟨280226486303138628939791843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186817657535425752626527895 280226486303138628939791843)
                ·
                  refine ⟨420339729454707943409687765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280226486303138628939791843 420339729454707943409687765)
                  ·
                    refine ⟨9851712409094717423664557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 420339729454707943409687765 9851712409094717423664557)
                    ·
                      refine ⟨3694392153410519033874209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9851712409094717423664557 3694392153410519033874209)
                      ·
                        rfl

theorem cell23_7194803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 3].length) (baseStart_7194803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194803 prefixEnd_7194803 := by exact prefixLift 7194803
  have htrace : WordTrace (prefixWord ++ tailWord_7194803) baseStart_7194803 baseEnd_7194803 := by
    simpa [prefixWord, tailWord_7194803, baseEnd_7194803] using wordTrace_append hprefix tailTrace_7194803
  have hstable : (prefixWord ++ tailWord_7194803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194803).length < 2 ^ (prefixWord ++ tailWord_7194803).sum := by decide
  have hdescent : baseEnd_7194803 < baseStart_7194803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194823 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 7, 5]
def baseStart_7194823 : Nat := 118140960795 + 7194823 * 2 ^ 59
def prefixEnd_7194823 : Nat := 4983230072969 + 3 ^ 40 * 7194823 * 2
def baseEnd_7194823 : Nat := 1231467474341202985208039

theorem tailTrace_7194823 : CollatzResearch.WordTrace tailWord_7194823 prefixEnd_7194823 1231467474341202985208039 := by
  unfold tailWord_7194823
  simp only [CollatzResearch.WordTrace]
  refine ⟨262416753213392523785501123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174944502142261682523667415 262416753213392523785501123)
  ·
    refine ⟨393625129820088785678251685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262416753213392523785501123 393625129820088785678251685)
    ·
      refine ⟨73804711841266647314672191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393625129820088785678251685 73804711841266647314672191)
      ·
        refine ⟨110707067761899970972008287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73804711841266647314672191 110707067761899970972008287)
        ·
          refine ⟨166060601642849956458012431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110707067761899970972008287 166060601642849956458012431)
          ·
            refine ⟨249090902464274934687018647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166060601642849956458012431 249090902464274934687018647)
            ·
              refine ⟨373636353696412402030527971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249090902464274934687018647 373636353696412402030527971)
              ·
                refine ⟨560454530544618603045791957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373636353696412402030527971 560454530544618603045791957)
                ·
                  refine ⟨13135653059639498508885749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 560454530544618603045791957 13135653059639498508885749)
                  ·
                    refine ⟨1231467474341202985208039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13135653059639498508885749 1231467474341202985208039)
                    ·
                      rfl

theorem cell23_7194823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_7194823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194823 prefixEnd_7194823 := by exact prefixLift 7194823
  have htrace : WordTrace (prefixWord ++ tailWord_7194823) baseStart_7194823 baseEnd_7194823 := by
    simpa [prefixWord, tailWord_7194823, baseEnd_7194823] using wordTrace_append hprefix tailTrace_7194823
  have hstable : (prefixWord ++ tailWord_7194823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194823).length < 2 ^ (prefixWord ++ tailWord_7194823).sum := by decide
  have hdescent : baseEnd_7194823 < baseStart_7194823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194844 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 6]
def baseStart_7194844 : Nat := 118140960795 + 7194844 * 2 ^ 59
def prefixEnd_7194844 : Nat := 4983230072969 + 3 ^ 40 * 7194844 * 2
def baseEnd_7194844 : Nat := 410490356235261485940169

theorem tailTrace_7194844 : CollatzResearch.WordTrace tailWord_7194844 prefixEnd_7194844 410490356235261485940169 := by
  unfold tailWord_7194844
  simp only [CollatzResearch.WordTrace]
  refine ⟨131208759573158222186007793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174945012764210962914677057 131208759573158222186007793)
  ·
    refine ⟨98406569679868666639505845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131208759573158222186007793 98406569679868666639505845)
    ·
      refine ⟨9225615907487687497453673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98406569679868666639505845 9225615907487687497453673)
      ·
        refine ⟨6919211930615765623090255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9225615907487687497453673 6919211930615765623090255)
        ·
          refine ⟨10378817895923648434635383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6919211930615765623090255 10378817895923648434635383)
          ·
            refine ⟨15568226843885472651953075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10378817895923648434635383 15568226843885472651953075)
            ·
              refine ⟨23352340265828208977929613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15568226843885472651953075 23352340265828208977929613)
              ·
                refine ⟨8757127599685578366723605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23352340265828208977929613 8757127599685578366723605)
                ·
                  refine ⟨410490356235261485940169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8757127599685578366723605 410490356235261485940169)
                  ·
                    rfl

theorem cell23_7194844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_7194844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194844 prefixEnd_7194844 := by exact prefixLift 7194844
  have htrace : WordTrace (prefixWord ++ tailWord_7194844) baseStart_7194844 baseEnd_7194844 := by
    simpa [prefixWord, tailWord_7194844, baseEnd_7194844] using wordTrace_append hprefix tailTrace_7194844
  have hstable : (prefixWord ++ tailWord_7194844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194844).length < 2 ^ (prefixWord ++ tailWord_7194844).sum := by decide
  have hdescent : baseEnd_7194844 < baseStart_7194844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194860 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_7194860 : Nat := 118140960795 + 7194860 * 2 ^ 59
def prefixEnd_7194860 : Nat := 4983230072969 + 3 ^ 40 * 7194860 * 2
def baseEnd_7194860 : Nat := 3694421421807825310861447

theorem tailTrace_7194860 : CollatzResearch.WordTrace tailWord_7194860 prefixEnd_7194860 3694421421807825310861447 := by
  unfold tailWord_7194860
  simp only [CollatzResearch.WordTrace]
  refine ⟨131209051357129239552299017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174945401809505652736398689 131209051357129239552299017)
  ·
    refine ⟨98406788517846929664224263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131209051357129239552299017 98406788517846929664224263)
    ·
      refine ⟨147610182776770394496336395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98406788517846929664224263 147610182776770394496336395)
      ·
        refine ⟨221415274165155591744504593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147610182776770394496336395 221415274165155591744504593)
        ·
          refine ⟨166061455623866693808378445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221415274165155591744504593 166061455623866693808378445)
          ·
            refine ⟨62273045858950010178141917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166061455623866693808378445 62273045858950010178141917)
            ·
              refine ⟨23352392197106253816803219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62273045858950010178141917 23352392197106253816803219)
              ·
                refine ⟨35028588295659380725204829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23352392197106253816803219 35028588295659380725204829)
                ·
                  refine ⟨13135720610872267771951811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35028588295659380725204829 13135720610872267771951811)
                  ·
                    refine ⟨19703580916308401657927717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13135720610872267771951811 19703580916308401657927717)
                    ·
                      refine ⟨3694421421807825310861447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19703580916308401657927717 3694421421807825310861447)
                      ·
                        rfl

theorem cell23_7194860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_7194860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194860 prefixEnd_7194860 := by exact prefixLift 7194860
  have htrace : WordTrace (prefixWord ++ tailWord_7194860) baseStart_7194860 baseEnd_7194860 := by
    simpa [prefixWord, tailWord_7194860, baseEnd_7194860] using wordTrace_append hprefix tailTrace_7194860
  have hstable : (prefixWord ++ tailWord_7194860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194860).length < 2 ^ (prefixWord ++ tailWord_7194860).sum := by decide
  have hdescent : baseEnd_7194860 < baseStart_7194860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194870 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_7194870 : Nat := 118140960795 + 7194870 * 2 ^ 59
def prefixEnd_7194870 : Nat := 4983230072969 + 3 ^ 40 * 7194870 * 2
def baseEnd_7194870 : Nat := 1231475518871456757245467

theorem tailTrace_7194870 : CollatzResearch.WordTrace tailWord_7194870 prefixEnd_7194870 1231475518871456757245467 := by
  unfold tailWord_7194870
  simp only [CollatzResearch.WordTrace]
  refine ⟨16401154215263890675778879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174945644962814833874974709 16401154215263890675778879)
  ·
    refine ⟨24601731322895836013668319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16401154215263890675778879 24601731322895836013668319)
    ·
      refine ⟨36902596984343754020502479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24601731322895836013668319 36902596984343754020502479)
      ·
        refine ⟨55353895476515631030753719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36902596984343754020502479 55353895476515631030753719)
        ·
          refine ⟨83030843214773446546130579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55353895476515631030753719 83030843214773446546130579)
          ·
            refine ⟨124546264822160169819195869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83030843214773446546130579 124546264822160169819195869)
            ·
              refine ⟨46704849308310063682198451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124546264822160169819195869 46704849308310063682198451)
              ·
                refine ⟨70057273962465095523297677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46704849308310063682198451 70057273962465095523297677)
                ·
                  refine ⟨26271477735924410821236629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70057273962465095523297677 26271477735924410821236629)
                  ·
                    refine ⟨1231475518871456757245467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26271477735924410821236629 1231475518871456757245467)
                    ·
                      rfl

theorem cell23_7194870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_7194870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194870 prefixEnd_7194870 := by exact prefixLift 7194870
  have htrace : WordTrace (prefixWord ++ tailWord_7194870) baseStart_7194870 baseEnd_7194870 := by
    simpa [prefixWord, tailWord_7194870, baseEnd_7194870] using wordTrace_append hprefix tailTrace_7194870
  have hstable : (prefixWord ++ tailWord_7194870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194870).length < 2 ^ (prefixWord ++ tailWord_7194870).sum := by decide
  have hdescent : baseEnd_7194870 < baseStart_7194870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194873 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_7194873 : Nat := 118140960795 + 7194873 * 2 ^ 59
def prefixEnd_7194873 : Nat := 4983230072969 + 3 ^ 40 * 7194873 * 2
def baseEnd_7194873 : Nat := 3694428097056333759998887

theorem tailTrace_7194873 : CollatzResearch.WordTrace tailWord_7194873 prefixEnd_7194873 3694428097056333759998887 := by
  unfold tailWord_7194873
  simp only [CollatzResearch.WordTrace]
  refine ⟨262418576863211382324821273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174945717908807588216547515 262418576863211382324821273)
  ·
    refine ⟨196813932647408536743615955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262418576863211382324821273 196813932647408536743615955)
    ·
      refine ⟨295220898971112805115423933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196813932647408536743615955 295220898971112805115423933)
      ·
        refine ⟨110707837114167301918283975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295220898971112805115423933 110707837114167301918283975)
        ·
          refine ⟨166061755671250952877425963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110707837114167301918283975 166061755671250952877425963)
          ·
            refine ⟨249092633506876429316138945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166061755671250952877425963 249092633506876429316138945)
            ·
              refine ⟨186819475130157321987104209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249092633506876429316138945 186819475130157321987104209)
              ·
                refine ⟨140114606347617991490328157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186819475130157321987104209 140114606347617991490328157)
                ·
                  refine ⟨52542977380356746808873059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140114606347617991490328157 52542977380356746808873059)
                  ·
                    refine ⟨78814466070535120213309589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52542977380356746808873059 78814466070535120213309589)
                    ·
                      refine ⟨3694428097056333759998887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78814466070535120213309589 3694428097056333759998887)
                      ·
                        rfl

theorem cell23_7194873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_7194873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194873 prefixEnd_7194873 := by exact prefixLift 7194873
  have htrace : WordTrace (prefixWord ++ tailWord_7194873) baseStart_7194873 baseEnd_7194873 := by
    simpa [prefixWord, tailWord_7194873, baseEnd_7194873] using wordTrace_append hprefix tailTrace_7194873
  have hstable : (prefixWord ++ tailWord_7194873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194873).length < 2 ^ (prefixWord ++ tailWord_7194873).sum := by decide
  have hdescent : baseEnd_7194873 < baseStart_7194873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194880 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 5]
def baseStart_7194880 : Nat := 118140960795 + 7194880 * 2 ^ 59
def prefixEnd_7194880 : Nat := 4983230072969 + 3 ^ 40 * 7194880 * 2
def baseEnd_7194880 : Nat := 3694431691420915232611355

theorem tailTrace_7194880 : CollatzResearch.WordTrace tailWord_7194880 prefixEnd_7194880 3694431691420915232611355 := by
  unfold tailWord_7194880
  simp only [CollatzResearch.WordTrace]
  refine ⟨131209416087093011260163047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174945888116124015013550729 131209416087093011260163047)
  ·
    refine ⟨196814124130639516890244571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131209416087093011260163047 196814124130639516890244571)
    ·
      refine ⟨295221186195959275335366857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196814124130639516890244571 295221186195959275335366857)
      ·
        refine ⟨221415889646969456501525143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295221186195959275335366857 221415889646969456501525143)
        ·
          refine ⟨332123834470454184752287715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221415889646969456501525143 332123834470454184752287715)
          ·
            refine ⟨498185751705681277128431573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332123834470454184752287715 498185751705681277128431573)
            ·
              refine ⟨11676228555601904932697615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 498185751705681277128431573 11676228555601904932697615)
              ·
                refine ⟨17514342833402857399046423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11676228555601904932697615 17514342833402857399046423)
                ·
                  refine ⟨26271514250104286098569635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17514342833402857399046423 26271514250104286098569635)
                  ·
                    refine ⟨39407271375156429147854453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26271514250104286098569635 39407271375156429147854453)
                    ·
                      refine ⟨3694431691420915232611355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39407271375156429147854453 3694431691420915232611355)
                      ·
                        rfl

theorem cell23_7194880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_7194880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194880 prefixEnd_7194880 := by exact prefixLift 7194880
  have htrace : WordTrace (prefixWord ++ tailWord_7194880) baseStart_7194880 baseEnd_7194880 := by
    simpa [prefixWord, tailWord_7194880, baseEnd_7194880] using wordTrace_append hprefix tailTrace_7194880
  have hstable : (prefixWord ++ tailWord_7194880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194880).length < 2 ^ (prefixWord ++ tailWord_7194880).sum := by decide
  have hdescent : baseEnd_7194880 < baseStart_7194880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194888 : List Nat := [2, 1, 3, 2, 3, 3, 2, 2, 1, 1, 3]
def baseStart_7194888 : Nat := 118140960795 + 7194888 * 2 ^ 59
def prefixEnd_7194888 : Nat := 4983230072969 + 3 ^ 40 * 7194888 * 2
def baseEnd_7194888 : Nat := 3694435799266151201311319

theorem tailTrace_7194888 : CollatzResearch.WordTrace tailWord_7194888 prefixEnd_7194888 3694435799266151201311319 := by
  unfold tailWord_7194888
  simp only [CollatzResearch.WordTrace]
  refine ⟨131209561979078519943308659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174946082638771359924411545 131209561979078519943308659)
  ·
    refine ⟨196814342968617779914962989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131209561979078519943308659 196814342968617779914962989)
    ·
      refine ⟨73805378613231667468111121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196814342968617779914962989 73805378613231667468111121)
      ·
        refine ⟨55354033959923750601083341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73805378613231667468111121 55354033959923750601083341)
        ·
          refine ⟨20757762734971406475406253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55354033959923750601083341 20757762734971406475406253)
          ·
            refine ⟨7784161025614277428277345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20757762734971406475406253 7784161025614277428277345)
            ·
              refine ⟨5838120769210708071208009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7784161025614277428277345 5838120769210708071208009)
              ·
                refine ⟨4378590576908031053406007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5838120769210708071208009 4378590576908031053406007)
                ·
                  refine ⟨6567885865362046580109011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4378590576908031053406007 6567885865362046580109011)
                  ·
                    refine ⟨9851828798043069870163517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6567885865362046580109011 9851828798043069870163517)
                    ·
                      refine ⟨3694435799266151201311319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9851828798043069870163517 3694435799266151201311319)
                      ·
                        rfl

theorem cell23_7194888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_7194888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194888 prefixEnd_7194888 := by exact prefixLift 7194888
  have htrace : WordTrace (prefixWord ++ tailWord_7194888) baseStart_7194888 baseEnd_7194888 := by
    simpa [prefixWord, tailWord_7194888, baseEnd_7194888] using wordTrace_append hprefix tailTrace_7194888
  have hstable : (prefixWord ++ tailWord_7194888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194888).length < 2 ^ (prefixWord ++ tailWord_7194888).sum := by decide
  have hdescent : baseEnd_7194888 < baseStart_7194888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194894 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2]
def baseStart_7194894 : Nat := 118140960795 + 7194894 * 2 ^ 59
def prefixEnd_7194894 : Nat := 4983230072969 + 3 ^ 40 * 7194894 * 2
def baseEnd_7194894 : Nat := 3694438880150078177836291

theorem tailTrace_7194894 : CollatzResearch.WordTrace tailWord_7194894 prefixEnd_7194894 3694438880150078177836291 := by
  unfold tailWord_7194894
  simp only [CollatzResearch.WordTrace]
  refine ⟨32802417849516912863916967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174946228530756868607557157 32802417849516912863916967)
  ·
    refine ⟨49203626774275369295875451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32802417849516912863916967 49203626774275369295875451)
    ·
      refine ⟨73805440161413053943813177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49203626774275369295875451 73805440161413053943813177)
      ·
        refine ⟨55354080121059790457859883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73805440161413053943813177 55354080121059790457859883)
        ·
          refine ⟨83031120181589685686789825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55354080121059790457859883 83031120181589685686789825)
          ·
            refine ⟨62273340136192264265092369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83031120181589685686789825 62273340136192264265092369)
            ·
              refine ⟨46705005102144198198819277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62273340136192264265092369 46705005102144198198819277)
              ·
                refine ⟨17514376913304074324557229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46705005102144198198819277 17514376913304074324557229)
                ·
                  refine ⟨6567891342489027871708961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17514376913304074324557229 6567891342489027871708961)
                  ·
                    refine ⟨4925918506866770903781721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6567891342489027871708961 4925918506866770903781721)
                    ·
                      refine ⟨3694438880150078177836291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4925918506866770903781721 3694438880150078177836291)
                      ·
                        rfl

theorem cell23_7194894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_7194894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194894 prefixEnd_7194894 := by exact prefixLift 7194894
  have htrace : WordTrace (prefixWord ++ tailWord_7194894) baseStart_7194894 baseEnd_7194894 := by
    simpa [prefixWord, tailWord_7194894, baseEnd_7194894] using wordTrace_append hprefix tailTrace_7194894
  have hstable : (prefixWord ++ tailWord_7194894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194894).length < 2 ^ (prefixWord ++ tailWord_7194894).sum := by decide
  have hdescent : baseEnd_7194894 < baseStart_7194894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194917 : List Nat := [1, 3, 1, 2, 5, 1, 3, 7]
def baseStart_7194917 : Nat := 118140960795 + 7194917 * 2 ^ 59
def prefixEnd_7194917 : Nat := 4983230072969 + 3 ^ 40 * 7194917 * 2
def baseEnd_7194917 : Nat := 136831507044634503253655

theorem tailTrace_7194917 : CollatzResearch.WordTrace tailWord_7194917 prefixEnd_7194917 136831507044634503253655 := by
  unfold tailWord_7194917
  simp only [CollatzResearch.WordTrace]
  refine ⟨262420181675051977839423005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174946787783367985226282003 262420181675051977839423005)
  ·
    refine ⟨98407568128144491689783627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262420181675051977839423005 98407568128144491689783627)
    ·
      refine ⟨147611352192216737534675441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98407568128144491689783627 147611352192216737534675441)
      ·
        refine ⟨110708514144162553151006581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147611352192216737534675441 110708514144162553151006581)
        ·
          refine ⟨10378923201015239357906867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110708514144162553151006581 10378923201015239357906867)
          ·
            refine ⟨15568384801522859036860301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10378923201015239357906867 15568384801522859036860301)
            ·
              refine ⟨5838144300571072138822613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15568384801522859036860301 5838144300571072138822613)
              ·
                refine ⟨136831507044634503253655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5838144300571072138822613 136831507044634503253655)
                ·
                  rfl

theorem cell23_7194917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 7].length) (baseStart_7194917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194917 prefixEnd_7194917 := by exact prefixLift 7194917
  have htrace : WordTrace (prefixWord ++ tailWord_7194917) baseStart_7194917 baseEnd_7194917 := by
    simpa [prefixWord, tailWord_7194917, baseEnd_7194917] using wordTrace_append hprefix tailTrace_7194917
  have hstable : (prefixWord ++ tailWord_7194917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194917).length < 2 ^ (prefixWord ++ tailWord_7194917).sum := by decide
  have hdescent : baseEnd_7194917 < baseStart_7194917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194960 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 2, 6]
def baseStart_7194960 : Nat := 118140960795 + 7194960 * 2 ^ 59
def prefixEnd_7194960 : Nat := 4983230072969 + 3 ^ 40 * 7194960 * 2
def baseEnd_7194960 : Nat := 1231490923291091639870329

theorem tailTrace_7194960 : CollatzResearch.WordTrace tailWord_7194960 prefixEnd_7194960 1231490923291091639870329 := by
  unfold tailWord_7194960
  simp only [CollatzResearch.WordTrace]
  refine ⟨131210875006948098091619167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174947833342597464122158889 131210875006948098091619167)
  ·
    refine ⟨196816312510422147137428751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131210875006948098091619167 196816312510422147137428751)
    ·
      refine ⟨295224468765633220706143127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196816312510422147137428751 295224468765633220706143127)
      ·
        refine ⟨442836703148449831059214691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295224468765633220706143127 442836703148449831059214691)
        ·
          refine ⟨664255054722674746588822037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442836703148449831059214691 664255054722674746588822037)
          ·
            refine ⟨31136955690125378746351033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 664255054722674746588822037 31136955690125378746351033)
            ·
              refine ⟨23352716767594034059763275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31136955690125378746351033 23352716767594034059763275)
              ·
                refine ⟨35029075151391051089644913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23352716767594034059763275 35029075151391051089644913)
                ·
                  refine ⟨26271806363543288317233685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35029075151391051089644913 26271806363543288317233685)
                  ·
                    refine ⟨1231490923291091639870329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26271806363543288317233685 1231490923291091639870329)
                    ·
                      rfl

theorem cell23_7194960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_7194960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194960 prefixEnd_7194960 := by exact prefixLift 7194960
  have htrace : WordTrace (prefixWord ++ tailWord_7194960) baseStart_7194960 baseEnd_7194960 := by
    simpa [prefixWord, tailWord_7194960, baseEnd_7194960] using wordTrace_append hprefix tailTrace_7194960
  have hstable : (prefixWord ++ tailWord_7194960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194960).length < 2 ^ (prefixWord ++ tailWord_7194960).sum := by decide
  have hdescent : baseEnd_7194960 < baseStart_7194960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194961 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 2, 1, 3]
def baseStart_7194961 : Nat := 118140960795 + 7194961 * 2 ^ 59
def prefixEnd_7194961 : Nat := 4983230072969 + 3 ^ 40 * 7194961 * 2
def baseEnd_7194961 : Nat := 3694473283353929415698483

theorem tailTrace_7194961 : CollatzResearch.WordTrace tailWord_7194961 prefixEnd_7194961 3694473283353929415698483 := by
  unfold tailWord_7194961
  simp only [CollatzResearch.WordTrace]
  refine ⟨262421786486892573354024737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174947857657928382236016491 262421786486892573354024737)
  ·
    refine ⟨196816339865169430015518553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262421786486892573354024737 196816339865169430015518553)
    ·
      refine ⟨147612254898877072511638915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196816339865169430015518553 147612254898877072511638915)
      ·
        refine ⟨221418382348315608767458373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147612254898877072511638915 221418382348315608767458373)
        ·
          refine ⟨41515946690309176643898445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221418382348315608767458373 41515946690309176643898445)
          ·
            refine ⟨15568480008865941241461917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41515946690309176643898445 15568480008865941241461917)
            ·
              refine ⟨5838180003324727965548219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15568480008865941241461917 5838180003324727965548219)
              ·
                refine ⟨8757270004987091948322329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5838180003324727965548219 8757270004987091948322329)
                ·
                  refine ⟨6567952503740318961241747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8757270004987091948322329 6567952503740318961241747)
                  ·
                    refine ⟨9851928755610478441862621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6567952503740318961241747 9851928755610478441862621)
                    ·
                      refine ⟨3694473283353929415698483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9851928755610478441862621 3694473283353929415698483)
                      ·
                        rfl

theorem cell23_7194961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 2, 1, 3].length) (baseStart_7194961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194961 prefixEnd_7194961 := by exact prefixLift 7194961
  have htrace : WordTrace (prefixWord ++ tailWord_7194961) baseStart_7194961 baseEnd_7194961 := by
    simpa [prefixWord, tailWord_7194961, baseEnd_7194961] using wordTrace_append hprefix tailTrace_7194961
  have hstable : (prefixWord ++ tailWord_7194961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194961).length < 2 ^ (prefixWord ++ tailWord_7194961).sum := by decide
  have hdescent : baseEnd_7194961 < baseStart_7194961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7194970 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_7194970 : Nat := 118140960795 + 7194970 * 2 ^ 59
def prefixEnd_7194970 : Nat := 4983230072969 + 3 ^ 40 * 7194970 * 2
def baseEnd_7194970 : Nat := 3694477904679819880485941

theorem tailTrace_7194970 : CollatzResearch.WordTrace tailWord_7194970 prefixEnd_7194970 3694477904679819880485941 := by
  unfold tailWord_7194970
  simp only [CollatzResearch.WordTrace]
  refine ⟨65605528685964991972775591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174948076495906645260734909 65605528685964991972775591)
  ·
    refine ⟨98408293028947487959163387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65605528685964991972775591 98408293028947487959163387)
    ·
      refine ⟨147612439543421231938745081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98408293028947487959163387 147612439543421231938745081)
      ·
        refine ⟨110709329657565923954058811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147612439543421231938745081 110709329657565923954058811)
        ·
          refine ⟨166063994486348885931088217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110709329657565923954058811 166063994486348885931088217)
          ·
            refine ⟨124547995864761664448316163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166063994486348885931088217 124547995864761664448316163)
            ·
              refine ⟨186821993797142496672474245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124547995864761664448316163 186821993797142496672474245)
              ·
                refine ⟨35029123836964218126088921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186821993797142496672474245 35029123836964218126088921)
                ·
                  refine ⟨26271842877723163594566691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35029123836964218126088921 26271842877723163594566691)
                  ·
                    refine ⟨39407764316584745391850037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26271842877723163594566691 39407764316584745391850037)
                    ·
                      refine ⟨3694477904679819880485941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39407764316584745391850037 3694477904679819880485941)
                      ·
                        rfl

theorem cell23_7194970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_7194970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7194970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7194970 prefixEnd_7194970 := by exact prefixLift 7194970
  have htrace : WordTrace (prefixWord ++ tailWord_7194970) baseStart_7194970 baseEnd_7194970 := by
    simpa [prefixWord, tailWord_7194970, baseEnd_7194970] using wordTrace_append hprefix tailTrace_7194970
  have hstable : (prefixWord ++ tailWord_7194970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7194970).length < 2 ^ (prefixWord ++ tailWord_7194970).sum := by decide
  have hdescent : baseEnd_7194970 < baseStart_7194970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7194970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195047 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_7195047 : Nat := 118140960795 + 7195047 * 2 ^ 59
def prefixEnd_7195047 : Nat := 4983230072969 + 3 ^ 40 * 7195047 * 2
def baseEnd_7195047 : Nat := 3694517442690216079223087

theorem tailTrace_7195047 : CollatzResearch.WordTrace tailWord_7195047 prefixEnd_7195047 3694517442690216079223087 := by
  unfold tailWord_7195047
  simp only [CollatzResearch.WordTrace]
  refine ⟨262424923164581010041655395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174949948776387340027770263 262424923164581010041655395)
  ·
    refine ⟨393637384746871515062483093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262424923164581010041655395 393637384746871515062483093)
    ·
      refine ⟨18451752410009602268553895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 393637384746871515062483093 18451752410009602268553895)
      ·
        refine ⟨27677628615014403402830843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18451752410009602268553895 27677628615014403402830843)
        ·
          refine ⟨41516442922521605104246265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27677628615014403402830843 41516442922521605104246265)
          ·
            refine ⟨31137332191891203828184699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41516442922521605104246265 31137332191891203828184699)
            ·
              refine ⟨46705998287836805742277049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31137332191891203828184699 46705998287836805742277049)
              ·
                refine ⟨35029498715877604306707787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46705998287836805742277049 35029498715877604306707787)
                ·
                  refine ⟨52544248073816406460061681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35029498715877604306707787 52544248073816406460061681)
                  ·
                    refine ⟨39408186055362304845046261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52544248073816406460061681 39408186055362304845046261)
                    ·
                      refine ⟨3694517442690216079223087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39408186055362304845046261 3694517442690216079223087)
                      ·
                        rfl

theorem cell23_7195047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_7195047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195047 prefixEnd_7195047 := by exact prefixLift 7195047
  have htrace : WordTrace (prefixWord ++ tailWord_7195047) baseStart_7195047 baseEnd_7195047 := by
    simpa [prefixWord, tailWord_7195047, baseEnd_7195047] using wordTrace_append hprefix tailTrace_7195047
  have hstable : (prefixWord ++ tailWord_7195047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195047).length < 2 ^ (prefixWord ++ tailWord_7195047).sum := by decide
  have hdescent : baseEnd_7195047 < baseStart_7195047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195114 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 6]
def baseStart_7195114 : Nat := 118140960795 + 7195114 * 2 ^ 59
def prefixEnd_7195114 : Nat := 4983230072969 + 3 ^ 40 * 7195114 * 2
def baseEnd_7195114 : Nat := 410505760654896368565031

theorem tailTrace_7195114 : CollatzResearch.WordTrace tailWord_7195114 prefixEnd_7195114 410505760654896368565031 := by
  unfold tailWord_7195114
  simp only [CollatzResearch.WordTrace]
  refine ⟨65606841713834570121086099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174951577903558853656229597 65606841713834570121086099)
  ·
    refine ⟨98410262570751855181629149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65606841713834570121086099 98410262570751855181629149)
    ·
      refine ⟨36903848464031945693110931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98410262570751855181629149 36903848464031945693110931)
      ·
        refine ⟨55355772696047918539666397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36903848464031945693110931 55355772696047918539666397)
        ·
          refine ⟨20758414761017969452374899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55355772696047918539666397 20758414761017969452374899)
          ·
            refine ⟨31137622141526954178562349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20758414761017969452374899 31137622141526954178562349)
            ·
              refine ⟨11676608303072607816960881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31137622141526954178562349 11676608303072607816960881)
              ·
                refine ⟨8757456227304455862720661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11676608303072607816960881 8757456227304455862720661)
                ·
                  refine ⟨410505760654896368565031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8757456227304455862720661 410505760654896368565031)
                  ·
                    rfl

theorem cell23_7195114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_7195114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195114 prefixEnd_7195114 := by exact prefixLift 7195114
  have htrace : WordTrace (prefixWord ++ tailWord_7195114) baseStart_7195114 baseEnd_7195114 := by
    simpa [prefixWord, tailWord_7195114, baseEnd_7195114] using wordTrace_append hprefix tailTrace_7195114
  have hstable : (prefixWord ++ tailWord_7195114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195114).length < 2 ^ (prefixWord ++ tailWord_7195114).sum := by decide
  have hdescent : baseEnd_7195114 < baseStart_7195114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195157 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_7195157 : Nat := 118140960795 + 7195157 * 2 ^ 59
def prefixEnd_7195157 : Nat := 4983230072969 + 3 ^ 40 * 7195157 * 2
def baseEnd_7195157 : Nat := 1231524641854070216282527

theorem tailTrace_7195157 : CollatzResearch.WordTrace tailWord_7195157 prefixEnd_7195157 1231524641854070216282527 := by
  unfold tailWord_7195157
  simp only [CollatzResearch.WordTrace]
  refine ⟨262428935194182498828159725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174952623462788332552106483 262428935194182498828159725)
  ·
    refine ⟨98410850697818437060559897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262428935194182498828159725 98410850697818437060559897)
    ·
      refine ⟨73808138023363827795419923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98410850697818437060559897 73808138023363827795419923)
      ·
        refine ⟨110712207035045741693129885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73808138023363827795419923 110712207035045741693129885)
        ·
          refine ⟨41517077638142153134923707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110712207035045741693129885 41517077638142153134923707)
          ·
            refine ⟨62275616457213229702385561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41517077638142153134923707 62275616457213229702385561)
            ·
              refine ⟨46706712342909922276789171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62275616457213229702385561 46706712342909922276789171)
              ·
                refine ⟨70060068514364883415183757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46706712342909922276789171 70060068514364883415183757)
                ·
                  refine ⟨26272525692886831280693909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70060068514364883415183757 26272525692886831280693909)
                  ·
                    refine ⟨1231524641854070216282527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26272525692886831280693909 1231524641854070216282527)
                    ·
                      rfl

theorem cell23_7195157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_7195157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195157 prefixEnd_7195157 := by exact prefixLift 7195157
  have htrace : WordTrace (prefixWord ++ tailWord_7195157) baseStart_7195157 baseEnd_7195157 := by
    simpa [prefixWord, tailWord_7195157, baseEnd_7195157] using wordTrace_append hprefix tailTrace_7195157
  have hstable : (prefixWord ++ tailWord_7195157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195157).length < 2 ^ (prefixWord ++ tailWord_7195157).sum := by decide
  have hdescent : baseEnd_7195157 < baseStart_7195157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195168 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7195168 : Nat := 118140960795 + 7195168 * 2 ^ 59
def prefixEnd_7195168 : Nat := 4983230072969 + 3 ^ 40 * 7195168 * 2
def baseEnd_7195168 : Nat := 3694579573849410105810031

theorem tailTrace_7195168 : CollatzResearch.WordTrace tailWord_7195168 prefixEnd_7195168 3694579573849410105810031 := by
  unfold tailWord_7195168
  simp only [CollatzResearch.WordTrace]
  refine ⟨131214668198571323853405079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174952890931428431804540105 131214668198571323853405079)
  ·
    refine ⟨196822002297856985780107619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131214668198571323853405079 196822002297856985780107619)
    ·
      refine ⟨295233003446785478670161429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196822002297856985780107619 295233003446785478670161429)
      ·
        refine ⟨13839047036568069312663817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 295233003446785478670161429 13839047036568069312663817)
        ·
          refine ⟨10379285277426051984497863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13839047036568069312663817 10379285277426051984497863)
          ·
            refine ⟨15568927916139077976746795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10379285277426051984497863 15568927916139077976746795)
            ·
              refine ⟨23353391874208616965120193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15568927916139077976746795 23353391874208616965120193)
              ·
                refine ⟨17515043905656462723840145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23353391874208616965120193 17515043905656462723840145)
                ·
                  refine ⟨13136282929242347042880109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17515043905656462723840145 13136282929242347042880109)
                  ·
                    refine ⟨4926106098465880141080041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13136282929242347042880109 4926106098465880141080041)
                    ·
                      refine ⟨3694579573849410105810031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4926106098465880141080041 3694579573849410105810031)
                      ·
                        rfl

theorem cell23_7195168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7195168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195168 prefixEnd_7195168 := by exact prefixLift 7195168
  have htrace : WordTrace (prefixWord ++ tailWord_7195168) baseStart_7195168 baseEnd_7195168 := by
    simpa [prefixWord, tailWord_7195168, baseEnd_7195168] using wordTrace_append hprefix tailTrace_7195168
  have hstable : (prefixWord ++ tailWord_7195168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195168).length < 2 ^ (prefixWord ++ tailWord_7195168).sum := by decide
  have hdescent : baseEnd_7195168 < baseStart_7195168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195187 : List Nat := [1, 1, 1, 2, 4, 2, 4, 8]
def baseStart_7195187 : Nat := 118140960795 + 7195187 * 2 ^ 59
def prefixEnd_7195187 : Nat := 4983230072969 + 3 ^ 40 * 7195187 * 2
def baseEnd_7195187 : Nat := 136836641851179464128609

theorem tailTrace_7195187 : CollatzResearch.WordTrace tailWord_7195187 prefixEnd_7195187 136836641851179464128609 := by
  unfold tailWord_7195187
  simp only [CollatzResearch.WordTrace]
  refine ⟨262430029384073813951751815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174953352922715875967834543 262430029384073813951751815)
  ·
    refine ⟨393645044076110720927627723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262430029384073813951751815 393645044076110720927627723)
    ·
      refine ⟨590467566114166081391441585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393645044076110720927627723 590467566114166081391441585)
      ·
        refine ⟨442850674585624561043581189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590467566114166081391441585 442850674585624561043581189)
        ·
          refine ⟨83034501484804605195671473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442850674585624561043581189 83034501484804605195671473)
          ·
            refine ⟨62275876113603453896753605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83034501484804605195671473 62275876113603453896753605)
            ·
              refine ⟨11676726771300647605641301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62275876113603453896753605 11676726771300647605641301)
              ·
                refine ⟨136836641851179464128609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11676726771300647605641301 136836641851179464128609)
                ·
                  rfl

theorem cell23_7195187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 8].length) (baseStart_7195187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195187 prefixEnd_7195187 := by exact prefixLift 7195187
  have htrace : WordTrace (prefixWord ++ tailWord_7195187) baseStart_7195187 baseEnd_7195187 := by
    simpa [prefixWord, tailWord_7195187, baseEnd_7195187] using wordTrace_append hprefix tailTrace_7195187
  have hstable : (prefixWord ++ tailWord_7195187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195187).length < 2 ^ (prefixWord ++ tailWord_7195187).sum := by decide
  have hdescent : baseEnd_7195187 < baseStart_7195187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195198 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_7195198 : Nat := 118140960795 + 7195198 * 2 ^ 59
def prefixEnd_7195198 : Nat := 4983230072969 + 3 ^ 40 * 7195198 * 2
def baseEnd_7195198 : Nat := 3694594978269044988434893

theorem tailTrace_7195198 : CollatzResearch.WordTrace tailWord_7195198 prefixEnd_7195198 3694594978269044988434893 := by
  unfold tailWord_7195198
  simp only [CollatzResearch.WordTrace]
  refine ⟨32803803823379245353800281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174953620391355975220268165 32803803823379245353800281)
  ·
    refine ⟨24602852867534434015350211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32803803823379245353800281 24602852867534434015350211)
    ·
      refine ⟨36904279301301651023025317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24602852867534434015350211 36904279301301651023025317)
      ·
        refine ⟨6919552368994059566817247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36904279301301651023025317 6919552368994059566817247)
        ·
          refine ⟨10379328553491089350225871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6919552368994059566817247 10379328553491089350225871)
          ·
            refine ⟨15568992830236634025338807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10379328553491089350225871 15568992830236634025338807)
            ·
              refine ⟨23353489245354951038008211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15568992830236634025338807 23353489245354951038008211)
              ·
                refine ⟨35030233868032426557012317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23353489245354951038008211 35030233868032426557012317)
                ·
                  refine ⟨13136337700512159958879619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35030233868032426557012317 13136337700512159958879619)
                  ·
                    refine ⟨19704506550768239938319429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13136337700512159958879619 19704506550768239938319429)
                    ·
                      refine ⟨3694594978269044988434893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19704506550768239938319429 3694594978269044988434893)
                      ·
                        rfl

theorem cell23_7195198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_7195198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195198 prefixEnd_7195198 := by exact prefixLift 7195198
  have htrace : WordTrace (prefixWord ++ tailWord_7195198) baseStart_7195198 baseEnd_7195198 := by
    simpa [prefixWord, tailWord_7195198, baseEnd_7195198] using wordTrace_append hprefix tailTrace_7195198
  have hstable : (prefixWord ++ tailWord_7195198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195198).length < 2 ^ (prefixWord ++ tailWord_7195198).sum := by decide
  have hdescent : baseEnd_7195198 < baseStart_7195198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195201 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_7195201 : Nat := 118140960795 + 7195201 * 2 ^ 59
def prefixEnd_7195201 : Nat := 4983230072969 + 3 ^ 40 * 7195201 * 2
def baseEnd_7195201 : Nat := 3694596518711008476697379

theorem tailTrace_7195201 : CollatzResearch.WordTrace tailWord_7195201 prefixEnd_7195201 3694596518711008476697379 := by
  unfold tailWord_7195201
  simp only [CollatzResearch.WordTrace]
  refine ⟨262430540006023094342761457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174953693337348729561840971 262430540006023094342761457)
  ·
    refine ⟨196822905004517320757071093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262430540006023094342761457 196822905004517320757071093)
    ·
      refine ⟨18452147344173498820975415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196822905004517320757071093 18452147344173498820975415)
      ·
        refine ⟨27678221016260248231463123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18452147344173498820975415 27678221016260248231463123)
        ·
          refine ⟨41517331524390372347194685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27678221016260248231463123 41517331524390372347194685)
          ·
            refine ⟨15568999321646389630198007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41517331524390372347194685 15568999321646389630198007)
            ·
              refine ⟨23353498982469584445297011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15568999321646389630198007 23353498982469584445297011)
              ·
                refine ⟨35030248473704376667945517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23353498982469584445297011 35030248473704376667945517)
                ·
                  refine ⟨13136343177639141250479569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35030248473704376667945517 13136343177639141250479569)
                  ·
                    refine ⟨9852257383229355937859677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13136343177639141250479569 9852257383229355937859677)
                    ·
                      refine ⟨3694596518711008476697379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9852257383229355937859677 3694596518711008476697379)
                      ·
                        rfl

theorem cell23_7195201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_7195201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195201 prefixEnd_7195201 := by exact prefixLift 7195201
  have htrace : WordTrace (prefixWord ++ tailWord_7195201) baseStart_7195201 baseEnd_7195201 := by
    simpa [prefixWord, tailWord_7195201, baseEnd_7195201] using wordTrace_append hprefix tailTrace_7195201
  have hstable : (prefixWord ++ tailWord_7195201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195201).length < 2 ^ (prefixWord ++ tailWord_7195201).sum := by decide
  have hdescent : baseEnd_7195201 < baseStart_7195201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195214 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_7195214 : Nat := 118140960795 + 7195214 * 2 ^ 59
def prefixEnd_7195214 : Nat := 4983230072969 + 3 ^ 40 * 7195214 * 2
def baseEnd_7195214 : Nat := 3694603193959516925834819

theorem tailTrace_7195214 : CollatzResearch.WordTrace tailWord_7195214 prefixEnd_7195214 3694603193959516925834819 := by
  unfold tailWord_7195214
  simp only [CollatzResearch.WordTrace]
  refine ⟨32803876769371999695373087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174954009436650665041989797 32803876769371999695373087)
  ·
    refine ⟨49205815154057999543059631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32803876769371999695373087 49205815154057999543059631)
    ·
      refine ⟨73808722731086999314589447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49205815154057999543059631 73808722731086999314589447)
      ·
        refine ⟨110713084096630498971884171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73808722731086999314589447 110713084096630498971884171)
        ·
          refine ⟨166069626144945748457826257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110713084096630498971884171 166069626144945748457826257)
          ·
            refine ⟨124552219608709311343369693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166069626144945748457826257 124552219608709311343369693)
            ·
              refine ⟨46707082353265991753763635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124552219608709311343369693 46707082353265991753763635)
              ·
                refine ⟨70060623529898987630645453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46707082353265991753763635 70060623529898987630645453)
                ·
                  refine ⟨26272733823712120361492045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70060623529898987630645453 26272733823712120361492045)
                  ·
                    refine ⟨9852275183892045135559517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26272733823712120361492045 9852275183892045135559517)
                    ·
                      refine ⟨3694603193959516925834819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9852275183892045135559517 3694603193959516925834819)
                      ·
                        rfl

theorem cell23_7195214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_7195214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195214 prefixEnd_7195214 := by exact prefixLift 7195214
  have htrace : WordTrace (prefixWord ++ tailWord_7195214) baseStart_7195214 baseEnd_7195214 := by
    simpa [prefixWord, tailWord_7195214, baseEnd_7195214] using wordTrace_append hprefix tailTrace_7195214
  have hstable : (prefixWord ++ tailWord_7195214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195214).length < 2 ^ (prefixWord ++ tailWord_7195214).sum := by decide
  have hdescent : baseEnd_7195214 < baseStart_7195214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195218 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_7195218 : Nat := 118140960795 + 7195218 * 2 ^ 59
def prefixEnd_7195218 : Nat := 4983230072969 + 3 ^ 40 * 7195218 * 2
def baseEnd_7195218 : Nat := 3694605247882134910184801

theorem tailTrace_7195218 : CollatzResearch.WordTrace tailWord_7195218 prefixEnd_7195218 3694605247882134910184801 := by
  unfold tailWord_7195218
  simp only [CollatzResearch.WordTrace]
  refine ⟨65607790011740376561532577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174954106697974337497420205 65607790011740376561532577)
  ·
    refine ⟨49205842508805282421149433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65607790011740376561532577 49205842508805282421149433)
    ·
      refine ⟨36904381881603961815862075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49205842508805282421149433 36904381881603961815862075)
      ·
        refine ⟨55356572822405942723793113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36904381881603961815862075 55356572822405942723793113)
        ·
          refine ⟨41517429616804457042844835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55356572822405942723793113 41517429616804457042844835)
          ·
            refine ⟨62276144425206685564267253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41517429616804457042844835 62276144425206685564267253)
            ·
              refine ⟨5838388539863126771650055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62276144425206685564267253 5838388539863126771650055)
              ·
                refine ⟨8757582809794690157475083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5838388539863126771650055 8757582809794690157475083)
                ·
                  refine ⟨13136374214692035236212625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8757582809794690157475083 13136374214692035236212625)
                  ·
                    refine ⟨9852280661019026427159469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13136374214692035236212625 9852280661019026427159469)
                    ·
                      refine ⟨3694605247882134910184801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9852280661019026427159469 3694605247882134910184801)
                      ·
                        rfl

theorem cell23_7195218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_7195218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195218 prefixEnd_7195218 := by exact prefixLift 7195218
  have htrace : WordTrace (prefixWord ++ tailWord_7195218) baseStart_7195218 baseEnd_7195218 := by
    simpa [prefixWord, tailWord_7195218, baseEnd_7195218] using wordTrace_append hprefix tailTrace_7195218
  have hstable : (prefixWord ++ tailWord_7195218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195218).length < 2 ^ (prefixWord ++ tailWord_7195218).sum := by decide
  have hdescent : baseEnd_7195218 < baseStart_7195218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195247 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 1, 8]
def baseStart_7195247 : Nat := 118140960795 + 7195247 * 2 ^ 59
def prefixEnd_7195247 : Nat := 4983230072969 + 3 ^ 40 * 7195247 * 2
def baseEnd_7195247 : Nat := 1231540046273705098907389

theorem tailTrace_7195247 : CollatzResearch.WordTrace tailWord_7195247 prefixEnd_7195247 1231540046273705098907389 := by
  unfold tailWord_7195247
  simp only [CollatzResearch.WordTrace]
  refine ⟨262432217763856444198935995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174954811842570962799290663 262432217763856444198935995)
  ·
    refine ⟨393648326645784666298403993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262432217763856444198935995 393648326645784666298403993)
    ·
      refine ⟨295236244984338499723802995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393648326645784666298403993 295236244984338499723802995)
      ·
        refine ⟨442854367476507749585704493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295236244984338499723802995 442854367476507749585704493)
        ·
          refine ⟨166070387803690406094639185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442854367476507749585704493 166070387803690406094639185)
          ·
            refine ⟨124552790852767804570979389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166070387803690406094639185 124552790852767804570979389)
            ·
              refine ⟨46707296569787926714117271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124552790852767804570979389 46707296569787926714117271)
              ·
                refine ⟨70060944854681890071175907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46707296569787926714117271 70060944854681890071175907)
                ·
                  refine ⟨105091417282022835106763861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70060944854681890071175907 105091417282022835106763861)
                  ·
                    refine ⟨1231540046273705098907389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105091417282022835106763861 1231540046273705098907389)
                    ·
                      rfl

theorem cell23_7195247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_7195247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195247 prefixEnd_7195247 := by exact prefixLift 7195247
  have htrace : WordTrace (prefixWord ++ tailWord_7195247) baseStart_7195247 baseEnd_7195247 := by
    simpa [prefixWord, tailWord_7195247, baseEnd_7195247] using wordTrace_append hprefix tailTrace_7195247
  have hstable : (prefixWord ++ tailWord_7195247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195247).length < 2 ^ (prefixWord ++ tailWord_7195247).sum := by decide
  have hdescent : baseEnd_7195247 < baseStart_7195247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195266 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7195266 : Nat := 118140960795 + 7195266 * 2 ^ 59
def prefixEnd_7195266 : Nat := 4983230072969 + 3 ^ 40 * 7195266 * 2
def baseEnd_7195266 : Nat := 3694629894953550722384581

theorem tailTrace_7195266 : CollatzResearch.WordTrace tailWord_7195266 prefixEnd_7195266 3694629894953550722384581 := by
  unfold tailWord_7195266
  simp only [CollatzResearch.WordTrace]
  refine ⟨65608227687696902610969413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174955273833858406962585101 65608227687696902610969413)
  ·
    refine ⟨12301542691443169239556765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65608227687696902610969413 12301542691443169239556765)
    ·
      refine ⟨4613078509291188464833787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12301542691443169239556765 4613078509291188464833787)
      ·
        refine ⟨6919617763936782697250681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613078509291188464833787 6919617763936782697250681)
        ·
          refine ⟨5189713322952587022938011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6919617763936782697250681 5189713322952587022938011)
          ·
            refine ⟨7784569984428880534407017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5189713322952587022938011 7784569984428880534407017)
            ·
              refine ⟨5838427488321660400805263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7784569984428880534407017 5838427488321660400805263)
              ·
                refine ⟨8757641232482490601207895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5838427488321660400805263 8757641232482490601207895)
                ·
                  refine ⟨13136461848723735901811843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8757641232482490601207895 13136461848723735901811843)
                  ·
                    refine ⟨19704692773085603852717765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13136461848723735901811843 19704692773085603852717765)
                    ·
                      refine ⟨3694629894953550722384581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19704692773085603852717765 3694629894953550722384581)
                      ·
                        rfl

theorem cell23_7195266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7195266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195266 prefixEnd_7195266 := by exact prefixLift 7195266
  have htrace : WordTrace (prefixWord ++ tailWord_7195266) baseStart_7195266 baseEnd_7195266 := by
    simpa [prefixWord, tailWord_7195266, baseEnd_7195266] using wordTrace_append hprefix tailTrace_7195266
  have hstable : (prefixWord ++ tailWord_7195266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195266).length < 2 ^ (prefixWord ++ tailWord_7195266).sum := by decide
  have hdescent : baseEnd_7195266 < baseStart_7195266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195271 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 1, 4, 2]
def baseStart_7195271 : Nat := 118140960795 + 7195271 * 2 ^ 59
def prefixEnd_7195271 : Nat := 4983230072969 + 3 ^ 40 * 7195271 * 2
def baseEnd_7195271 : Nat := 3694632462356823202822057

theorem tailTrace_7195271 : CollatzResearch.WordTrace tailWord_7195271 prefixEnd_7195271 3694632462356823202822057 := by
  unfold tailWord_7195271
  simp only [CollatzResearch.WordTrace]
  refine ⟨262433093115769496297809667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174955395410512997531873111 262433093115769496297809667)
  ·
    refine ⟨393649639673654244446714501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262433093115769496297809667 393649639673654244446714501)
    ·
      refine ⟨73809307438810170833758969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393649639673654244446714501 73809307438810170833758969)
      ·
        refine ⟨55356980579107628125319227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73809307438810170833758969 55356980579107628125319227)
        ·
          refine ⟨83035470868661442187978841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55356980579107628125319227 83035470868661442187978841)
          ·
            refine ⟨62276603151496081640984131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83035470868661442187978841 62276603151496081640984131)
            ·
              refine ⟨93414904727244122461476197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62276603151496081640984131 93414904727244122461476197)
              ·
                refine ⟨17515294636358272961526787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93414904727244122461476197 17515294636358272961526787)
                ·
                  refine ⟨26272941954537409442290181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17515294636358272961526787 26272941954537409442290181)
                  ·
                    refine ⟨4926176616475764270429409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26272941954537409442290181 4926176616475764270429409)
                    ·
                      refine ⟨3694632462356823202822057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4926176616475764270429409 3694632462356823202822057)
                      ·
                        rfl

theorem cell23_7195271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_7195271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195271 prefixEnd_7195271 := by exact prefixLift 7195271
  have htrace : WordTrace (prefixWord ++ tailWord_7195271) baseStart_7195271 baseEnd_7195271 := by
    simpa [prefixWord, tailWord_7195271, baseEnd_7195271] using wordTrace_append hprefix tailTrace_7195271
  have hstable : (prefixWord ++ tailWord_7195271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195271).length < 2 ^ (prefixWord ++ tailWord_7195271).sum := by decide
  have hdescent : baseEnd_7195271 < baseStart_7195271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195288 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 4, 2, 2]
def baseStart_7195288 : Nat := 118140960795 + 7195288 * 2 ^ 59
def prefixEnd_7195288 : Nat := 4983230072969 + 3 ^ 40 * 7195288 * 2
def baseEnd_7195288 : Nat := 3694641191527949636309479

theorem tailTrace_7195288 : CollatzResearch.WordTrace tailWord_7195288 prefixEnd_7195288 3694641191527949636309479 := by
  unfold tailWord_7195288
  simp only [CollatzResearch.WordTrace]
  refine ⟨131216856578353954100589259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174955808771138605467452345 131216856578353954100589259)
  ·
    refine ⟨196825284867530931150883889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131216856578353954100589259 196825284867530931150883889)
    ·
      refine ⟨147618963650648198363162917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196825284867530931150883889 147618963650648198363162917)
      ·
        refine ⟨27678555684496537193093047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147618963650648198363162917 27678555684496537193093047)
        ·
          refine ⟨41517833526744805789639571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27678555684496537193093047 41517833526744805789639571)
          ·
            refine ⟨62276750290117208684459357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41517833526744805789639571 62276750290117208684459357)
            ·
              refine ⟨23353781358793953256672259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62276750290117208684459357 23353781358793953256672259)
              ·
                refine ⟨35030672038190929885008389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23353781358793953256672259 35030672038190929885008389)
                ·
                  refine ⟨6568251007160799353439073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35030672038190929885008389 6568251007160799353439073)
                  ·
                    refine ⟨4926188255370599515079305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6568251007160799353439073 4926188255370599515079305)
                    ·
                      refine ⟨3694641191527949636309479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4926188255370599515079305 3694641191527949636309479)
                      ·
                        rfl

theorem cell23_7195288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_7195288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195288 prefixEnd_7195288 := by exact prefixLift 7195288
  have htrace : WordTrace (prefixWord ++ tailWord_7195288) baseStart_7195288 baseEnd_7195288 := by
    simpa [prefixWord, tailWord_7195288, baseEnd_7195288] using wordTrace_append hprefix tailTrace_7195288
  have hstable : (prefixWord ++ tailWord_7195288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195288).length < 2 ^ (prefixWord ++ tailWord_7195288).sum := by decide
  have hdescent : baseEnd_7195288 < baseStart_7195288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195324 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_7195324 : Nat := 118140960795 + 7195324 * 2 ^ 59
def prefixEnd_7195324 : Nat := 4983230072969 + 3 ^ 40 * 7195324 * 2
def baseEnd_7195324 : Nat := 1231553225610503831819771

theorem tailTrace_7195324 : CollatzResearch.WordTrace tailWord_7195324 prefixEnd_7195324 1231553225610503831819771 := by
  unfold tailWord_7195324
  simp only [CollatzResearch.WordTrace]
  refine ⟨131217513092288743174744513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174956684123051657566326017 131217513092288743174744513)
  ·
    refine ⟨98413134819216557381058385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131217513092288743174744513 98413134819216557381058385)
    ·
      refine ⟨73809851114412418035793789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98413134819216557381058385 73809851114412418035793789)
      ·
        refine ⟨27678694167904656763422671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73809851114412418035793789 27678694167904656763422671)
        ·
          refine ⟨41518041251856985145134007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27678694167904656763422671 41518041251856985145134007)
          ·
            refine ⟨62277061877785477717701011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41518041251856985145134007 62277061877785477717701011)
            ·
              refine ⟨93415592816678216576551517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62277061877785477717701011 93415592816678216576551517)
              ·
                refine ⟨35030847306254331216206819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93415592816678216576551517 35030847306254331216206819)
                ·
                  refine ⟨52546270959381496824310229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35030847306254331216206819 52546270959381496824310229)
                  ·
                    refine ⟨1231553225610503831819771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52546270959381496824310229 1231553225610503831819771)
                    ·
                      rfl

theorem cell23_7195324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_7195324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195324 prefixEnd_7195324 := by exact prefixLift 7195324
  have htrace : WordTrace (prefixWord ++ tailWord_7195324) baseStart_7195324 baseEnd_7195324 := by
    simpa [prefixWord, tailWord_7195324, baseEnd_7195324] using wordTrace_append hprefix tailTrace_7195324
  have hstable : (prefixWord ++ tailWord_7195324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195324).length < 2 ^ (prefixWord ++ tailWord_7195324).sum := by decide
  have hdescent : baseEnd_7195324 < baseStart_7195324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195328 : List Nat := [2, 1, 1, 2, 4, 4, 1, 3, 5]
def baseStart_7195328 : Nat := 118140960795 + 7195328 * 2 ^ 59
def prefixEnd_7195328 : Nat := 4983230072969 + 3 ^ 40 * 7195328 * 2
def baseEnd_7195328 : Nat := 410517970083792164423255

theorem tailTrace_7195328 : CollatzResearch.WordTrace tailWord_7195328 prefixEnd_7195328 410517970083792164423255 := by
  unfold tailWord_7195328
  simp only [CollatzResearch.WordTrace]
  refine ⟨131217586038281497516317319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174956781384375330021756425 131217586038281497516317319)
  ·
    refine ⟨196826379057422246274475979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131217586038281497516317319 196826379057422246274475979)
    ·
      refine ⟨295239568586133369411713969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196826379057422246274475979 295239568586133369411713969)
      ·
        refine ⟨221429676439600027058785477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295239568586133369411713969 221429676439600027058785477)
        ·
          refine ⟨41518064332425005073522277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221429676439600027058785477 41518064332425005073522277)
          ·
            refine ⟨7784637062329688451285427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41518064332425005073522277 7784637062329688451285427)
            ·
              refine ⟨11676955593494532676928141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7784637062329688451285427 11676955593494532676928141)
              ·
                refine ⟨4378858347560449753848053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11676955593494532676928141 4378858347560449753848053)
                ·
                  refine ⟨410517970083792164423255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4378858347560449753848053 410517970083792164423255)
                  ·
                    rfl

theorem cell23_7195328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 5].length) (baseStart_7195328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195328 prefixEnd_7195328 := by exact prefixLift 7195328
  have htrace : WordTrace (prefixWord ++ tailWord_7195328) baseStart_7195328 baseEnd_7195328 := by
    simpa [prefixWord, tailWord_7195328, baseEnd_7195328] using wordTrace_append hprefix tailTrace_7195328
  have hstable : (prefixWord ++ tailWord_7195328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195328).length < 2 ^ (prefixWord ++ tailWord_7195328).sum := by decide
  have hdescent : baseEnd_7195328 < baseStart_7195328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195378 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_7195378 : Nat := 118140960795 + 7195378 * 2 ^ 59
def prefixEnd_7195378 : Nat := 4983230072969 + 3 ^ 40 * 7195378 * 2
def baseEnd_7195378 : Nat := 3694687404786854284184065

theorem tailTrace_7195378 : CollatzResearch.WordTrace tailWord_7195378 prefixEnd_7195378 3694687404786854284184065 := by
  unfold tailWord_7195378
  simp only [CollatzResearch.WordTrace]
  refine ⟨65609248931595463392988697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174957997150921235714636525 65609248931595463392988697)
  ·
    refine ⟨49206936698696597544741523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65609248931595463392988697 49206936698696597544741523)
    ·
      refine ⟨73810405048044896317112285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49206936698696597544741523 73810405048044896317112285)
      ·
        refine ⟨27678901893016836118917107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73810405048044896317112285 27678901893016836118917107)
        ·
          refine ⟨41518352839525254178375661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27678901893016836118917107 41518352839525254178375661)
          ·
            refine ⟨15569382314821970316890873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41518352839525254178375661 15569382314821970316890873)
            ·
              refine ⟨11677036736116477737668155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15569382314821970316890873 11677036736116477737668155)
              ·
                refine ⟨17515555104174716606502233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11677036736116477737668155 17515555104174716606502233)
                ·
                  refine ⟨13136666328131037454876675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17515555104174716606502233 13136666328131037454876675)
                  ·
                    refine ⟨19704999492196556182315013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13136666328131037454876675 19704999492196556182315013)
                    ·
                      refine ⟨3694687404786854284184065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19704999492196556182315013 3694687404786854284184065)
                      ·
                        rfl

theorem cell23_7195378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_7195378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195378 prefixEnd_7195378 := by exact prefixLift 7195378
  have htrace : WordTrace (prefixWord ++ tailWord_7195378) baseStart_7195378 baseEnd_7195378 := by
    simpa [prefixWord, tailWord_7195378, baseEnd_7195378] using wordTrace_append hprefix tailTrace_7195378
  have hstable : (prefixWord ++ tailWord_7195378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195378).length < 2 ^ (prefixWord ++ tailWord_7195378).sum := by decide
  have hdescent : baseEnd_7195378 < baseStart_7195378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195404 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_7195404 : Nat := 118140960795 + 7195404 * 2 ^ 59
def prefixEnd_7195404 : Nat := 4983230072969 + 3 ^ 40 * 7195404 * 2
def baseEnd_7195404 : Nat := 3694700755283871182458945

theorem tailTrace_7195404 : CollatzResearch.WordTrace tailWord_7195404 prefixEnd_7195404 3694700755283871182458945 := by
  unfold tailWord_7195404
  simp only [CollatzResearch.WordTrace]
  refine ⟨131218972012143830006200633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174958629349525106674934177 131218972012143830006200633)
  ·
    refine ⟨98414229009107872504650475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131218972012143830006200633 98414229009107872504650475)
    ·
      refine ⟨147621343513661808756975713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98414229009107872504650475 147621343513661808756975713)
      ·
        refine ⟨110716007635246356567731785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147621343513661808756975713 110716007635246356567731785)
        ·
          refine ⟨83037005726434767425798839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110716007635246356567731785 83037005726434767425798839)
          ·
            refine ⟨124555508589652151138698259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83037005726434767425798839 124555508589652151138698259)
            ·
              refine ⟨186833262884478226708047389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124555508589652151138698259 186833262884478226708047389)
              ·
                refine ⟨70062473581679335015517771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186833262884478226708047389 70062473581679335015517771)
                ·
                  refine ⟨105093710372519002523276657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70062473581679335015517771 105093710372519002523276657)
                  ·
                    refine ⟨78820282779389251892457493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105093710372519002523276657 78820282779389251892457493)
                    ·
                      refine ⟨3694700755283871182458945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78820282779389251892457493 3694700755283871182458945)
                      ·
                        rfl

theorem cell23_7195404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_7195404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195404 prefixEnd_7195404 := by exact prefixLift 7195404
  have htrace : WordTrace (prefixWord ++ tailWord_7195404) baseStart_7195404 baseEnd_7195404 := by
    simpa [prefixWord, tailWord_7195404, baseEnd_7195404] using wordTrace_append hprefix tailTrace_7195404
  have hstable : (prefixWord ++ tailWord_7195404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195404).length < 2 ^ (prefixWord ++ tailWord_7195404).sum := by decide
  have hdescent : baseEnd_7195404 < baseStart_7195404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195481 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 6]
def baseStart_7195481 : Nat := 118140960795 + 7195481 * 2 ^ 59
def prefixEnd_7195481 : Nat := 4983230072969 + 3 ^ 40 * 7195481 * 2
def baseEnd_7195481 : Nat := 3694740293294267381196091

theorem tailTrace_7195481 : CollatzResearch.WordTrace tailWord_7195481 prefixEnd_7195481 3694740293294267381196091 := by
  unfold tailWord_7195481
  simp only [CollatzResearch.WordTrace]
  refine ⟨262440752445008702162954297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174960501630005801441969531 262440752445008702162954297)
  ·
    refine ⟨196830564333756526622215723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262440752445008702162954297 196830564333756526622215723)
    ·
      refine ⟨295245846500634789933323585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196830564333756526622215723 295245846500634789933323585)
      ·
        refine ⟨221434384875476092449992689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295245846500634789933323585 221434384875476092449992689)
        ·
          refine ⟨166075788656607069337494517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221434384875476092449992689 166075788656607069337494517)
          ·
            refine ⟨15569605186556912750390111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166075788656607069337494517 15569605186556912750390111)
            ·
              refine ⟨23354407779835369125585167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15569605186556912750390111 23354407779835369125585167)
              ·
                refine ⟨35031611669753053688377751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23354407779835369125585167 35031611669753053688377751)
                ·
                  refine ⟨52547417504629580532566627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35031611669753053688377751 52547417504629580532566627)
                  ·
                    refine ⟨78821126256944370798849941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52547417504629580532566627 78821126256944370798849941)
                    ·
                      refine ⟨3694740293294267381196091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78821126256944370798849941 3694740293294267381196091)
                      ·
                        rfl

theorem cell23_7195481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_7195481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195481 prefixEnd_7195481 := by exact prefixLift 7195481
  have htrace : WordTrace (prefixWord ++ tailWord_7195481) baseStart_7195481 baseEnd_7195481 := by
    simpa [prefixWord, tailWord_7195481, baseEnd_7195481] using wordTrace_append hprefix tailTrace_7195481
  have hstable : (prefixWord ++ tailWord_7195481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195481).length < 2 ^ (prefixWord ++ tailWord_7195481).sum := by decide
  have hdescent : baseEnd_7195481 < baseStart_7195481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195491 : List Nat := [1, 1, 1, 5, 3, 2, 1, 9]
def baseStart_7195491 : Nat := 118140960795 + 7195491 * 2 ^ 59
def prefixEnd_7195491 : Nat := 4983230072969 + 3 ^ 40 * 7195491 * 2
def baseEnd_7195491 : Nat := 136842423262993049706335

theorem tailTrace_7195491 : CollatzResearch.WordTrace tailWord_7195491 prefixEnd_7195491 136842423262993049706335 := by
  unfold tailWord_7195491
  simp only [CollatzResearch.WordTrace]
  refine ⟨262441117174972473870818327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174960744783314982580545551 262441117174972473870818327)
  ·
    refine ⟨393661675762458710806227491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262441117174972473870818327 393661675762458710806227491)
    ·
      refine ⟨590492513643688066209341237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393661675762458710806227491 590492513643688066209341237)
      ·
        refine ⟨55358673154095756207125741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 590492513643688066209341237 55358673154095756207125741)
        ·
          refine ⟨20759502432785908577672153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55358673154095756207125741 20759502432785908577672153)
          ·
            refine ⟨15569626824589431433254115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20759502432785908577672153 15569626824589431433254115)
            ·
              refine ⟨23354440236884147149881173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15569626824589431433254115 23354440236884147149881173)
              ·
                refine ⟨136842423262993049706335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23354440236884147149881173 136842423262993049706335)
                ·
                  rfl

theorem cell23_7195491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 9].length) (baseStart_7195491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195491 prefixEnd_7195491 := by exact prefixLift 7195491
  have htrace : WordTrace (prefixWord ++ tailWord_7195491) baseStart_7195491 baseEnd_7195491 := by
    simpa [prefixWord, tailWord_7195491, baseEnd_7195491] using wordTrace_append hprefix tailTrace_7195491
  have hstable : (prefixWord ++ tailWord_7195491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195491).length < 2 ^ (prefixWord ++ tailWord_7195491).sum := by decide
  have hdescent : baseEnd_7195491 < baseStart_7195491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195561 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 5]
def baseStart_7195561 : Nat := 118140960795 + 7195561 * 2 ^ 59
def prefixEnd_7195561 : Nat := 4983230072969 + 3 ^ 40 * 7195561 * 2
def baseEnd_7195561 : Nat := 3694781371746627068195723

theorem tailTrace_7195561 : CollatzResearch.WordTrace tailWord_7195561 prefixEnd_7195561 3694781371746627068195723 := by
  unfold tailWord_7195561
  simp only [CollatzResearch.WordTrace]
  refine ⟨262443670284718875825866537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174962446856479250550577691 262443670284718875825866537)
  ·
    refine ⟨196832752713539156869399903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262443670284718875825866537 196832752713539156869399903)
    ·
      refine ⟨295249129070308735304099855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196832752713539156869399903 295249129070308735304099855)
      ·
        refine ⟨442873693605463102956149783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295249129070308735304099855 442873693605463102956149783)
        ·
          refine ⟨664310540408194654434224675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442873693605463102956149783 664310540408194654434224675)
          ·
            refine ⟨996465810612291981651337013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664310540408194654434224675 996465810612291981651337013)
            ·
              refine ⟨93418669744902373279812845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 996465810612291981651337013 93418669744902373279812845)
              ·
                refine ⟨35032001154338389979929817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93418669744902373279812845 35032001154338389979929817)
                ·
                  refine ⟨26274000865753792484947363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35032001154338389979929817 26274000865753792484947363)
                  ·
                    refine ⟨39411001298630688727421045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26274000865753792484947363 39411001298630688727421045)
                    ·
                      refine ⟨3694781371746627068195723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39411001298630688727421045 3694781371746627068195723)
                      ·
                        rfl

theorem cell23_7195561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_7195561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195561 prefixEnd_7195561 := by exact prefixLift 7195561
  have htrace : WordTrace (prefixWord ++ tailWord_7195561) baseStart_7195561 baseEnd_7195561 := by
    simpa [prefixWord, tailWord_7195561, baseEnd_7195561] using wordTrace_append hprefix tailTrace_7195561
  have hstable : (prefixWord ++ tailWord_7195561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195561).length < 2 ^ (prefixWord ++ tailWord_7195561).sum := by decide
  have hdescent : baseEnd_7195561 < baseStart_7195561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195575 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 4, 2, 2]
def baseStart_7195575 : Nat := 118140960795 + 7195575 * 2 ^ 59
def prefixEnd_7195575 : Nat := 4983230072969 + 3 ^ 40 * 7195575 * 2
def baseEnd_7195575 : Nat := 3694788560475790013420659

theorem tailTrace_7195575 : CollatzResearch.WordTrace tailWord_7195575 prefixEnd_7195575 3694788560475790013420659 := by
  unfold tailWord_7195575
  simp only [CollatzResearch.WordTrace]
  refine ⟨262444180906668156216876179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174962787271112104144584119 262444180906668156216876179)
  ·
    refine ⟨393666271360002234325314269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262444180906668156216876179 393666271360002234325314269)
    ·
      refine ⟨147624851760000837871992851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393666271360002234325314269 147624851760000837871992851)
      ·
        refine ⟨221437277640001256807989277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147624851760000837871992851 221437277640001256807989277)
        ·
          refine ⟨83038979115000471302995979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221437277640001256807989277 83038979115000471302995979)
          ·
            refine ⟨124558468672500706954493969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83038979115000471302995979 124558468672500706954493969)
            ·
              refine ⟨93418851504375530215870477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124558468672500706954493969 93418851504375530215870477)
              ·
                refine ⟨35032069314140823830951429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93418851504375530215870477 35032069314140823830951429)
                ·
                  refine ⟨6568512996401404468303393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35032069314140823830951429 6568512996401404468303393)
                  ·
                    refine ⟨4926384747301053351227545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6568512996401404468303393 4926384747301053351227545)
                    ·
                      refine ⟨3694788560475790013420659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4926384747301053351227545 3694788560475790013420659)
                      ·
                        rfl

theorem cell23_7195575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 2, 2].length) (baseStart_7195575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195575 prefixEnd_7195575 := by exact prefixLift 7195575
  have htrace : WordTrace (prefixWord ++ tailWord_7195575) baseStart_7195575 baseEnd_7195575 := by
    simpa [prefixWord, tailWord_7195575, baseEnd_7195575] using wordTrace_append hprefix tailTrace_7195575
  have hstable : (prefixWord ++ tailWord_7195575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195575).length < 2 ^ (prefixWord ++ tailWord_7195575).sum := by decide
  have hdescent : baseEnd_7195575 < baseStart_7195575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195592 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 1, 4, 2]
def baseStart_7195592 : Nat := 118140960795 + 7195592 * 2 ^ 59
def prefixEnd_7195592 : Nat := 4983230072969 + 3 ^ 40 * 7195592 * 2
def baseEnd_7195592 : Nat := 3694797289646916446908081

theorem tailTrace_7195592 : CollatzResearch.WordTrace tailWord_7195592 prefixEnd_7195592 3694797289646916446908081 := by
  unfold tailWord_7195592
  simp only [CollatzResearch.WordTrace]
  refine ⟨131222400473803284060122515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174963200631737712080163353 131222400473803284060122515)
  ·
    refine ⟨196833600710704926090183773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131222400473803284060122515 196833600710704926090183773)
    ·
      refine ⟨73812600266514347283818915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196833600710704926090183773 73812600266514347283818915)
      ·
        refine ⟨110718900399771520925728373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73812600266514347283818915 110718900399771520925728373)
        ·
          refine ⟨10379896912478580086787035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110718900399771520925728373 10379896912478580086787035)
          ·
            refine ⟨15569845368717870130180553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10379896912478580086787035 15569845368717870130180553)
            ·
              refine ⟨11677384026538402597635415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15569845368717870130180553 11677384026538402597635415)
              ·
                refine ⟨17516076039807603896453123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11677384026538402597635415 17516076039807603896453123)
                ·
                  refine ⟨26274114059711405844679685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17516076039807603896453123 26274114059711405844679685)
                  ·
                    refine ⟨4926396386195888595877441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26274114059711405844679685 4926396386195888595877441)
                    ·
                      refine ⟨3694797289646916446908081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4926396386195888595877441 3694797289646916446908081)
                      ·
                        rfl

theorem cell23_7195592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_7195592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195592 prefixEnd_7195592 := by exact prefixLift 7195592
  have htrace : WordTrace (prefixWord ++ tailWord_7195592) baseStart_7195592 baseEnd_7195592 := by
    simpa [prefixWord, tailWord_7195592, baseEnd_7195592] using wordTrace_append hprefix tailTrace_7195592
  have hstable : (prefixWord ++ tailWord_7195592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195592).length < 2 ^ (prefixWord ++ tailWord_7195592).sum := by decide
  have hdescent : baseEnd_7195592 < baseStart_7195592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195598 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_7195598 : Nat := 118140960795 + 7195598 * 2 ^ 59
def prefixEnd_7195598 : Nat := 4983230072969 + 3 ^ 40 * 7195598 * 2
def baseEnd_7195598 : Nat := 410533374503427047048117

theorem tailTrace_7195598 : CollatzResearch.WordTrace tailWord_7195598 prefixEnd_7195598 410533374503427047048117 := by
  unfold tailWord_7195598
  simp only [CollatzResearch.WordTrace]
  refine ⟨32805627473198103893120431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174963346523723220763308965 32805627473198103893120431)
  ·
    refine ⟨49208441209797155839680647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32805627473198103893120431 49208441209797155839680647)
    ·
      refine ⟨73812661814695733759520971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49208441209797155839680647 73812661814695733759520971)
      ·
        refine ⟨110718992722043600639281457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73812661814695733759520971 110718992722043600639281457)
        ·
          refine ⟨83039244541532700479461093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110718992722043600639281457 83039244541532700479461093)
          ·
            refine ⟨15569858351537381339898955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83039244541532700479461093 15569858351537381339898955)
            ·
              refine ⟨23354787527306072009848433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15569858351537381339898955 23354787527306072009848433)
              ·
                refine ⟨17516090645479554007386325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23354787527306072009848433 17516090645479554007386325)
                ·
                  refine ⟨410533374503427047048117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17516090645479554007386325 410533374503427047048117)
                  ·
                    rfl

theorem cell23_7195598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_7195598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195598 prefixEnd_7195598 := by exact prefixLift 7195598
  have htrace : WordTrace (prefixWord ++ tailWord_7195598) baseStart_7195598 baseEnd_7195598 := by
    simpa [prefixWord, tailWord_7195598, baseEnd_7195598] using wordTrace_append hprefix tailTrace_7195598
  have hstable : (prefixWord ++ tailWord_7195598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195598).length < 2 ^ (prefixWord ++ tailWord_7195598).sum := by decide
  have hdescent : baseEnd_7195598 < baseStart_7195598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195685 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 2, 2, 3]
def baseStart_7195685 : Nat := 118140960795 + 7195685 * 2 ^ 59
def prefixEnd_7195685 : Nat := 4983230072969 + 3 ^ 40 * 7195685 * 2
def baseEnd_7195685 : Nat := 3694845043347784583045153

theorem tailTrace_7195685 : CollatzResearch.WordTrace tailWord_7195685 prefixEnd_7195685 3694845043347784583045153 := by
  unfold tailWord_7195685
  simp only [CollatzResearch.WordTrace]
  refine ⟨262448192936269645003380509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174965461957513096668920339 262448192936269645003380509)
  ·
    refine ⟨98418072351101116876267691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262448192936269645003380509 98418072351101116876267691)
    ·
      refine ⟨147627108526651675314401537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98418072351101116876267691 147627108526651675314401537)
      ·
        refine ⟨110720331394988756485801153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147627108526651675314401537 110720331394988756485801153)
        ·
          refine ⟨83040248546241567364350865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110720331394988756485801153 83040248546241567364350865)
          ·
            refine ⟨62280186409681175523263149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83040248546241567364350865 62280186409681175523263149)
            ·
              refine ⟨23355069903630440821223681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62280186409681175523263149 23355069903630440821223681)
              ·
                refine ⟨17516302427722830615917761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23355069903630440821223681 17516302427722830615917761)
                ·
                  refine ⟨13137226820792122961938321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17516302427722830615917761 13137226820792122961938321)
                  ·
                    refine ⟨9852920115594092221453741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13137226820792122961938321 9852920115594092221453741)
                    ·
                      refine ⟨3694845043347784583045153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9852920115594092221453741 3694845043347784583045153)
                      ·
                        rfl

theorem cell23_7195685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_7195685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195685 prefixEnd_7195685 := by exact prefixLift 7195685
  have htrace : WordTrace (prefixWord ++ tailWord_7195685) baseStart_7195685 baseEnd_7195685 := by
    simpa [prefixWord, tailWord_7195685, baseEnd_7195685] using wordTrace_append hprefix tailTrace_7195685
  have hstable : (prefixWord ++ tailWord_7195685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195685).length < 2 ^ (prefixWord ++ tailWord_7195685).sum := by decide
  have hdescent : baseEnd_7195685 < baseStart_7195685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195705 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 6]
def baseStart_7195705 : Nat := 118140960795 + 7195705 * 2 ^ 59
def prefixEnd_7195705 : Nat := 4983230072969 + 3 ^ 40 * 7195705 * 2
def baseEnd_7195705 : Nat := 410539479217874944977229

theorem tailTrace_7195705 : CollatzResearch.WordTrace tailWord_7195705 prefixEnd_7195705 410539479217874944977229 := by
  unfold tailWord_7195705
  simp only [CollatzResearch.WordTrace]
  refine ⟨262448922396197188419108569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174965948264131458946072379 262448922396197188419108569)
  ·
    refine ⟨196836691797147891314331427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262448922396197188419108569 196836691797147891314331427)
    ·
      refine ⟨295255037695721836971497141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196836691797147891314331427 295255037695721836971497141)
      ·
        refine ⟨27680159783973922216077857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295255037695721836971497141 27680159783973922216077857)
        ·
          refine ⟨20760119837980441662058393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27680159783973922216077857 20760119837980441662058393)
          ·
            refine ⟨15570089878485331246543795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20760119837980441662058393 15570089878485331246543795)
            ·
              refine ⟨23355134817727996869815693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15570089878485331246543795 23355134817727996869815693)
              ·
                refine ⟨8758175556647998826180885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23355134817727996869815693 8758175556647998826180885)
                ·
                  refine ⟨410539479217874944977229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8758175556647998826180885 410539479217874944977229)
                  ·
                    rfl

theorem cell23_7195705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 6].length) (baseStart_7195705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195705 prefixEnd_7195705 := by exact prefixLift 7195705
  have htrace : WordTrace (prefixWord ++ tailWord_7195705) baseStart_7195705 baseEnd_7195705 := by
    simpa [prefixWord, tailWord_7195705, baseEnd_7195705] using wordTrace_append hprefix tailTrace_7195705
  have hstable : (prefixWord ++ tailWord_7195705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195705).length < 2 ^ (prefixWord ++ tailWord_7195705).sum := by decide
  have hdescent : baseEnd_7195705 < baseStart_7195705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195715 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 5, 1, 3]
def baseStart_7195715 : Nat := 118140960795 + 7195715 * 2 ^ 59
def prefixEnd_7195715 : Nat := 4983230072969 + 3 ^ 40 * 7195715 * 2
def baseEnd_7195715 : Nat := 3694860447767419465670015

theorem tailTrace_7195715 : CollatzResearch.WordTrace tailWord_7195715 prefixEnd_7195715 3694860447767419465670015 := by
  unfold tailWord_7195715
  simp only [CollatzResearch.WordTrace]
  refine ⟨262449287126160960126972599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174966191417440640084648399 262449287126160960126972599)
  ·
    refine ⟨393673930689241440190458899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262449287126160960126972599 393673930689241440190458899)
    ·
      refine ⟨590510896033862160285688349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393673930689241440190458899 590510896033862160285688349)
      ·
        refine ⟨221441586012698310107133131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 590510896033862160285688349 221441586012698310107133131)
        ·
          refine ⟨332162379019047465160699697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221441586012698310107133131 332162379019047465160699697)
          ·
            refine ⟨249121784264285598870524773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332162379019047465160699697 249121784264285598870524773)
            ·
              refine ⟨46710334549553549788223395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249121784264285598870524773 46710334549553549788223395)
              ·
                refine ⟨70065501824330324682335093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46710334549553549788223395 70065501824330324682335093)
                ·
                  refine ⟨6568640796030967938968915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70065501824330324682335093 6568640796030967938968915)
                  ·
                    refine ⟨9852961194046451908453373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6568640796030967938968915 9852961194046451908453373)
                    ·
                      refine ⟨3694860447767419465670015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9852961194046451908453373 3694860447767419465670015)
                      ·
                        rfl

theorem cell23_7195715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_7195715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195715 prefixEnd_7195715 := by exact prefixLift 7195715
  have htrace : WordTrace (prefixWord ++ tailWord_7195715) baseStart_7195715 baseEnd_7195715 := by
    simpa [prefixWord, tailWord_7195715, baseEnd_7195715] using wordTrace_append hprefix tailTrace_7195715
  have hstable : (prefixWord ++ tailWord_7195715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195715).length < 2 ^ (prefixWord ++ tailWord_7195715).sum := by decide
  have hdescent : baseEnd_7195715 < baseStart_7195715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195748 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_7195748 : Nat := 118140960795 + 7195748 * 2 ^ 59
def prefixEnd_7195748 : Nat := 4983230072969 + 3 ^ 40 * 7195748 * 2
def baseEnd_7195748 : Nat := 1231625797543005945519121

theorem tailTrace_7195748 : CollatzResearch.WordTrace tailWord_7195748 prefixEnd_7195748 1231625797543005945519121 := by
  unfold tailWord_7195748
  simp only [CollatzResearch.WordTrace]
  refine ⟨131225245367520703381461949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174966993823360937841949265 131225245367520703381461949)
  ·
    refine ⟨49209467012820263768048231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131225245367520703381461949 49209467012820263768048231)
    ·
      refine ⟨73814200519230395652072347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49209467012820263768048231 73814200519230395652072347)
      ·
        refine ⟨110721300778845593478108521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73814200519230395652072347 110721300778845593478108521)
        ·
          refine ⟨83040975584134195108581391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110721300778845593478108521 83040975584134195108581391)
          ·
            refine ⟨124561463376201292662872087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83040975584134195108581391 124561463376201292662872087)
            ·
              refine ⟨186842195064301938994308131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124561463376201292662872087 186842195064301938994308131)
              ·
                refine ⟨280263292596452908491462197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186842195064301938994308131 280263292596452908491462197)
                ·
                  refine ⟨26274683680917460171074581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 280263292596452908491462197 26274683680917460171074581)
                  ·
                    refine ⟨1231625797543005945519121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26274683680917460171074581 1231625797543005945519121)
                    ·
                      rfl

theorem cell23_7195748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_7195748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195748 prefixEnd_7195748 := by exact prefixLift 7195748
  have htrace : WordTrace (prefixWord ++ tailWord_7195748) baseStart_7195748 baseEnd_7195748 := by
    simpa [prefixWord, tailWord_7195748, baseEnd_7195748] using wordTrace_append hprefix tailTrace_7195748
  have hstable : (prefixWord ++ tailWord_7195748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195748).length < 2 ^ (prefixWord ++ tailWord_7195748).sum := by decide
  have hdescent : baseEnd_7195748 < baseStart_7195748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195749 : List Nat := [1, 3, 1, 3, 2, 1, 3, 4, 1, 1, 3]
def baseStart_7195749 : Nat := 118140960795 + 7195749 * 2 ^ 59
def prefixEnd_7195749 : Nat := 4983230072969 + 3 ^ 40 * 7195749 * 2
def baseEnd_7195749 : Nat := 3694877906109672332644859

theorem tailTrace_7195749 : CollatzResearch.WordTrace tailWord_7195749 prefixEnd_7195749 3694877906109672332644859 := by
  unfold tailWord_7195749
  simp only [CollatzResearch.WordTrace]
  refine ⟨262450527208037783933710301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174967018138691855955806867 262450527208037783933710301)
  ·
    refine ⟨98418947703014168975141363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262450527208037783933710301 98418947703014168975141363)
    ·
      refine ⟨147628421554521253462712045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98418947703014168975141363 147628421554521253462712045)
      ·
        refine ⟨55360658082945470048517017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147628421554521253462712045 55360658082945470048517017)
        ·
          refine ⟨41520493562209102536387763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55360658082945470048517017 41520493562209102536387763)
          ·
            refine ⟨62280740343313653804581645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41520493562209102536387763 62280740343313653804581645)
            ·
              refine ⟨23355277628742620176718117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62280740343313653804581645 23355277628742620176718117)
              ·
                refine ⟨4379114555389241283134647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23355277628742620176718117 4379114555389241283134647)
                ·
                  refine ⟨6568671833083861924701971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379114555389241283134647 6568671833083861924701971)
                  ·
                    refine ⟨9853007749625792887052957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6568671833083861924701971 9853007749625792887052957)
                    ·
                      refine ⟨3694877906109672332644859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9853007749625792887052957 3694877906109672332644859)
                      ·
                        rfl

theorem cell23_7195749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_7195749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195749 prefixEnd_7195749 := by exact prefixLift 7195749
  have htrace : WordTrace (prefixWord ++ tailWord_7195749) baseStart_7195749 baseEnd_7195749 := by
    simpa [prefixWord, tailWord_7195749, baseEnd_7195749] using wordTrace_append hprefix tailTrace_7195749
  have hstable : (prefixWord ++ tailWord_7195749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195749).length < 2 ^ (prefixWord ++ tailWord_7195749).sum := by decide
  have hdescent : baseEnd_7195749 < baseStart_7195749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195768 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_7195768 : Nat := 118140960795 + 7195768 * 2 ^ 59
def prefixEnd_7195768 : Nat := 4983230072969 + 3 ^ 40 * 7195768 * 2
def baseEnd_7195768 : Nat := 3694887662242107758307271

theorem tailTrace_7195768 : CollatzResearch.WordTrace tailWord_7195768 prefixEnd_7195768 3694887662242107758307271 := by
  unfold tailWord_7195768
  simp only [CollatzResearch.WordTrace]
  refine ⟨131225610097484475089325979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174967480129979300119101305 131225610097484475089325979)
  ·
    refine ⟨196838415146226712633988969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131225610097484475089325979 196838415146226712633988969)
    ·
      refine ⟨147628811359670034475491727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196838415146226712633988969 147628811359670034475491727)
      ·
        refine ⟨221443217039505051713237591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147628811359670034475491727 221443217039505051713237591)
        ·
          refine ⟨332164825559257577569856387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221443217039505051713237591 332164825559257577569856387)
          ·
            refine ⟨498247238338886366354784581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332164825559257577569856387 498247238338886366354784581)
            ·
              refine ⟨93421357188541193691522109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 498247238338886366354784581 93421357188541193691522109)
              ·
                refine ⟨35033008945702947634320791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93421357188541193691522109 35033008945702947634320791)
                ·
                  refine ⟨52549513418554421451481187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35033008945702947634320791 52549513418554421451481187)
                  ·
                    refine ⟨78824270127831632177221781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52549513418554421451481187 78824270127831632177221781)
                    ·
                      refine ⟨3694887662242107758307271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78824270127831632177221781 3694887662242107758307271)
                      ·
                        rfl

theorem cell23_7195768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_7195768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195768 prefixEnd_7195768 := by exact prefixLift 7195768
  have htrace : WordTrace (prefixWord ++ tailWord_7195768) baseStart_7195768 baseEnd_7195768 := by
    simpa [prefixWord, tailWord_7195768, baseEnd_7195768] using wordTrace_append hprefix tailTrace_7195768
  have hstable : (prefixWord ++ tailWord_7195768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195768).length < 2 ^ (prefixWord ++ tailWord_7195768).sum := by decide
  have hdescent : baseEnd_7195768 < baseStart_7195768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195785 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 4]
def baseStart_7195785 : Nat := 118140960795 + 7195785 * 2 ^ 59
def prefixEnd_7195785 : Nat := 4983230072969 + 3 ^ 40 * 7195785 * 2
def baseEnd_7195785 : Nat := 3694896391413234191794693

theorem tailTrace_7195785 : CollatzResearch.WordTrace tailWord_7195785 prefixEnd_7195785 3694896391413234191794693 := by
  unfold tailWord_7195785
  simp only [CollatzResearch.WordTrace]
  refine ⟨262451840235907362082020809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174967893490604908054680539 262451840235907362082020809)
  ·
    refine ⟨196838880176930521561515607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262451840235907362082020809 196838880176930521561515607)
    ·
      refine ⟨295258320265395782342273411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196838880176930521561515607 295258320265395782342273411)
      ·
        refine ⟨442887480398093673513410117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295258320265395782342273411 442887480398093673513410117)
        ·
          refine ⟨83041402574642563783764397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442887480398093673513410117 83041402574642563783764397)
          ·
            refine ⟨31140525965490961418911649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83041402574642563783764397 31140525965490961418911649)
            ·
              refine ⟨23355394474118221064183737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31140525965490961418911649 23355394474118221064183737)
              ·
                refine ⟨17516545855588665798137803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23355394474118221064183737 17516545855588665798137803)
                ·
                  refine ⟨26274818783382998697206705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17516545855588665798137803 26274818783382998697206705)
                  ·
                    refine ⟨19706114087537249022905029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26274818783382998697206705 19706114087537249022905029)
                    ·
                      refine ⟨3694896391413234191794693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19706114087537249022905029 3694896391413234191794693)
                      ·
                        rfl

theorem cell23_7195785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_7195785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195785 prefixEnd_7195785 := by exact prefixLift 7195785
  have htrace : WordTrace (prefixWord ++ tailWord_7195785) baseStart_7195785 baseEnd_7195785 := by
    simpa [prefixWord, tailWord_7195785, baseEnd_7195785] using wordTrace_append hprefix tailTrace_7195785
  have hstable : (prefixWord ++ tailWord_7195785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195785).length < 2 ^ (prefixWord ++ tailWord_7195785).sum := by decide
  have hdescent : baseEnd_7195785 < baseStart_7195785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195799 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 2, 4]
def baseStart_7195799 : Nat := 118140960795 + 7195799 * 2 ^ 59
def prefixEnd_7195799 : Nat := 4983230072969 + 3 ^ 40 * 7195799 * 2
def baseEnd_7195799 : Nat := 1231634526714132379006543

theorem tailTrace_7195799 : CollatzResearch.WordTrace tailWord_7195799 prefixEnd_7195799 1231634526714132379006543 := by
  unfold tailWord_7195799
  simp only [CollatzResearch.WordTrace]
  refine ⟨262452350857856642473030451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174968233905237761648686967 262452350857856642473030451)
  ·
    refine ⟨393678526286784963709545677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262452350857856642473030451 393678526286784963709545677)
    ·
      refine ⟨147629447357544361391079629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393678526286784963709545677 147629447357544361391079629)
      ·
        refine ⟨55361042759079135521654861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147629447357544361391079629 55361042759079135521654861)
        ·
          refine ⟨20760391034654675820620573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55361042759079135521654861 20760391034654675820620573)
          ·
            refine ⟨7785146637995503432732715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20760391034654675820620573 7785146637995503432732715)
            ·
              refine ⟨11677719956993255149099073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785146637995503432732715 11677719956993255149099073)
              ·
                refine ⟨8758289967744941361824305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11677719956993255149099073 8758289967744941361824305)
                ·
                  refine ⟨6568717475808706021368229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8758289967744941361824305 6568717475808706021368229)
                  ·
                    refine ⟨1231634526714132379006543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6568717475808706021368229 1231634526714132379006543)
                    ·
                      rfl

theorem cell23_7195799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_7195799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195799 prefixEnd_7195799 := by exact prefixLift 7195799
  have htrace : WordTrace (prefixWord ++ tailWord_7195799) baseStart_7195799 baseEnd_7195799 := by
    simpa [prefixWord, tailWord_7195799, baseEnd_7195799] using wordTrace_append hprefix tailTrace_7195799
  have hstable : (prefixWord ++ tailWord_7195799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195799).length < 2 ^ (prefixWord ++ tailWord_7195799).sum := by decide
  have hdescent : baseEnd_7195799 < baseStart_7195799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195806 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_7195806 : Nat := 118140960795 + 7195806 * 2 ^ 59
def prefixEnd_7195806 : Nat := 4983230072969 + 3 ^ 40 * 7195806 * 2
def baseEnd_7195806 : Nat := 3694907174506978609632097

theorem tailTrace_7195806 : CollatzResearch.WordTrace tailWord_7195806 prefixEnd_7195806 3694907174506978609632097 := by
  unfold tailWord_7195806
  simp only [CollatzResearch.WordTrace]
  refine ⟨32806575771103910333566909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174968404112554188445690181 32806575771103910333566909)
  ·
    refine ⟨12302465914163966375087591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32806575771103910333566909 12302465914163966375087591)
    ·
      refine ⟨18453698871245949562631387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12302465914163966375087591 18453698871245949562631387)
      ·
        refine ⟨27680548306868924343947081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18453698871245949562631387 27680548306868924343947081)
        ·
          refine ⟨20760411230151693257960311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27680548306868924343947081 20760411230151693257960311)
          ·
            refine ⟨31140616845227539886940467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20760411230151693257960311 31140616845227539886940467)
            ·
              refine ⟨46710925267841309830410701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31140616845227539886940467 46710925267841309830410701)
              ·
                refine ⟨17516596975440491186404013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46710925267841309830410701 17516596975440491186404013)
                ·
                  refine ⟨6568723865790184194901505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17516596975440491186404013 6568723865790184194901505)
                  ·
                    refine ⟨4926542899342638146176129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6568723865790184194901505 4926542899342638146176129)
                    ·
                      refine ⟨3694907174506978609632097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4926542899342638146176129 3694907174506978609632097)
                      ·
                        rfl

theorem cell23_7195806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_7195806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195806 prefixEnd_7195806 := by exact prefixLift 7195806
  have htrace : WordTrace (prefixWord ++ tailWord_7195806) baseStart_7195806 baseEnd_7195806 := by
    simpa [prefixWord, tailWord_7195806, baseEnd_7195806] using wordTrace_append hprefix tailTrace_7195806
  have hstable : (prefixWord ++ tailWord_7195806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195806).length < 2 ^ (prefixWord ++ tailWord_7195806).sum := by decide
  have hdescent : baseEnd_7195806 < baseStart_7195806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195840 : List Nat := [2, 1, 1, 2, 7, 1, 1, 3, 1, 2, 2]
def baseStart_7195840 : Nat := 118140960795 + 7195840 * 2 ^ 59
def prefixEnd_7195840 : Nat := 4983230072969 + 3 ^ 40 * 7195840 * 2
def baseEnd_7195840 : Nat := 3694924632849231476606941

theorem tailTrace_7195840 : CollatzResearch.WordTrace tailWord_7195840 prefixEnd_7195840 3694924632849231476606941 := by
  unfold tailWord_7195840
  simp only [CollatzResearch.WordTrace]
  refine ⟨131226923125354053237636487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174969230833805404316848649 131226923125354053237636487)
  ·
    refine ⟨196840384688031079856454731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131226923125354053237636487 196840384688031079856454731)
    ·
      refine ⟨295260577032046619784682097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196840384688031079856454731 295260577032046619784682097)
      ·
        refine ⟨221445432774034964838511573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295260577032046619784682097 221445432774034964838511573)
        ·
          refine ⟨5190127330641444488402615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 221445432774034964838511573 5190127330641444488402615)
          ·
            refine ⟨7785190995962166732603923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190127330641444488402615 7785190995962166732603923)
            ·
              refine ⟨11677786493943250098905885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785190995962166732603923 11677786493943250098905885)
              ·
                refine ⟨4379169935228718787089707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11677786493943250098905885 4379169935228718787089707)
                ·
                  refine ⟨6568754902843078180634561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379169935228718787089707 6568754902843078180634561)
                  ·
                    refine ⟨4926566177132308635475921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6568754902843078180634561 4926566177132308635475921)
                    ·
                      refine ⟨3694924632849231476606941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4926566177132308635475921 3694924632849231476606941)
                      ·
                        rfl

theorem cell23_7195840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 1, 2, 2].length) (baseStart_7195840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195840 prefixEnd_7195840 := by exact prefixLift 7195840
  have htrace : WordTrace (prefixWord ++ tailWord_7195840) baseStart_7195840 baseEnd_7195840 := by
    simpa [prefixWord, tailWord_7195840, baseEnd_7195840] using wordTrace_append hprefix tailTrace_7195840
  have hstable : (prefixWord ++ tailWord_7195840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195840).length < 2 ^ (prefixWord ++ tailWord_7195840).sum := by decide
  have hdescent : baseEnd_7195840 < baseStart_7195840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195846 : List Nat := [6, 1, 2, 2, 1, 2, 9]
def baseStart_7195846 : Nat := 118140960795 + 7195846 * 2 ^ 59
def prefixEnd_7195846 : Nat := 4983230072969 + 3 ^ 40 * 7195846 * 2
def baseEnd_7195846 : Nat := 45616391527569857446073

theorem tailTrace_7195846 : CollatzResearch.WordTrace tailWord_7195846 prefixEnd_7195846 45616391527569857446073 := by
  unfold tailWord_7195846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8201689534021449046874731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174969376725790912999994261 8201689534021449046874731)
  ·
    refine ⟨12302534301032173570312097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8201689534021449046874731 12302534301032173570312097)
    ·
      refine ⟨9226900725774130177734073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12302534301032173570312097 9226900725774130177734073)
      ·
        refine ⟨6920175544330597633300555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9226900725774130177734073 6920175544330597633300555)
        ·
          refine ⟨10380263316495896449950833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6920175544330597633300555 10380263316495896449950833)
          ·
            refine ⟨7785197487371922337463125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10380263316495896449950833 7785197487371922337463125)
            ·
              refine ⟨45616391527569857446073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7785197487371922337463125 45616391527569857446073)
              ·
                rfl

theorem cell23_7195846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 9].length) (baseStart_7195846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195846 prefixEnd_7195846 := by exact prefixLift 7195846
  have htrace : WordTrace (prefixWord ++ tailWord_7195846) baseStart_7195846 baseEnd_7195846 := by
    simpa [prefixWord, tailWord_7195846, baseEnd_7195846] using wordTrace_append hprefix tailTrace_7195846
  have hstable : (prefixWord ++ tailWord_7195846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195846).length < 2 ^ (prefixWord ++ tailWord_7195846).sum := by decide
  have hdescent : baseEnd_7195846 < baseStart_7195846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195865 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 2, 4, 3]
def baseStart_7195865 : Nat := 118140960795 + 7195865 * 2 ^ 59
def prefixEnd_7195865 : Nat := 4983230072969 + 3 ^ 40 * 7195865 * 2
def baseEnd_7195865 : Nat := 3694937469865593878794325

theorem tailTrace_7195865 : CollatzResearch.WordTrace tailWord_7195865 prefixEnd_7195865 3694937469865593878794325 := by
  unfold tailWord_7195865
  simp only [CollatzResearch.WordTrace]
  refine ⟨262454758075617535744933049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174969838717078357163288699 262454758075617535744933049)
  ·
    refine ⟨196841068556713151808699787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262454758075617535744933049 196841068556713151808699787)
    ·
      refine ⟨295261602835069727713049681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196841068556713151808699787 295261602835069727713049681)
      ·
        refine ⟨221446202126302295784787261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295261602835069727713049681 221446202126302295784787261)
        ·
          refine ⟨83042325797363360919295223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221446202126302295784787261 83042325797363360919295223)
          ·
            refine ⟨124563488696045041378942835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83042325797363360919295223 124563488696045041378942835)
            ·
              refine ⟨186845233044067562068414253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124563488696045041378942835 186845233044067562068414253)
              ·
                refine ⟨70066962391525335775655345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186845233044067562068414253 70066962391525335775655345)
                ·
                  refine ⟨52550221793644001831741509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70066962391525335775655345 52550221793644001831741509)
                  ·
                    refine ⟨9853166586308250343451533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52550221793644001831741509 9853166586308250343451533)
                    ·
                      refine ⟨3694937469865593878794325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9853166586308250343451533 3694937469865593878794325)
                      ·
                        rfl

theorem cell23_7195865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_7195865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195865 prefixEnd_7195865 := by exact prefixLift 7195865
  have htrace : WordTrace (prefixWord ++ tailWord_7195865) baseStart_7195865 baseEnd_7195865 := by
    simpa [prefixWord, tailWord_7195865, baseEnd_7195865] using wordTrace_append hprefix tailTrace_7195865
  have hstable : (prefixWord ++ tailWord_7195865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195865).length < 2 ^ (prefixWord ++ tailWord_7195865).sum := by decide
  have hdescent : baseEnd_7195865 < baseStart_7195865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195895 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 3]
def baseStart_7195895 : Nat := 118140960795 + 7195895 * 2 ^ 59
def prefixEnd_7195895 : Nat := 4983230072969 + 3 ^ 40 * 7195895 * 2
def baseEnd_7195895 : Nat := 3694952874285228761419187

theorem tailTrace_7195895 : CollatzResearch.WordTrace tailWord_7195895 prefixEnd_7195895 3694952874285228761419187 := by
  unfold tailWord_7195895
  simp only [CollatzResearch.WordTrace]
  refine ⟨262455852265508850868525139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174970568177005900579016759 262455852265508850868525139)
  ·
    refine ⟨393683778398263276302787709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262455852265508850868525139 393683778398263276302787709)
    ·
      refine ⟨147631416899348728613545391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393683778398263276302787709 147631416899348728613545391)
      ·
        refine ⟨221447125349023092920318087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147631416899348728613545391 221447125349023092920318087)
        ·
          refine ⟨332170688023534639380477131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221447125349023092920318087 332170688023534639380477131)
          ·
            refine ⟨498256032035301959070715697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332170688023534639380477131 498256032035301959070715697)
            ·
              refine ⟨373692024026476469303036773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498256032035301959070715697 373692024026476469303036773)
              ·
                refine ⟨70067254504964337994319395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373692024026476469303036773 70067254504964337994319395)
                ·
                  refine ⟨105100881757446506991479093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70067254504964337994319395 105100881757446506991479093)
                  ·
                    refine ⟨9853207664760610030451165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105100881757446506991479093 9853207664760610030451165)
                    ·
                      refine ⟨3694952874285228761419187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9853207664760610030451165 3694952874285228761419187)
                      ·
                        rfl

theorem cell23_7195895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_7195895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195895 prefixEnd_7195895 := by exact prefixLift 7195895
  have htrace : WordTrace (prefixWord ++ tailWord_7195895) baseStart_7195895 baseEnd_7195895 := by
    simpa [prefixWord, tailWord_7195895, baseEnd_7195895] using wordTrace_append hprefix tailTrace_7195895
  have hstable : (prefixWord ++ tailWord_7195895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195895).length < 2 ^ (prefixWord ++ tailWord_7195895).sum := by decide
  have hdescent : baseEnd_7195895 < baseStart_7195895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195949 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_7195949 : Nat := 118140960795 + 7195949 * 2 ^ 59
def prefixEnd_7195949 : Nat := 4983230072969 + 3 ^ 40 * 7195949 * 2
def baseEnd_7195949 : Nat := 1231660200746857183381313

theorem tailTrace_7195949 : CollatzResearch.WordTrace tailWord_7195949 prefixEnd_7195949 1231660200746857183381313 := by
  unfold tailWord_7195949
  simp only [CollatzResearch.WordTrace]
  refine ⟨262457821807313218090990901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174971881204875478727327267 262457821807313218090990901)
  ·
    refine ⟨24605420794435614196030397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262457821807313218090990901 24605420794435614196030397)
    ·
      refine ⟨9227032797913355323511399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24605420794435614196030397 9227032797913355323511399)
      ·
        refine ⟨13840549196870032985267099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9227032797913355323511399 13840549196870032985267099)
        ·
          refine ⟨20760823795305049477900649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13840549196870032985267099 20760823795305049477900649)
          ·
            refine ⟨15570617846478787108425487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20760823795305049477900649 15570617846478787108425487)
            ·
              refine ⟨23355926769718180662638231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15570617846478787108425487 23355926769718180662638231)
              ·
                refine ⟨35033890154577270993957347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23355926769718180662638231 35033890154577270993957347)
                ·
                  refine ⟨52550835231865906490936021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35033890154577270993957347 52550835231865906490936021)
                  ·
                    refine ⟨1231660200746857183381313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52550835231865906490936021 1231660200746857183381313)
                    ·
                      rfl

theorem cell23_7195949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_7195949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195949 prefixEnd_7195949 := by exact prefixLift 7195949
  have htrace : WordTrace (prefixWord ++ tailWord_7195949) baseStart_7195949 baseEnd_7195949 := by
    simpa [prefixWord, tailWord_7195949, baseEnd_7195949] using wordTrace_append hprefix tailTrace_7195949
  have hstable : (prefixWord ++ tailWord_7195949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195949).length < 2 ^ (prefixWord ++ tailWord_7195949).sum := by decide
  have hdescent : baseEnd_7195949 < baseStart_7195949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195952 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 1, 6, 2]
def baseStart_7195952 : Nat := 118140960795 + 7195952 * 2 ^ 59
def prefixEnd_7195952 : Nat := 4983230072969 + 3 ^ 40 * 7195952 * 2
def baseEnd_7195952 : Nat := 3694982142682535038406425

theorem tailTrace_7195952 : CollatzResearch.WordTrace tailWord_7195952 prefixEnd_7195952 3694982142682535038406425 := by
  unfold tailWord_7195952
  simp only [CollatzResearch.WordTrace]
  refine ⟨131228965613151174801675055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174971954150868233068900073 131228965613151174801675055)
  ·
    refine ⟨196843448419726762202512583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131228965613151174801675055 196843448419726762202512583)
    ·
      refine ⟨295265172629590143303768875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196843448419726762202512583 295265172629590143303768875)
      ·
        refine ⟨442897758944385214955653313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295265172629590143303768875 442897758944385214955653313)
        ·
          refine ⟨332173319208288911216739985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442897758944385214955653313 332173319208288911216739985)
          ·
            refine ⟨249129989406216683412554989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332173319208288911216739985 249129989406216683412554989)
            ·
              refine ⟨93423746027331256279708121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249129989406216683412554989 93423746027331256279708121)
              ·
                refine ⟨70067809520498442209781091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93423746027331256279708121 70067809520498442209781091)
                ·
                  refine ⟨105101714280747663314671637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70067809520498442209781091 105101714280747663314671637)
                  ·
                    refine ⟨4926642856910046717875233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105101714280747663314671637 4926642856910046717875233)
                    ·
                      refine ⟨3694982142682535038406425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4926642856910046717875233 3694982142682535038406425)
                      ·
                        rfl

theorem cell23_7195952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 6, 2].length) (baseStart_7195952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195952 prefixEnd_7195952 := by exact prefixLift 7195952
  have htrace : WordTrace (prefixWord ++ tailWord_7195952) baseStart_7195952 baseEnd_7195952 := by
    simpa [prefixWord, tailWord_7195952, baseEnd_7195952] using wordTrace_append hprefix tailTrace_7195952
  have hstable : (prefixWord ++ tailWord_7195952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195952).length < 2 ^ (prefixWord ++ tailWord_7195952).sum := by decide
  have hdescent : baseEnd_7195952 < baseStart_7195952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7195962 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 5, 4]
def baseStart_7195962 : Nat := 118140960795 + 7195962 * 2 ^ 59
def prefixEnd_7195962 : Nat := 4983230072969 + 3 ^ 40 * 7195962 * 2
def baseEnd_7195962 : Nat := 1231662425829693333093793

theorem tailTrace_7195962 : CollatzResearch.WordTrace tailWord_7195962 prefixEnd_7195962 1231662425829693333093793 := by
  unfold tailWord_7195962
  simp only [CollatzResearch.WordTrace]
  refine ⟨65614573989066530327803535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174972197304177414207476093 65614573989066530327803535)
  ·
    refine ⟨98421860983599795491705303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65614573989066530327803535 98421860983599795491705303)
    ·
      refine ⟨147632791475399693237557955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98421860983599795491705303 147632791475399693237557955)
      ·
        refine ⟨221449187213099539856336933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147632791475399693237557955 221449187213099539856336933)
        ·
          refine ⟨41521722602456163723063175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221449187213099539856336933 41521722602456163723063175)
          ·
            refine ⟨62282583903684245584594763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41521722602456163723063175 62282583903684245584594763)
            ·
              refine ⟨93423875855526368376892145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62282583903684245584594763 93423875855526368376892145)
              ·
                refine ⟨70067906891644776282669109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93423875855526368376892145 70067906891644776282669109)
                ·
                  refine ⟨6568866271091697776500229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70067906891644776282669109 6568866271091697776500229)
                  ·
                    refine ⟨1231662425829693333093793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6568866271091697776500229 1231662425829693333093793)
                    ·
                      rfl

theorem cell23_7195962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_7195962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7195962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7195962 prefixEnd_7195962 := by exact prefixLift 7195962
  have htrace : WordTrace (prefixWord ++ tailWord_7195962) baseStart_7195962 baseEnd_7195962 := by
    simpa [prefixWord, tailWord_7195962, baseEnd_7195962] using wordTrace_append hprefix tailTrace_7195962
  have hstable : (prefixWord ++ tailWord_7195962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7195962).length < 2 ^ (prefixWord ++ tailWord_7195962).sum := by decide
  have hdescent : baseEnd_7195962 < baseStart_7195962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7195962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196013 : List Nat := [1, 5, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_7196013 : Nat := 118140960795 + 7196013 * 2 ^ 59
def prefixEnd_7196013 : Nat := 4983230072969 + 3 ^ 40 * 7196013 * 2
def baseEnd_7196013 : Nat := 1231671155000819766581215

theorem tailTrace_7196013 : CollatzResearch.WordTrace tailWord_7196013 prefixEnd_7196013 1231671155000819766581215 := by
  unfold tailWord_7196013
  simp only [CollatzResearch.WordTrace]
  refine ⟨262460156079081357021320693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174973437386054238014213795 262460156079081357021320693)
  ·
    refine ⟨24605639632413877220748815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262460156079081357021320693 24605639632413877220748815)
    ·
      refine ⟨36908459448620815831123223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24605639632413877220748815 36908459448620815831123223)
      ·
        refine ⟨55362689172931223746684835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36908459448620815831123223 55362689172931223746684835)
        ·
          refine ⟨83044033759396835620027253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55362689172931223746684835 83044033759396835620027253)
          ·
            refine ⟨7785378164943453339377555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83044033759396835620027253 7785378164943453339377555)
            ·
              refine ⟨11678067247415180009066333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785378164943453339377555 11678067247415180009066333)
              ·
                refine ⟨4379275217780692503399875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11678067247415180009066333 4379275217780692503399875)
                ·
                  refine ⟨6568912826671038755099813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379275217780692503399875 6568912826671038755099813)
                  ·
                    refine ⟨1231671155000819766581215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6568912826671038755099813 1231671155000819766581215)
                    ·
                      rfl

theorem cell23_7196013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_7196013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196013 prefixEnd_7196013 := by exact prefixLift 7196013
  have htrace : WordTrace (prefixWord ++ tailWord_7196013) baseStart_7196013 baseEnd_7196013 := by
    simpa [prefixWord, tailWord_7196013, baseEnd_7196013] using wordTrace_append hprefix tailTrace_7196013
  have hstable : (prefixWord ++ tailWord_7196013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196013).length < 2 ^ (prefixWord ++ tailWord_7196013).sum := by decide
  have hdescent : baseEnd_7196013 < baseStart_7196013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196030 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7196030 : Nat := 118140960795 + 7196030 * 2 ^ 59
def prefixEnd_7196030 : Nat := 4983230072969 + 3 ^ 40 * 7196030 * 2
def baseEnd_7196030 : Nat := 1231674064724528577743689

theorem tailTrace_7196030 : CollatzResearch.WordTrace tailWord_7196030 prefixEnd_7196030 1231674064724528577743689 := by
  unfold tailWord_7196030
  simp only [CollatzResearch.WordTrace]
  refine ⟨32807597015002471115586193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174973850746679845949793029 32807597015002471115586193)
  ·
    refine ⟨24605697761251853336689645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32807597015002471115586193 24605697761251853336689645)
    ·
      refine ⟨9227136660469445001258617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24605697761251853336689645 9227136660469445001258617)
      ·
        refine ⟨6920352495352083750943963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9227136660469445001258617 6920352495352083750943963)
        ·
          refine ⟨10380528743028125626415945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6920352495352083750943963 10380528743028125626415945)
          ·
            refine ⟨7785396557271094219811959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10380528743028125626415945 7785396557271094219811959)
            ·
              refine ⟨11678094835906641329717939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785396557271094219811959 11678094835906641329717939)
              ·
                refine ⟨17517142253859961994576909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11678094835906641329717939 17517142253859961994576909)
                ·
                  refine ⟨6568928345197485747966341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17517142253859961994576909 6568928345197485747966341)
                  ·
                    refine ⟨1231674064724528577743689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6568928345197485747966341 1231674064724528577743689)
                    ·
                      rfl

theorem cell23_7196030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7196030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196030 prefixEnd_7196030 := by exact prefixLift 7196030
  have htrace : WordTrace (prefixWord ++ tailWord_7196030) baseStart_7196030 baseEnd_7196030 := by
    simpa [prefixWord, tailWord_7196030, baseEnd_7196030] using wordTrace_append hprefix tailTrace_7196030
  have hstable : (prefixWord ++ tailWord_7196030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196030).length < 2 ^ (prefixWord ++ tailWord_7196030).sum := by decide
  have hdescent : baseEnd_7196030 < baseStart_7196030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196036 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_7196036 : Nat := 118140960795 + 7196036 * 2 ^ 59
def prefixEnd_7196036 : Nat := 4983230072969 + 3 ^ 40 * 7196036 * 2
def baseEnd_7196036 : Nat := 3695025275057512709756039

theorem tailTrace_7196036 : CollatzResearch.WordTrace tailWord_7196036 prefixEnd_7196036 3695025275057512709756039 := by
  unfold tailWord_7196036
  simp only [CollatzResearch.WordTrace]
  refine ⟨131230497478999015974703981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174973996638665354632938641 131230497478999015974703981)
  ·
    refine ⟨49211436554624630990513993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131230497478999015974703981 49211436554624630990513993)
    ·
      refine ⟨36908577415968473242885495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49211436554624630990513993 36908577415968473242885495)
      ·
        refine ⟨55362866123952709864328243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36908577415968473242885495 55362866123952709864328243)
        ·
          refine ⟨83044299185929064796492365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55362866123952709864328243 83044299185929064796492365)
          ·
            refine ⟨31141612194723399298684637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83044299185929064796492365 31141612194723399298684637)
            ·
              refine ⟨11678104573021274737006739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31141612194723399298684637 11678104573021274737006739)
              ·
                refine ⟨17517156859531912105510109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11678104573021274737006739 17517156859531912105510109)
                ·
                  refine ⟨6568933822324467039566291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17517156859531912105510109 6568933822324467039566291)
                  ·
                    refine ⟨9853400733486700559349437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6568933822324467039566291 9853400733486700559349437)
                    ·
                      refine ⟨3695025275057512709756039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9853400733486700559349437 3695025275057512709756039)
                      ·
                        rfl

theorem cell23_7196036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_7196036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196036 prefixEnd_7196036 := by exact prefixLift 7196036
  have htrace : WordTrace (prefixWord ++ tailWord_7196036) baseStart_7196036 baseEnd_7196036 := by
    simpa [prefixWord, tailWord_7196036, baseEnd_7196036] using wordTrace_append hprefix tailTrace_7196036
  have hstable : (prefixWord ++ tailWord_7196036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196036).length < 2 ^ (prefixWord ++ tailWord_7196036).sum := by decide
  have hdescent : baseEnd_7196036 < baseStart_7196036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196079 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 1, 2, 3]
def baseStart_7196079 : Nat := 118140960795 + 7196079 * 2 ^ 59
def prefixEnd_7196079 : Nat := 4983230072969 + 3 ^ 40 * 7196079 * 2
def baseEnd_7196079 : Nat := 3695047354725656041518341

theorem tailTrace_7196079 : CollatzResearch.WordTrace tailWord_7196079 prefixEnd_7196079 3695047354725656041518341 := by
  unfold tailWord_7196079
  simp only [CollatzResearch.WordTrace]
  refine ⟨262462563296842250293223291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174975042197894833528815527 262462563296842250293223291)
  ·
    refine ⟨393693844945263375439834937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262462563296842250293223291 393693844945263375439834937)
    ·
      refine ⟨295270383708947531579876203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393693844945263375439834937 295270383708947531579876203)
      ·
        refine ⟨442905575563421297369814305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295270383708947531579876203 442905575563421297369814305)
        ·
          refine ⟨332179181672565973027360729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442905575563421297369814305 332179181672565973027360729)
          ·
            refine ⟨249134386254424479770520547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332179181672565973027360729 249134386254424479770520547)
            ·
              refine ⟨373701579381636719655780821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249134386254424479770520547 373701579381636719655780821)
              ·
                refine ⟨8758630766757110616932363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 373701579381636719655780821 8758630766757110616932363)
                ·
                  refine ⟨13137946150135665925398545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8758630766757110616932363 13137946150135665925398545)
                  ·
                    refine ⟨9853459612601749444048909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13137946150135665925398545 9853459612601749444048909)
                    ·
                      refine ⟨3695047354725656041518341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9853459612601749444048909 3695047354725656041518341)
                      ·
                        rfl

theorem cell23_7196079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 2, 3].length) (baseStart_7196079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196079 prefixEnd_7196079 := by exact prefixLift 7196079
  have htrace : WordTrace (prefixWord ++ tailWord_7196079) baseStart_7196079 baseEnd_7196079 := by
    simpa [prefixWord, tailWord_7196079, baseEnd_7196079] using wordTrace_append hprefix tailTrace_7196079
  have hstable : (prefixWord ++ tailWord_7196079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196079).length < 2 ^ (prefixWord ++ tailWord_7196079).sum := by decide
  have hdescent : baseEnd_7196079 < baseStart_7196079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196116 : List Nat := [2, 4, 1, 2, 3, 1, 3, 7]
def baseStart_7196116 : Nat := 118140960795 + 7196116 * 2 ^ 59
def prefixEnd_7196116 : Nat := 4983230072969 + 3 ^ 40 * 7196116 * 2
def baseEnd_7196116 : Nat := 136854309389254533213173

theorem tailTrace_7196116 : CollatzResearch.WordTrace tailWord_7196116 prefixEnd_7196116 136854309389254533213173 := by
  unfold tailWord_7196116
  simp only [CollatzResearch.WordTrace]
  refine ⟨131231956398854102806160101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174975941865138803741546801 131231956398854102806160101)
  ·
    refine ⟨24605991824785144276155019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131231956398854102806160101 24605991824785144276155019)
    ·
      refine ⟨36908987737177716414232529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24605991824785144276155019 36908987737177716414232529)
      ·
        refine ⟨27681740802883287310674397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36908987737177716414232529 27681740802883287310674397)
        ·
          refine ⟨10380652801081232741502899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27681740802883287310674397 10380652801081232741502899)
          ·
            refine ⟨15570979201621849112254349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10380652801081232741502899 15570979201621849112254349)
            ·
              refine ⟨5839117200608193417095381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15570979201621849112254349 5839117200608193417095381)
              ·
                refine ⟨136854309389254533213173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5839117200608193417095381 136854309389254533213173)
                ·
                  rfl

theorem cell23_7196116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 7].length) (baseStart_7196116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196116 prefixEnd_7196116 := by exact prefixLift 7196116
  have htrace : WordTrace (prefixWord ++ tailWord_7196116) baseStart_7196116 baseEnd_7196116 := by
    simpa [prefixWord, tailWord_7196116, baseEnd_7196116] using wordTrace_append hprefix tailTrace_7196116
  have hstable : (prefixWord ++ tailWord_7196116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196116).length < 2 ^ (prefixWord ++ tailWord_7196116).sum := by decide
  have hdescent : baseEnd_7196116 < baseStart_7196116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196206 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_7196206 : Nat := 118140960795 + 7196206 * 2 ^ 59
def prefixEnd_7196206 : Nat := 4983230072969 + 3 ^ 40 * 7196206 * 2
def baseEnd_7196206 : Nat := 410568062974308560514473

theorem tailTrace_7196206 : CollatzResearch.WordTrace tailWord_7196206 prefixEnd_7196206 410568062974308560514473 := by
  unfold tailWord_7196206
  simp only [CollatzResearch.WordTrace]
  refine ⟨32808399420922768872887059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174978130244921433988730981 32808399420922768872887059)
  ·
    refine ⟨49212599131384153309330589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32808399420922768872887059 49212599131384153309330589)
    ·
      refine ⟨18454724674269057490998971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49212599131384153309330589 18454724674269057490998971)
      ·
        refine ⟨27682087011403586236498457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18454724674269057490998971 27682087011403586236498457)
        ·
          refine ⟨20761565258552689677373843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27682087011403586236498457 20761565258552689677373843)
          ·
            refine ⟨31142347887829034516060765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20761565258552689677373843 31142347887829034516060765)
            ·
              refine ⟨11678380457935887943522787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31142347887829034516060765 11678380457935887943522787)
              ·
                refine ⟨17517570686903831915284181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11678380457935887943522787 17517570686903831915284181)
                ·
                  refine ⟨410568062974308560514473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17517570686903831915284181 410568062974308560514473)
                  ·
                    rfl

theorem cell23_7196206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_7196206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196206 prefixEnd_7196206 := by exact prefixLift 7196206
  have htrace : WordTrace (prefixWord ++ tailWord_7196206) baseStart_7196206 baseEnd_7196206 := by
    simpa [prefixWord, tailWord_7196206, baseEnd_7196206] using wordTrace_append hprefix tailTrace_7196206
  have hstable : (prefixWord ++ tailWord_7196206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196206).length < 2 ^ (prefixWord ++ tailWord_7196206).sum := by decide
  have hdescent : baseEnd_7196206 < baseStart_7196206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196217 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 2, 2, 2]
def baseStart_7196217 : Nat := 118140960795 + 7196217 * 2 ^ 59
def prefixEnd_7196217 : Nat := 4983230072969 + 3 ^ 40 * 7196217 * 2
def baseEnd_7196217 : Nat := 3695118215055976501592707

theorem tailTrace_7196217 : CollatzResearch.WordTrace tailWord_7196217 prefixEnd_7196217 3695118215055976501592707 := by
  unfold tailWord_7196217
  simp only [CollatzResearch.WordTrace]
  refine ⟨262467596570342299861746905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174978397713561533241164603 262467596570342299861746905)
  ·
    refine ⟨196850697427756724896310179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262467596570342299861746905 196850697427756724896310179)
    ·
      refine ⟨295276046141635087344465269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196850697427756724896310179 295276046141635087344465269)
      ·
        refine ⟨27682129325778289438543619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295276046141635087344465269 27682129325778289438543619)
        ·
          refine ⟨41523193988667434157815429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27682129325778289438543619 41523193988667434157815429)
          ·
            refine ⟨7785598872875143904590393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41523193988667434157815429 7785598872875143904590393)
            ·
              refine ⟨5839199154656357928442795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7785598872875143904590393 5839199154656357928442795)
              ·
                refine ⟨8758798731984536892664193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5839199154656357928442795 8758798731984536892664193)
                ·
                  refine ⟨6569099048988402669498145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8758798731984536892664193 6569099048988402669498145)
                  ·
                    refine ⟨4926824286741302002123609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6569099048988402669498145 4926824286741302002123609)
                    ·
                      refine ⟨3695118215055976501592707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4926824286741302002123609 3695118215055976501592707)
                      ·
                        rfl

theorem cell23_7196217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_7196217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196217 prefixEnd_7196217 := by exact prefixLift 7196217
  have htrace : WordTrace (prefixWord ++ tailWord_7196217) baseStart_7196217 baseEnd_7196217 := by
    simpa [prefixWord, tailWord_7196217, baseEnd_7196217] using wordTrace_append hprefix tailTrace_7196217
  have hstable : (prefixWord ++ tailWord_7196217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196217).length < 2 ^ (prefixWord ++ tailWord_7196217).sum := by decide
  have hdescent : baseEnd_7196217 < baseStart_7196217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196236 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 2, 5]
def baseStart_7196236 : Nat := 118140960795 + 7196236 * 2 ^ 59
def prefixEnd_7196236 : Nat := 4983230072969 + 3 ^ 40 * 7196236 * 2
def baseEnd_7196236 : Nat := 1231709323729470642418373

theorem tailTrace_7196236 : CollatzResearch.WordTrace tailWord_7196236 prefixEnd_7196236 1231709323729470642418373 := by
  unfold tailWord_7196236
  simp only [CollatzResearch.WordTrace]
  refine ⟨131234144778636733053344281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174978859704848977404459041 131234144778636733053344281)
  ·
    refine ⟨98425608583977549790008211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131234144778636733053344281 98425608583977549790008211)
    ·
      refine ⟨147638412875966324685012317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98425608583977549790008211 147638412875966324685012317)
      ·
        refine ⟨55364404828487371756879619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147638412875966324685012317 55364404828487371756879619)
        ·
          refine ⟨83046607242731057635319429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55364404828487371756879619 83046607242731057635319429)
          ·
            refine ⟨15571238858012073306622393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83046607242731057635319429 15571238858012073306622393)
            ·
              refine ⟨11678429143509054979966795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15571238858012073306622393 11678429143509054979966795)
              ·
                refine ⟨17517643715263582469950193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11678429143509054979966795 17517643715263582469950193)
                ·
                  refine ⟨13138232786447686852462645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17517643715263582469950193 13138232786447686852462645)
                  ·
                    refine ⟨1231709323729470642418373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13138232786447686852462645 1231709323729470642418373)
                    ·
                      rfl

theorem cell23_7196236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_7196236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196236 prefixEnd_7196236 := by exact prefixLift 7196236
  have htrace : WordTrace (prefixWord ++ tailWord_7196236) baseStart_7196236 baseEnd_7196236 := by
    simpa [prefixWord, tailWord_7196236, baseEnd_7196236] using wordTrace_append hprefix tailTrace_7196236
  have hstable : (prefixWord ++ tailWord_7196236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196236).length < 2 ^ (prefixWord ++ tailWord_7196236).sum := by decide
  have hdescent : baseEnd_7196236 < baseStart_7196236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196256 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 2, 4, 2]
def baseStart_7196256 : Nat := 118140960795 + 7196256 * 2 ^ 59
def prefixEnd_7196256 : Nat := 4983230072969 + 3 ^ 40 * 7196256 * 2
def baseEnd_7196256 : Nat := 3695138240801501849005027

theorem tailTrace_7196256 : CollatzResearch.WordTrace tailWord_7196256 prefixEnd_7196256 3695138240801501849005027 := by
  unfold tailWord_7196256
  simp only [CollatzResearch.WordTrace]
  refine ⟨131234509508600504761208311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174979346011467339681611081 131234509508600504761208311)
  ·
    refine ⟨196851764262900757141812467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131234509508600504761208311 196851764262900757141812467)
    ·
      refine ⟨295277646394351135712718701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196851764262900757141812467 295277646394351135712718701)
      ·
        refine ⟨110729117397881675892269513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295277646394351135712718701 110729117397881675892269513)
        ·
          refine ⟨83046838048411256919202135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110729117397881675892269513 83046838048411256919202135)
          ·
            refine ⟨124570257072616885378803203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83046838048411256919202135 124570257072616885378803203)
            ·
              refine ⟨186855385608925328068204805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124570257072616885378803203 186855385608925328068204805)
              ·
                refine ⟨35035384801673499012788401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186855385608925328068204805 35035384801673499012788401)
                ·
                  refine ⟨26276538601255124259591301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35035384801673499012788401 26276538601255124259591301)
                  ·
                    refine ⟨4926850987735335798673369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26276538601255124259591301 4926850987735335798673369)
                    ·
                      refine ⟨3695138240801501849005027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4926850987735335798673369 3695138240801501849005027)
                      ·
                        rfl

theorem cell23_7196256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_7196256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196256 prefixEnd_7196256 := by exact prefixLift 7196256
  have htrace : WordTrace (prefixWord ++ tailWord_7196256) baseStart_7196256 baseEnd_7196256 := by
    simpa [prefixWord, tailWord_7196256, baseEnd_7196256] using wordTrace_append hprefix tailTrace_7196256
  have hstable : (prefixWord ++ tailWord_7196256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196256).length < 2 ^ (prefixWord ++ tailWord_7196256).sum := by decide
  have hdescent : baseEnd_7196256 < baseStart_7196256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196323 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 3, 1, 3]
def baseStart_7196323 : Nat := 118140960795 + 7196323 * 2 ^ 59
def prefixEnd_7196323 : Nat := 4983230072969 + 3 ^ 40 * 7196323 * 2
def baseEnd_7196323 : Nat := 3695172644005353086867219

theorem tailTrace_7196323 : CollatzResearch.WordTrace tailWord_7196323 prefixEnd_7196323 3695172644005353086867219 := by
  unfold tailWord_7196323
  simp only [CollatzResearch.WordTrace]
  refine ⟨262471462707958279965105623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174980975138638853310070415 262471462707958279965105623)
  ·
    refine ⟨393707194061937419947658435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262471462707958279965105623 393707194061937419947658435)
    ·
      refine ⟨590560791092906129921487653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393707194061937419947658435 590560791092906129921487653)
      ·
        refine ⟨110730148329919899360278935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 590560791092906129921487653 110730148329919899360278935)
        ·
          refine ⟨166095222494879849040418403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110730148329919899360278935 166095222494879849040418403)
          ·
            refine ⟨249142833742319773560627605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166095222494879849040418403 249142833742319773560627605)
            ·
              refine ⟨11678570331671239385654419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 249142833742319773560627605 11678570331671239385654419)
              ·
                refine ⟨17517855497506859078481629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11678570331671239385654419 17517855497506859078481629)
                ·
                  refine ⟨6569195811565072154430611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17517855497506859078481629 6569195811565072154430611)
                  ·
                    refine ⟨9853793717347608231645917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6569195811565072154430611 9853793717347608231645917)
                    ·
                      refine ⟨3695172644005353086867219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9853793717347608231645917 3695172644005353086867219)
                      ·
                        rfl

theorem cell23_7196323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_7196323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196323 prefixEnd_7196323 := by exact prefixLift 7196323
  have htrace : WordTrace (prefixWord ++ tailWord_7196323) baseStart_7196323 baseEnd_7196323 := by
    simpa [prefixWord, tailWord_7196323, baseEnd_7196323] using wordTrace_append hprefix tailTrace_7196323
  have hstable : (prefixWord ++ tailWord_7196323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196323).length < 2 ^ (prefixWord ++ tailWord_7196323).sum := by decide
  have hdescent : baseEnd_7196323 < baseStart_7196323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196333 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_7196333 : Nat := 118140960795 + 7196333 * 2 ^ 59
def prefixEnd_7196333 : Nat := 4983230072969 + 3 ^ 40 * 7196333 * 2
def baseEnd_7196333 : Nat := 3695177778811898047742173

theorem tailTrace_7196333 : CollatzResearch.WordTrace tailWord_7196333 prefixEnd_7196333 3695177778811898047742173 := by
  unfold tailWord_7196333
  simp only [CollatzResearch.WordTrace]
  refine ⟨262471827437922051672969653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174981218291948034448646435 262471827437922051672969653)
  ·
    refine ⟨24606733822305192344340905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262471827437922051672969653 24606733822305192344340905)
    ·
      refine ⟨18455050366728894258255679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24606733822305192344340905 18455050366728894258255679)
      ·
        refine ⟨27682575550093341387383519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18455050366728894258255679 27682575550093341387383519)
        ·
          refine ⟨41523863325140012081075279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27682575550093341387383519 41523863325140012081075279)
          ·
            refine ⟨62285794987710018121612919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41523863325140012081075279 62285794987710018121612919)
            ·
              refine ⟨93428692481565027182419379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62285794987710018121612919 93428692481565027182419379)
              ·
                refine ⟨140143038722347540773629069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93428692481565027182419379 140143038722347540773629069)
                ·
                  refine ⟨52553639520880327790110901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140143038722347540773629069 52553639520880327790110901)
                  ·
                    refine ⟨4926903705082530730322897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52553639520880327790110901 4926903705082530730322897)
                    ·
                      refine ⟨3695177778811898047742173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4926903705082530730322897 3695177778811898047742173)
                      ·
                        rfl

theorem cell23_7196333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_7196333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196333 prefixEnd_7196333 := by exact prefixLift 7196333
  have htrace : WordTrace (prefixWord ++ tailWord_7196333) baseStart_7196333 baseEnd_7196333 := by
    simpa [prefixWord, tailWord_7196333, baseEnd_7196333] using wordTrace_append hprefix tailTrace_7196333
  have hstable : (prefixWord ++ tailWord_7196333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196333).length < 2 ^ (prefixWord ++ tailWord_7196333).sum := by decide
  have hdescent : baseEnd_7196333 < baseStart_7196333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196343 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 1, 5]
def baseStart_7196343 : Nat := 118140960795 + 7196343 * 2 ^ 59
def prefixEnd_7196343 : Nat := 4983230072969 + 3 ^ 40 * 7196343 * 2
def baseEnd_7196343 : Nat := 1231727637872814336205709

theorem tailTrace_7196343 : CollatzResearch.WordTrace tailWord_7196343 prefixEnd_7196343 1231727637872814336205709 := by
  unfold tailWord_7196343
  simp only [CollatzResearch.WordTrace]
  refine ⟨262472192167885823380833683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174981461445257215587222455 262472192167885823380833683)
  ·
    refine ⟨393708288251828735071250525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262472192167885823380833683 393708288251828735071250525)
    ·
      refine ⟨147640608094435775651718947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393708288251828735071250525 147640608094435775651718947)
      ·
        refine ⟨221460912141653663477578421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147640608094435775651718947 221460912141653663477578421)
        ·
          refine ⟨20761960513280030951022977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221460912141653663477578421 20761960513280030951022977)
          ·
            refine ⟨15571470384960023213267233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20761960513280030951022977 15571470384960023213267233)
            ·
              refine ⟨11678602788720017409950425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15571470384960023213267233 11678602788720017409950425)
              ·
                refine ⟨8758952091540013057462819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11678602788720017409950425 8758952091540013057462819)
                ·
                  refine ⟨13138428137310019586194229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8758952091540013057462819 13138428137310019586194229)
                  ·
                    refine ⟨1231727637872814336205709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13138428137310019586194229 1231727637872814336205709)
                    ·
                      rfl

theorem cell23_7196343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_7196343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196343 prefixEnd_7196343 := by exact prefixLift 7196343
  have htrace : WordTrace (prefixWord ++ tailWord_7196343) baseStart_7196343 baseEnd_7196343 := by
    simpa [prefixWord, tailWord_7196343, baseEnd_7196343] using wordTrace_append hprefix tailTrace_7196343
  have hstable : (prefixWord ++ tailWord_7196343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196343).length < 2 ^ (prefixWord ++ tailWord_7196343).sum := by decide
  have hdescent : baseEnd_7196343 < baseStart_7196343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196356 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_7196356 : Nat := 118140960795 + 7196356 * 2 ^ 59
def prefixEnd_7196356 : Nat := 4983230072969 + 3 ^ 40 * 7196356 * 2
def baseEnd_7196356 : Nat := 1231729862955650485918189

theorem tailTrace_7196356 : CollatzResearch.WordTrace tailWord_7196356 prefixEnd_7196356 1231729862955650485918189 := by
  unfold tailWord_7196356
  simp only [CollatzResearch.WordTrace]
  refine ⟨131236333158419363300528461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174981777544559151067371281 131236333158419363300528461)
  ·
    refine ⟨49213624934407261237698173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131236333158419363300528461 49213624934407261237698173)
    ·
      refine ⟨18455109350402722964136815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49213624934407261237698173 18455109350402722964136815)
      ·
        refine ⟨27682664025604084446205223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18455109350402722964136815 27682664025604084446205223)
        ·
          refine ⟨41523996038406126669307835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27682664025604084446205223 41523996038406126669307835)
          ·
            refine ⟨62285994057609190003961753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41523996038406126669307835 62285994057609190003961753)
            ·
              refine ⟨46714495543206892502971315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62285994057609190003961753 46714495543206892502971315)
              ·
                refine ⟨70071743314810338754456973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46714495543206892502971315 70071743314810338754456973)
                ·
                  refine ⟨26276903743053877032921365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70071743314810338754456973 26276903743053877032921365)
                  ·
                    refine ⟨1231729862955650485918189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26276903743053877032921365 1231729862955650485918189)
                    ·
                      rfl

theorem cell23_7196356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_7196356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196356 prefixEnd_7196356 := by exact prefixLift 7196356
  have htrace : WordTrace (prefixWord ++ tailWord_7196356) baseStart_7196356 baseEnd_7196356 := by
    simpa [prefixWord, tailWord_7196356, baseEnd_7196356] using wordTrace_append hprefix tailTrace_7196356
  have hstable : (prefixWord ++ tailWord_7196356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196356).length < 2 ^ (prefixWord ++ tailWord_7196356).sum := by decide
  have hdescent : baseEnd_7196356 < baseStart_7196356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196363 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 5, 2, 2]
def baseStart_7196363 : Nat := 118140960795 + 7196363 * 2 ^ 59
def prefixEnd_7196363 : Nat := 4983230072969 + 3 ^ 40 * 7196363 * 2
def baseEnd_7196363 : Nat := 3695193183231532930367035

theorem tailTrace_7196363 : CollatzResearch.WordTrace tailWord_7196363 prefixEnd_7196363 3695193183231532930367035 := by
  unfold tailWord_7196363
  simp only [CollatzResearch.WordTrace]
  refine ⟨262472921627813366796561743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174981947751875577864374495 262472921627813366796561743)
  ·
    refine ⟨393709382441720050194842615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262472921627813366796561743 393709382441720050194842615)
    ·
      refine ⟨590564073662580075292263923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393709382441720050194842615 590564073662580075292263923)
      ·
        refine ⟨885846110493870112938395885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590564073662580075292263923 885846110493870112938395885)
        ·
          refine ⟨332192291435201292351898457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 885846110493870112938395885 332192291435201292351898457)
          ·
            refine ⟨249144218576400969263923843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332192291435201292351898457 249144218576400969263923843)
            ·
              refine ⟨373716327864601453895885765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249144218576400969263923843 373716327864601453895885765)
              ·
                refine ⟨70071811474612772605478581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373716327864601453895885765 70071811474612772605478581)
                ·
                  refine ⟨6569232325744947431763617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70071811474612772605478581 6569232325744947431763617)
                  ·
                    refine ⟨4926924244308710573822713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6569232325744947431763617 4926924244308710573822713)
                    ·
                      refine ⟨3695193183231532930367035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4926924244308710573822713 3695193183231532930367035)
                      ·
                        rfl

theorem cell23_7196363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 2, 2].length) (baseStart_7196363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196363 prefixEnd_7196363 := by exact prefixLift 7196363
  have htrace : WordTrace (prefixWord ++ tailWord_7196363) baseStart_7196363 baseEnd_7196363 := by
    simpa [prefixWord, tailWord_7196363, baseEnd_7196363] using wordTrace_append hprefix tailTrace_7196363
  have hstable : (prefixWord ++ tailWord_7196363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196363).length < 2 ^ (prefixWord ++ tailWord_7196363).sum := by decide
  have hdescent : baseEnd_7196363 < baseStart_7196363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196369 : List Nat := [1, 2, 2, 1, 2, 4, 11]
def baseStart_7196369 : Nat := 118140960795 + 7196369 * 2 ^ 59
def prefixEnd_7196369 : Nat := 4983230072969 + 3 ^ 40 * 7196369 * 2
def baseEnd_7196369 : Nat := 45619706964388393912247

theorem tailTrace_7196369 : CollatzResearch.WordTrace tailWord_7196369 prefixEnd_7196369 45619706964388393912247 := by
  unfold tailWord_7196369
  simp only [CollatzResearch.WordTrace]
  refine ⟨262473140465791629821280161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174982093643861086547520107 262473140465791629821280161)
  ·
    refine ⟨196854855349343722365960121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262473140465791629821280161 196854855349343722365960121)
    ·
      refine ⟨147641141512007791774470091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196854855349343722365960121 147641141512007791774470091)
      ·
        refine ⟨221461712268011687661705137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147641141512007791774470091 221461712268011687661705137)
        ·
          refine ⟨166096284201008765746278853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221461712268011687661705137 166096284201008765746278853)
          ·
            refine ⟨31143053287689143577427285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166096284201008765746278853 31143053287689143577427285)
            ·
              refine ⟨45619706964388393912247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31143053287689143577427285 45619706964388393912247)
              ·
                rfl

theorem cell23_7196369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 11].length) (baseStart_7196369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196369 prefixEnd_7196369 := by exact prefixLift 7196369
  have htrace : WordTrace (prefixWord ++ tailWord_7196369) baseStart_7196369 baseEnd_7196369 := by
    simpa [prefixWord, tailWord_7196369, baseEnd_7196369] using wordTrace_append hprefix tailTrace_7196369
  have hstable : (prefixWord ++ tailWord_7196369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196369).length < 2 ^ (prefixWord ++ tailWord_7196369).sum := by decide
  have hdescent : baseEnd_7196369 < baseStart_7196369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196413 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_7196413 : Nat := 118140960795 + 7196413 * 2 ^ 59
def prefixEnd_7196413 : Nat := 4983230072969 + 3 ^ 40 * 7196413 * 2
def baseEnd_7196413 : Nat := 3695218857264257734741805

theorem tailTrace_7196413 : CollatzResearch.WordTrace tailWord_7196413 prefixEnd_7196413 3695218857264257734741805 := by
  unfold tailWord_7196413
  simp only [CollatzResearch.WordTrace]
  refine ⟨262474745277632225335881893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174983163518421483557254595 262474745277632225335881893)
  ·
    refine ⟨49214014739556042250477855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262474745277632225335881893 49214014739556042250477855)
    ·
      refine ⟨73821022109334063375716783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49214014739556042250477855 73821022109334063375716783)
      ·
        refine ⟨110731533164001095063575175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73821022109334063375716783 110731533164001095063575175)
        ·
          refine ⟨166097299746001642595362763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110731533164001095063575175 166097299746001642595362763)
          ·
            refine ⟨249145949619002463893044145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166097299746001642595362763 249145949619002463893044145)
            ·
              refine ⟨186859462214251847919783109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249145949619002463893044145 186859462214251847919783109)
              ·
                refine ⟨35036149165172221484959333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186859462214251847919783109 35036149165172221484959333)
                ·
                  refine ⟨6569277968469791528429875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35036149165172221484959333 6569277968469791528429875)
                  ·
                    refine ⟨9853916952704687292644813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6569277968469791528429875 9853916952704687292644813)
                    ·
                      refine ⟨3695218857264257734741805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9853916952704687292644813 3695218857264257734741805)
                      ·
                        rfl

theorem cell23_7196413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_7196413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196413 prefixEnd_7196413 := by exact prefixLift 7196413
  have htrace : WordTrace (prefixWord ++ tailWord_7196413) baseStart_7196413 baseEnd_7196413 := by
    simpa [prefixWord, tailWord_7196413, baseEnd_7196413] using wordTrace_append hprefix tailTrace_7196413
  have hstable : (prefixWord ++ tailWord_7196413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196413).length < 2 ^ (prefixWord ++ tailWord_7196413).sum := by decide
  have hdescent : baseEnd_7196413 < baseStart_7196413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196430 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_7196430 : Nat := 118140960795 + 7196430 * 2 ^ 59
def prefixEnd_7196430 : Nat := 4983230072969 + 3 ^ 40 * 7196430 * 2
def baseEnd_7196430 : Nat := 3695227586435384168229227

theorem tailTrace_7196430 : CollatzResearch.WordTrace tailWord_7196430 prefixEnd_7196430 3695227586435384168229227 := by
  unfold tailWord_7196430
  simp only [CollatzResearch.WordTrace]
  refine ⟨32809420664821329654906343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174983576879047091492833829 32809420664821329654906343)
  ·
    refine ⟨49214130997231994482359515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32809420664821329654906343 49214130997231994482359515)
    ·
      refine ⟨73821196495847991723539273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49214130997231994482359515 73821196495847991723539273)
      ·
        refine ⟨55365897371885993792654455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73821196495847991723539273 55365897371885993792654455)
        ·
          refine ⟨83048846057828990688981683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55365897371885993792654455 83048846057828990688981683)
          ·
            refine ⟨124573269086743486033472525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83048846057828990688981683 124573269086743486033472525)
            ·
              refine ⟨46714975907528807262552197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124573269086743486033472525 46714975907528807262552197)
              ·
                refine ⟨8759057982661651361728537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46714975907528807262552197 8759057982661651361728537)
                ·
                  refine ⟨6569293486996238521296403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8759057982661651361728537 6569293486996238521296403)
                  ·
                    refine ⟨9853940230494357781944605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6569293486996238521296403 9853940230494357781944605)
                    ·
                      refine ⟨3695227586435384168229227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9853940230494357781944605 3695227586435384168229227)
                      ·
                        rfl

theorem cell23_7196430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_7196430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196430 prefixEnd_7196430 := by exact prefixLift 7196430
  have htrace : WordTrace (prefixWord ++ tailWord_7196430) baseStart_7196430 baseEnd_7196430 := by
    simpa [prefixWord, tailWord_7196430, baseEnd_7196430] using wordTrace_append hprefix tailTrace_7196430
  have hstable : (prefixWord ++ tailWord_7196430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196430).length < 2 ^ (prefixWord ++ tailWord_7196430).sum := by decide
  have hdescent : baseEnd_7196430 < baseStart_7196430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196474 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2]
def baseStart_7196474 : Nat := 118140960795 + 7196474 * 2 ^ 59
def prefixEnd_7196474 : Nat := 4983230072969 + 3 ^ 40 * 7196474 * 2
def baseEnd_7196474 : Nat := 3695250179584181996079025

theorem tailTrace_7196474 : CollatzResearch.WordTrace tailWord_7196474 prefixEnd_7196474 3695250179584181996079025 := by
  unfold tailWord_7196474
  simp only [CollatzResearch.WordTrace]
  refine ⟨65619242532602808188463119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174984646753607488502568317 65619242532602808188463119)
  ·
    refine ⟨98428863798904212282694679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65619242532602808188463119 98428863798904212282694679)
    ·
      refine ⟨147643295698356318424042019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98428863798904212282694679 147643295698356318424042019)
      ·
        refine ⟨221464943547534477636063029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147643295698356318424042019 221464943547534477636063029)
        ·
          refine ⟨20762338457581357278380909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221464943547534477636063029 20762338457581357278380909)
          ·
            refine ⟨7785876921593008979392841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20762338457581357278380909 7785876921593008979392841)
            ·
              refine ⟨5839407691194756734544631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7785876921593008979392841 5839407691194756734544631)
              ·
                refine ⟨8759111536792135101816947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5839407691194756734544631 8759111536792135101816947)
                ·
                  refine ⟨13138667305188202652725421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8759111536792135101816947 13138667305188202652725421)
                  ·
                    refine ⟨4927000239445575994772033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13138667305188202652725421 4927000239445575994772033)
                    ·
                      refine ⟨3695250179584181996079025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927000239445575994772033 3695250179584181996079025)
                      ·
                        rfl

theorem cell23_7196474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2].length) (baseStart_7196474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196474 prefixEnd_7196474 := by exact prefixLift 7196474
  have htrace : WordTrace (prefixWord ++ tailWord_7196474) baseStart_7196474 baseEnd_7196474 := by
    simpa [prefixWord, tailWord_7196474, baseEnd_7196474] using wordTrace_append hprefix tailTrace_7196474
  have hstable : (prefixWord ++ tailWord_7196474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196474).length < 2 ^ (prefixWord ++ tailWord_7196474).sum := by decide
  have hdescent : baseEnd_7196474 < baseStart_7196474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196487 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 2, 2, 2]
def baseStart_7196487 : Nat := 118140960795 + 7196487 * 2 ^ 59
def prefixEnd_7196487 : Nat := 4983230072969 + 3 ^ 40 * 7196487 * 2
def baseEnd_7196487 : Nat := 3695256854832690445216465

theorem tailTrace_7196487 : CollatzResearch.WordTrace tailWord_7196487 prefixEnd_7196487 3695256854832690445216465 := by
  unfold tailWord_7196487
  simp only [CollatzResearch.WordTrace]
  refine ⟨262477444279364135974075715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174984962852909423982717143 262477444279364135974075715)
  ·
    refine ⟨393716166419046203961113573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262477444279364135974075715 393716166419046203961113573)
    ·
      refine ⟨73821781203571163242708795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393716166419046203961113573 73821781203571163242708795)
      ·
        refine ⟨110732671805356744864063193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73821781203571163242708795 110732671805356744864063193)
        ·
          refine ⟨83049503854017558648047395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110732671805356744864063193 83049503854017558648047395)
          ·
            refine ⟨124574255781026337972071093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83049503854017558648047395 124574255781026337972071093)
            ·
              refine ⟨11678836479471219184881665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124574255781026337972071093 11678836479471219184881665)
              ·
                refine ⟨8759127359603414388661249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11678836479471219184881665 8759127359603414388661249)
                ·
                  refine ⟨6569345519702560791495937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8759127359603414388661249 6569345519702560791495937)
                  ·
                    refine ⟨4927009139776920593621953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6569345519702560791495937 4927009139776920593621953)
                    ·
                      refine ⟨3695256854832690445216465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927009139776920593621953 3695256854832690445216465)
                      ·
                        rfl

theorem cell23_7196487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_7196487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196487 prefixEnd_7196487 := by exact prefixLift 7196487
  have htrace : WordTrace (prefixWord ++ tailWord_7196487) baseStart_7196487 baseEnd_7196487 := by
    simpa [prefixWord, tailWord_7196487, baseEnd_7196487] using wordTrace_append hprefix tailTrace_7196487
  have hstable : (prefixWord ++ tailWord_7196487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196487).length < 2 ^ (prefixWord ++ tailWord_7196487).sum := by decide
  have hdescent : baseEnd_7196487 < baseStart_7196487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196506 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_7196506 : Nat := 118140960795 + 7196506 * 2 ^ 59
def prefixEnd_7196506 : Nat := 4983230072969 + 3 ^ 40 * 7196506 * 2
def baseEnd_7196506 : Nat := 1231755536988375290292959

theorem tailTrace_7196506 : CollatzResearch.WordTrace tailWord_7196506 prefixEnd_7196506 1231755536988375290292959 := by
  unfold tailWord_7196506
  simp only [CollatzResearch.WordTrace]
  refine ⟨65619534316573825554754343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174985424844196868146011581 65619534316573825554754343)
  ·
    refine ⟨98429301474860738332131515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65619534316573825554754343 98429301474860738332131515)
    ·
      refine ⟨147643952212291107498197273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98429301474860738332131515 147643952212291107498197273)
      ·
        refine ⟨110732964159218330623647955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147643952212291107498197273 110732964159218330623647955)
        ·
          refine ⟨166099446238827495935471933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110732964159218330623647955 166099446238827495935471933)
          ·
            refine ⟨62287292339560310975801975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166099446238827495935471933 62287292339560310975801975)
            ·
              refine ⟨93430938509340466463702963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62287292339560310975801975 93430938509340466463702963)
              ·
                refine ⟨140146407764010699695554445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93430938509340466463702963 140146407764010699695554445)
                ·
                  refine ⟨52554902911504012385832917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140146407764010699695554445 52554902911504012385832917)
                  ·
                    refine ⟨1231755536988375290292959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52554902911504012385832917 1231755536988375290292959)
                    ·
                      rfl

theorem cell23_7196506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_7196506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196506 prefixEnd_7196506 := by exact prefixLift 7196506
  have htrace : WordTrace (prefixWord ++ tailWord_7196506) baseStart_7196506 baseEnd_7196506 := by
    simpa [prefixWord, tailWord_7196506, baseEnd_7196506] using wordTrace_append hprefix tailTrace_7196506
  have hstable : (prefixWord ++ tailWord_7196506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196506).length < 2 ^ (prefixWord ++ tailWord_7196506).sum := by decide
  have hdescent : baseEnd_7196506 < baseStart_7196506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196533 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_7196533 : Nat := 118140960795 + 7196533 * 2 ^ 59
def prefixEnd_7196533 : Nat := 4983230072969 + 3 ^ 40 * 7196533 * 2
def baseEnd_7196533 : Nat := 3695280474942797265241253

theorem tailTrace_7196533 : CollatzResearch.WordTrace tailWord_7196533 prefixEnd_7196533 3695280474942797265241253 := by
  unfold tailWord_7196533
  simp only [CollatzResearch.WordTrace]
  refine ⟨262479122037197485830250253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174986081358131657220166835 262479122037197485830250253)
  ·
    refine ⟨98429670763949057186343845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262479122037197485830250253 98429670763949057186343845)
    ·
      refine ⟨18455563268240448222439471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98429670763949057186343845 18455563268240448222439471)
      ·
        refine ⟨27683344902360672333659207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18455563268240448222439471 27683344902360672333659207)
        ·
          refine ⟨41525017353541008500488811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27683344902360672333659207 41525017353541008500488811)
          ·
            refine ⟨62287526030311512750733217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41525017353541008500488811 62287526030311512750733217)
            ·
              refine ⟨46715644522733634563049913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62287526030311512750733217 46715644522733634563049913)
              ·
                refine ⟨35036733392050225922287435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46715644522733634563049913 35036733392050225922287435)
                ·
                  refine ⟨52555100088075338883431153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35036733392050225922287435 52555100088075338883431153)
                  ·
                    refine ⟨39416325066056504162573365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52555100088075338883431153 39416325066056504162573365)
                    ·
                      refine ⟨3695280474942797265241253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39416325066056504162573365 3695280474942797265241253)
                      ·
                        rfl

theorem cell23_7196533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_7196533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196533 prefixEnd_7196533 := by exact prefixLift 7196533
  have htrace : WordTrace (prefixWord ++ tailWord_7196533) baseStart_7196533 baseEnd_7196533 := by
    simpa [prefixWord, tailWord_7196533, baseEnd_7196533] using wordTrace_append hprefix tailTrace_7196533
  have hstable : (prefixWord ++ tailWord_7196533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196533).length < 2 ^ (prefixWord ++ tailWord_7196533).sum := by decide
  have hdescent : baseEnd_7196533 < baseStart_7196533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196574 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_7196574 : Nat := 118140960795 + 7196574 * 2 ^ 59
def prefixEnd_7196574 : Nat := 4983230072969 + 3 ^ 40 * 7196574 * 2
def baseEnd_7196574 : Nat := 1231767175883210534942855

theorem tailTrace_7196574 : CollatzResearch.WordTrace tailWord_7196574 prefixEnd_7196574 1231767175883210534942855 := by
  unfold tailWord_7196574
  simp only [CollatzResearch.WordTrace]
  refine ⟨32810077178756118729061597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174987078286699299888328517 32810077178756118729061597)
  ·
    refine ⟨12303778942033544523398099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32810077178756118729061597 12303778942033544523398099)
    ·
      refine ⟨18455668413050316785097149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12303778942033544523398099 18455668413050316785097149)
      ·
        refine ⟨6920875654893868794411431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18455668413050316785097149 6920875654893868794411431)
        ·
          refine ⟨10381313482340803191617147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6920875654893868794411431 10381313482340803191617147)
          ·
            refine ⟨15571970223511204787425721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10381313482340803191617147 15571970223511204787425721)
            ·
              refine ⟨11678977667633403590569291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15571970223511204787425721 11678977667633403590569291)
              ·
                refine ⟨17518466501450105385853937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11678977667633403590569291 17518466501450105385853937)
                ·
                  refine ⟨13138849876087579039390453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17518466501450105385853937 13138849876087579039390453)
                  ·
                    refine ⟨1231767175883210534942855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13138849876087579039390453 1231767175883210534942855)
                    ·
                      rfl

theorem cell23_7196574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_7196574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196574 prefixEnd_7196574 := by exact prefixLift 7196574
  have htrace : WordTrace (prefixWord ++ tailWord_7196574) baseStart_7196574 baseEnd_7196574 := by
    simpa [prefixWord, tailWord_7196574, baseEnd_7196574] using wordTrace_append hprefix tailTrace_7196574
  have hstable : (prefixWord ++ tailWord_7196574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196574).length < 2 ^ (prefixWord ++ tailWord_7196574).sum := by decide
  have hdescent : baseEnd_7196574 < baseStart_7196574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196577 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_7196577 : Nat := 118140960795 + 7196577 * 2 ^ 59
def prefixEnd_7196577 : Nat := 4983230072969 + 3 ^ 40 * 7196577 * 2
def baseEnd_7196577 : Nat := 3695303068091595093091051

theorem tailTrace_7196577 : CollatzResearch.WordTrace tailWord_7196577 prefixEnd_7196577 3695303068091595093091051 := by
  unfold tailWord_7196577
  simp only [CollatzResearch.WordTrace]
  refine ⟨262480726849038081344851985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174987151232692054229901323 262480726849038081344851985)
  ·
    refine ⟨196860545136778561008638989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262480726849038081344851985 196860545136778561008638989)
    ·
      refine ⟨73822704426291960378239621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196860545136778561008638989 73822704426291960378239621)
      ·
        refine ⟨13841757079929742570919929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73822704426291960378239621 13841757079929742570919929)
        ·
          refine ⟨10381317809947306928189947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13841757079929742570919929 10381317809947306928189947)
          ·
            refine ⟨15571976714920960392284921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10381317809947306928189947 15571976714920960392284921)
            ·
              refine ⟨11678982536190720294213691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15571976714920960392284921 11678982536190720294213691)
              ·
                refine ⟨17518473804286080441320537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11678982536190720294213691 17518473804286080441320537)
                ·
                  refine ⟨13138855353214560330990403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17518473804286080441320537 13138855353214560330990403)
                  ·
                    refine ⟨19708283029821840496485605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13138855353214560330990403 19708283029821840496485605)
                    ·
                      refine ⟨3695303068091595093091051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19708283029821840496485605 3695303068091595093091051)
                      ·
                        rfl

theorem cell23_7196577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_7196577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196577 prefixEnd_7196577 := by exact prefixLift 7196577
  have htrace : WordTrace (prefixWord ++ tailWord_7196577) baseStart_7196577 baseEnd_7196577 := by
    simpa [prefixWord, tailWord_7196577, baseEnd_7196577] using wordTrace_append hprefix tailTrace_7196577
  have hstable : (prefixWord ++ tailWord_7196577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196577).length < 2 ^ (prefixWord ++ tailWord_7196577).sum := by decide
  have hdescent : baseEnd_7196577 < baseStart_7196577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196580 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_7196580 : Nat := 118140960795 + 7196580 * 2 ^ 59
def prefixEnd_7196580 : Nat := 4983230072969 + 3 ^ 40 * 7196580 * 2
def baseEnd_7196580 : Nat := 3695304608533558581353537

theorem tailTrace_7196580 : CollatzResearch.WordTrace tailWord_7196580 prefixEnd_7196580 3695304608533558581353537 := by
  unfold tailWord_7196580
  simp only [CollatzResearch.WordTrace]
  refine ⟨131240418134013606428605597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174987224178684808571474129 131240418134013606428605597)
  ·
    refine ⟨49215156800255102410727099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131240418134013606428605597 49215156800255102410727099)
    ·
      refine ⟨73822735200382653616090649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49215156800255102410727099 73822735200382653616090649)
      ·
        refine ⟨55367051400286990212067987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73822735200382653616090649 55367051400286990212067987)
        ·
          refine ⟨83050577100430485318101981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55367051400286990212067987 83050577100430485318101981)
          ·
            refine ⟨31143966412661431994288243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83050577100430485318101981 31143966412661431994288243)
            ·
              refine ⟨46715949618992147991432365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31143966412661431994288243 46715949618992147991432365)
              ·
                refine ⟨17518481107122055496787137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46715949618992147991432365 17518481107122055496787137)
                ·
                  refine ⟨13138860830341541622590353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17518481107122055496787137 13138860830341541622590353)
                  ·
                    refine ⟨9854145622756156216942765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13138860830341541622590353 9854145622756156216942765)
                    ·
                      refine ⟨3695304608533558581353537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9854145622756156216942765 3695304608533558581353537)
                      ·
                        rfl

theorem cell23_7196580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_7196580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196580 prefixEnd_7196580 := by exact prefixLift 7196580
  have htrace : WordTrace (prefixWord ++ tailWord_7196580) baseStart_7196580 baseEnd_7196580 := by
    simpa [prefixWord, tailWord_7196580, baseEnd_7196580] using wordTrace_append hprefix tailTrace_7196580
  have hstable : (prefixWord ++ tailWord_7196580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196580).length < 2 ^ (prefixWord ++ tailWord_7196580).sum := by decide
  have hdescent : baseEnd_7196580 < baseStart_7196580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196644 : List Nat := [2, 3, 1, 1, 1, 1, 6, 3, 1, 1, 3]
def baseStart_7196644 : Nat := 118140960795 + 7196644 * 2 ^ 59
def prefixEnd_7196644 : Nat := 4983230072969 + 3 ^ 40 * 7196644 * 2
def baseEnd_7196644 : Nat := 3695337471295446330953243

theorem tailTrace_7196644 : CollatzResearch.WordTrace tailWord_7196644 prefixEnd_7196644 3695337471295446330953243 := by
  unfold tailWord_7196644
  simp only [CollatzResearch.WordTrace]
  refine ⟨131241585269897675893770493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174988780359863567858360657 131241585269897675893770493)
  ·
    refine ⟨49215594476211628460163935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131241585269897675893770493 49215594476211628460163935)
    ·
      refine ⟨73823391714317442690245903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49215594476211628460163935 73823391714317442690245903)
      ·
        refine ⟨110735087571476164035368855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73823391714317442690245903 110735087571476164035368855)
        ·
          refine ⟨166102631357214246053053283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110735087571476164035368855 166102631357214246053053283)
          ·
            refine ⟨249153947035821369079579925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166102631357214246053053283 249153947035821369079579925)
            ·
              refine ⟨11679091267304126675605309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 249153947035821369079579925 11679091267304126675605309)
              ·
                refine ⟨4379659225239047503351991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11679091267304126675605309 4379659225239047503351991)
                ·
                  refine ⟨6569488837858571255027987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379659225239047503351991 6569488837858571255027987)
                  ·
                    refine ⟨9854233256787856882541981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6569488837858571255027987 9854233256787856882541981)
                    ·
                      refine ⟨3695337471295446330953243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9854233256787856882541981 3695337471295446330953243)
                      ·
                        rfl

theorem cell23_7196644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_7196644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196644 prefixEnd_7196644 := by exact prefixLift 7196644
  have htrace : WordTrace (prefixWord ++ tailWord_7196644) baseStart_7196644 baseEnd_7196644 := by
    simpa [prefixWord, tailWord_7196644, baseEnd_7196644] using wordTrace_append hprefix tailTrace_7196644
  have hstable : (prefixWord ++ tailWord_7196644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196644).length < 2 ^ (prefixWord ++ tailWord_7196644).sum := by decide
  have hdescent : baseEnd_7196644 < baseStart_7196644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196647 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 1, 5]
def baseStart_7196647 : Nat := 118140960795 + 7196647 * 2 ^ 59
def prefixEnd_7196647 : Nat := 4983230072969 + 3 ^ 40 * 7196647 * 2
def baseEnd_7196647 : Nat := 1231779670579136606405243

theorem tailTrace_7196647 : CollatzResearch.WordTrace tailWord_7196647 prefixEnd_7196647 1231779670579136606405243 := by
  unfold tailWord_7196647
  simp only [CollatzResearch.WordTrace]
  refine ⟨262483279958784483299900195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174988853305856322199933463 262483279958784483299900195)
  ·
    refine ⟨393724919938176724949850293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262483279958784483299900195 393724919938176724949850293)
    ·
      refine ⟨36911711244204067964048465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 393724919938176724949850293 36911711244204067964048465)
      ·
        refine ⟨27683783433153050973036349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36911711244204067964048465 27683783433153050973036349)
        ·
          refine ⟨10381418787432394114888631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27683783433153050973036349 10381418787432394114888631)
          ·
            refine ⟨15572128181148591172332947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10381418787432394114888631 15572128181148591172332947)
            ·
              refine ⟨23358192271722886758499421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15572128181148591172332947 23358192271722886758499421)
              ·
                refine ⟨8759322101896082534437283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23358192271722886758499421 8759322101896082534437283)
                ·
                  refine ⟨13138983152844123801655925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8759322101896082534437283 13138983152844123801655925)
                  ·
                    refine ⟨1231779670579136606405243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13138983152844123801655925 1231779670579136606405243)
                    ·
                      rfl

theorem cell23_7196647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_7196647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196647 prefixEnd_7196647 := by exact prefixLift 7196647
  have htrace : WordTrace (prefixWord ++ tailWord_7196647) baseStart_7196647 baseEnd_7196647 := by
    simpa [prefixWord, tailWord_7196647, baseEnd_7196647] using wordTrace_append hprefix tailTrace_7196647
  have hstable : (prefixWord ++ tailWord_7196647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196647).length < 2 ^ (prefixWord ++ tailWord_7196647).sum := by decide
  have hdescent : baseEnd_7196647 < baseStart_7196647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196667 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 3, 2, 2]
def baseStart_7196667 : Nat := 118140960795 + 7196667 * 2 ^ 59
def prefixEnd_7196667 : Nat := 4983230072969 + 3 ^ 40 * 7196667 * 2
def baseEnd_7196667 : Nat := 3695349281350499740965637

theorem tailTrace_7196667 : CollatzResearch.WordTrace tailWord_7196667 prefixEnd_7196667 3695349281350499740965637 := by
  unfold tailWord_7196667
  simp only [CollatzResearch.WordTrace]
  refine ⟨262484009418712026715628255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174989339612474684477085503 262484009418712026715628255)
  ·
    refine ⟨393726014128068040073442383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262484009418712026715628255 393726014128068040073442383)
    ·
      refine ⟨590589021192102060110163575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393726014128068040073442383 590589021192102060110163575)
      ·
        refine ⟨885883531788153090165245363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590589021192102060110163575 885883531788153090165245363)
        ·
          refine ⟨1328825297682229635247868045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885883531788153090165245363 1328825297682229635247868045)
          ·
            refine ⟨498309486630836113217950517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1328825297682229635247868045 498309486630836113217950517)
            ·
              refine ⟨46716514371640885614182861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 498309486630836113217950517 46716514371640885614182861)
              ·
                refine ⟨17518692889365332105318573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46716514371640885614182861 17518692889365332105318573)
                ·
                  refine ⟨6569509833511999539494465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17518692889365332105318573 6569509833511999539494465)
                  ·
                    refine ⟨4927132375133999654620849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6569509833511999539494465 4927132375133999654620849)
                    ·
                      refine ⟨3695349281350499740965637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927132375133999654620849 3695349281350499740965637)
                      ·
                        rfl

theorem cell23_7196667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 2, 2].length) (baseStart_7196667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196667 prefixEnd_7196667 := by exact prefixLift 7196667
  have htrace : WordTrace (prefixWord ++ tailWord_7196667) baseStart_7196667 baseEnd_7196667 := by
    simpa [prefixWord, tailWord_7196667, baseEnd_7196667] using wordTrace_append hprefix tailTrace_7196667
  have hstable : (prefixWord ++ tailWord_7196667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196667).length < 2 ^ (prefixWord ++ tailWord_7196667).sum := by decide
  have hdescent : baseEnd_7196667 < baseStart_7196667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196673 : List Nat := [1, 2, 4, 1, 2, 1, 2, 10]
def baseStart_7196673 : Nat := 118140960795 + 7196673 * 2 ^ 59
def prefixEnd_7196673 : Nat := 4983230072969 + 3 ^ 40 * 7196673 * 2
def baseEnd_7196673 : Nat := 136864902304978767314467

theorem tailTrace_7196673 : CollatzResearch.WordTrace tailWord_7196673 prefixEnd_7196673 136864902304978767314467 := by
  unfold tailWord_7196673
  simp only [CollatzResearch.WordTrace]
  refine ⟨262484228256690289740346673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174989485504460193160231115 262484228256690289740346673)
  ·
    refine ⟨196863171192517717305260005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262484228256690289740346673 196863171192517717305260005)
    ·
      refine ⟨36911844598597071994736251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196863171192517717305260005 36911844598597071994736251)
      ·
        refine ⟨55367766897895607992104377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36911844598597071994736251 55367766897895607992104377)
        ·
          refine ⟨41525825173421705994078283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55367766897895607992104377 41525825173421705994078283)
          ·
            refine ⟨62288737760132558991117425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41525825173421705994078283 62288737760132558991117425)
            ·
              refine ⟨46716553320099419243338069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62288737760132558991117425 46716553320099419243338069)
              ·
                refine ⟨136864902304978767314467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46716553320099419243338069 136864902304978767314467)
                ·
                  rfl

theorem cell23_7196673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 10].length) (baseStart_7196673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196673 prefixEnd_7196673 := by exact prefixLift 7196673
  have htrace : WordTrace (prefixWord ++ tailWord_7196673) baseStart_7196673 baseEnd_7196673 := by
    simpa [prefixWord, tailWord_7196673, baseEnd_7196673] using wordTrace_append hprefix tailTrace_7196673
  have hstable : (prefixWord ++ tailWord_7196673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196673).length < 2 ^ (prefixWord ++ tailWord_7196673).sum := by decide
  have hdescent : baseEnd_7196673 < baseStart_7196673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196757 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 3, 4, 2]
def baseStart_7196757 : Nat := 118140960795 + 7196757 * 2 ^ 59
def prefixEnd_7196757 : Nat := 4983230072969 + 3 ^ 40 * 7196757 * 2
def baseEnd_7196757 : Nat := 3695395494609404388840223

theorem tailTrace_7196757 : CollatzResearch.WordTrace tailWord_7196757 prefixEnd_7196757 3695395494609404388840223 := by
  unfold tailWord_7196757
  simp only [CollatzResearch.WordTrace]
  refine ⟨262487291988385972086404525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174991527992257314724269683 262487291988385972086404525)
  ·
    refine ⟨98432734495644739532401697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262487291988385972086404525 98432734495644739532401697)
    ·
      refine ⟨73824550871733554649301273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98432734495644739532401697 73824550871733554649301273)
      ·
        refine ⟨55368413153800165986975955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73824550871733554649301273 55368413153800165986975955)
        ·
          refine ⟨83052619730700248980463933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55368413153800165986975955 83052619730700248980463933)
          ·
            refine ⟨31144732399012593367673975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83052619730700248980463933 31144732399012593367673975)
            ·
              refine ⟨46717098598518890051510963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31144732399012593367673975 46717098598518890051510963)
              ·
                refine ⟨70075647897778335077266445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46717098598518890051510963 70075647897778335077266445)
                ·
                  refine ⟨26278367961666875653974917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70075647897778335077266445 26278367961666875653974917)
                  ·
                    refine ⟨4927193992812539185120297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26278367961666875653974917 4927193992812539185120297)
                    ·
                      refine ⟨3695395494609404388840223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927193992812539185120297 3695395494609404388840223)
                      ·
                        rfl

theorem cell23_7196757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_7196757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196757 prefixEnd_7196757 := by exact prefixLift 7196757
  have htrace : WordTrace (prefixWord ++ tailWord_7196757) baseStart_7196757 baseEnd_7196757 := by
    simpa [prefixWord, tailWord_7196757, baseEnd_7196757] using wordTrace_append hprefix tailTrace_7196757
  have hstable : (prefixWord ++ tailWord_7196757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196757).length < 2 ^ (prefixWord ++ tailWord_7196757).sum := by decide
  have hdescent : baseEnd_7196757 < baseStart_7196757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196760 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_7196760 : Nat := 118140960795 + 7196760 * 2 ^ 59
def prefixEnd_7196760 : Nat := 4983230072969 + 3 ^ 40 * 7196760 * 2
def baseEnd_7196760 : Nat := 3695397035051367877102709

theorem tailTrace_7196760 : CollatzResearch.WordTrace tailWord_7196760 prefixEnd_7196760 3695397035051367877102709 := by
  unfold tailWord_7196760
  simp only [CollatzResearch.WordTrace]
  refine ⟨131243700703687551799381867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174991600938250069065842489 131243700703687551799381867)
  ·
    refine ⟨196865551055531327699072801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131243700703687551799381867 196865551055531327699072801)
    ·
      refine ⟨147649163291648495774304601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196865551055531327699072801 147649163291648495774304601)
      ·
        refine ⟨110736872468736371830728451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147649163291648495774304601 110736872468736371830728451)
        ·
          refine ⟨166105308703104557746092677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110736872468736371830728451 166105308703104557746092677)
          ·
            refine ⟨31144745381832104577392377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166105308703104557746092677 31144745381832104577392377)
            ·
              refine ⟨23358559036374078433044283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31144745381832104577392377 23358559036374078433044283)
              ·
                refine ⟨35037838554561117649566425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23358559036374078433044283 35037838554561117649566425)
                ·
                  refine ⟨26278378915920838237174819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35037838554561117649566425 26278378915920838237174819)
                  ·
                    refine ⟨39417568373881257355762229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26278378915920838237174819 39417568373881257355762229)
                    ·
                      refine ⟨3695397035051367877102709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39417568373881257355762229 3695397035051367877102709)
                      ·
                        rfl

theorem cell23_7196760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_7196760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196760 prefixEnd_7196760 := by exact prefixLift 7196760
  have htrace : WordTrace (prefixWord ++ tailWord_7196760) baseStart_7196760 baseEnd_7196760 := by
    simpa [prefixWord, tailWord_7196760, baseEnd_7196760] using wordTrace_append hprefix tailTrace_7196760
  have hstable : (prefixWord ++ tailWord_7196760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196760).length < 2 ^ (prefixWord ++ tailWord_7196760).sum := by decide
  have hdescent : baseEnd_7196760 < baseStart_7196760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196857 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 3, 4]
def baseStart_7196857 : Nat := 118140960795 + 7196857 * 2 ^ 59
def prefixEnd_7196857 : Nat := 4983230072969 + 3 ^ 40 * 7196857 * 2
def baseEnd_7196857 : Nat := 1231815614224951332529921

theorem tailTrace_7196857 : CollatzResearch.WordTrace tailWord_7196857 prefixEnd_7196857 1231815614224951332529921 := by
  unfold tailWord_7196857
  simp only [CollatzResearch.WordTrace]
  refine ⟨262490939288023689165044825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174993959525349126110029883 262490939288023689165044825)
  ·
    refine ⟨196868204466017766873783619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262490939288023689165044825 196868204466017766873783619)
    ·
      refine ⟨295302306699026650310675429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196868204466017766873783619 295302306699026650310675429)
      ·
        refine ⟨55369182506067496933251643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295302306699026650310675429 55369182506067496933251643)
        ·
          refine ⟨83053773759101245399877465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55369182506067496933251643 83053773759101245399877465)
          ·
            refine ⟨62290330319325934049908099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83053773759101245399877465 62290330319325934049908099)
            ·
              refine ⟨93435495478988901074862149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62290330319325934049908099 93435495478988901074862149)
              ·
                refine ⟨17519155402310418951536653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93435495478988901074862149 17519155402310418951536653)
                ·
                  refine ⟨6569683275866407106826245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17519155402310418951536653 6569683275866407106826245)
                  ·
                    refine ⟨1231815614224951332529921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6569683275866407106826245 1231815614224951332529921)
                    ·
                      rfl

theorem cell23_7196857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 4].length) (baseStart_7196857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196857 prefixEnd_7196857 := by exact prefixLift 7196857
  have htrace : WordTrace (prefixWord ++ tailWord_7196857) baseStart_7196857 baseEnd_7196857 := by
    simpa [prefixWord, tailWord_7196857, baseEnd_7196857] using wordTrace_append hprefix tailTrace_7196857
  have hstable : (prefixWord ++ tailWord_7196857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196857).length < 2 ^ (prefixWord ++ tailWord_7196857).sum := by decide
  have hdescent : baseEnd_7196857 < baseStart_7196857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196890 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_7196890 : Nat := 118140960795 + 7196890 * 2 ^ 59
def prefixEnd_7196890 : Nat := 4983230072969 + 3 ^ 40 * 7196890 * 2
def baseEnd_7196890 : Nat := 3695463787536452368477111

theorem tailTrace_7196890 : CollatzResearch.WordTrace tailWord_7196890 prefixEnd_7196890 3695463787536452368477111 := by
  unfold tailWord_7196890
  simp only [CollatzResearch.WordTrace]
  refine ⟨65623035724226033950249031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174994761931269423867330749 65623035724226033950249031)
  ·
    refine ⟨98434553586339050925373547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65623035724226033950249031 98434553586339050925373547)
    ·
      refine ⟨147651830379508576388060321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98434553586339050925373547 147651830379508576388060321)
      ·
        refine ⟨110738872784631432291045241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147651830379508576388060321 110738872784631432291045241)
        ·
          refine ⟨83054154588473574218283931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110738872784631432291045241 83054154588473574218283931)
          ·
            refine ⟨124581231882710361327425897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83054154588473574218283931 124581231882710361327425897)
            ·
              refine ⟨93435923912032770995569423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124581231882710361327425897 93435923912032770995569423)
              ·
                refine ⟨140153885868049156493354135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93435923912032770995569423 140153885868049156493354135)
                ·
                  refine ⟨210230828802073734740031203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140153885868049156493354135 210230828802073734740031203)
                  ·
                    refine ⟨315346243203110602110046805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210230828802073734740031203 315346243203110602110046805)
                    ·
                      refine ⟨3695463787536452368477111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 315346243203110602110046805 3695463787536452368477111)
                      ·
                        rfl

theorem cell23_7196890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_7196890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196890 prefixEnd_7196890 := by exact prefixLift 7196890
  have htrace : WordTrace (prefixWord ++ tailWord_7196890) baseStart_7196890 baseEnd_7196890 := by
    simpa [prefixWord, tailWord_7196890, baseEnd_7196890] using wordTrace_append hprefix tailTrace_7196890
  have hstable : (prefixWord ++ tailWord_7196890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196890).length < 2 ^ (prefixWord ++ tailWord_7196890).sum := by decide
  have hdescent : baseEnd_7196890 < baseStart_7196890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196900 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_7196900 : Nat := 118140960795 + 7196900 * 2 ^ 59
def prefixEnd_7196900 : Nat := 4983230072969 + 3 ^ 40 * 7196900 * 2
def baseEnd_7196900 : Nat := 1231822974114332443117355

theorem tailTrace_7196900 : CollatzResearch.WordTrace tailWord_7196900 prefixEnd_7196900 1231822974114332443117355 := by
  unfold tailWord_7196900
  simp only [CollatzResearch.WordTrace]
  refine ⟨131246253813433953754430077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174995005084578605005906769 131246253813433953754430077)
  ·
    refine ⟨49217345180037732657911279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131246253813433953754430077 49217345180037732657911279)
    ·
      refine ⟨73826017770056598986866919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49217345180037732657911279 73826017770056598986866919)
      ·
        refine ⟨110739026655084898480300379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73826017770056598986866919 110739026655084898480300379)
        ·
          refine ⟨166108539982627347720450569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110739026655084898480300379 166108539982627347720450569)
          ·
            refine ⟨124581404986970510790337927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166108539982627347720450569 124581404986970510790337927)
            ·
              refine ⟨186872107480455766185506891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124581404986970510790337927 186872107480455766185506891)
              ·
                refine ⟨280308161220683649278260337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186872107480455766185506891 280308161220683649278260337)
                ·
                  refine ⟨210231120915512736958695253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280308161220683649278260337 210231120915512736958695253)
                  ·
                    refine ⟨1231822974114332443117355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 210231120915512736958695253 1231822974114332443117355)
                    ·
                      rfl

theorem cell23_7196900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_7196900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196900 prefixEnd_7196900 := by exact prefixLift 7196900
  have htrace : WordTrace (prefixWord ++ tailWord_7196900) baseStart_7196900 baseEnd_7196900 := by
    simpa [prefixWord, tailWord_7196900, baseEnd_7196900] using wordTrace_append hprefix tailTrace_7196900
  have hstable : (prefixWord ++ tailWord_7196900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196900).length < 2 ^ (prefixWord ++ tailWord_7196900).sum := by decide
  have hdescent : baseEnd_7196900 < baseStart_7196900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196904 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 6]
def baseStart_7196904 : Nat := 118140960795 + 7196904 * 2 ^ 59
def prefixEnd_7196904 : Nat := 4983230072969 + 3 ^ 40 * 7196904 * 2
def baseEnd_7196904 : Nat := 410607886251735034855783

theorem tailTrace_7196904 : CollatzResearch.WordTrace tailWord_7196904 prefixEnd_7196904 410607886251735034855783 := by
  unfold tailWord_7196904
  simp only [CollatzResearch.WordTrace]
  refine ⟨131246326759426708096002883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174995102345902277461337177 131246326759426708096002883)
  ·
    refine ⟨196869490139140062144004325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131246326759426708096002883 196869490139140062144004325)
    ·
      refine ⟨36913029401088761652000811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196869490139140062144004325 36913029401088761652000811)
      ·
        refine ⟨55369544101633142478001217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36913029401088761652000811 55369544101633142478001217)
        ·
          refine ⟨41527158076224856858500913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55369544101633142478001217 41527158076224856858500913)
          ·
            refine ⟨31145368557168642643875685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41527158076224856858500913 31145368557168642643875685)
            ·
              refine ⟨5839756604469120495726691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31145368557168642643875685 5839756604469120495726691)
              ·
                refine ⟨8759634906703680743590037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5839756604469120495726691 8759634906703680743590037)
                ·
                  refine ⟨410607886251735034855783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8759634906703680743590037 410607886251735034855783)
                  ·
                    rfl

theorem cell23_7196904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 6].length) (baseStart_7196904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196904 prefixEnd_7196904 := by exact prefixLift 7196904
  have htrace : WordTrace (prefixWord ++ tailWord_7196904) baseStart_7196904 baseEnd_7196904 := by
    simpa [prefixWord, tailWord_7196904, baseEnd_7196904] using wordTrace_append hprefix tailTrace_7196904
  have hstable : (prefixWord ++ tailWord_7196904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196904).length < 2 ^ (prefixWord ++ tailWord_7196904).sum := by decide
  have hdescent : baseEnd_7196904 < baseStart_7196904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196931 : List Nat := [1, 1, 1, 3, 2, 3, 2, 5, 1, 1, 3]
def baseStart_7196931 : Nat := 118140960795 + 7196931 * 2 ^ 59
def prefixEnd_7196931 : Nat := 4983230072969 + 3 ^ 40 * 7196931 * 2
def baseEnd_7196931 : Nat := 3695484840243286708064423

theorem tailTrace_7196931 : CollatzResearch.WordTrace tailWord_7196931 prefixEnd_7196931 3695484840243286708064423 := by
  unfold tailWord_7196931
  simp only [CollatzResearch.WordTrace]
  refine ⟨262493638289755599803238647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174995758859837066535492431 262493638289755599803238647)
  ·
    refine ⟨393740457434633399704857971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262493638289755599803238647 393740457434633399704857971)
    ·
      refine ⟨590610686151950099557286957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393740457434633399704857971 590610686151950099557286957)
      ·
        refine ⟨221479007306981287333982609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 590610686151950099557286957 221479007306981287333982609)
        ·
          refine ⟨166109255480235965500486957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221479007306981287333982609 166109255480235965500486957)
          ·
            refine ⟨62290970805088487062682609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166109255480235965500486957 62290970805088487062682609)
            ·
              refine ⟨46718228103816365297011957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62290970805088487062682609 46718228103816365297011957)
              ·
                refine ⟨4379833884732784246594871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46718228103816365297011957 4379833884732784246594871)
                ·
                  refine ⟨6569750827099176369892307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379833884732784246594871 6569750827099176369892307)
                  ·
                    refine ⟨9854626240648764554838461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6569750827099176369892307 9854626240648764554838461)
                    ·
                      refine ⟨3695484840243286708064423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9854626240648764554838461 3695484840243286708064423)
                      ·
                        rfl

theorem cell23_7196931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 1, 1, 3].length) (baseStart_7196931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196931 prefixEnd_7196931 := by exact prefixLift 7196931
  have htrace : WordTrace (prefixWord ++ tailWord_7196931) baseStart_7196931 baseEnd_7196931 := by
    simpa [prefixWord, tailWord_7196931, baseEnd_7196931] using wordTrace_append hprefix tailTrace_7196931
  have hstable : (prefixWord ++ tailWord_7196931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196931).length < 2 ^ (prefixWord ++ tailWord_7196931).sum := by decide
  have hdescent : baseEnd_7196931 < baseStart_7196931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196947 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 4, 4]
def baseStart_7196947 : Nat := 118140960795 + 7196947 * 2 ^ 59
def prefixEnd_7196947 : Nat := 4983230072969 + 3 ^ 40 * 7196947 * 2
def baseEnd_7196947 : Nat := 1231831018644586215154783

theorem tailTrace_7196947 : CollatzResearch.WordTrace tailWord_7196947 prefixEnd_7196947 1231831018644586215154783 := by
  unfold tailWord_7196947
  simp only [CollatzResearch.WordTrace]
  refine ⟨262494221857697634535821095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174996147905131756357214063 262494221857697634535821095)
  ·
    refine ⟨393741332786546451803731643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262494221857697634535821095 393741332786546451803731643)
    ·
      refine ⟨590611999179819677705597465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393741332786546451803731643 590611999179819677705597465)
      ·
        refine ⟨442958999384864758279198099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590611999179819677705597465 442958999384864758279198099)
        ·
          refine ⟨664438499077297137418797149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442958999384864758279198099 664438499077297137418797149)
          ·
            refine ⟨249164437153986426532048931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 664438499077297137418797149 249164437153986426532048931)
            ·
              refine ⟨373746655730979639798073397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249164437153986426532048931 373746655730979639798073397)
              ·
                refine ⟨35038748974779341231069381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 373746655730979639798073397 35038748974779341231069381)
                ·
                  refine ⟨6569765432771126480825509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35038748974779341231069381 6569765432771126480825509)
                  ·
                    refine ⟨1231831018644586215154783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6569765432771126480825509 1231831018644586215154783)
                    ·
                      rfl

theorem cell23_7196947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 4].length) (baseStart_7196947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196947 prefixEnd_7196947 := by exact prefixLift 7196947
  have htrace : WordTrace (prefixWord ++ tailWord_7196947) baseStart_7196947 baseEnd_7196947 := by
    simpa [prefixWord, tailWord_7196947, baseEnd_7196947] using wordTrace_append hprefix tailTrace_7196947
  have hstable : (prefixWord ++ tailWord_7196947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196947).length < 2 ^ (prefixWord ++ tailWord_7196947).sum := by decide
  have hdescent : baseEnd_7196947 < baseStart_7196947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196964 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_7196964 : Nat := 118140960795 + 7196964 * 2 ^ 59
def prefixEnd_7196964 : Nat := 4983230072969 + 3 ^ 40 * 7196964 * 2
def baseEnd_7196964 : Nat := 1231833928368295026317257

theorem tailTrace_7196964 : CollatzResearch.WordTrace tailWord_7196964 prefixEnd_7196964 1231833928368295026317257 := by
  unfold tailWord_7196964
  simp only [CollatzResearch.WordTrace]
  refine ⟨131247420949318023219594973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174996561265757364292793297 131247420949318023219594973)
  ·
    refine ⟨49217782855994258707348115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131247420949318023219594973 49217782855994258707348115)
    ·
      refine ⟨73826674283991388061022173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49217782855994258707348115 73826674283991388061022173)
      ·
        refine ⟨27685002856496770522883315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73826674283991388061022173 27685002856496770522883315)
        ·
          refine ⟨41527504284745155784324973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27685002856496770522883315 41527504284745155784324973)
          ·
            refine ⟨15572814106779433419121865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41527504284745155784324973 15572814106779433419121865)
            ·
              refine ⟨11679610580084575064341399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15572814106779433419121865 11679610580084575064341399)
              ·
                refine ⟨17519415870126862596512099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11679610580084575064341399 17519415870126862596512099)
                ·
                  refine ⟨26279123805190293894768149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17519415870126862596512099 26279123805190293894768149)
                  ·
                    refine ⟨1231833928368295026317257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26279123805190293894768149 1231833928368295026317257)
                    ·
                      rfl

theorem cell23_7196964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_7196964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7196964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7196964 prefixEnd_7196964 := by exact prefixLift 7196964
  have htrace : WordTrace (prefixWord ++ tailWord_7196964) baseStart_7196964 baseEnd_7196964 := by
    simpa [prefixWord, tailWord_7196964, baseEnd_7196964] using wordTrace_append hprefix tailTrace_7196964
  have hstable : (prefixWord ++ tailWord_7196964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196964).length < 2 ^ (prefixWord ++ tailWord_7196964).sum := by decide
  have hdescent : baseEnd_7196964 < baseStart_7196964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197034 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7197034 : Nat := 118140960795 + 7197034 * 2 ^ 59
def prefixEnd_7197034 : Nat := 4983230072969 + 3 ^ 40 * 7197034 * 2
def baseEnd_7197034 : Nat := 3695537728750699805076449

theorem tailTrace_7197034 : CollatzResearch.WordTrace tailWord_7197034 prefixEnd_7197034 3695537728750699805076449 := by
  unfold tailWord_7197034
  simp only [CollatzResearch.WordTrace]
  refine ⟨65624348752095612098559539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174998263338921632262825437 65624348752095612098559539)
  ·
    refine ⟨98436523128143418147839309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65624348752095612098559539 98436523128143418147839309)
    ·
      refine ⟨36913696173053781805439741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98436523128143418147839309 36913696173053781805439741)
      ·
        refine ⟨13842636064895168177039903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36913696173053781805439741 13842636064895168177039903)
        ·
          refine ⟨20763954097342752265559855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13842636064895168177039903 20763954097342752265559855)
          ·
            refine ⟨31145931146014128398339783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20763954097342752265559855 31145931146014128398339783)
            ·
              refine ⟨46718896719021192597509675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31145931146014128398339783 46718896719021192597509675)
              ·
                refine ⟨70078345078531788896264513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46718896719021192597509675 70078345078531788896264513)
                ·
                  refine ⟨52558758808898841672198385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70078345078531788896264513 52558758808898841672198385)
                  ·
                    refine ⟨39419069106674131254148789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52558758808898841672198385 39419069106674131254148789)
                    ·
                      refine ⟨3695537728750699805076449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39419069106674131254148789 3695537728750699805076449)
                      ·
                        rfl

theorem cell23_7197034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7197034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197034 prefixEnd_7197034 := by exact prefixLift 7197034
  have htrace : WordTrace (prefixWord ++ tailWord_7197034) baseStart_7197034 baseEnd_7197034 := by
    simpa [prefixWord, tailWord_7197034, baseEnd_7197034] using wordTrace_append hprefix tailTrace_7197034
  have hstable : (prefixWord ++ tailWord_7197034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197034).length < 2 ^ (prefixWord ++ tailWord_7197034).sum := by decide
  have hdescent : baseEnd_7197034 < baseStart_7197034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197064 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_7197064 : Nat := 118140960795 + 7197064 * 2 ^ 59
def prefixEnd_7197064 : Nat := 4983230072969 + 3 ^ 40 * 7197064 * 2
def baseEnd_7197064 : Nat := 3695553133170334687701311

theorem tailTrace_7197064 : CollatzResearch.WordTrace tailWord_7197064 prefixEnd_7197064 3695553133170334687701311 := by
  unfold tailWord_7197064
  simp only [CollatzResearch.WordTrace]
  refine ⟨131249244599136881758915123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174998992798849175678553497 131249244599136881758915123)
  ·
    refine ⟨196873866898705322638372685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131249244599136881758915123 196873866898705322638372685)
    ·
      refine ⟨73827700087014495989389757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196873866898705322638372685 73827700087014495989389757)
      ·
        refine ⟨27685387532630435996021159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73827700087014495989389757 27685387532630435996021159)
        ·
          refine ⟨41528081298945653994031739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27685387532630435996021159 41528081298945653994031739)
          ·
            refine ⟨62292121948418480991047609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41528081298945653994031739 62292121948418480991047609)
            ·
              refine ⟨46719091461313860743285707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62292121948418480991047609 46719091461313860743285707)
              ·
                refine ⟨70078637191970791114928561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46719091461313860743285707 70078637191970791114928561)
                ·
                  refine ⟨52558977893978093336196421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70078637191970791114928561 52558977893978093336196421)
                  ·
                    refine ⟨9854808355120892500536829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52558977893978093336196421 9854808355120892500536829)
                    ·
                      refine ⟨3695553133170334687701311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9854808355120892500536829 3695553133170334687701311)
                      ·
                        rfl

theorem cell23_7197064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_7197064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197064 prefixEnd_7197064 := by exact prefixLift 7197064
  have htrace : WordTrace (prefixWord ++ tailWord_7197064) baseStart_7197064 baseEnd_7197064 := by
    simpa [prefixWord, tailWord_7197064, baseEnd_7197064] using wordTrace_append hprefix tailTrace_7197064
  have hstable : (prefixWord ++ tailWord_7197064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197064).length < 2 ^ (prefixWord ++ tailWord_7197064).sum := by decide
  have hdescent : baseEnd_7197064 < baseStart_7197064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197097 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 1, 7]
def baseStart_7197097 : Nat := 118140960795 + 7197097 * 2 ^ 59
def prefixEnd_7197097 : Nat := 4983230072969 + 3 ^ 40 * 7197097 * 2
def baseEnd_7197097 : Nat := 1231856692677311019529553

theorem tailTrace_7197097 : CollatzResearch.WordTrace tailWord_7197097 prefixEnd_7197097 1231856692677311019529553 := by
  unfold tailWord_7197097
  simp only [CollatzResearch.WordTrace]
  refine ⟨262499692807154210153781545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174999795204769473435854363 262499692807154210153781545)
  ·
    refine ⟨196874769605365657615336159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262499692807154210153781545 196874769605365657615336159)
    ·
      refine ⟨295312154408048486423004239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196874769605365657615336159 295312154408048486423004239)
      ·
        refine ⟨442968231612072729634506359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295312154408048486423004239 442968231612072729634506359)
        ·
          refine ⟨664452347418109094451759539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442968231612072729634506359 664452347418109094451759539)
          ·
            refine ⟨996678521127163641677639309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664452347418109094451759539 996678521127163641677639309)
            ·
              refine ⟨373754445422686365629114741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 996678521127163641677639309 373754445422686365629114741)
              ·
                refine ⟨35039479258376846777729507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 373754445422686365629114741 35039479258376846777729507)
                ·
                  refine ⟨52559218887565270166594261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35039479258376846777729507 52559218887565270166594261)
                  ·
                    refine ⟨1231856692677311019529553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52559218887565270166594261 1231856692677311019529553)
                    ·
                      rfl

theorem cell23_7197097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_7197097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197097 prefixEnd_7197097 := by exact prefixLift 7197097
  have htrace : WordTrace (prefixWord ++ tailWord_7197097) baseStart_7197097 baseEnd_7197097 := by
    simpa [prefixWord, tailWord_7197097, baseEnd_7197097] using wordTrace_append hprefix tailTrace_7197097
  have hstable : (prefixWord ++ tailWord_7197097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197097).length < 2 ^ (prefixWord ++ tailWord_7197097).sum := by decide
  have hdescent : baseEnd_7197097 < baseStart_7197097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197118 : List Nat := [4, 2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_7197118 : Nat := 118140960795 + 7197118 * 2 ^ 59
def prefixEnd_7197118 : Nat := 4983230072969 + 3 ^ 40 * 7197118 * 2
def baseEnd_7197118 : Nat := 410620095680630830714007

theorem tailTrace_7197118 : CollatzResearch.WordTrace tailWord_7197118 prefixEnd_7197118 410620095680630830714007 := by
  unfold tailWord_7197118
  simp only [CollatzResearch.WordTrace]
  refine ⟨32812557342509766342537001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175000305826718753826864005 32812557342509766342537001)
  ·
    refine ⟨24609418006882324756902751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32812557342509766342537001 24609418006882324756902751)
    ·
      refine ⟨36914127010323487135354127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24609418006882324756902751 36914127010323487135354127)
      ·
        refine ⟨55371190515485230703031191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36914127010323487135354127 55371190515485230703031191)
        ·
          refine ⟨83056785773227846054546787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55371190515485230703031191 83056785773227846054546787)
          ·
            refine ⟨124585178659841769081820181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83056785773227846054546787 124585178659841769081820181)
            ·
              refine ⟨5839930249680082925710321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124585178659841769081820181 5839930249680082925710321)
              ·
                refine ⟨4379947687260062194282741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5839930249680082925710321 4379947687260062194282741)
                ·
                  refine ⟨410620095680630830714007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4379947687260062194282741 410620095680630830714007)
                  ·
                    rfl

theorem cell23_7197118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_7197118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197118 prefixEnd_7197118 := by exact prefixLift 7197118
  have htrace : WordTrace (prefixWord ++ tailWord_7197118) baseStart_7197118 baseEnd_7197118 := by
    simpa [prefixWord, tailWord_7197118, baseEnd_7197118] using wordTrace_append hprefix tailTrace_7197118
  have hstable : (prefixWord ++ tailWord_7197118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197118).length < 2 ^ (prefixWord ++ tailWord_7197118).sum := by decide
  have hdescent : baseEnd_7197118 < baseStart_7197118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197134 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_7197134 : Nat := 118140960795 + 7197134 * 2 ^ 59
def prefixEnd_7197134 : Nat := 4983230072969 + 3 ^ 40 * 7197134 * 2
def baseEnd_7197134 : Nat := 3695589076816149413825989

theorem tailTrace_7197134 : CollatzResearch.WordTrace tailWord_7197134 prefixEnd_7197134 3695589076816149413825989 := by
  unfold tailWord_7197134
  simp only [CollatzResearch.WordTrace]
  refine ⟨32812630288502520684109807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175000694872013443648585637 32812630288502520684109807)
  ·
    refine ⟨49218945432753781026164711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32812630288502520684109807 49218945432753781026164711)
    ·
      refine ⟨73828418149130671539247067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49218945432753781026164711 73828418149130671539247067)
      ·
        refine ⟨110742627223696007308870601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73828418149130671539247067 110742627223696007308870601)
        ·
          refine ⟨83056970417772005481652951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110742627223696007308870601 83056970417772005481652951)
          ·
            refine ⟨124585455626658008222479427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83056970417772005481652951 124585455626658008222479427)
            ·
              refine ⟨186878183439987012333719141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124585455626658008222479427 186878183439987012333719141)
              ·
                refine ⟨35039659394997564812572339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186878183439987012333719141 35039659394997564812572339)
                ·
                  refine ⟨52559489092496347218858509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35039659394997564812572339 52559489092496347218858509)
                  ·
                    refine ⟨19709808409686130207071941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52559489092496347218858509 19709808409686130207071941)
                    ·
                      refine ⟨3695589076816149413825989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19709808409686130207071941 3695589076816149413825989)
                      ·
                        rfl

theorem cell23_7197134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_7197134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197134 prefixEnd_7197134 := by exact prefixLift 7197134
  have htrace : WordTrace (prefixWord ++ tailWord_7197134) baseStart_7197134 baseEnd_7197134 := by
    simpa [prefixWord, tailWord_7197134, baseEnd_7197134] using wordTrace_append hprefix tailTrace_7197134
  have hstable : (prefixWord ++ tailWord_7197134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197134).length < 2 ^ (prefixWord ++ tailWord_7197134).sum := by decide
  have hdescent : baseEnd_7197134 < baseStart_7197134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197151 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 4]
def baseStart_7197151 : Nat := 118140960795 + 7197151 * 2 ^ 59
def prefixEnd_7197151 : Nat := 4983230072969 + 3 ^ 40 * 7197151 * 2
def baseEnd_7197151 : Nat := 3695597805987275847313411

theorem tailTrace_7197151 : CollatzResearch.WordTrace tailWord_7197151 prefixEnd_7197151 3695597805987275847313411 := by
  unfold tailWord_7197151
  simp only [CollatzResearch.WordTrace]
  refine ⟨262501662348958577376247307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175001108232639051584164871 262501662348958577376247307)
  ·
    refine ⟨393752493523437866064370961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262501662348958577376247307 393752493523437866064370961)
    ·
      refine ⟨295314370142578399548278221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393752493523437866064370961 295314370142578399548278221)
      ·
        refine ⟨110742888803466899830604333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295314370142578399548278221 110742888803466899830604333)
        ·
          refine ⟨41528583301300087436476625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110742888803466899830604333 41528583301300087436476625)
          ·
            refine ⟨31146437475975065577357469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41528583301300087436476625 31146437475975065577357469)
            ·
              refine ⟨11679914053490649591509051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31146437475975065577357469 11679914053490649591509051)
              ·
                refine ⟨17519871080235974387263577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11679914053490649591509051 17519871080235974387263577)
                ·
                  refine ⟨13139903310176980790447683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17519871080235974387263577 13139903310176980790447683)
                  ·
                    refine ⟨19709854965265471185671525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13139903310176980790447683 19709854965265471185671525)
                    ·
                      refine ⟨3695597805987275847313411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19709854965265471185671525 3695597805987275847313411)
                      ·
                        rfl

theorem cell23_7197151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_7197151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197151 prefixEnd_7197151 := by exact prefixLift 7197151
  have htrace : WordTrace (prefixWord ++ tailWord_7197151) baseStart_7197151 baseEnd_7197151 := by
    simpa [prefixWord, tailWord_7197151, baseEnd_7197151] using wordTrace_append hprefix tailTrace_7197151
  have hstable : (prefixWord ++ tailWord_7197151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197151).length < 2 ^ (prefixWord ++ tailWord_7197151).sum := by decide
  have hdescent : baseEnd_7197151 < baseStart_7197151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197194 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_7197194 : Nat := 118140960795 + 7197194 * 2 ^ 59
def prefixEnd_7197194 : Nat := 4983230072969 + 3 ^ 40 * 7197194 * 2
def baseEnd_7197194 : Nat := 3695619885655419179075713

theorem tailTrace_7197194 : CollatzResearch.WordTrace tailWord_7197194 prefixEnd_7197194 3695619885655419179075713 := by
  unfold tailWord_7197194
  simp only [CollatzResearch.WordTrace]
  refine ⟨65625807671950698930015659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175002153791868530480041757 65625807671950698930015659)
  ·
    refine ⟨98438711507926048395023489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65625807671950698930015659 98438711507926048395023489)
    ·
      refine ⟨73829033630944536296267617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98438711507926048395023489 73829033630944536296267617)
      ·
        refine ⟨55371775223208402222200713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73829033630944536296267617 55371775223208402222200713)
        ·
          refine ⟨41528831417406301666650535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55371775223208402222200713 41528831417406301666650535)
          ·
            refine ⟨62293247126109452499975803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41528831417406301666650535 62293247126109452499975803)
            ·
              refine ⟨93439870689164178749963705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62293247126109452499975803 93439870689164178749963705)
              ·
                refine ⟨70079903016873134062472779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93439870689164178749963705 70079903016873134062472779)
                ·
                  refine ⟨105119854525309701093709169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70079903016873134062472779 105119854525309701093709169)
                  ·
                    refine ⟨78839890893982275820281877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105119854525309701093709169 78839890893982275820281877)
                    ·
                      refine ⟨3695619885655419179075713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78839890893982275820281877 3695619885655419179075713)
                      ·
                        rfl

theorem cell23_7197194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_7197194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197194 prefixEnd_7197194 := by exact prefixLift 7197194
  have htrace : WordTrace (prefixWord ++ tailWord_7197194) baseStart_7197194 baseEnd_7197194 := by
    simpa [prefixWord, tailWord_7197194, baseEnd_7197194] using wordTrace_append hprefix tailTrace_7197194
  have hstable : (prefixWord ++ tailWord_7197194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197194).length < 2 ^ (prefixWord ++ tailWord_7197194).sum := by decide
  have hdescent : baseEnd_7197194 < baseStart_7197194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197201 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 5, 1, 3]
def baseStart_7197201 : Nat := 118140960795 + 7197201 * 2 ^ 59
def prefixEnd_7197201 : Nat := 4983230072969 + 3 ^ 40 * 7197201 * 2
def baseEnd_7197201 : Nat := 3695623480020000651688181

theorem tailTrace_7197201 : CollatzResearch.WordTrace tailWord_7197201 prefixEnd_7197201 3695623480020000651688181 := by
  unfold tailWord_7197201
  simp only [CollatzResearch.WordTrace]
  refine ⟨262503485998777435915567457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175002323999184957277044971 262503485998777435915567457)
  ·
    refine ⟨196877614499083076936675593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262503485998777435915567457 196877614499083076936675593)
    ·
      refine ⟨147658210874312307702506695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196877614499083076936675593 147658210874312307702506695)
      ·
        refine ⟨221487316311468461553760043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147658210874312307702506695 221487316311468461553760043)
        ·
          refine ⟨332230974467202692330640065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221487316311468461553760043 332230974467202692330640065)
          ·
            refine ⟨249173230850402019247980049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332230974467202692330640065 249173230850402019247980049)
            ·
              refine ⟨186879923137801514435985037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249173230850402019247980049 186879923137801514435985037)
              ·
                refine ⟨70079971176675567913494389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186879923137801514435985037 70079971176675567913494389)
                ·
                  refine ⟨6569997297813334491890099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70079971176675567913494389 6569997297813334491890099)
                  ·
                    refine ⟨9854995946720001737835149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6569997297813334491890099 9854995946720001737835149)
                    ·
                      refine ⟨3695623480020000651688181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9854995946720001737835149 3695623480020000651688181)
                      ·
                        rfl

theorem cell23_7197201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_7197201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197201 prefixEnd_7197201 := by exact prefixLift 7197201
  have htrace : WordTrace (prefixWord ++ tailWord_7197201) baseStart_7197201 baseEnd_7197201 := by
    simpa [prefixWord, tailWord_7197201, baseEnd_7197201] using wordTrace_append hprefix tailTrace_7197201
  have hstable : (prefixWord ++ tailWord_7197201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197201).length < 2 ^ (prefixWord ++ tailWord_7197201).sum := by decide
  have hdescent : baseEnd_7197201 < baseStart_7197201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197211 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 8, 3, 2]
def baseStart_7197211 : Nat := 118140960795 + 7197211 * 2 ^ 59
def prefixEnd_7197211 : Nat := 4983230072969 + 3 ^ 40 * 7197211 * 2
def baseEnd_7197211 : Nat := 3695628614826545612563135

theorem tailTrace_7197211 : CollatzResearch.WordTrace tailWord_7197211 prefixEnd_7197211 3695628614826545612563135 := by
  unfold tailWord_7197211
  simp only [CollatzResearch.WordTrace]
  refine ⟨262503850728741207623431487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175002567152494138415620991 262503850728741207623431487)
  ·
    refine ⟨393755776093111811435147231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262503850728741207623431487 393755776093111811435147231)
    ·
      refine ⟨590633664139667717152720847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393755776093111811435147231 590633664139667717152720847)
      ·
        refine ⟨885950496209501575729081271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590633664139667717152720847 885950496209501575729081271)
        ·
          refine ⟨1328925744314252363593621907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885950496209501575729081271 1328925744314252363593621907)
          ·
            refine ⟨1993388616471378545390432861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328925744314252363593621907 1993388616471378545390432861)
            ·
              refine ⟨747520731176766954521412323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1993388616471378545390432861 747520731176766954521412323)
              ·
                refine ⟨1121281096765150431782118485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747520731176766954521412323 1121281096765150431782118485)
                ·
                  refine ⟨13140012852716606622446701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1121281096765150431782118485 13140012852716606622446701)
                  ·
                    refine ⟨4927504819768727483417513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13140012852716606622446701 4927504819768727483417513)
                    ·
                      refine ⟨3695628614826545612563135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927504819768727483417513 3695628614826545612563135)
                      ·
                        rfl

theorem cell23_7197211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 3, 2].length) (baseStart_7197211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197211 prefixEnd_7197211 := by exact prefixLift 7197211
  have htrace : WordTrace (prefixWord ++ tailWord_7197211) baseStart_7197211 baseEnd_7197211 := by
    simpa [prefixWord, tailWord_7197211, baseEnd_7197211] using wordTrace_append hprefix tailTrace_7197211
  have hstable : (prefixWord ++ tailWord_7197211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197211).length < 2 ^ (prefixWord ++ tailWord_7197211).sum := by decide
  have hdescent : baseEnd_7197211 < baseStart_7197211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197221 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 1, 5]
def baseStart_7197221 : Nat := 118140960795 + 7197221 * 2 ^ 59
def prefixEnd_7197221 : Nat := 4983230072969 + 3 ^ 40 * 7197221 * 2
def baseEnd_7197221 : Nat := 1231877916544363524479363

theorem tailTrace_7197221 : CollatzResearch.WordTrace tailWord_7197221 prefixEnd_7197221 1231877916544363524479363 := by
  unfold tailWord_7197221
  simp only [CollatzResearch.WordTrace]
  refine ⟨262504215458704979331295517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175002810305803319554197011 262504215458704979331295517)
  ·
    refine ⟨98439080797014367249235819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262504215458704979331295517 98439080797014367249235819)
    ·
      refine ⟨147658621195521550873853729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98439080797014367249235819 147658621195521550873853729)
      ·
        refine ⟨110743965896641163155390297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147658621195521550873853729 110743965896641163155390297)
        ·
          refine ⟨83057974422480872366542723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110743965896641163155390297 83057974422480872366542723)
          ·
            refine ⟨124586961633721308549814085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83057974422480872366542723 124586961633721308549814085)
            ·
              refine ⟨23360055306322745353090141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124586961633721308549814085 23360055306322745353090141)
              ·
                refine ⟨8760020739871029507408803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23360055306322745353090141 8760020739871029507408803)
                ·
                  refine ⟨13140031109806544261113205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8760020739871029507408803 13140031109806544261113205)
                  ·
                    refine ⟨1231877916544363524479363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13140031109806544261113205 1231877916544363524479363)
                    ·
                      rfl

theorem cell23_7197221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_7197221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197221 prefixEnd_7197221 := by exact prefixLift 7197221
  have htrace : WordTrace (prefixWord ++ tailWord_7197221) baseStart_7197221 baseEnd_7197221 := by
    simpa [prefixWord, tailWord_7197221, baseEnd_7197221] using wordTrace_append hprefix tailTrace_7197221
  have hstable : (prefixWord ++ tailWord_7197221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197221).length < 2 ^ (prefixWord ++ tailWord_7197221).sum := by decide
  have hdescent : baseEnd_7197221 < baseStart_7197221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197229 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7197229 : Nat := 118140960795 + 7197229 * 2 ^ 59
def prefixEnd_7197229 : Nat := 4983230072969 + 3 ^ 40 * 7197229 * 2
def baseEnd_7197229 : Nat := 1231879285826108847379351

theorem tailTrace_7197229 : CollatzResearch.WordTrace tailWord_7197229 prefixEnd_7197229 1231879285826108847379351 := by
  unfold tailWord_7197229
  simp only [CollatzResearch.WordTrace]
  refine ⟨262504507242675996697586741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175003004828450664465057827 262504507242675996697586741)
  ·
    refine ⟨24609797554000874690398757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262504507242675996697586741 24609797554000874690398757)
    ·
      refine ⟨4614337041375164004449767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24609797554000874690398757 4614337041375164004449767)
      ·
        refine ⟨6921505562062746006674651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4614337041375164004449767 6921505562062746006674651)
        ·
          refine ⟨10382258343094119010011977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6921505562062746006674651 10382258343094119010011977)
          ·
            refine ⟨7786693757320589257508983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10382258343094119010011977 7786693757320589257508983)
            ·
              refine ⟨11680040635980883886263475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7786693757320589257508983 11680040635980883886263475)
              ·
                refine ⟨17520060953971325829395213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11680040635980883886263475 17520060953971325829395213)
                ·
                  refine ⟨6570022857739247186023205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17520060953971325829395213 6570022857739247186023205)
                  ·
                    refine ⟨1231879285826108847379351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6570022857739247186023205 1231879285826108847379351)
                    ·
                      rfl

theorem cell23_7197229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7197229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197229 prefixEnd_7197229 := by exact prefixLift 7197229
  have htrace : WordTrace (prefixWord ++ tailWord_7197229) baseStart_7197229 baseEnd_7197229 := by
    simpa [prefixWord, tailWord_7197229, baseEnd_7197229] using wordTrace_append hprefix tailTrace_7197229
  have hstable : (prefixWord ++ tailWord_7197229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197229).length < 2 ^ (prefixWord ++ tailWord_7197229).sum := by decide
  have hdescent : baseEnd_7197229 < baseStart_7197229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197241 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7197241 : Nat := 118140960795 + 7197241 * 2 ^ 59
def prefixEnd_7197241 : Nat := 4983230072969 + 3 ^ 40 * 7197241 * 2
def baseEnd_7197241 : Nat := 3695644019246180495187997

theorem tailTrace_7197241 : CollatzResearch.WordTrace tailWord_7197241 prefixEnd_7197241 3695644019246180495187997 := by
  unfold tailWord_7197241
  simp only [CollatzResearch.WordTrace]
  refine ⟨262504944918632522747023577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175003296612421681831349051 262504944918632522747023577)
  ·
    refine ⟨196878708688974392060267683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262504944918632522747023577 196878708688974392060267683)
    ·
      refine ⟨295318063033461588090401525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196878708688974392060267683 295318063033461588090401525)
      ·
        refine ⟨27686068409387023883475143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295318063033461588090401525 27686068409387023883475143)
        ·
          refine ⟨41529102614080535825212715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27686068409387023883475143 41529102614080535825212715)
          ·
            refine ⟨62293653921120803737819073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41529102614080535825212715 62293653921120803737819073)
            ·
              refine ⟨46720240440840602803364305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62293653921120803737819073 46720240440840602803364305)
              ·
                refine ⟨35040180330630452102523229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46720240440840602803364305 35040180330630452102523229)
                ·
                  refine ⟨13140067623986419538446211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35040180330630452102523229 13140067623986419538446211)
                  ·
                    refine ⟨19710101435979629307669317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13140067623986419538446211 19710101435979629307669317)
                    ·
                      refine ⟨3695644019246180495187997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19710101435979629307669317 3695644019246180495187997)
                      ·
                        rfl

theorem cell23_7197241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7197241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197241 prefixEnd_7197241 := by exact prefixLift 7197241
  have htrace : WordTrace (prefixWord ++ tailWord_7197241) baseStart_7197241 baseEnd_7197241 := by
    simpa [prefixWord, tailWord_7197241, baseEnd_7197241] using wordTrace_append hprefix tailTrace_7197241
  have hstable : (prefixWord ++ tailWord_7197241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197241).length < 2 ^ (prefixWord ++ tailWord_7197241).sum := by decide
  have hdescent : baseEnd_7197241 < baseStart_7197241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197258 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_7197258 : Nat := 118140960795 + 7197258 * 2 ^ 59
def prefixEnd_7197258 : Nat := 4983230072969 + 3 ^ 40 * 7197258 * 2
def baseEnd_7197258 : Nat := 3695652748417306928675419

theorem tailTrace_7197258 : CollatzResearch.WordTrace tailWord_7197258 prefixEnd_7197258 3695652748417306928675419 := by
  unfold tailWord_7197258
  simp only [CollatzResearch.WordTrace]
  refine ⟨65626391239892733662598107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175003709973047289766928285 65626391239892733662598107)
  ·
    refine ⟨98439586859839100493897161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65626391239892733662598107 98439586859839100493897161)
    ·
      refine ⟨73829690144879325370422871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98439586859839100493897161 73829690144879325370422871)
      ·
        refine ⟨110744535217318988055634307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73829690144879325370422871 110744535217318988055634307)
        ·
          refine ⟨166116802825978482083451461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110744535217318988055634307 166116802825978482083451461)
          ·
            refine ⟨31146900529870965390647149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166116802825978482083451461 31146900529870965390647149)
            ·
              refine ⟨11680087698701612021492681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31146900529870965390647149 11680087698701612021492681)
              ·
                refine ⟨8760065774026209016119511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11680087698701612021492681 8760065774026209016119511)
                ·
                  refine ⟨13140098661039313524179267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8760065774026209016119511 13140098661039313524179267)
                  ·
                    refine ⟨19710147991558970286268901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13140098661039313524179267 19710147991558970286268901)
                    ·
                      refine ⟨3695652748417306928675419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19710147991558970286268901 3695652748417306928675419)
                      ·
                        rfl

theorem cell23_7197258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_7197258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197258 prefixEnd_7197258 := by exact prefixLift 7197258
  have htrace : WordTrace (prefixWord ++ tailWord_7197258) baseStart_7197258 baseEnd_7197258 := by
    simpa [prefixWord, tailWord_7197258, baseEnd_7197258] using wordTrace_append hprefix tailTrace_7197258
  have hstable : (prefixWord ++ tailWord_7197258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197258).length < 2 ^ (prefixWord ++ tailWord_7197258).sum := by decide
  have hdescent : baseEnd_7197258 < baseStart_7197258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197271 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_7197271 : Nat := 118140960795 + 7197271 * 2 ^ 59
def prefixEnd_7197271 : Nat := 4983230072969 + 3 ^ 40 * 7197271 * 2
def baseEnd_7197271 : Nat := 3695659423665815377812859

theorem tailTrace_7197271 : CollatzResearch.WordTrace tailWord_7197271 prefixEnd_7197271 3695659423665815377812859 := by
  unfold tailWord_7197271
  simp only [CollatzResearch.WordTrace]
  refine ⟨262506039108523837870615667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175004026072349225247077111 262506039108523837870615667)
  ·
    refine ⟨393759058662785756805923501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262506039108523837870615667 393759058662785756805923501)
    ·
      refine ⟨147659646998544658802221313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393759058662785756805923501 147659646998544658802221313)
      ·
        refine ⟨110744735248908494101665985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147659646998544658802221313 110744735248908494101665985)
        ·
          refine ⟨83058551436681370576249489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110744735248908494101665985 83058551436681370576249489)
          ·
            refine ⟨62293913577511027932187117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83058551436681370576249489 62293913577511027932187117)
            ·
              refine ⟨23360217591566635474570169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62293913577511027932187117 23360217591566635474570169)
              ·
                refine ⟨17520163193674976605927627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23360217591566635474570169 17520163193674976605927627)
                ·
                  refine ⟨26280244790512464908891441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17520163193674976605927627 26280244790512464908891441)
                  ·
                    refine ⟨19710183592884348681668581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26280244790512464908891441 19710183592884348681668581)
                    ·
                      refine ⟨3695659423665815377812859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19710183592884348681668581 3695659423665815377812859)
                      ·
                        rfl

theorem cell23_7197271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_7197271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197271 prefixEnd_7197271 := by exact prefixLift 7197271
  have htrace : WordTrace (prefixWord ++ tailWord_7197271) baseStart_7197271 baseEnd_7197271 := by
    simpa [prefixWord, tailWord_7197271, baseEnd_7197271] using wordTrace_append hprefix tailTrace_7197271
  have hstable : (prefixWord ++ tailWord_7197271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197271).length < 2 ^ (prefixWord ++ tailWord_7197271).sum := by decide
  have hdescent : baseEnd_7197271 < baseStart_7197271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197285 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 2, 4]
def baseStart_7197285 : Nat := 118140960795 + 7197285 * 2 ^ 59
def prefixEnd_7197285 : Nat := 4983230072969 + 3 ^ 40 * 7197285 * 2
def baseEnd_7197285 : Nat := 1231888870798326107679265

theorem tailTrace_7197285 : CollatzResearch.WordTrace tailWord_7197285 prefixEnd_7197285 1231888870798326107679265 := by
  unfold tailWord_7197285
  simp only [CollatzResearch.WordTrace]
  refine ⟨262506549730473118261625309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175004366486982078841083539 262506549730473118261625309)
  ·
    refine ⟨98439956148927419348109491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262506549730473118261625309 98439956148927419348109491)
    ·
      refine ⟨147659934223391129022164237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98439956148927419348109491 147659934223391129022164237)
      ·
        refine ⟨55372475333771673383311589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147659934223391129022164237 55372475333771673383311589)
        ·
          refine ⟨10382339125082188759370923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55372475333771673383311589 10382339125082188759370923)
          ·
            refine ⟨15573508687623283139056385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10382339125082188759370923 15573508687623283139056385)
            ·
              refine ⟨11680131515717462354292289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15573508687623283139056385 11680131515717462354292289)
              ·
                refine ⟨8760098636788096765719217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11680131515717462354292289 8760098636788096765719217)
                ·
                  refine ⟨6570073977591072574289413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760098636788096765719217 6570073977591072574289413)
                  ·
                    refine ⟨1231888870798326107679265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6570073977591072574289413 1231888870798326107679265)
                    ·
                      rfl

theorem cell23_7197285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_7197285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197285 prefixEnd_7197285 := by exact prefixLift 7197285
  have htrace : WordTrace (prefixWord ++ tailWord_7197285) baseStart_7197285 baseEnd_7197285 := by
    simpa [prefixWord, tailWord_7197285, baseEnd_7197285] using wordTrace_append hprefix tailTrace_7197285
  have hstable : (prefixWord ++ tailWord_7197285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197285).length < 2 ^ (prefixWord ++ tailWord_7197285).sum := by decide
  have hdescent : baseEnd_7197285 < baseStart_7197285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197298 : List Nat := [3, 2, 1, 2, 4, 2, 1, 8]
def baseStart_7197298 : Nat := 118140960795 + 7197298 * 2 ^ 59
def prefixEnd_7197298 : Nat := 4983230072969 + 3 ^ 40 * 7197298 * 2
def baseEnd_7197298 : Nat := 136876788431240250821305

theorem tailTrace_7197298 : CollatzResearch.WordTrace tailWord_7197298 prefixEnd_7197298 136876788431240250821305 := by
  unfold tailWord_7197298
  simp only [CollatzResearch.WordTrace]
  refine ⟨65626755969856505370462137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175004682586284014321232365 65626755969856505370462137)
  ·
    refine ⟨49220066977392379027846603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65626755969856505370462137 49220066977392379027846603)
    ·
      refine ⟨73830100466088568541769905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49220066977392379027846603 73830100466088568541769905)
      ·
        refine ⟨55372575349566426406327429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73830100466088568541769905 55372575349566426406327429)
        ·
          refine ⟨10382357878043704951186393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55372575349566426406327429 10382357878043704951186393)
          ·
            refine ⟨7786768408532778713389795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10382357878043704951186393 7786768408532778713389795)
            ·
              refine ⟨11680152612799168070084693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7786768408532778713389795 11680152612799168070084693)
              ·
                refine ⟨136876788431240250821305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11680152612799168070084693 136876788431240250821305)
                ·
                  rfl

theorem cell23_7197298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 8].length) (baseStart_7197298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197298 prefixEnd_7197298 := by exact prefixLift 7197298
  have htrace : WordTrace (prefixWord ++ tailWord_7197298) baseStart_7197298 baseEnd_7197298 := by
    simpa [prefixWord, tailWord_7197298, baseEnd_7197298] using wordTrace_append hprefix tailTrace_7197298
  have hstable : (prefixWord ++ tailWord_7197298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197298).length < 2 ^ (prefixWord ++ tailWord_7197298).sum := by decide
  have hdescent : baseEnd_7197298 < baseStart_7197298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197335 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 1, 3, 2]
def baseStart_7197335 : Nat := 118140960795 + 7197335 * 2 ^ 59
def prefixEnd_7197335 : Nat := 4983230072969 + 3 ^ 40 * 7197335 * 2
def baseEnd_7197335 : Nat := 3695692286427703127412565

theorem tailTrace_7197335 : CollatzResearch.WordTrace tailWord_7197335 prefixEnd_7197335 3695692286427703127412565 := by
  unfold tailWord_7197335
  simp only [CollatzResearch.WordTrace]
  refine ⟨262508373380291976800945459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175005582253527984533963639 262508373380291976800945459)
  ·
    refine ⟨393762560070437965201418189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262508373380291976800945459 393762560070437965201418189)
    ·
      refine ⟨147660960026414236950531821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393762560070437965201418189 147660960026414236950531821)
      ·
        refine ⟨55372860009905338856449433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147660960026414236950531821 55372860009905338856449433)
        ·
          refine ⟨41529645007429004142337075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55372860009905338856449433 41529645007429004142337075)
          ·
            refine ⟨62294467511143506213505613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41529645007429004142337075 62294467511143506213505613)
            ·
              refine ⟨23360425316678814830064605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62294467511143506213505613 23360425316678814830064605)
              ·
                refine ⟨8760159493754555561274227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23360425316678814830064605 8760159493754555561274227)
                ·
                  refine ⟨13140239240631833341911341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8760159493754555561274227 13140239240631833341911341)
                  ·
                    refine ⟨4927589715236937503216753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13140239240631833341911341 4927589715236937503216753)
                    ·
                      refine ⟨3695692286427703127412565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927589715236937503216753 3695692286427703127412565)
                      ·
                        rfl

theorem cell23_7197335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_7197335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197335 prefixEnd_7197335 := by exact prefixLift 7197335
  have htrace : WordTrace (prefixWord ++ tailWord_7197335) baseStart_7197335 baseEnd_7197335 := by
    simpa [prefixWord, tailWord_7197335, baseEnd_7197335] using wordTrace_append hprefix tailTrace_7197335
  have hstable : (prefixWord ++ tailWord_7197335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197335).length < 2 ^ (prefixWord ++ tailWord_7197335).sum := by decide
  have hdescent : baseEnd_7197335 < baseStart_7197335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197341 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_7197341 : Nat := 118140960795 + 7197341 * 2 ^ 59
def prefixEnd_7197341 : Nat := 4983230072969 + 3 ^ 40 * 7197341 * 2
def baseEnd_7197341 : Nat := 1231898455770543367979179

theorem tailTrace_7197341 : CollatzResearch.WordTrace tailWord_7197341 prefixEnd_7197341 1231898455770543367979179 := by
  unfold tailWord_7197341
  simp only [CollatzResearch.WordTrace]
  refine ⟨262508592218270239825663877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175005728145513493217109251 262508592218270239825663877)
  ·
    refine ⟨49220361040925669967311977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262508592218270239825663877 49220361040925669967311977)
    ·
      refine ⟨36915270780694252475483983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49220361040925669967311977 36915270780694252475483983)
      ·
        refine ⟨55372906171041378713225975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36915270780694252475483983 55372906171041378713225975)
        ·
          refine ⟨83059359256562068069838963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55372906171041378713225975 83059359256562068069838963)
          ·
            refine ⟨124589038884843102104758445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83059359256562068069838963 124589038884843102104758445)
            ·
              refine ⟨46720889581816163289284417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124589038884843102104758445 46720889581816163289284417)
              ·
                refine ⟨35040667186362122466963313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46720889581816163289284417 35040667186362122466963313)
                ·
                  refine ⟨26280500389771591850222485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35040667186362122466963313 26280500389771591850222485)
                  ·
                    refine ⟨1231898455770543367979179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26280500389771591850222485 1231898455770543367979179)
                    ·
                      rfl

theorem cell23_7197341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_7197341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197341 prefixEnd_7197341 := by exact prefixLift 7197341
  have htrace : WordTrace (prefixWord ++ tailWord_7197341) baseStart_7197341 baseEnd_7197341 := by
    simpa [prefixWord, tailWord_7197341, baseEnd_7197341] using wordTrace_append hprefix tailTrace_7197341
  have hstable : (prefixWord ++ tailWord_7197341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197341).length < 2 ^ (prefixWord ++ tailWord_7197341).sum := by decide
  have hdescent : baseEnd_7197341 < baseStart_7197341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197408 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 2, 5, 2]
def baseStart_7197408 : Nat := 118140960795 + 7197408 * 2 ^ 59
def prefixEnd_7197408 : Nat := 4983230072969 + 3 ^ 40 * 7197408 * 2
def baseEnd_7197408 : Nat := 3695729770515481341799729

theorem tailTrace_7197408 : CollatzResearch.WordTrace tailWord_7197408 prefixEnd_7197408 3695729770515481341799729 := by
  unfold tailWord_7197408
  simp only [CollatzResearch.WordTrace]
  refine ⟨131255517954513755134176439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175007357272685006845568585 131255517954513755134176439)
  ·
    refine ⟨196883276931770632701264659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131255517954513755134176439 196883276931770632701264659)
    ·
      refine ⟨295324915397655949051896989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196883276931770632701264659 295324915397655949051896989)
      ·
        refine ⟨110746843274120980894461371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295324915397655949051896989 110746843274120980894461371)
        ·
          refine ⟨166120264911181471341692057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110746843274120980894461371 166120264911181471341692057)
          ·
            refine ⟨124590198683386103506269043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166120264911181471341692057 124590198683386103506269043)
            ·
              refine ⟨186885298025079155259403565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124590198683386103506269043 186885298025079155259403565)
              ·
                refine ⟨70081986759404683222276337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186885298025079155259403565 70081986759404683222276337)
                ·
                  refine ⟨52561490069553512416707253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70081986759404683222276337 52561490069553512416707253)
                  ·
                    refine ⟨4927639694020641789066305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52561490069553512416707253 4927639694020641789066305)
                    ·
                      refine ⟨3695729770515481341799729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927639694020641789066305 3695729770515481341799729)
                      ·
                        rfl

theorem cell23_7197408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_7197408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197408 prefixEnd_7197408 := by exact prefixLift 7197408
  have htrace : WordTrace (prefixWord ++ tailWord_7197408) baseStart_7197408 baseEnd_7197408 := by
    simpa [prefixWord, tailWord_7197408, baseEnd_7197408] using wordTrace_append hprefix tailTrace_7197408
  have hstable : (prefixWord ++ tailWord_7197408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197408).length < 2 ^ (prefixWord ++ tailWord_7197408).sum := by decide
  have hdescent : baseEnd_7197408 < baseStart_7197408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197416 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_7197416 : Nat := 118140960795 + 7197416 * 2 ^ 59
def prefixEnd_7197416 : Nat := 4983230072969 + 3 ^ 40 * 7197416 * 2
def baseEnd_7197416 : Nat := 3695733878360717310499693

theorem tailTrace_7197416 : CollatzResearch.WordTrace tailWord_7197416 prefixEnd_7197416 3695733878360717310499693 := by
  unfold tailWord_7197416
  simp only [CollatzResearch.WordTrace]
  refine ⟨131255663846499263817322051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175007551795332351756429401 131255663846499263817322051)
  ·
    refine ⟨196883495769748895725983077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131255663846499263817322051 196883495769748895725983077)
    ·
      refine ⟨36915655456827917948621827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196883495769748895725983077 36915655456827917948621827)
      ·
        refine ⟨55373483185241876922932741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36915655456827917948621827 55373483185241876922932741)
        ·
          refine ⟨10382528097232851923049889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55373483185241876922932741 10382528097232851923049889)
          ·
            refine ⟨7786896072924638942287417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10382528097232851923049889 7786896072924638942287417)
            ·
              refine ⟨5840172054693479206715563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7786896072924638942287417 5840172054693479206715563)
              ·
                refine ⟨8760258082040218810073345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5840172054693479206715563 8760258082040218810073345)
                ·
                  refine ⟨6570193561530164107555009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760258082040218810073345 6570193561530164107555009)
                  ·
                    refine ⟨4927645171147623080666257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6570193561530164107555009 4927645171147623080666257)
                    ·
                      refine ⟨3695733878360717310499693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927645171147623080666257 3695733878360717310499693)
                      ·
                        rfl

theorem cell23_7197416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_7197416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197416 prefixEnd_7197416 := by exact prefixLift 7197416
  have htrace : WordTrace (prefixWord ++ tailWord_7197416) baseStart_7197416 baseEnd_7197416 := by
    simpa [prefixWord, tailWord_7197416, baseEnd_7197416] using wordTrace_append hprefix tailTrace_7197416
  have hstable : (prefixWord ++ tailWord_7197416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197416).length < 2 ^ (prefixWord ++ tailWord_7197416).sum := by decide
  have hdescent : baseEnd_7197416 < baseStart_7197416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197451 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 6]
def baseStart_7197451 : Nat := 118140960795 + 7197451 * 2 ^ 59
def prefixEnd_7197451 : Nat := 4983230072969 + 3 ^ 40 * 7197451 * 2
def baseEnd_7197451 : Nat := 3695751850183624673562031

theorem tailTrace_7197451 : CollatzResearch.WordTrace tailWord_7197451 prefixEnd_7197451 3695751850183624673562031 := by
  unfold tailWord_7197451
  simp only [CollatzResearch.WordTrace]
  refine ⟨262512604247871728612168207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175008402831914485741445471 262512604247871728612168207)
  ·
    refine ⟨393768906371807592918252311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262512604247871728612168207 393768906371807592918252311)
    ·
      refine ⟨590653359557711389377378467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393768906371807592918252311 590653359557711389377378467)
      ·
        refine ⟨885980039336567084066067701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590653359557711389377378467 885980039336567084066067701)
        ·
          refine ⟨83060628687803164131193847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 885980039336567084066067701 83060628687803164131193847)
          ·
            refine ⟨124590943031704746196790771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83060628687803164131193847 124590943031704746196790771)
            ·
              refine ⟨186886414547557119295186157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124590943031704746196790771 186886414547557119295186157)
              ·
                refine ⟨70082405455333919735694809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186886414547557119295186157 70082405455333919735694809)
                ·
                  refine ⟨52561804091500439801771107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70082405455333919735694809 52561804091500439801771107)
                  ·
                    refine ⟨78842706137250659702656661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52561804091500439801771107 78842706137250659702656661)
                    ·
                      refine ⟨3695751850183624673562031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78842706137250659702656661 3695751850183624673562031)
                      ·
                        rfl

theorem cell23_7197451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_7197451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197451 prefixEnd_7197451 := by exact prefixLift 7197451
  have htrace : WordTrace (prefixWord ++ tailWord_7197451) baseStart_7197451 baseEnd_7197451 := by
    simpa [prefixWord, tailWord_7197451, baseEnd_7197451] using wordTrace_append hprefix tailTrace_7197451
  have hstable : (prefixWord ++ tailWord_7197451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197451).length < 2 ^ (prefixWord ++ tailWord_7197451).sum := by decide
  have hdescent : baseEnd_7197451 < baseStart_7197451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197481 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_7197481 : Nat := 118140960795 + 7197481 * 2 ^ 59
def prefixEnd_7197481 : Nat := 4983230072969 + 3 ^ 40 * 7197481 * 2
def baseEnd_7197481 : Nat := 3695767254603259556186893

theorem tailTrace_7197481 : CollatzResearch.WordTrace tailWord_7197481 prefixEnd_7197481 3695767254603259556186893 := by
  unfold tailWord_7197481
  simp only [CollatzResearch.WordTrace]
  refine ⟨262513698437763043735760297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175009132291842029157173531 262513698437763043735760297)
  ·
    refine ⟨196885273828322282801820223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262513698437763043735760297 196885273828322282801820223)
    ·
      refine ⟨295327910742483424202730335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196885273828322282801820223 295327910742483424202730335)
      ·
        refine ⟨442991866113725136304095503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295327910742483424202730335 442991866113725136304095503)
        ·
          refine ⟨664487799170587704456143255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442991866113725136304095503 664487799170587704456143255)
          ·
            refine ⟨996731698755881556684214883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664487799170587704456143255 996731698755881556684214883)
            ·
              refine ⟨1495097548133822335026322325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996731698755881556684214883 1495097548133822335026322325)
              ·
                refine ⟨70082697568772921954358859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1495097548133822335026322325 70082697568772921954358859)
                ·
                  refine ⟨105124046353159382931538289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70082697568772921954358859 105124046353159382931538289)
                  ·
                    refine ⟨78843034764869537198653717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105124046353159382931538289 78843034764869537198653717)
                    ·
                      refine ⟨3695767254603259556186893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78843034764869537198653717 3695767254603259556186893)
                      ·
                        rfl

theorem cell23_7197481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_7197481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197481 prefixEnd_7197481 := by exact prefixLift 7197481
  have htrace : WordTrace (prefixWord ++ tailWord_7197481) baseStart_7197481 baseEnd_7197481 := by
    simpa [prefixWord, tailWord_7197481, baseEnd_7197481] using wordTrace_append hprefix tailTrace_7197481
  have hstable : (prefixWord ++ tailWord_7197481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197481).length < 2 ^ (prefixWord ++ tailWord_7197481).sum := by decide
  have hdescent : baseEnd_7197481 < baseStart_7197481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197492 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_7197492 : Nat := 118140960795 + 7197492 * 2 ^ 59
def prefixEnd_7197492 : Nat := 4983230072969 + 3 ^ 40 * 7197492 * 2
def baseEnd_7197492 : Nat := 3695772902890459013149343

theorem tailTrace_7197492 : CollatzResearch.WordTrace tailWord_7197492 prefixEnd_7197492 3695772902890459013149343 := by
  unfold tailWord_7197492
  simp only [CollatzResearch.WordTrace]
  refine ⟨131257049820361596307205365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175009399760482128409607153 131257049820361596307205365)
  ·
    refine ⟨12305348420658899653800503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131257049820361596307205365 12305348420658899653800503)
    ·
      refine ⟨18458022630988349480700755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12305348420658899653800503 18458022630988349480700755)
      ·
        refine ⟨27687033946482524221051133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18458022630988349480700755 27687033946482524221051133)
        ·
          refine ⟨10382637729930946582894175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27687033946482524221051133 10382637729930946582894175)
          ·
            refine ⟨15573956594896419874341263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10382637729930946582894175 15573956594896419874341263)
            ·
              refine ⟨23360934892344629811511895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15573956594896419874341263 23360934892344629811511895)
              ·
                refine ⟨35041402338516944717267843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23360934892344629811511895 35041402338516944717267843)
                ·
                  refine ⟨52562103507775417075901765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35041402338516944717267843 52562103507775417075901765)
                  ·
                    refine ⟨9855394407707890701731581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52562103507775417075901765 9855394407707890701731581)
                    ·
                      refine ⟨3695772902890459013149343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9855394407707890701731581 3695772902890459013149343)
                      ·
                        rfl

theorem cell23_7197492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_7197492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197492 prefixEnd_7197492 := by exact prefixLift 7197492
  have htrace : WordTrace (prefixWord ++ tailWord_7197492) baseStart_7197492 baseEnd_7197492 := by
    simpa [prefixWord, tailWord_7197492, baseEnd_7197492] using wordTrace_append hprefix tailTrace_7197492
  have hstable : (prefixWord ++ tailWord_7197492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197492).length < 2 ^ (prefixWord ++ tailWord_7197492).sum := by decide
  have hdescent : baseEnd_7197492 < baseStart_7197492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197522 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_7197522 : Nat := 118140960795 + 7197522 * 2 ^ 59
def prefixEnd_7197522 : Nat := 4983230072969 + 3 ^ 40 * 7197522 * 2
def baseEnd_7197522 : Nat := 3695788307310093895774205

theorem tailTrace_7197522 : CollatzResearch.WordTrace tailWord_7197522 prefixEnd_7197522 3695788307310093895774205 := by
  unfold tailWord_7197522
  simp only [CollatzResearch.WordTrace]
  refine ⟨65628798457653626934500705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175010129220409671825335213 65628798457653626934500705)
  ·
    refine ⟨49221598843240220200875529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65628798457653626934500705 49221598843240220200875529)
    ·
      refine ⟨36916199132430165150656647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49221598843240220200875529 36916199132430165150656647)
      ·
        refine ⟨55374298698645247725984971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36916199132430165150656647 55374298698645247725984971)
        ·
          refine ⟨83061448047967871588977457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55374298698645247725984971 83061448047967871588977457)
          ·
            refine ⟨62296086035975903691733093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83061448047967871588977457 62296086035975903691733093)
            ·
              refine ⟨11680516131745481942199955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62296086035975903691733093 11680516131745481942199955)
              ·
                refine ⟨17520774197618222913299933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11680516131745481942199955 17520774197618222913299933)
                ·
                  refine ⟨6570290324106833592487475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17520774197618222913299933 6570290324106833592487475)
                  ·
                    refine ⟨9855435486160250388731213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6570290324106833592487475 9855435486160250388731213)
                    ·
                      refine ⟨3695788307310093895774205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9855435486160250388731213 3695788307310093895774205)
                      ·
                        rfl

theorem cell23_7197522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_7197522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197522 prefixEnd_7197522 := by exact prefixLift 7197522
  have htrace : WordTrace (prefixWord ++ tailWord_7197522) baseStart_7197522 baseEnd_7197522 := by
    simpa [prefixWord, tailWord_7197522, baseEnd_7197522] using wordTrace_append hprefix tailTrace_7197522
  have hstable : (prefixWord ++ tailWord_7197522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197522).length < 2 ^ (prefixWord ++ tailWord_7197522).sum := by decide
  have hdescent : baseEnd_7197522 < baseStart_7197522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197528 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_7197528 : Nat := 118140960795 + 7197528 * 2 ^ 59
def prefixEnd_7197528 : Nat := 4983230072969 + 3 ^ 40 * 7197528 * 2
def baseEnd_7197528 : Nat := 3695791388194020872299177

theorem tailTrace_7197528 : CollatzResearch.WordTrace tailWord_7197528 prefixEnd_7197528 3695791388194020872299177 := by
  unfold tailWord_7197528
  simp only [CollatzResearch.WordTrace]
  refine ⟨131257706334296385381360619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175010275112395180508480825 131257706334296385381360619)
  ·
    refine ⟨196886559501444578072040929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131257706334296385381360619 196886559501444578072040929)
    ·
      refine ⟨147664919626083433554030697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196886559501444578072040929 147664919626083433554030697)
      ·
        refine ⟨110748689719562575165523023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147664919626083433554030697 110748689719562575165523023)
        ·
          refine ⟨166123034579343862748284535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110748689719562575165523023 166123034579343862748284535)
          ·
            refine ⟨249184551869015794122426803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166123034579343862748284535 249184551869015794122426803)
            ·
              refine ⟨373776827803523691183640205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249184551869015794122426803 373776827803523691183640205)
              ·
                refine ⟨140166310426321384193865077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373776827803523691183640205 140166310426321384193865077)
                ·
                  refine ⟨13140591602467629768174851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140166310426321384193865077 13140591602467629768174851)
                  ·
                    refine ⟨19710887403701444652262277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13140591602467629768174851 19710887403701444652262277)
                    ·
                      refine ⟨3695791388194020872299177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19710887403701444652262277 3695791388194020872299177)
                      ·
                        rfl

theorem cell23_7197528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_7197528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197528 prefixEnd_7197528 := by exact prefixLift 7197528
  have htrace : WordTrace (prefixWord ++ tailWord_7197528) baseStart_7197528 baseEnd_7197528 := by
    simpa [prefixWord, tailWord_7197528, baseEnd_7197528] using wordTrace_append hprefix tailTrace_7197528
  have hstable : (prefixWord ++ tailWord_7197528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197528).length < 2 ^ (prefixWord ++ tailWord_7197528).sum := by decide
  have hdescent : baseEnd_7197528 < baseStart_7197528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197532 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_7197532 : Nat := 118140960795 + 7197532 * 2 ^ 59
def prefixEnd_7197532 : Nat := 4983230072969 + 3 ^ 40 * 7197532 * 2
def baseEnd_7197532 : Nat := 3695793442116638856649159

theorem tailTrace_7197532 : CollatzResearch.WordTrace tailWord_7197532 prefixEnd_7197532 3695793442116638856649159 := by
  unfold tailWord_7197532
  simp only [CollatzResearch.WordTrace]
  refine ⟨131257779280289139722933425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175010372373718852963911233 131257779280289139722933425)
  ·
    refine ⟨98443334460216854792200069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131257779280289139722933425 98443334460216854792200069)
    ·
      refine ⟨18458125211290660273537513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98443334460216854792200069 18458125211290660273537513)
      ·
        refine ⟨13843593908467995205153135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18458125211290660273537513 13843593908467995205153135)
        ·
          refine ⟨20765390862701992807729703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13843593908467995205153135 20765390862701992807729703)
          ·
            refine ⟨31148086294052989211594555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20765390862701992807729703 31148086294052989211594555)
            ·
              refine ⟨46722129441079483817391833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31148086294052989211594555 46722129441079483817391833)
              ·
                refine ⟨35041597080809612863043875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46722129441079483817391833 35041597080809612863043875)
                ·
                  refine ⟨52562395621214419294565813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35041597080809612863043875 52562395621214419294565813)
                  ·
                    refine ⟨4927724589488851808865545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52562395621214419294565813 4927724589488851808865545)
                    ·
                      refine ⟨3695793442116638856649159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927724589488851808865545 3695793442116638856649159)
                      ·
                        rfl

theorem cell23_7197532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_7197532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197532 prefixEnd_7197532 := by exact prefixLift 7197532
  have htrace : WordTrace (prefixWord ++ tailWord_7197532) baseStart_7197532 baseEnd_7197532 := by
    simpa [prefixWord, tailWord_7197532, baseEnd_7197532] using wordTrace_append hprefix tailTrace_7197532
  have hstable : (prefixWord ++ tailWord_7197532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197532).length < 2 ^ (prefixWord ++ tailWord_7197532).sum := by decide
  have hdescent : baseEnd_7197532 < baseStart_7197532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197548 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_7197548 : Nat := 118140960795 + 7197548 * 2 ^ 59
def prefixEnd_7197548 : Nat := 4983230072969 + 3 ^ 40 * 7197548 * 2
def baseEnd_7197548 : Nat := 3695801657807110794049085

theorem tailTrace_7197548 : CollatzResearch.WordTrace tailWord_7197548 prefixEnd_7197548 3695801657807110794049085 := by
  unfold tailWord_7197548
  simp only [CollatzResearch.WordTrace]
  refine ⟨131258071064260157089224649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175010761419013542785632865 131258071064260157089224649)
  ·
    refine ⟨98443553298195117816918487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131258071064260157089224649 98443553298195117816918487)
    ·
      refine ⟨147665329947292676725377731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98443553298195117816918487 147665329947292676725377731)
      ·
        refine ⟨221497994920939015088066597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147665329947292676725377731 221497994920939015088066597)
        ·
          refine ⟨41530874047676065329012487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221497994920939015088066597 41530874047676065329012487)
          ·
            refine ⟨62296311071514097993518731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41530874047676065329012487 62296311071514097993518731)
            ·
              refine ⟨93444466607271146990278097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62296311071514097993518731 93444466607271146990278097)
              ·
                refine ⟨70083349955453360242708573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93444466607271146990278097 70083349955453360242708573)
                ·
                  refine ⟨26281256233295010091015715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70083349955453360242708573 26281256233295010091015715)
                  ·
                    refine ⟨39421884349942515136523573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26281256233295010091015715 39421884349942515136523573)
                    ·
                      refine ⟨3695801657807110794049085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39421884349942515136523573 3695801657807110794049085)
                      ·
                        rfl

theorem cell23_7197548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_7197548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197548 prefixEnd_7197548 := by exact prefixLift 7197548
  have htrace : WordTrace (prefixWord ++ tailWord_7197548) baseStart_7197548 baseEnd_7197548 := by
    simpa [prefixWord, tailWord_7197548, baseEnd_7197548] using wordTrace_append hprefix tailTrace_7197548
  have hstable : (prefixWord ++ tailWord_7197548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197548).length < 2 ^ (prefixWord ++ tailWord_7197548).sum := by decide
  have hdescent : baseEnd_7197548 < baseStart_7197548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197566 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7197566 : Nat := 118140960795 + 7197566 * 2 ^ 59
def prefixEnd_7197566 : Nat := 4983230072969 + 3 ^ 40 * 7197566 * 2
def baseEnd_7197566 : Nat := 3695810900458891723624003

theorem tailTrace_7197566 : CollatzResearch.WordTrace tailWord_7197566 prefixEnd_7197566 3695810900458891723624003 := by
  unfold tailWord_7197566
  simp only [CollatzResearch.WordTrace]
  refine ⟨32814599830306887906575569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175011199094970068835069701 32814599830306887906575569)
  ·
    refine ⟨24610949872730165929931677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32814599830306887906575569 24610949872730165929931677)
    ·
      refine ⟨9229106202273812223724379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24610949872730165929931677 9229106202273812223724379)
      ·
        refine ⟨13843659303410718335586569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9229106202273812223724379 13843659303410718335586569)
        ·
          refine ⟨10382744477558038751689927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13843659303410718335586569 10382744477558038751689927)
          ·
            refine ⟨15574116716337058127534891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10382744477558038751689927 15574116716337058127534891)
            ·
              refine ⟨23361175074505587191302337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15574116716337058127534891 23361175074505587191302337)
              ·
                refine ⟨17520881305879190393476753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23361175074505587191302337 17520881305879190393476753)
                ·
                  refine ⟨13140660979409392795107565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17520881305879190393476753 13140660979409392795107565)
                  ·
                    refine ⟨4927747867278522298165337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13140660979409392795107565 4927747867278522298165337)
                    ·
                      refine ⟨3695810900458891723624003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927747867278522298165337 3695810900458891723624003)
                      ·
                        rfl

theorem cell23_7197566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7197566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197566 prefixEnd_7197566 := by exact prefixLift 7197566
  have htrace : WordTrace (prefixWord ++ tailWord_7197566) baseStart_7197566 baseEnd_7197566 := by
    simpa [prefixWord, tailWord_7197566, baseEnd_7197566] using wordTrace_append hprefix tailTrace_7197566
  have hstable : (prefixWord ++ tailWord_7197566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197566).length < 2 ^ (prefixWord ++ tailWord_7197566).sum := by decide
  have hdescent : baseEnd_7197566 < baseStart_7197566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197579 : List Nat := [1, 1, 1, 1, 4, 2, 2, 6, 1, 2, 2]
def baseStart_7197579 : Nat := 118140960795 + 7197579 * 2 ^ 59
def prefixEnd_7197579 : Nat := 4983230072969 + 3 ^ 40 * 7197579 * 2
def baseEnd_7197579 : Nat := 3695817575707400172761443

theorem tailTrace_7197579 : CollatzResearch.WordTrace tailWord_7197579 prefixEnd_7197579 3695817575707400172761443 := by
  unfold tailWord_7197579
  simp only [CollatzResearch.WordTrace]
  refine ⟨262517272791408006472827791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175011515194272004315218527 262517272791408006472827791)
  ·
    refine ⟨393775909187112009709241687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262517272791408006472827791 393775909187112009709241687)
    ·
      refine ⟨590663863780668014563862531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393775909187112009709241687 590663863780668014563862531)
      ·
        refine ⟨885995795671002021845793797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590663863780668014563862531 885995795671002021845793797)
        ·
          refine ⟨166124211688312879096086337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 885995795671002021845793797 166124211688312879096086337)
          ·
            refine ⟨124593158766234659322064753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166124211688312879096086337 124593158766234659322064753)
            ·
              refine ⟨93444869074675994491548565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124593158766234659322064753 93444869074675994491548565)
              ·
                refine ⟨4380228237875437241791339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93444869074675994491548565 4380228237875437241791339)
                ·
                  refine ⟨6570342356813155862687009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380228237875437241791339 6570342356813155862687009)
                  ·
                    refine ⟨4927756767609866897015257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6570342356813155862687009 4927756767609866897015257)
                    ·
                      refine ⟨3695817575707400172761443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927756767609866897015257 3695817575707400172761443)
                      ·
                        rfl

theorem cell23_7197579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 1, 2, 2].length) (baseStart_7197579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197579 prefixEnd_7197579 := by exact prefixLift 7197579
  have htrace : WordTrace (prefixWord ++ tailWord_7197579) baseStart_7197579 baseEnd_7197579 := by
    simpa [prefixWord, tailWord_7197579, baseEnd_7197579] using wordTrace_append hprefix tailTrace_7197579
  have hstable : (prefixWord ++ tailWord_7197579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197579).length < 2 ^ (prefixWord ++ tailWord_7197579).sum := by decide
  have hdescent : baseEnd_7197579 < baseStart_7197579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197589 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 2, 4]
def baseStart_7197589 : Nat := 118140960795 + 7197589 * 2 ^ 59
def prefixEnd_7197589 : Nat := 4983230072969 + 3 ^ 40 * 7197589 * 2
def baseEnd_7197589 : Nat := 1231940903504648377878799

theorem tailTrace_7197589 : CollatzResearch.WordTrace tailWord_7197589 prefixEnd_7197589 1231940903504648377878799 := by
  unfold tailWord_7197589
  simp only [CollatzResearch.WordTrace]
  refine ⟨262517637521371778180691821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175011758347581185453794547 262517637521371778180691821)
  ·
    refine ⟨98444114070514416817759433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262517637521371778180691821 98444114070514416817759433)
    ·
      refine ⟨73833085552885812613319575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98444114070514416817759433 73833085552885812613319575)
      ·
        refine ⟨110749628329328718919979363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73833085552885812613319575 110749628329328718919979363)
        ·
          refine ⟨166124442493993078379969045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110749628329328718919979363 166124442493993078379969045)
          ·
            refine ⟨7787083241905925549061049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166124442493993078379969045 7787083241905925549061049)
            ·
              refine ⟨5840312431429444161795787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7787083241905925549061049 5840312431429444161795787)
              ·
                refine ⟨8760468647144166242693681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5840312431429444161795787 8760468647144166242693681)
                ·
                  refine ⟨6570351485358124682020261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760468647144166242693681 6570351485358124682020261)
                  ·
                    refine ⟨1231940903504648377878799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6570351485358124682020261 1231940903504648377878799)
                    ·
                      rfl

theorem cell23_7197589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_7197589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197589 prefixEnd_7197589 := by exact prefixLift 7197589
  have htrace : WordTrace (prefixWord ++ tailWord_7197589) baseStart_7197589 baseEnd_7197589 := by
    simpa [prefixWord, tailWord_7197589, baseEnd_7197589] using wordTrace_append hprefix tailTrace_7197589
  have hstable : (prefixWord ++ tailWord_7197589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197589).length < 2 ^ (prefixWord ++ tailWord_7197589).sum := by decide
  have hdescent : baseEnd_7197589 < baseStart_7197589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197596 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_7197596 : Nat := 118140960795 + 7197596 * 2 ^ 59
def prefixEnd_7197596 : Nat := 4983230072969 + 3 ^ 40 * 7197596 * 2
def baseEnd_7197596 : Nat := 3695826304878526606248865

theorem tailTrace_7197596 : CollatzResearch.WordTrace tailWord_7197596 prefixEnd_7197596 3695826304878526606248865 := by
  unfold tailWord_7197596
  simp only [CollatzResearch.WordTrace]
  refine ⟨131258946416173209188098321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175011928554897612250797761 131258946416173209188098321)
  ·
    refine ⟨98444209812129906891073741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131258946416173209188098321 98444209812129906891073741)
    ·
      refine ⟨36916578679548715084152653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98444209812129906891073741 36916578679548715084152653)
      ·
        refine ⟨13843717004830768156557245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36916578679548715084152653 13843717004830768156557245)
        ·
          refine ⟨5191393876811538058708967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13843717004830768156557245 5191393876811538058708967)
          ·
            refine ⟨7787090815217307088063451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191393876811538058708967 7787090815217307088063451)
            ·
              refine ⟨11680636222825960632095177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787090815217307088063451 11680636222825960632095177)
              ·
                refine ⟨8760477167119470474071383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11680636222825960632095177 8760477167119470474071383)
                ·
                  refine ⟨13140715750679205711107075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8760477167119470474071383 13140715750679205711107075)
                  ·
                    refine ⟨19711073626018808566660613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13140715750679205711107075 19711073626018808566660613)
                    ·
                      refine ⟨3695826304878526606248865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19711073626018808566660613 3695826304878526606248865)
                      ·
                        rfl

theorem cell23_7197596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_7197596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197596 prefixEnd_7197596 := by exact prefixLift 7197596
  have htrace : WordTrace (prefixWord ++ tailWord_7197596) baseStart_7197596 baseEnd_7197596 := by
    simpa [prefixWord, tailWord_7197596, baseEnd_7197596] using wordTrace_append hprefix tailTrace_7197596
  have hstable : (prefixWord ++ tailWord_7197596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197596).length < 2 ^ (prefixWord ++ tailWord_7197596).sum := by decide
  have hdescent : baseEnd_7197596 < baseStart_7197596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197599 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 1, 2, 3]
def baseStart_7197599 : Nat := 118140960795 + 7197599 * 2 ^ 59
def prefixEnd_7197599 : Nat := 4983230072969 + 3 ^ 40 * 7197599 * 2
def baseEnd_7197599 : Nat := 3695827845320490094511351

theorem tailTrace_7197599 : CollatzResearch.WordTrace tailWord_7197599 prefixEnd_7197599 3695827845320490094511351 := by
  unfold tailWord_7197599
  simp only [CollatzResearch.WordTrace]
  refine ⟨262518002251335549888555851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175012001500890366592370567 262518002251335549888555851)
  ·
    refine ⟨393777003377003324832833777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262518002251335549888555851 393777003377003324832833777)
    ·
      refine ⟨295332752532752493624625333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393777003377003324832833777 295332752532752493624625333)
      ·
        refine ⟨27687445549945546277308625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295332752532752493624625333 27687445549945546277308625)
        ·
          refine ⟨20765584162459159707981469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27687445549945546277308625 20765584162459159707981469)
          ·
            refine ⟨7787094060922184890493051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20765584162459159707981469 7787094060922184890493051)
            ·
              refine ⟨11680641091383277335739577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787094060922184890493051 11680641091383277335739577)
              ·
                refine ⟨8760480818537458001804683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11680641091383277335739577 8760480818537458001804683)
                ·
                  refine ⟨13140721227806187002707025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8760480818537458001804683 13140721227806187002707025)
                  ·
                    refine ⟨9855540920854640252030269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13140721227806187002707025 9855540920854640252030269)
                    ·
                      refine ⟨3695827845320490094511351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9855540920854640252030269 3695827845320490094511351)
                      ·
                        rfl

theorem cell23_7197599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_7197599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197599 prefixEnd_7197599 := by exact prefixLift 7197599
  have htrace : WordTrace (prefixWord ++ tailWord_7197599) baseStart_7197599 baseEnd_7197599 := by
    simpa [prefixWord, tailWord_7197599, baseEnd_7197599] using wordTrace_append hprefix tailTrace_7197599
  have hstable : (prefixWord ++ tailWord_7197599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197599).length < 2 ^ (prefixWord ++ tailWord_7197599).sum := by decide
  have hdescent : baseEnd_7197599 < baseStart_7197599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197686 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_7197686 : Nat := 118140960795 + 7197686 * 2 ^ 59
def prefixEnd_7197686 : Nat := 4983230072969 + 3 ^ 40 * 7197686 * 2
def baseEnd_7197686 : Nat := 3695872518137431254123451

theorem tailTrace_7197686 : CollatzResearch.WordTrace tailWord_7197686 prefixEnd_7197686 3695872518137431254123451 := by
  unfold tailWord_7197686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16407573462626272734185807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175014116934680242497981941 16407573462626272734185807)
  ·
    refine ⟨24611360193939409101278711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16407573462626272734185807 24611360193939409101278711)
    ·
      refine ⟨36917040290909113651918067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24611360193939409101278711 36917040290909113651918067)
      ·
        refine ⟨55375560436363670477877101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36917040290909113651918067 55375560436363670477877101)
        ·
          refine ⟨20765835163636376429203913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55375560436363670477877101 20765835163636376429203913)
          ·
            refine ⟨15574376372727282321902935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20765835163636376429203913 15574376372727282321902935)
            ·
              refine ⟨23361564559090923482854403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15574376372727282321902935 23361564559090923482854403)
              ·
                refine ⟨35042346838636385224281605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23361564559090923482854403 35042346838636385224281605)
                ·
                  refine ⟨6570440032244322229552801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35042346838636385224281605 6570440032244322229552801)
                  ·
                    refine ⟨4927830024183241672164601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6570440032244322229552801 4927830024183241672164601)
                    ·
                      refine ⟨3695872518137431254123451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927830024183241672164601 3695872518137431254123451)
                      ·
                        rfl

theorem cell23_7197686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_7197686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197686 prefixEnd_7197686 := by exact prefixLift 7197686
  have htrace : WordTrace (prefixWord ++ tailWord_7197686) baseStart_7197686 baseEnd_7197686 := by
    simpa [prefixWord, tailWord_7197686, baseEnd_7197686] using wordTrace_append hprefix tailTrace_7197686
  have hstable : (prefixWord ++ tailWord_7197686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197686).length < 2 ^ (prefixWord ++ tailWord_7197686).sum := by decide
  have hdescent : baseEnd_7197686 < baseStart_7197686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197692 : List Nat := [2, 2, 2, 1, 2, 3, 2, 4, 5]
def baseStart_7197692 : Nat := 118140960795 + 7197692 * 2 ^ 59
def prefixEnd_7197692 : Nat := 4983230072969 + 3 ^ 40 * 7197692 * 2
def baseEnd_7197692 : Nat := 410652844335706470072047

theorem tailTrace_7197692 : CollatzResearch.WordTrace tailWord_7197692 prefixEnd_7197692 410652844335706470072047 := by
  unfold tailWord_7197692
  simp only [CollatzResearch.WordTrace]
  refine ⟨131260697119999313385845665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175014262826665751181127553 131260697119999313385845665)
  ·
    refine ⟨98445522839999485039384249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131260697119999313385845665 98445522839999485039384249)
    ·
      refine ⟨73834142129999613779538187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98445522839999485039384249 73834142129999613779538187)
      ·
        refine ⟨110751213194999420669307281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73834142129999613779538187 110751213194999420669307281)
        ·
          refine ⟨83063409896249565501980461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110751213194999420669307281 83063409896249565501980461)
          ·
            refine ⟨31148778711093587063242673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83063409896249565501980461 31148778711093587063242673)
            ·
              refine ⟨23361584033320190297432005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31148778711093587063242673 23361584033320190297432005)
              ·
                refine ⟨4380297006247535680768501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23361584033320190297432005 4380297006247535680768501)
                ·
                  refine ⟨410652844335706470072047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4380297006247535680768501 410652844335706470072047)
                  ·
                    rfl

theorem cell23_7197692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_7197692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197692 prefixEnd_7197692 := by exact prefixLift 7197692
  have htrace : WordTrace (prefixWord ++ tailWord_7197692) baseStart_7197692 baseEnd_7197692 := by
    simpa [prefixWord, tailWord_7197692, baseEnd_7197692] using wordTrace_append hprefix tailTrace_7197692
  have hstable : (prefixWord ++ tailWord_7197692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197692).length < 2 ^ (prefixWord ++ tailWord_7197692).sum := by decide
  have hdescent : baseEnd_7197692 < baseStart_7197692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197886 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_7197886 : Nat := 118140960795 + 7197886 * 2 ^ 59
def prefixEnd_7197886 : Nat := 4983230072969 + 3 ^ 40 * 7197886 * 2
def baseEnd_7197886 : Nat := 3695975214268330471622531

theorem tailTrace_7197886 : CollatzResearch.WordTrace tailWord_7197886 prefixEnd_7197886 3695975214268330471622531 := by
  unfold tailWord_7197886
  simp only [CollatzResearch.WordTrace]
  refine ⟨32816058750161974738031689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175018980000863865269502341 32816058750161974738031689)
  ·
    refine ⟨24612044062621481053523767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32816058750161974738031689 24612044062621481053523767)
    ·
      refine ⟨36918066093932221580285651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24612044062621481053523767 36918066093932221580285651)
      ·
        refine ⟨55377099140898332370428477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36918066093932221580285651 55377099140898332370428477)
        ·
          refine ⟨20766412177836874638910679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55377099140898332370428477 20766412177836874638910679)
          ·
            refine ⟨31149618266755311958366019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20766412177836874638910679 31149618266755311958366019)
            ·
              refine ⟨46724427400132967937549029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31149618266755311958366019 46724427400132967937549029)
              ·
                refine ⟨8760830137524931488290443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46724427400132967937549029 8760830137524931488290443)
                ·
                  refine ⟨13141245206287397232435665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8760830137524931488290443 13141245206287397232435665)
                  ·
                    refine ⟨9855933904715547924326749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13141245206287397232435665 9855933904715547924326749)
                    ·
                      refine ⟨3695975214268330471622531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9855933904715547924326749 3695975214268330471622531)
                      ·
                        rfl

theorem cell23_7197886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_7197886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197886 prefixEnd_7197886 := by exact prefixLift 7197886
  have htrace : WordTrace (prefixWord ++ tailWord_7197886) baseStart_7197886 baseEnd_7197886 := by
    simpa [prefixWord, tailWord_7197886, baseEnd_7197886] using wordTrace_append hprefix tailTrace_7197886
  have hstable : (prefixWord ++ tailWord_7197886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197886).length < 2 ^ (prefixWord ++ tailWord_7197886).sum := by decide
  have hdescent : baseEnd_7197886 < baseStart_7197886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197889 : List Nat := [1, 2, 6, 1, 1, 2, 1, 9]
def baseStart_7197889 : Nat := 118140960795 + 7197889 * 2 ^ 59
def prefixEnd_7197889 : Nat := 4983230072969 + 3 ^ 40 * 7197889 * 2
def baseEnd_7197889 : Nat := 136888027952233109625371

theorem tailTrace_7197889 : CollatzResearch.WordTrace tailWord_7197889 prefixEnd_7197889 136888027952233109625371 := by
  unfold tailWord_7197889
  simp only [CollatzResearch.WordTrace]
  refine ⟨262528579420284929416612721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175019052946856619611075147 262528579420284929416612721)
  ·
    refine ⟨196896434565213697062459541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262528579420284929416612721 196896434565213697062459541)
    ·
      refine ⟨9229520370244392049802791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 196896434565213697062459541 9229520370244392049802791)
      ·
        refine ⟨13844280555366588074704187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9229520370244392049802791 13844280555366588074704187)
        ·
          refine ⟨20766420833049882112056281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13844280555366588074704187 20766420833049882112056281)
          ·
            refine ⟨15574815624787411584042211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20766420833049882112056281 15574815624787411584042211)
            ·
              refine ⟨23362223437181117376063317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15574815624787411584042211 23362223437181117376063317)
              ·
                refine ⟨136888027952233109625371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23362223437181117376063317 136888027952233109625371)
                ·
                  rfl

theorem cell23_7197889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 9].length) (baseStart_7197889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197889 prefixEnd_7197889 := by exact prefixLift 7197889
  have htrace : WordTrace (prefixWord ++ tailWord_7197889) baseStart_7197889 baseEnd_7197889 := by
    simpa [prefixWord, tailWord_7197889, baseEnd_7197889] using wordTrace_append hprefix tailTrace_7197889
  have hstable : (prefixWord ++ tailWord_7197889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197889).length < 2 ^ (prefixWord ++ tailWord_7197889).sum := by decide
  have hdescent : baseEnd_7197889 < baseStart_7197889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197917 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_7197917 : Nat := 118140960795 + 7197917 * 2 ^ 59
def prefixEnd_7197917 : Nat := 4983230072969 + 3 ^ 40 * 7197917 * 2
def baseEnd_7197917 : Nat := 3695991132168619850334889

theorem tailTrace_7197917 : CollatzResearch.WordTrace tailWord_7197917 prefixEnd_7197917 3695991132168619850334889 := by
  unfold tailWord_7197917
  simp only [CollatzResearch.WordTrace]
  refine ⟨262529600664183490198632005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175019733776122326799088003 262529600664183490198632005)
  ·
    refine ⟨49224300124534404412243501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262529600664183490198632005 49224300124534404412243501)
    ·
      refine ⟨18459112546700401654591313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49224300124534404412243501 18459112546700401654591313)
      ·
        refine ⟨13844334410025301240943485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18459112546700401654591313 13844334410025301240943485)
        ·
          refine ⟨5191625403759487965353807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13844334410025301240943485 5191625403759487965353807)
          ·
            refine ⟨7787438105639231948030711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191625403759487965353807 7787438105639231948030711)
            ·
              refine ⟨11681157158458847922046067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787438105639231948030711 11681157158458847922046067)
              ·
                refine ⟨17521735737688271883069101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11681157158458847922046067 17521735737688271883069101)
                ·
                  refine ⟨6570650901633101956150913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17521735737688271883069101 6570650901633101956150913)
                  ·
                    refine ⟨4927988176224826467113185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6570650901633101956150913 4927988176224826467113185)
                    ·
                      refine ⟨3695991132168619850334889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4927988176224826467113185 3695991132168619850334889)
                      ·
                        rfl

theorem cell23_7197917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_7197917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197917 prefixEnd_7197917 := by exact prefixLift 7197917
  have htrace : WordTrace (prefixWord ++ tailWord_7197917) baseStart_7197917 baseEnd_7197917 := by
    simpa [prefixWord, tailWord_7197917, baseEnd_7197917] using wordTrace_append hprefix tailTrace_7197917
  have hstable : (prefixWord ++ tailWord_7197917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197917).length < 2 ^ (prefixWord ++ tailWord_7197917).sum := by decide
  have hdescent : baseEnd_7197917 < baseStart_7197917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197933 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_7197933 : Nat := 118140960795 + 7197933 * 2 ^ 59
def prefixEnd_7197933 : Nat := 4983230072969 + 3 ^ 40 * 7197933 * 2
def baseEnd_7197933 : Nat := 3695999347859091787734815

theorem tailTrace_7197933 : CollatzResearch.WordTrace tailWord_7197933 prefixEnd_7197933 3695999347859091787734815 := by
  unfold tailWord_7197933
  simp only [CollatzResearch.WordTrace]
  refine ⟨262530184232125524931214453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175020122821417016620809635 262530184232125524931214453)
  ·
    refine ⟨24612204771761767962301355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262530184232125524931214453 24612204771761767962301355)
    ·
      refine ⟨36918307157642651943452033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24612204771761767962301355 36918307157642651943452033)
      ·
        refine ⟨27688730368231988957589025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36918307157642651943452033 27688730368231988957589025)
        ·
          refine ⟨20766547776173991718191769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27688730368231988957589025 20766547776173991718191769)
          ·
            refine ⟨15574910832130493788643827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20766547776173991718191769 15574910832130493788643827)
            ·
              refine ⟨23362366248195740682965741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15574910832130493788643827 23362366248195740682965741)
              ·
                refine ⟨8760887343073402756112153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23362366248195740682965741 8760887343073402756112153)
                ·
                  refine ⟨6570665507305052067084115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760887343073402756112153 6570665507305052067084115)
                  ·
                    refine ⟨9855998260957578100626173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6570665507305052067084115 9855998260957578100626173)
                    ·
                      refine ⟨3695999347859091787734815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9855998260957578100626173 3695999347859091787734815)
                      ·
                        rfl

theorem cell23_7197933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_7197933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197933 prefixEnd_7197933 := by exact prefixLift 7197933
  have htrace : WordTrace (prefixWord ++ tailWord_7197933) baseStart_7197933 baseEnd_7197933 := by
    simpa [prefixWord, tailWord_7197933, baseEnd_7197933] using wordTrace_append hprefix tailTrace_7197933
  have hstable : (prefixWord ++ tailWord_7197933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197933).length < 2 ^ (prefixWord ++ tailWord_7197933).sum := by decide
  have hdescent : baseEnd_7197933 < baseStart_7197933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197952 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 4]
def baseStart_7197952 : Nat := 118140960795 + 7197952 * 2 ^ 59
def prefixEnd_7197952 : Nat := 4983230072969 + 3 ^ 40 * 7197952 * 2
def baseEnd_7197952 : Nat := 3696009103991527213397227

theorem tailTrace_7197952 : CollatzResearch.WordTrace tailWord_7197952 prefixEnd_7197952 3696009103991527213397227 := by
  unfold tailWord_7197952
  simp only [CollatzResearch.WordTrace]
  refine ⟨131265438609528345588078055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175020584812704460784104073 131265438609528345588078055)
  ·
    refine ⟨196898157914292518382117083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131265438609528345588078055 196898157914292518382117083)
    ·
      refine ⟨295347236871438777573175625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196898157914292518382117083 295347236871438777573175625)
      ·
        refine ⟨221510427653579083179881719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295347236871438777573175625 221510427653579083179881719)
        ·
          refine ⟨332265641480368624769822579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221510427653579083179881719 332265641480368624769822579)
          ·
            refine ⟨498398462220552937154733869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332265641480368624769822579 498398462220552937154733869)
            ·
              refine ⟨186899423332707351433025201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 498398462220552937154733869 186899423332707351433025201)
              ·
                refine ⟨140174567499530513574768901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186899423332707351433025201 140174567499530513574768901)
                ·
                  refine ⟨26282731406161971295269169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140174567499530513574768901 26282731406161971295269169)
                  ·
                    refine ⟨19712048554621478471451877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26282731406161971295269169 19712048554621478471451877)
                    ·
                      refine ⟨3696009103991527213397227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19712048554621478471451877 3696009103991527213397227)
                      ·
                        rfl

theorem cell23_7197952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_7197952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197952 prefixEnd_7197952 := by exact prefixLift 7197952
  have htrace : WordTrace (prefixWord ++ tailWord_7197952) baseStart_7197952 baseEnd_7197952 := by
    simpa [prefixWord, tailWord_7197952, baseEnd_7197952] using wordTrace_append hprefix tailTrace_7197952
  have hstable : (prefixWord ++ tailWord_7197952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197952).length < 2 ^ (prefixWord ++ tailWord_7197952).sum := by decide
  have hdescent : baseEnd_7197952 < baseStart_7197952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197956 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_7197956 : Nat := 118140960795 + 7197956 * 2 ^ 59
def prefixEnd_7197956 : Nat := 4983230072969 + 3 ^ 40 * 7197956 * 2
def baseEnd_7197956 : Nat := 3696011157914145197747209

theorem tailTrace_7197956 : CollatzResearch.WordTrace tailWord_7197956 prefixEnd_7197956 3696011157914145197747209 := by
  unfold tailWord_7197956
  simp only [CollatzResearch.WordTrace]
  refine ⟨131265511555521099929650861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175020682074028133239534481 131265511555521099929650861)
  ·
    refine ⟨49224566833320412473619073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131265511555521099929650861 49224566833320412473619073)
    ·
      refine ⟨36918425124990309355214305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49224566833320412473619073 36918425124990309355214305)
      ·
        refine ⟨27688818843742732016410729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36918425124990309355214305 27688818843742732016410729)
        ·
          refine ⟨20766614132807049012308047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27688818843742732016410729 20766614132807049012308047)
          ·
            refine ⟨31149921199210573518462071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20766614132807049012308047 31149921199210573518462071)
            ·
              refine ⟨46724881798815860277693107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31149921199210573518462071 46724881798815860277693107)
              ·
                refine ⟨70087322698223790416539661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46724881798815860277693107 70087322698223790416539661)
                ·
                  refine ⟨26282746011833921406202373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70087322698223790416539661 26282746011833921406202373)
                  ·
                    refine ⟨4928014877218860263662945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26282746011833921406202373 4928014877218860263662945)
                    ·
                      refine ⟨3696011157914145197747209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4928014877218860263662945 3696011157914145197747209)
                      ·
                        rfl

theorem cell23_7197956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_7197956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197956 prefixEnd_7197956 := by exact prefixLift 7197956
  have htrace : WordTrace (prefixWord ++ tailWord_7197956) baseStart_7197956 baseEnd_7197956 := by
    simpa [prefixWord, tailWord_7197956, baseEnd_7197956] using wordTrace_append hprefix tailTrace_7197956
  have hstable : (prefixWord ++ tailWord_7197956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197956).length < 2 ^ (prefixWord ++ tailWord_7197956).sum := by decide
  have hdescent : baseEnd_7197956 < baseStart_7197956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197960 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 1, 3, 2]
def baseStart_7197960 : Nat := 118140960795 + 7197960 * 2 ^ 59
def prefixEnd_7197960 : Nat := 4983230072969 + 3 ^ 40 * 7197960 * 2
def baseEnd_7197960 : Nat := 3696013211836763182097191

theorem tailTrace_7197960 : CollatzResearch.WordTrace tailWord_7197960 prefixEnd_7197960 3696013211836763182097191 := by
  unfold tailWord_7197960
  simp only [CollatzResearch.WordTrace]
  refine ⟨131265584501513854271223667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175020779335351805694964889 131265584501513854271223667)
  ·
    refine ⟨196898376752270781406835501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131265584501513854271223667 196898376752270781406835501)
    ·
      refine ⟨73836891282101543027563313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196898376752270781406835501 73836891282101543027563313)
      ·
        refine ⟨55377668461576157270672485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73836891282101543027563313 55377668461576157270672485)
        ·
          refine ⟨10383312836545529488251091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55377668461576157270672485 10383312836545529488251091)
          ·
            refine ⟨15574969254818294232376637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10383312836545529488251091 15574969254818294232376637)
            ·
              refine ⟨5840613470556860337141239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15574969254818294232376637 5840613470556860337141239)
              ·
                refine ⟨8760920205835290505711859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5840613470556860337141239 8760920205835290505711859)
                ·
                  refine ⟨13141380308752935758567789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8760920205835290505711859 13141380308752935758567789)
                  ·
                    refine ⟨4928017615782350909462921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13141380308752935758567789 4928017615782350909462921)
                    ·
                      refine ⟨3696013211836763182097191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4928017615782350909462921 3696013211836763182097191)
                      ·
                        rfl

theorem cell23_7197960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_7197960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197960 prefixEnd_7197960 := by exact prefixLift 7197960
  have htrace : WordTrace (prefixWord ++ tailWord_7197960) baseStart_7197960 baseEnd_7197960 := by
    simpa [prefixWord, tailWord_7197960, baseEnd_7197960] using wordTrace_append hprefix tailTrace_7197960
  have hstable : (prefixWord ++ tailWord_7197960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197960).length < 2 ^ (prefixWord ++ tailWord_7197960).sum := by decide
  have hdescent : baseEnd_7197960 < baseStart_7197960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197986 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_7197986 : Nat := 118140960795 + 7197986 * 2 ^ 59
def prefixEnd_7197986 : Nat := 4983230072969 + 3 ^ 40 * 7197986 * 2
def baseEnd_7197986 : Nat := 3696026562333780080372071

theorem tailTrace_7197986 : CollatzResearch.WordTrace tailWord_7197986 prefixEnd_7197986 3696026562333780080372071 := by
  unfold tailWord_7197986
  simp only [CollatzResearch.WordTrace]
  refine ⟨65633029325233378745723453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175021411533955676655262541 65633029325233378745723453)
  ·
    refine ⟨24612385996962517029646295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65633029325233378745723453 24612385996962517029646295)
    ·
      refine ⟨36918578995443775544469443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24612385996962517029646295 36918578995443775544469443)
      ·
        refine ⟨55377868493165663316704165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36918578995443775544469443 55377868493165663316704165)
        ·
          refine ⟨10383350342468561871882031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55377868493165663316704165 10383350342468561871882031)
          ·
            refine ⟨15575025513702842807823047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10383350342468561871882031 15575025513702842807823047)
            ·
              refine ⟨23362538270554264211734571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15575025513702842807823047 23362538270554264211734571)
              ·
                refine ⟨35043807405831396317601857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23362538270554264211734571 35043807405831396317601857)
                ·
                  refine ⟨26282855554373547238201393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35043807405831396317601857 26282855554373547238201393)
                  ·
                    refine ⟨19712141665780160428651045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26282855554373547238201393 19712141665780160428651045)
                    ·
                      refine ⟨3696026562333780080372071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19712141665780160428651045 3696026562333780080372071)
                      ·
                        rfl

theorem cell23_7197986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_7197986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197986 prefixEnd_7197986 := by exact prefixLift 7197986
  have htrace : WordTrace (prefixWord ++ tailWord_7197986) baseStart_7197986 baseEnd_7197986 := by
    simpa [prefixWord, tailWord_7197986, baseEnd_7197986] using wordTrace_append hprefix tailTrace_7197986
  have hstable : (prefixWord ++ tailWord_7197986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197986).length < 2 ^ (prefixWord ++ tailWord_7197986).sum := by decide
  have hdescent : baseEnd_7197986 < baseStart_7197986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197989 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 1, 5, 3]
def baseStart_7197989 : Nat := 118140960795 + 7197989 * 2 ^ 59
def prefixEnd_7197989 : Nat := 4983230072969 + 3 ^ 40 * 7197989 * 2
def baseEnd_7197989 : Nat := 3696028102775743568634557

theorem tailTrace_7197989 : CollatzResearch.WordTrace tailWord_7197989 prefixEnd_7197989 3696028102775743568634557 := by
  unfold tailWord_7197989
  simp only [CollatzResearch.WordTrace]
  refine ⟨262532226719922646495253021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175021484479948430996835347 262532226719922646495253021)
  ·
    refine ⟨98449585019970992435719883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262532226719922646495253021 98449585019970992435719883)
    ·
      refine ⟨147674377529956488653579825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98449585019970992435719883 147674377529956488653579825)
      ·
        refine ⟨110755783147467366490184869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147674377529956488653579825 110755783147467366490184869)
        ·
          refine ⟨20766709340150131216909663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110755783147467366490184869 20766709340150131216909663)
          ·
            refine ⟨31150064010225196825364495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20766709340150131216909663 31150064010225196825364495)
            ·
              refine ⟨46725096015337795238046743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31150064010225196825364495 46725096015337795238046743)
              ·
                refine ⟨70087644023006692857070115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46725096015337795238046743 70087644023006692857070115)
                ·
                  refine ⟨105131466034510039285605173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70087644023006692857070115 105131466034510039285605173)
                  ·
                    refine ⟨9856074940735316183025485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105131466034510039285605173 9856074940735316183025485)
                    ·
                      refine ⟨3696028102775743568634557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9856074940735316183025485 3696028102775743568634557)
                      ·
                        rfl

theorem cell23_7197989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_7197989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197989 prefixEnd_7197989 := by exact prefixLift 7197989
  have htrace : WordTrace (prefixWord ++ tailWord_7197989) baseStart_7197989 baseEnd_7197989 := by
    simpa [prefixWord, tailWord_7197989, baseEnd_7197989] using wordTrace_append hprefix tailTrace_7197989
  have hstable : (prefixWord ++ tailWord_7197989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197989).length < 2 ^ (prefixWord ++ tailWord_7197989).sum := by decide
  have hdescent : baseEnd_7197989 < baseStart_7197989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7197999 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 4, 5, 2]
def baseStart_7197999 : Nat := 118140960795 + 7197999 * 2 ^ 59
def prefixEnd_7197999 : Nat := 4983230072969 + 3 ^ 40 * 7197999 * 2
def baseEnd_7197999 : Nat := 3696033237582288529509511

theorem tailTrace_7197999 : CollatzResearch.WordTrace tailWord_7197999 prefixEnd_7197999 3696033237582288529509511 := by
  unfold tailWord_7197999
  simp only [CollatzResearch.WordTrace]
  refine ⟨262532591449886418203117051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175021727633257612135411367 262532591449886418203117051)
  ·
    refine ⟨393798887174829627304675577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262532591449886418203117051 393798887174829627304675577)
    ·
      refine ⟨295349165381122220478506683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393798887174829627304675577 295349165381122220478506683)
      ·
        refine ⟨443023748071683330717760025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295349165381122220478506683 443023748071683330717760025)
        ·
          refine ⟨332267811053762498038320019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443023748071683330717760025 332267811053762498038320019)
          ·
            refine ⟨498401716580643747057480029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332267811053762498038320019 498401716580643747057480029)
            ·
              refine ⟨186900643717741405146555011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 498401716580643747057480029 186900643717741405146555011)
              ·
                refine ⟨280350965576612107719832517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186900643717741405146555011 280350965576612107719832517)
                ·
                  refine ⟨52565806045614770197468597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280350965576612107719832517 52565806045614770197468597)
                  ·
                    refine ⟨4928044316776384706012681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52565806045614770197468597 4928044316776384706012681)
                    ·
                      refine ⟨3696033237582288529509511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4928044316776384706012681 3696033237582288529509511)
                      ·
                        rfl

theorem cell23_7197999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 5, 2].length) (baseStart_7197999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7197999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7197999 prefixEnd_7197999 := by exact prefixLift 7197999
  have htrace : WordTrace (prefixWord ++ tailWord_7197999) baseStart_7197999 baseEnd_7197999 := by
    simpa [prefixWord, tailWord_7197999, baseEnd_7197999] using wordTrace_append hprefix tailTrace_7197999
  have hstable : (prefixWord ++ tailWord_7197999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7197999).length < 2 ^ (prefixWord ++ tailWord_7197999).sum := by decide
  have hdescent : baseEnd_7197999 < baseStart_7197999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7197999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198066 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_7198066 : Nat := 118140960795 + 7198066 * 2 ^ 59
def prefixEnd_7198066 : Nat := 4983230072969 + 3 ^ 40 * 7198066 * 2
def baseEnd_7198066 : Nat := 3696067640786139767371703

theorem tailTrace_7198066 : CollatzResearch.WordTrace tailWord_7198066 prefixEnd_7198066 3696067640786139767371703 := by
  unfold tailWord_7198066
  simp only [CollatzResearch.WordTrace]
  refine ⟨65633758785160922161451513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175023356760429125763870701 65633758785160922161451513)
  ·
    refine ⟨49225319088870691621088635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65633758785160922161451513 49225319088870691621088635)
    ·
      refine ⟨73837978633306037431632953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49225319088870691621088635 73837978633306037431632953)
      ·
        refine ⟨55378483974979528073724715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73837978633306037431632953 55378483974979528073724715)
        ·
          refine ⟨83067725962469292110587073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55378483974979528073724715 83067725962469292110587073)
          ·
            refine ⟨62300794471851969082940305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83067725962469292110587073 62300794471851969082940305)
            ·
              refine ⟨46725595853888976812205229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62300794471851969082940305 46725595853888976812205229)
              ·
                refine ⟨17522098445208366304576961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46725595853888976812205229 17522098445208366304576961)
                ·
                  refine ⟨13141573833906274728432721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17522098445208366304576961 13141573833906274728432721)
                  ·
                    refine ⟨9856180375429706046324541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13141573833906274728432721 9856180375429706046324541)
                    ·
                      refine ⟨3696067640786139767371703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9856180375429706046324541 3696067640786139767371703)
                      ·
                        rfl

theorem cell23_7198066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_7198066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198066 prefixEnd_7198066 := by exact prefixLift 7198066
  have htrace : WordTrace (prefixWord ++ tailWord_7198066) baseStart_7198066 baseEnd_7198066 := by
    simpa [prefixWord, tailWord_7198066, baseEnd_7198066] using wordTrace_append hprefix tailTrace_7198066
  have hstable : (prefixWord ++ tailWord_7198066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198066).length < 2 ^ (prefixWord ++ tailWord_7198066).sum := by decide
  have hdescent : baseEnd_7198066 < baseStart_7198066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198073 : List Nat := [1, 2, 1, 3, 2, 1, 5, 3, 1, 4]
def baseStart_7198073 : Nat := 118140960795 + 7198073 * 2 ^ 59
def prefixEnd_7198073 : Nat := 4983230072969 + 3 ^ 40 * 7198073 * 2
def baseEnd_7198073 : Nat := 1232023745050240413328057

theorem tailTrace_7198073 : CollatzResearch.WordTrace tailWord_7198073 prefixEnd_7198073 1232023745050240413328057 := by
  unfold tailWord_7198073
  simp only [CollatzResearch.WordTrace]
  refine ⟨262535290451618328841310873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175023526967745552560873915 262535290451618328841310873)
  ·
    refine ⟨196901467838713746630983155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262535290451618328841310873 196901467838713746630983155)
    ·
      refine ⟨295352201758070619946474733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196901467838713746630983155 295352201758070619946474733)
      ·
        refine ⟨110757075659276482479928025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295352201758070619946474733 110757075659276482479928025)
        ·
          refine ⟨83067806744457361859946019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110757075659276482479928025 83067806744457361859946019)
          ·
            refine ⟨124601710116686042789919029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83067806744457361859946019 124601710116686042789919029)
            ·
              refine ⟨11681410323439316511554909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124601710116686042789919029 11681410323439316511554909)
              ·
                refine ⟨4380528871289743691833091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11681410323439316511554909 4380528871289743691833091)
                ·
                  refine ⟨6570793306934615537749637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380528871289743691833091 6570793306934615537749637)
                  ·
                    refine ⟨1232023745050240413328057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6570793306934615537749637 1232023745050240413328057)
                    ·
                      rfl

theorem cell23_7198073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 1, 4].length) (baseStart_7198073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198073 prefixEnd_7198073 := by exact prefixLift 7198073
  have htrace : WordTrace (prefixWord ++ tailWord_7198073) baseStart_7198073 baseEnd_7198073 := by
    simpa [prefixWord, tailWord_7198073, baseEnd_7198073] using wordTrace_append hprefix tailTrace_7198073
  have hstable : (prefixWord ++ tailWord_7198073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198073).length < 2 ^ (prefixWord ++ tailWord_7198073).sum := by decide
  have hdescent : baseEnd_7198073 < baseStart_7198073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198136 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 1, 1, 4]
def baseStart_7198136 : Nat := 118140960795 + 7198136 * 2 ^ 59
def prefixEnd_7198136 : Nat := 4983230072969 + 3 ^ 40 * 7198136 * 2
def baseEnd_7198136 : Nat := 3696103584431954493496381

theorem tailTrace_7198136 : CollatzResearch.WordTrace tailWord_7198136 prefixEnd_7198136 3696103584431954493496381 := by
  unfold tailWord_7198136
  simp only [CollatzResearch.WordTrace]
  refine ⟨131268794125195045300427131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175025058833593393733902841 131268794125195045300427131)
  ·
    refine ⟨196903191187792567950640697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131268794125195045300427131 196903191187792567950640697)
    ·
      refine ⟨147677393390844425962980523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196903191187792567950640697 147677393390844425962980523)
      ·
        refine ⟨221516090086266638944470785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147677393390844425962980523 221516090086266638944470785)
        ·
          refine ⟨166137067564699979208353089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221516090086266638944470785 166137067564699979208353089)
          ·
            refine ⟨124602800673524984406264817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166137067564699979208353089 124602800673524984406264817)
            ·
              refine ⟨93452100505143738304698613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124602800673524984406264817 93452100505143738304698613)
              ·
                refine ⟨8761134422357225466065495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93452100505143738304698613 8761134422357225466065495)
                ·
                  refine ⟨13141701633535838199098243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8761134422357225466065495 13141701633535838199098243)
                  ·
                    refine ⟨19712552450303757298647365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13141701633535838199098243 19712552450303757298647365)
                    ·
                      refine ⟨3696103584431954493496381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19712552450303757298647365 3696103584431954493496381)
                      ·
                        rfl

theorem cell23_7198136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_7198136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198136 prefixEnd_7198136 := by exact prefixLift 7198136
  have htrace : WordTrace (prefixWord ++ tailWord_7198136) baseStart_7198136 baseEnd_7198136 := by
    simpa [prefixWord, tailWord_7198136, baseEnd_7198136] using wordTrace_append hprefix tailTrace_7198136
  have hstable : (prefixWord ++ tailWord_7198136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198136).length < 2 ^ (prefixWord ++ tailWord_7198136).sum := by decide
  have hdescent : baseEnd_7198136 < baseStart_7198136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198153 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 3, 2, 2]
def baseStart_7198153 : Nat := 118140960795 + 7198153 * 2 ^ 59
def prefixEnd_7198153 : Nat := 4983230072969 + 3 ^ 40 * 7198153 * 2
def baseEnd_7198153 : Nat := 3696112313603080926983803

theorem tailTrace_7198153 : CollatzResearch.WordTrace tailWord_7198153 prefixEnd_7198153 3696112313603080926983803 := by
  unfold tailWord_7198153
  simp only [CollatzResearch.WordTrace]
  refine ⟨262538208291328502504223113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175025472194219001669482075 262538208291328502504223113)
  ·
    refine ⟨196903656218496376878167335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262538208291328502504223113 196903656218496376878167335)
    ·
      refine ⟨295355484327744565317251003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196903656218496376878167335 295355484327744565317251003)
      ·
        refine ⟨443033226491616847975876505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295355484327744565317251003 443033226491616847975876505)
        ·
          refine ⟨332274919868712635981907379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443033226491616847975876505 332274919868712635981907379)
          ·
            refine ⟨498412379803068953972861069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332274919868712635981907379 498412379803068953972861069)
            ·
              refine ⟨186904642426150857739822901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 498412379803068953972861069 186904642426150857739822901)
              ·
                refine ⟨17522310227451642913108397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186904642426150857739822901 17522310227451642913108397)
                ·
                  refine ⟨6570866335294366092415649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17522310227451642913108397 6570866335294366092415649)
                  ·
                    refine ⟨4928149751470774569311737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6570866335294366092415649 4928149751470774569311737)
                    ·
                      refine ⟨3696112313603080926983803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4928149751470774569311737 3696112313603080926983803)
                      ·
                        rfl

theorem cell23_7198153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 2, 2].length) (baseStart_7198153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198153 prefixEnd_7198153 := by exact prefixLift 7198153
  have htrace : WordTrace (prefixWord ++ tailWord_7198153) baseStart_7198153 baseEnd_7198153 := by
    simpa [prefixWord, tailWord_7198153, baseEnd_7198153] using wordTrace_append hprefix tailTrace_7198153
  have hstable : (prefixWord ++ tailWord_7198153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198153).length < 2 ^ (prefixWord ++ tailWord_7198153).sum := by decide
  have hdescent : baseEnd_7198153 < baseStart_7198153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198159 : List Nat := [1, 1, 2, 1, 1, 4, 5, 8]
def baseStart_7198159 : Nat := 118140960795 + 7198159 * 2 ^ 59
def prefixEnd_7198159 : Nat := 4983230072969 + 3 ^ 40 * 7198159 * 2
def baseEnd_7198159 : Nat := 136893162758778070500325

theorem tailTrace_7198159 : CollatzResearch.WordTrace tailWord_7198159 prefixEnd_7198159 136893162758778070500325 := by
  unfold tailWord_7198159
  simp only [CollatzResearch.WordTrace]
  refine ⟨262538427129306765528941531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175025618086204510352627687 262538427129306765528941531)
  ·
    refine ⟨393807640693960148293412297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262538427129306765528941531 393807640693960148293412297)
    ·
      refine ⟨295355730520470111220059223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393807640693960148293412297 295355730520470111220059223)
      ·
        refine ⟨443033595780705166830088835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295355730520470111220059223 443033595780705166830088835)
        ·
          refine ⟨664550393671057750245133253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443033595780705166830088835 664550393671057750245133253)
          ·
            refine ⟨124603198813323328170962485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 664550393671057750245133253 124603198813323328170962485)
            ·
              refine ⟨11681549888749062016027733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124603198813323328170962485 11681549888749062016027733)
              ·
                refine ⟨136893162758778070500325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11681549888749062016027733 136893162758778070500325)
                ·
                  rfl

theorem cell23_7198159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 8].length) (baseStart_7198159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198159 prefixEnd_7198159 := by exact prefixLift 7198159
  have htrace : WordTrace (prefixWord ++ tailWord_7198159) baseStart_7198159 baseEnd_7198159 := by
    simpa [prefixWord, tailWord_7198159, baseEnd_7198159] using wordTrace_append hprefix tailTrace_7198159
  have hstable : (prefixWord ++ tailWord_7198159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198159).length < 2 ^ (prefixWord ++ tailWord_7198159).sum := by decide
  have hdescent : baseEnd_7198159 < baseStart_7198159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198170 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2]
def baseStart_7198170 : Nat := 118140960795 + 7198170 * 2 ^ 59
def prefixEnd_7198170 : Nat := 4983230072969 + 3 ^ 40 * 7198170 * 2
def baseEnd_7198170 : Nat := 3696121042774207360471225

theorem tailTrace_7198170 : CollatzResearch.WordTrace tailWord_7198170 prefixEnd_7198170 3696121042774207360471225 := by
  unfold tailWord_7198170
  simp only [CollatzResearch.WordTrace]
  refine ⟨65634707083066728601897991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175025885554844609605061309 65634707083066728601897991)
  ·
    refine ⟨98452060624600092902846987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65634707083066728601897991 98452060624600092902846987)
    ·
      refine ⟨147678090936900139354270481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98452060624600092902846987 147678090936900139354270481)
      ·
        refine ⟨110758568202675104515702861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147678090936900139354270481 110758568202675104515702861)
        ·
          refine ⟨41534463076003164193388573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110758568202675104515702861 41534463076003164193388573)
          ·
            refine ⟨15575423653501186572520715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41534463076003164193388573 15575423653501186572520715)
            ·
              refine ⟨23363135480251779858781073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15575423653501186572520715 23363135480251779858781073)
              ·
                refine ⟨17522351610188834894085805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23363135480251779858781073 17522351610188834894085805)
                ·
                  refine ⟨6570881853820813085282177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17522351610188834894085805 6570881853820813085282177)
                  ·
                    refine ⟨4928161390365609813961633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6570881853820813085282177 4928161390365609813961633)
                    ·
                      refine ⟨3696121042774207360471225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4928161390365609813961633 3696121042774207360471225)
                      ·
                        rfl

theorem cell23_7198170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_7198170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198170 prefixEnd_7198170 := by exact prefixLift 7198170
  have htrace : WordTrace (prefixWord ++ tailWord_7198170) baseStart_7198170 baseEnd_7198170 := by
    simpa [prefixWord, tailWord_7198170, baseEnd_7198170] using wordTrace_append hprefix tailTrace_7198170
  have hstable : (prefixWord ++ tailWord_7198170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198170).length < 2 ^ (prefixWord ++ tailWord_7198170).sum := by decide
  have hdescent : baseEnd_7198170 < baseStart_7198170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198173 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_7198173 : Nat := 118140960795 + 7198173 * 2 ^ 59
def prefixEnd_7198173 : Nat := 4983230072969 + 3 ^ 40 * 7198173 * 2
def baseEnd_7198173 : Nat := 3696122583216170848733711

theorem tailTrace_7198173 : CollatzResearch.WordTrace tailWord_7198173 prefixEnd_7198173 3696122583216170848733711 := by
  unfold tailWord_7198173
  simp only [CollatzResearch.WordTrace]
  refine ⟨262538937751256045919951173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175025958500837363946634115 262538937751256045919951173)
  ·
    refine ⟨49226050828360508609990845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262538937751256045919951173 49226050828360508609990845)
    ·
      refine ⟨18459769060635190728746567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49226050828360508609990845 18459769060635190728746567)
      ·
        refine ⟨27689653590952786093119851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18459769060635190728746567 27689653590952786093119851)
        ·
          refine ⟨41534480386429179139679777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27689653590952786093119851 41534480386429179139679777)
          ·
            refine ⟨31150860289821884354759833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41534480386429179139679777 31150860289821884354759833)
            ·
              refine ⟨23363145217366413266069875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31150860289821884354759833 23363145217366413266069875)
              ·
                refine ⟨35044717826049619899104813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23363145217366413266069875 35044717826049619899104813)
                ·
                  refine ⟨13141769184768607462164305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35044717826049619899104813 13141769184768607462164305)
                  ·
                    refine ⟨9856326888576455596623229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13141769184768607462164305 9856326888576455596623229)
                    ·
                      refine ⟨3696122583216170848733711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9856326888576455596623229 3696122583216170848733711)
                      ·
                        rfl

theorem cell23_7198173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_7198173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198173 prefixEnd_7198173 := by exact prefixLift 7198173
  have htrace : WordTrace (prefixWord ++ tailWord_7198173) baseStart_7198173 baseEnd_7198173 := by
    simpa [prefixWord, tailWord_7198173, baseEnd_7198173] using wordTrace_append hprefix tailTrace_7198173
  have hstable : (prefixWord ++ tailWord_7198173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198173).length < 2 ^ (prefixWord ++ tailWord_7198173).sum := by decide
  have hdescent : baseEnd_7198173 < baseStart_7198173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198197 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 2, 4]
def baseStart_7198197 : Nat := 118140960795 + 7198197 * 2 ^ 59
def prefixEnd_7198197 : Nat := 4983230072969 + 3 ^ 40 * 7198197 * 2
def baseEnd_7198197 : Nat := 1232044968917292918277867

theorem tailTrace_7198197 : CollatzResearch.WordTrace tailWord_7198197 prefixEnd_7198197 1232044968917292918277867 := by
  unfold tailWord_7198197
  simp only [CollatzResearch.WordTrace]
  refine ⟨262539813103169098018824845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175026542068779398679216563 262539813103169098018824845)
  ·
    refine ⟨98452429913688411757059317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262539813103169098018824845 98452429913688411757059317)
    ·
      refine ⟨9229915304408288602224311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98452429913688411757059317 9229915304408288602224311)
      ·
        refine ⟨13844872956612432903336467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9229915304408288602224311 13844872956612432903336467)
        ·
          refine ⟨20767309434918649355004701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13844872956612432903336467 20767309434918649355004701)
          ·
            refine ⟨7787741038094493508126763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20767309434918649355004701 7787741038094493508126763)
            ·
              refine ⟨11681611557141740262190145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787741038094493508126763 11681611557141740262190145)
              ·
                refine ⟨8761208667856305196642609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11681611557141740262190145 8761208667856305196642609)
                ·
                  refine ⟨6570906500892228897481957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8761208667856305196642609 6570906500892228897481957)
                  ·
                    refine ⟨1232044968917292918277867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6570906500892228897481957 1232044968917292918277867)
                    ·
                      rfl

theorem cell23_7198197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_7198197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198197 prefixEnd_7198197 := by exact prefixLift 7198197
  have htrace : WordTrace (prefixWord ++ tailWord_7198197) baseStart_7198197 baseEnd_7198197 := by
    simpa [prefixWord, tailWord_7198197, baseEnd_7198197] using wordTrace_append hprefix tailTrace_7198197
  have hstable : (prefixWord ++ tailWord_7198197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198197).length < 2 ^ (prefixWord ++ tailWord_7198197).sum := by decide
  have hdescent : baseEnd_7198197 < baseStart_7198197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198199 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_7198199 : Nat := 118140960795 + 7198199 * 2 ^ 59
def prefixEnd_7198199 : Nat := 4983230072969 + 3 ^ 40 * 7198199 * 2
def baseEnd_7198199 : Nat := 3696135933713187747008591

theorem tailTrace_7198199 : CollatzResearch.WordTrace tailWord_7198199 prefixEnd_7198199 3696135933713187747008591 := by
  unfold tailWord_7198199
  simp only [CollatzResearch.WordTrace]
  refine ⟨262539886049161852360397651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175026590699441234906931767 262539886049161852360397651)
  ·
    refine ⟨393809829073742778540596477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262539886049161852360397651 393809829073742778540596477)
    ·
      refine ⟨147678685902653541952723679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393809829073742778540596477 147678685902653541952723679)
      ·
        refine ⟨221518028853980312929085519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147678685902653541952723679 221518028853980312929085519)
        ·
          refine ⟨332277043280970469393628279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221518028853980312929085519 332277043280970469393628279)
          ·
            refine ⟨498415564921455704090442419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332277043280970469393628279 498415564921455704090442419)
            ·
              refine ⟨747623347382183556135663629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498415564921455704090442419 747623347382183556135663629)
              ·
                refine ⟨280358755268318833550873861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 747623347382183556135663629 280358755268318833550873861)
                ·
                  refine ⟨52567266612809781290788849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280358755268318833550873861 52567266612809781290788849)
                  ·
                    refine ⟨39425449959607335968091637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52567266612809781290788849 39425449959607335968091637)
                    ·
                      refine ⟨3696135933713187747008591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39425449959607335968091637 3696135933713187747008591)
                      ·
                        rfl

theorem cell23_7198199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_7198199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198199 prefixEnd_7198199 := by exact prefixLift 7198199
  have htrace : WordTrace (prefixWord ++ tailWord_7198199) baseStart_7198199 baseEnd_7198199 := by
    simpa [prefixWord, tailWord_7198199, baseEnd_7198199] using wordTrace_append hprefix tailTrace_7198199
  have hstable : (prefixWord ++ tailWord_7198199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198199).length < 2 ^ (prefixWord ++ tailWord_7198199).sum := by decide
  have hdescent : baseEnd_7198199 < baseStart_7198199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198214 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_7198214 : Nat := 118140960795 + 7198214 * 2 ^ 59
def prefixEnd_7198214 : Nat := 4983230072969 + 3 ^ 40 * 7198214 * 2
def baseEnd_7198214 : Nat := 1232047878641001729440341

theorem tailTrace_7198214 : CollatzResearch.WordTrace tailWord_7198214 prefixEnd_7198214 1232047878641001729440341 := by
  unfold tailWord_7198214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8204388535753359685068553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175026955429405006614795797 8204388535753359685068553)
  ·
    refine ⟨6153291401815019763801415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8204388535753359685068553 6153291401815019763801415)
    ·
      refine ⟨9229937102722529645702123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6153291401815019763801415 9229937102722529645702123)
      ·
        refine ⟨13844905654083794468553185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9229937102722529645702123 13844905654083794468553185)
        ·
          refine ⟨10383679240562845851414889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13844905654083794468553185 10383679240562845851414889)
          ·
            refine ⟨7787759430422134388561167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10383679240562845851414889 7787759430422134388561167)
            ·
              refine ⟨11681639145633201582841751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787759430422134388561167 11681639145633201582841751)
              ·
                refine ⟨17522458718449802374262627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11681639145633201582841751 17522458718449802374262627)
                ·
                  refine ⟨26283688077674703561393941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17522458718449802374262627 26283688077674703561393941)
                  ·
                    refine ⟨1232047878641001729440341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26283688077674703561393941 1232047878641001729440341)
                    ·
                      rfl

theorem cell23_7198214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_7198214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198214 prefixEnd_7198214 := by exact prefixLift 7198214
  have htrace : WordTrace (prefixWord ++ tailWord_7198214) baseStart_7198214 baseEnd_7198214 := by
    simpa [prefixWord, tailWord_7198214, baseEnd_7198214] using wordTrace_append hprefix tailTrace_7198214
  have hstable : (prefixWord ++ tailWord_7198214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198214).length < 2 ^ (prefixWord ++ tailWord_7198214).sum := by decide
  have hdescent : baseEnd_7198214 < baseStart_7198214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198220 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 1, 3, 3]
def baseStart_7198220 : Nat := 118140960795 + 7198220 * 2 ^ 59
def prefixEnd_7198220 : Nat := 4983230072969 + 3 ^ 40 * 7198220 * 2
def baseEnd_7198220 : Nat := 3696146716806932164845995

theorem tailTrace_7198220 : CollatzResearch.WordTrace tailWord_7198220 prefixEnd_7198220 3696146716806932164845995 := by
  unfold tailWord_7198220
  simp only [CollatzResearch.WordTrace]
  refine ⟨131270325991042886473456057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175027101321390515297941409 131270325991042886473456057)
  ·
    refine ⟨98452744493282164855092043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131270325991042886473456057 98452744493282164855092043)
    ·
      refine ⟨147679116739923247282638065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98452744493282164855092043 147679116739923247282638065)
      ·
        refine ⟨110759337554942435461978549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147679116739923247282638065 110759337554942435461978549)
        ·
          refine ⟨10383687895775853324560489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110759337554942435461978549 10383687895775853324560489)
          ·
            refine ⟨7787765921831889993420367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10383687895775853324560489 7787765921831889993420367)
            ·
              refine ⟨11681648882747834990130551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787765921831889993420367 11681648882747834990130551)
              ·
                refine ⟨17522473324121752485195827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11681648882747834990130551 17522473324121752485195827)
                ·
                  refine ⟨26283709986182628727793741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17522473324121752485195827 26283709986182628727793741)
                  ·
                    refine ⟨9856391244818485772922653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26283709986182628727793741 9856391244818485772922653)
                    ·
                      refine ⟨3696146716806932164845995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9856391244818485772922653 3696146716806932164845995)
                      ·
                        rfl

theorem cell23_7198220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_7198220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198220 prefixEnd_7198220 := by exact prefixLift 7198220
  have htrace : WordTrace (prefixWord ++ tailWord_7198220) baseStart_7198220 baseEnd_7198220 := by
    simpa [prefixWord, tailWord_7198220, baseEnd_7198220] using wordTrace_append hprefix tailTrace_7198220
  have hstable : (prefixWord ++ tailWord_7198220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198220).length < 2 ^ (prefixWord ++ tailWord_7198220).sum := by decide
  have hdescent : baseEnd_7198220 < baseStart_7198220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198316 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_7198316 : Nat := 118140960795 + 7198316 * 2 ^ 59
def prefixEnd_7198316 : Nat := 4983230072969 + 3 ^ 40 * 7198316 * 2
def baseEnd_7198316 : Nat := 3696196010949763789245553

theorem tailTrace_7198316 : CollatzResearch.WordTrace tailWord_7198316 prefixEnd_7198316 3696196010949763789245553 := by
  unfold tailWord_7198316
  simp only [CollatzResearch.WordTrace]
  refine ⟨131272076694868990671203401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175029435593158654228271201 131272076694868990671203401)
  ·
    refine ⟨98454057521151743003402551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131272076694868990671203401 98454057521151743003402551)
    ·
      refine ⟨147681086281727614505103827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98454057521151743003402551 147681086281727614505103827)
      ·
        refine ⟨221521629422591421757655741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147681086281727614505103827 221521629422591421757655741)
        ·
          refine ⟨83070611033471783159120903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221521629422591421757655741 83070611033471783159120903)
          ·
            refine ⟨124605916550207674738681355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83070611033471783159120903 124605916550207674738681355)
            ·
              refine ⟨186908874825311512108022033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124605916550207674738681355 186908874825311512108022033)
              ·
                refine ⟨140181656118983634081016525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186908874825311512108022033 140181656118983634081016525)
                ·
                  refine ⟨52568121044618862780381197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140181656118983634081016525 52568121044618862780381197)
                  ·
                    refine ⟨19713045391732073542642949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52568121044618862780381197 19713045391732073542642949)
                    ·
                      refine ⟨3696196010949763789245553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19713045391732073542642949 3696196010949763789245553)
                      ·
                        rfl

theorem cell23_7198316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_7198316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198316 prefixEnd_7198316 := by exact prefixLift 7198316
  have htrace : WordTrace (prefixWord ++ tailWord_7198316) baseStart_7198316 baseEnd_7198316 := by
    simpa [prefixWord, tailWord_7198316, baseEnd_7198316] using wordTrace_append hprefix tailTrace_7198316
  have hstable : (prefixWord ++ tailWord_7198316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198316).length < 2 ^ (prefixWord ++ tailWord_7198316).sum := by decide
  have hdescent : baseEnd_7198316 < baseStart_7198316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198343 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 5, 4]
def baseStart_7198343 : Nat := 118140960795 + 7198343 * 2 ^ 59
def prefixEnd_7198343 : Nat := 4983230072969 + 3 ^ 40 * 7198343 * 2
def baseEnd_7198343 : Nat := 1232069958309145061202643

theorem tailTrace_7198343 : CollatzResearch.WordTrace tailWord_7198343 prefixEnd_7198343 1232069958309145061202643 := by
  unfold tailWord_7198343
  simp only [CollatzResearch.WordTrace]
  refine ⟨262545138160640164953639683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175030092107093443302426455 262545138160640164953639683)
  ·
    refine ⟨393817707240960247430459525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262545138160640164953639683 393817707240960247430459525)
    ·
      refine ⟨73840820107680046393211161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393817707240960247430459525 73840820107680046393211161)
      ·
        refine ⟨55380615080760034794908371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73840820107680046393211161 55380615080760034794908371)
        ·
          refine ⟨83070922621140052192362557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55380615080760034794908371 83070922621140052192362557)
          ·
            refine ⟨31151595982927519572135959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83070922621140052192362557 31151595982927519572135959)
            ·
              refine ⟨46727393974391279358203939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31151595982927519572135959 46727393974391279358203939)
              ·
                refine ⟨70091090961586919037305909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46727393974391279358203939 70091090961586919037305909)
                ·
                  refine ⟨6571039777648773659747429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70091090961586919037305909 6571039777648773659747429)
                  ·
                    refine ⟨1232069958309145061202643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6571039777648773659747429 1232069958309145061202643)
                    ·
                      rfl

theorem cell23_7198343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_7198343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198343 prefixEnd_7198343 := by exact prefixLift 7198343
  have htrace : WordTrace (prefixWord ++ tailWord_7198343) baseStart_7198343 baseEnd_7198343 := by
    simpa [prefixWord, tailWord_7198343, baseEnd_7198343] using wordTrace_append hprefix tailTrace_7198343
  have hstable : (prefixWord ++ tailWord_7198343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198343).length < 2 ^ (prefixWord ++ tailWord_7198343).sum := by decide
  have hdescent : baseEnd_7198343 < baseStart_7198343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198350 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_7198350 : Nat := 118140960795 + 7198350 * 2 ^ 59
def prefixEnd_7198350 : Nat := 4983230072969 + 3 ^ 40 * 7198350 * 2
def baseEnd_7198350 : Nat := 3696213469292016656220397

theorem tailTrace_7198350 : CollatzResearch.WordTrace tailWord_7198350 prefixEnd_7198350 3696213469292016656220397 := by
  unfold tailWord_7198350
  simp only [CollatzResearch.WordTrace]
  refine ⟨32818174183951850643643063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175030262314409870099429669 32818174183951850643643063)
  ·
    refine ⟨49227261275927775965464595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32818174183951850643643063 49227261275927775965464595)
    ·
      refine ⟨73840891913891663948196893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49227261275927775965464595 73840891913891663948196893)
      ·
        refine ⟨27690334467709373980573835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73840891913891663948196893 27690334467709373980573835)
        ·
          refine ⟨41535501701564060970860753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27690334467709373980573835 41535501701564060970860753)
          ·
            refine ⟨31151626276173045728145565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41535501701564060970860753 31151626276173045728145565)
            ·
              refine ⟨11681859853564892148054587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31151626276173045728145565 11681859853564892148054587)
              ·
                refine ⟨17522789780347338222081881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11681859853564892148054587 17522789780347338222081881)
                ·
                  refine ⟨13142092335260503666561411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17522789780347338222081881 13142092335260503666561411)
                  ·
                    refine ⟨19713138502890755499842117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13142092335260503666561411 19713138502890755499842117)
                    ·
                      refine ⟨3696213469292016656220397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19713138502890755499842117 3696213469292016656220397)
                      ·
                        rfl

theorem cell23_7198350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_7198350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198350 prefixEnd_7198350 := by exact prefixLift 7198350
  have htrace : WordTrace (prefixWord ++ tailWord_7198350) baseStart_7198350 baseEnd_7198350 := by
    simpa [prefixWord, tailWord_7198350, baseEnd_7198350] using wordTrace_append hprefix tailTrace_7198350
  have hstable : (prefixWord ++ tailWord_7198350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198350).length < 2 ^ (prefixWord ++ tailWord_7198350).sum := by decide
  have hdescent : baseEnd_7198350 < baseStart_7198350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198353 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 3]
def baseStart_7198353 : Nat := 118140960795 + 7198353 * 2 ^ 59
def prefixEnd_7198353 : Nat := 4983230072969 + 3 ^ 40 * 7198353 * 2
def baseEnd_7198353 : Nat := 3696215009733980144482883

theorem tailTrace_7198353 : CollatzResearch.WordTrace tailWord_7198353 prefixEnd_7198353 3696215009733980144482883 := by
  unfold tailWord_7198353
  simp only [CollatzResearch.WordTrace]
  refine ⟨262545502890603936661503713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175030335260402624441002475 262545502890603936661503713)
  ·
    refine ⟨196909127167952952496127785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262545502890603936661503713 196909127167952952496127785)
    ·
      refine ⟨147681845375964714372095839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196909127167952952496127785 147681845375964714372095839)
      ·
        refine ⟨221522768063947071558143759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147681845375964714372095839 221522768063947071558143759)
        ·
          refine ⟨332284152095920607337215639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221522768063947071558143759 332284152095920607337215639)
          ·
            refine ⟨498426228143880911005823459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332284152095920607337215639 498426228143880911005823459)
            ·
              refine ⟨747639342215821366508735189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498426228143880911005823459 747639342215821366508735189)
              ·
                refine ⟨17522797083183313277548481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 747639342215821366508735189 17522797083183313277548481)
                ·
                  refine ⟨13142097812387484958161361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17522797083183313277548481 13142097812387484958161361)
                  ·
                    refine ⟨9856573359290613718621021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13142097812387484958161361 9856573359290613718621021)
                    ·
                      refine ⟨3696215009733980144482883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9856573359290613718621021 3696215009733980144482883)
                      ·
                        rfl

theorem cell23_7198353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_7198353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198353 prefixEnd_7198353 := by exact prefixLift 7198353
  have htrace : WordTrace (prefixWord ++ tailWord_7198353) baseStart_7198353 baseEnd_7198353 := by
    simpa [prefixWord, tailWord_7198353, baseEnd_7198353] using wordTrace_append hprefix tailTrace_7198353
  have hstable : (prefixWord ++ tailWord_7198353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198353).length < 2 ^ (prefixWord ++ tailWord_7198353).sum := by decide
  have hdescent : baseEnd_7198353 < baseStart_7198353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198373 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 6]
def baseStart_7198373 : Nat := 118140960795 + 7198373 * 2 ^ 59
def prefixEnd_7198373 : Nat := 4983230072969 + 3 ^ 40 * 7198373 * 2
def baseEnd_7198373 : Nat := 410691697705230007359199

theorem tailTrace_7198373 : CollatzResearch.WordTrace tailWord_7198373 prefixEnd_7198373 410691697705230007359199 := by
  unfold tailWord_7198373
  simp only [CollatzResearch.WordTrace]
  refine ⟨262546232350531480077231773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175030821567020986718154515 262546232350531480077231773)
  ·
    refine ⟨98454837131449305028961915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262546232350531480077231773 98454837131449305028961915)
    ·
      refine ⟨147682255697173957543442873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98454837131449305028961915 147682255697173957543442873)
      ·
        refine ⟨110761691772880468157582155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147682255697173957543442873 110761691772880468157582155)
        ·
          refine ⟨166142537659320702236373233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110761691772880468157582155 166142537659320702236373233)
          ·
            refine ⟨124606903244490526677279925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166142537659320702236373233 124606903244490526677279925)
            ·
              refine ⟨11681897179170986875994993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124606903244490526677279925 11681897179170986875994993)
              ·
                refine ⟨8761422884378240156996245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11681897179170986875994993 8761422884378240156996245)
                ·
                  refine ⟨410691697705230007359199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8761422884378240156996245 410691697705230007359199)
                  ·
                    rfl

theorem cell23_7198373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_7198373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198373 prefixEnd_7198373 := by exact prefixLift 7198373
  have htrace : WordTrace (prefixWord ++ tailWord_7198373) baseStart_7198373 baseEnd_7198373 := by
    simpa [prefixWord, tailWord_7198373, baseEnd_7198373] using wordTrace_append hprefix tailTrace_7198373
  have hstable : (prefixWord ++ tailWord_7198373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198373).length < 2 ^ (prefixWord ++ tailWord_7198373).sum := by decide
  have hdescent : baseEnd_7198373 < baseStart_7198373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
